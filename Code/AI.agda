{-# OPTIONS --guardedness #-}
module Code.AI where

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; concatMap; map; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList; unlines) renaming (_++_ to _++ˢ_)
import Data.Char as Char
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import System.Environment.Primitive using (lookupEnv)
open import OwnershipIO using (RunningIO)
open import OwnershipIO.FFI
open import Code using (_==ˢ_; eqList; elemᵇ; filterᵇ; anyᵇ)
open import Code.Protocol public using (AIReq; propose; accept; forkNode; bindNode; AIReply; aiReply)
open import Code.Prompt using (PromptHeader; nativeHeader)
open import Code.SExpr using (escape; str; showSExpr)

record CodexConfig : Set where
  constructor codexConfig
  field
    executable model effort serviceTier scratch sessions : String
    timeoutMs : ℕ
    mcpMode repoDir workspace refFile narrowLog : String
    ancestorDirs : List String
open CodexConfig public

defaultCodex : String → CodexConfig
defaultCodex dir = codexConfig
  "/root/.local/bin/codex" "gpt-6.2-sol" "max" "ultrafast"
  (dir ++ˢ "/ai") (dir ++ˢ "/threads") 0
  "node" "" "" "" (dir ++ˢ "/narrowing-events.jsonl") []

nodeCodex : String → String → List String → CodexConfig
nodeCodex repo dir ancestors = record (defaultCodex dir)
  { mcpMode = "node" ; repoDir = repo ; ancestorDirs = ancestors }

sessionCodex : String → String → String → CodexConfig
sessionCodex repo ws refPath = record (defaultCodex ws)
  { mcpMode = "session" ; repoDir = repo ; workspace = ws ; refFile = refPath ; narrowLog = ws ++ˢ "/narrowing-events.jsonl" }

data Backend : Set where
  CodexCLIBackend : CodexConfig → Backend
  ScriptedBackend : List String → Backend
  ServiceBackend : IO.IO (RunningIO AIReq AIReply (⊤ × ⊤)) → Backend
  ParallelServiceBackend : IO.IO (RunningIO AIReq AIReply (⊤ × ⊤)) → Backend
  RawHTTPBackend : String → List String → PromptHeader → Backend

isConcurrentBackend : Backend → Bool
isConcurrentBackend (CodexCLIBackend _)        = true
isConcurrentBackend (ParallelServiceBackend _) = true
isConcurrentBackend (RawHTTPBackend _ _ _)     = true
isConcurrentBackend (ScriptedBackend _)        = false
isConcurrentBackend (ServiceBackend _)         = false

withBackendAncestors : String → List String → Backend → Backend
withBackendAncestors repo dirs (CodexCLIBackend cfg) =
  CodexCLIBackend (record cfg
    { repoDir = if repoDir cfg ==ˢ "" then repo else repoDir cfg
    ; ancestorDirs = dirs })
withBackendAncestors _ _ b = b

withBackendNarrowLog : String → Backend → Backend
withBackendNarrowLog logPath (CodexCLIBackend cfg) =
  CodexCLIBackend (record cfg { narrowLog = logPath })
withBackendNarrowLog _ b = b

private
  infixl 1 _>>=_ _>>_
  _>>=_ = IO._>>=_
  _>>_ : ∀ {a b} {A : Set a} {B : Set b} → IO.IO A → IO.IO B → IO.IO B
  m >> n = m >>= λ _ → n

record SessionState : Set where
  constructor sessionState
  field
    mainThread scratchThread slot : String
open SessionState

private
  record TrackedSession : Set where
    constructor tracked
    field
      session : SessionState
      ownedScratch durableThreads : List String
  open TrackedSession

  withoutThread : String → List String → List String
  withoutThread tid = filterᵇ (λ other → not (tid ==ˢ other))

  rememberDurable : String → TrackedSession → TrackedSession
  rememberDurable "" s = s
  rememberDurable tid s = record s
    { session = record (session s) { scratchThread = if tid ==ˢ draft then "" else draft }
    ; ownedScratch = withoutThread tid (ownedScratch s)
    ; durableThreads = tid ∷ withoutThread tid (durableThreads s) }
    where draft = scratchThread (session s)

  bindMain : String → String → TrackedSession → TrackedSession
  bindMain tid n s = rememberDurable tid (record s { session = sessionState tid "" n })

  isUUID : String → Bool
  isUUID tid = eqList digitOrDash (toList "xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx") (toList tid)
    where
      digitOrDash : Char.Char → Char.Char → Bool
      digitOrDash '-' c = c Char.≈ᵇ '-'
      digitOrDash _   c = Char.isHexDigit c

  rolloutDirectory : IO.IO String
  rolloutDirectory = lookupEnv "CODEX_HOME" >>= λ where
      (just dir) → if dir ==ˢ "" then defaultDir else IO.return (dir ++ˢ "/sessions")
      nothing → defaultDir
    where
      defaultDir : IO.IO String
      defaultDir = lookupEnv "HOME" >>= λ where
        nothing → IO.return ""
        (just dir) → IO.return (if dir ==ˢ "" then "" else dir ++ˢ "/.codex/sessions")

  -- Match only regular session files. find -P never descends through a symlink.
  removeThreadFiles : String → String → IO.IO ⊤
  removeThreadFiles "" _ = IO.return tt
  removeThreadFiles dir tid = dirExists dir >>= λ where
    false → IO.return tt
    true → absolutePath dir >>= λ path → readProcessAt "" 0 "find"
      ("-P" ∷ path ∷ "-ignore_readdir_race" ∷ "-type" ∷ "f" ∷ "(" ∷
       "-name" ∷ (tid ++ˢ ".thread") ∷ "-o" ∷ "-name" ∷ (tid ++ˢ ".jsonl") ∷
       "-o" ∷ "-name" ∷ ("rollout-????-??-??T??-??-??-" ++ˢ tid ++ˢ ".jsonl") ∷ ")" ∷ "-delete" ∷ []) "" >>= λ where
        (procResult zero _ _) → IO.return tt
        (procResult (suc _) _ err) → failIO ("cannot retire scratch thread " ++ˢ tid ++ˢ ": " ++ˢ err)

  startsWithChars : List Char.Char → List Char.Char → Maybe (List Char.Char)
  startsWithChars [] ys = just ys
  startsWithChars (_ ∷ _) [] = nothing
  startsWithChars (x ∷ xs) (y ∷ ys) = if Char.toℕ x ≡ᵇ Char.toℕ y then startsWithChars xs ys else nothing

  findLastLoop : List Char.Char → List Char.Char → Maybe (List Char.Char) → Maybe (List Char.Char)
  findLastLoop pat [] best with startsWithChars pat []
  ... | just after = just after
  ... | nothing = best
  findLastLoop pat ys@(_ ∷ rest) best with startsWithChars pat ys
  ... | just after = findLastLoop pat rest (just after)
  ... | nothing = findLastLoop pat rest best

  hasSubstring : String → String → Bool
  hasSubstring pat txt with findLastLoop (toList pat) (toList txt) nothing
  ... | just _  = true
  ... | nothing = false

  retryDelta : String → String
  retryDelta prompt with findLastLoop (toList "\nTRANSIENT DIAGNOSTIC\n") (toList prompt) nothing
  ... | nothing = prompt
  ... | just after =
    "Your previous proposal in this turn was rejected by a mechanical gate. "
    ++ˢ "Use `read_draft` / `patch_draft` and `check_agda` (or `check_spec` / `check_entry` / `run_agda_script`) in your scratch draft store to make minimal targeted fixes without rewriting unchanged code, then output the corrected envelope referencing `@<name>` (do not mention compiler/gate retries in `why`):\n\nTRANSIENT DIAGNOSTIC\n"
    ++ˢ fromList after

  envOr : String → String → IO.IO String
  envOr var fallback = lookupEnv var >>= λ where
    (just v) → IO.return (if v ==ˢ "" then fallback else v)
    nothing  → IO.return fallback

  quoteToml : String → String
  quoteToml s = showSExpr (str s)

  joinComma : List String → String
  joinComma []       = ""
  joinComma (x ∷ []) = x
  joinComma (x ∷ xs) = x ++ˢ "," ++ˢ joinComma xs

  mcpTomlFlag : CodexConfig → String → IO.IO (List String)
  mcpTomlFlag cfg isolated = do
    effRepo ← if repoDir cfg ==ˢ "" then currentDirectory else IO.return (repoDir cfg)
    let mcpBin = effRepo ++ˢ "/runtime/lean-prism/.lake/build/bin/agda2lean"
        libDir = effRepo ++ˢ "/runtime/lean-prism/.lake/build/lib/lean"
        irDir  = effRepo ++ˢ "/runtime/lean-prism/.lake/build/ir"
        dumpB  = effRepo ++ˢ "/dump/dump"
        ctxDir = isolated ++ˢ "/mcp"
    hasMcp ← fileExists mcpBin
    if not hasMcp then IO.return [] else do
      mkdirP (ctxDir ++ˢ "/drafts")
      let modeStr = if mcpMode cfg ==ˢ "session" then "session" else "node"
          extraArgs = if modeStr ==ˢ "session"
            then ("--workspace" ∷ workspace cfg ∷ "--ref-file" ∷ refFile cfg ∷ [])
            else []
          narrowArgs = if narrowLog cfg ==ˢ "" then [] else ("--narrow-log" ∷ narrowLog cfg ∷ [])
          allArgs = "mcp" ∷ "--mode" ∷ modeStr ∷ "--repo" ∷ effRepo
                    ∷ "--lib-dir" ∷ libDir ∷ "--ir-dir" ∷ irDir
                    ∷ "--dump-bin" ∷ dumpB ∷ "--ctx-dir" ∷ ctxDir ∷ extraArgs ++ narrowArgs
          tomlArr = "[" ++ˢ joinComma (map quoteToml allArgs) ++ˢ "]"
          tomlVal = "mcp_servers.codetransport={command=" ++ˢ quoteToml mcpBin
                    ++ˢ ",args=" ++ˢ tomlArr
                    ++ˢ ",startup_timeout_sec=30,tool_timeout_sec=300}"
      IO.return ("-c" ∷ tomlVal ∷ [])

  stageAncestorsForMCP : List String → String → IO.IO ⊤
  stageAncestorsForMCP [] _ = IO.return tt
  stageAncestorsForMCP dirs isolated = do
    let ancDst = isolated ++ˢ "/mcp/ancestors"
    removeAll ancDst
    mkdirP ancDst
    copyDirs 0 dirs ancDst
    where
      copyDirs : ℕ → List String → String → IO.IO ⊤
      copyDirs _ [] _ = IO.return tt
      copyDirs idx (d ∷ ds) dst = do
        ex ← dirExists d
        (if ex then
          readProcessAt "" 30000 "cp" ("-R" ∷ (d ++ˢ "/.") ∷ dst ∷ []) "" >> IO.return tt
         else IO.return tt)
        copyDirs (suc idx) ds dst

  endsWithBlock : String → Maybe String
  endsWithBlock fn with reverse (toList fn)
  ... | 'k' ∷ 'c' ∷ 'o' ∷ 'l' ∷ 'b' ∷ '.' ∷ revStem = just (fromList (reverse revStem))
  ... | _ = nothing

  -- Automatically append any `@<stem>` saved via `write_draft` / `patch_draft`
  -- that is referenced in `txt` without an inline ```agda <stem> fence, saving
  -- thousands of output tokens on large modules and incremental retries!
  attachSavedDrafts : String → String → IO.IO String
  attachSavedDrafts isolated txt = do
    let dDir = isolated ++ˢ "/mcp/drafts"
    ex ← dirExists dDir
    if not ex then IO.return txt else do
      files ← listDirectory dDir
      collect dDir files txt
    where
      collect : String → List String → String → IO.IO String
      collect _ [] acc = IO.return acc
      collect dDir (f ∷ fs) acc with endsWithBlock f
      ... | nothing = collect dDir fs acc
      ... | just stem =
        let refTag   = "@" ++ˢ stem
            fenceTag = "```agda " ++ˢ stem
        in if hasSubstring refTag acc ∧ not (hasSubstring fenceTag acc) then
             (F.readFile (dDir ++ˢ "/" ++ˢ f) >>= λ body →
              collect dDir fs (acc ++ˢ "\n```agda " ++ˢ stem ++ˢ "\n" ++ˢ body ++ˢ "\n```\n"))
           else collect dDir fs acc

baseArgsWith : String → String → String → String → String → List String → List String
baseArgsWith modelStr effortStr tierStr isolated output extra =
  let tierArgs = if tierStr ==ˢ "" then [] else ("-c" ∷ ("service_tier=" ++ˢ quoteToml tierStr) ∷ [])
  in "exec" ∷ "--skip-git-repo-check" ∷ "-s" ∷ "read-only" ∷ "-C" ∷ isolated
     ∷ "-m" ∷ modelStr
     ∷ "-c" ∷ ("model_reasoning_effort=" ++ˢ quoteToml effortStr)
     ∷ tierArgs
     ++ ("-c" ∷ "approval_policy=\"never\""
         ∷ "-c" ∷ "features.shell_tool=false"
         ∷ "-c" ∷ "features.unified_exec=false"
         ∷ "-c" ∷ "features.multi_agent=false" ∷ extra)
     ++ ("--json" ∷ "-o" ∷ output ∷ [])

baseArgs : CodexConfig → String → String → List String
baseArgs cfg isolated output =
  baseArgsWith (model cfg) (effort cfg) (serviceTier cfg) isolated output []

private
  invokeWith : CodexConfig → Bool → String → String → List String → String → IO.IO AIReply
  invokeWith cfg enableMCP effortOverride isolated mode prompt = do
    effModel  ← envOr "CODETRANSPORT_MODEL" (model cfg)
    effEffort ← if effortOverride ==ˢ "" then envOr "CODETRANSPORT_EFFORT" (effort cfg) else IO.return effortOverride
    effTier   ← envOr "CODETRANSPORT_SERVICE_TIER" (serviceTier cfg)
    mcpExtra  ← if enableMCP then mcpTomlFlag cfg isolated else IO.return []
    files     ← freshDirectory (scratch cfg)
    let args = baseArgsWith effModel effEffort effTier isolated (files ++ˢ "/last") mcpExtra ++ mode ++ ("-" ∷ [])
    res ← readProcessAt isolated (timeoutMs cfg) (executable cfg) args prompt
    case res of λ where
      (procResult zero events _) → do
        exists ← fileExists (files ++ˢ "/last")
        rawTxt ← if exists then F.readFile (files ++ˢ "/last") else IO.return ""
        txt    ← if enableMCP then attachSavedDrafts isolated rawTxt else IO.return rawTxt
        removeAll files
        IO.return (aiReply txt (jsonString "thread_id" events))
      (procResult (suc _) out err) → do
        removeAll files
        IO.return (aiReply ("AI process failed: " ++ˢ out ++ˢ err) "")
    where open import Function.Base using (case_of_)

invoke : CodexConfig → String → List String → String → IO.IO AIReply
invoke cfg = invokeWith cfg false ""

-- A durable thread contains only initialization and accepted semantic changes.
-- Each semantic turn forks one temporary scratch thread that retains draft context
-- (including its MCP draft blocks!) across mechanical retries and is discarded
-- as soon as the turn is accepted.
codexService : CodexConfig → IO.IO (RunningIO AIReq AIReply (⊤ × ⊤))
codexService cfg = freshDirectory (scratch cfg) >>= λ isolated →
  stageAncestorsForMCP (ancestorDirs cfg) isolated >>
  newIORef (tracked (sessionState "" "" "") [] []) >>= λ ref → IO.return (record
    { onCall = request isolated ref
    ; onStop = replaceScratch isolated ref "" >> removeAll isolated >> IO.return (tt , tt) })
  where
    retire : List String → IO.IO ⊤
    retire [] = IO.return tt
    retire (tid ∷ rest) = do
      removeThreadFiles (sessions cfg) tid
      dir ← rolloutDirectory
      removeThreadFiles dir tid
      retire rest

    -- Only proposal forks acquire scratch ownership. Keep retired IDs in the
    -- ledger until unlink succeeds, so a failed cleanup can be retried at stop.
    replaceScratch : String → IORef TrackedSession → String → IO.IO ⊤
    replaceScratch isolated ref tid = do
      s ← readIORef ref
      let draft = if elemᵇ _==ˢ_ tid (durableThreads s) then "" else tid
          owned = if isUUID draft then draft ∷ [] else []
          retired = withoutThread draft (ownedScratch s)
          next = record s { session = record (session s) { scratchThread = draft } ; ownedScratch = owned }
      writeIORef ref (record next { ownedScratch = owned ++ retired })
      retire retired
      (if draft ==ˢ "" then removeAll (isolated ++ˢ "/mcp/drafts") else IO.return tt)
      writeIORef ref next

    ensure : String → IORef TrackedSession → IO.IO String
    ensure isolated ref = readIORef ref >>= λ s →
      if mainThread (session s) ==ˢ "" then
        (invokeWith cfg false "low" isolated [] "You are one CodeTransport ownership node. Only accepted Agda submissions and semantic reasons are durable. Reply READY." >>= λ r →
        let tid = AIReply.threadId r in if tid ==ˢ "" then IO.return "" else
        (writeIORef ref (bindMain tid (slot (session s)) s) >>
         mkdirP (sessions cfg) >> F.writeFile (sessions cfg ++ˢ "/" ++ˢ tid ++ˢ ".thread") tid >>
         IO.return tid))
      else IO.return (mainThread (session s))

    forkScratch : String → IORef TrackedSession → SessionState → String → IO.IO AIReply
    forkScratch isolated ref s prompt = do
      removeAll (isolated ++ˢ "/mcp/drafts")
      mkdirP (isolated ++ˢ "/mcp/drafts")
      mkdirP (scratch cfg)
      F.writeFile (scratch cfg ++ˢ "/" ++ˢ slot s ++ˢ ".latest-prompt") prompt
      r ← invokeWith cfg true "" isolated ("fork" ∷ mainThread s ∷ []) prompt
      replaceScratch isolated ref (AIReply.threadId r)
      IO.return r

    request : String → IORef TrackedSession → AIReq → IO.IO AIReply
    request isolated ref (bindNode n inherited) = choose inherited
      where
        save : String → IO.IO AIReply
        save tid = readIORef ref >>= λ s →
          writeIORef ref (bindMain tid n s) >>
          replaceScratch isolated ref "" >> mkdirP (sessions cfg) >>
          F.writeFile (sessions cfg ++ˢ "/" ++ˢ n ++ˢ ".id") tid >> IO.return (aiReply "bound" tid)
        choose : Maybe String → IO.IO AIReply
        choose (just tid) = save tid
        choose nothing = fileExists (sessions cfg ++ˢ "/" ++ˢ n ++ˢ ".id") >>= λ where
          true → F.readFile (sessions cfg ++ˢ "/" ++ˢ n ++ˢ ".id") >>= save
          false → ensure isolated ref >>= save
    request isolated ref (propose prompt retry context) = do
      -- Refresh the read-only MCP view on retries as well as fresh forks.
      mkdirP (isolated ++ˢ "/mcp")
      F.writeFile (isolated ++ˢ "/mcp/node-prompt.txt") prompt
      if context ==ˢ "" then removeAll (isolated ++ˢ "/mcp/plan-context.sexp")
        else F.writeFile (isolated ++ˢ "/mcp/plan-context.sexp") context
      tid ← ensure isolated ref
      s ← readIORef ref
      let state = session s
      r ← if tid ==ˢ "" then IO.return (aiReply "AI thread initialization failed; retry binding before proposing" "")
       else if retry ∧ not (scratchThread state ==ˢ "") then
         (let delta = retryDelta prompt in
          F.putStrLn ("Retrying " ++ˢ slot state ++ˢ " on scratch (" ++ˢ scratchThread state ++ˢ ")") >>
          mkdirP (scratch cfg) >>
          F.writeFile (scratch cfg ++ˢ "/" ++ˢ slot state ++ˢ ".latest-prompt") delta >>
          invokeWith cfg true "" isolated ("resume" ∷ scratchThread state ∷ []) delta >>= λ r →
          if AIReply.threadId r ==ˢ "" then
            (F.putStrLn ("Scratch resume failed; forking fresh scratch from " ++ˢ tid) >>
             forkScratch isolated ref state prompt)
          else IO.return r)
       else
         (F.putStrLn ("Planning " ++ˢ slot state ++ˢ " (" ++ˢ tid ++ˢ ")") >>
          forkScratch isolated ref state prompt)
      mkdirP (scratch cfg)
      F.writeFile (scratch cfg ++ˢ "/" ++ˢ slot state ++ˢ ".latest-reply") (AIReply.text r)
      IO.return (aiReply (AIReply.text r) tid)
    request isolated ref (accept summary) = ensure isolated ref >>= λ tid →
      replaceScratch isolated ref "" >>
      invokeWith cfg false "low" isolated ("resume" ∷ tid ∷ []) ("Accepted semantic change and compiler-verified implementation:\n" ++ˢ summary ++ˢ "\nAcknowledge only.") >>= λ r →
      F.writeFile (sessions cfg ++ˢ "/" ++ˢ tid ++ˢ ".accepted") summary >> IO.return (aiReply (AIReply.text r) tid)
    request isolated ref (forkNode name) = ensure isolated ref >>= λ tid →
      invokeWith cfg false "low" isolated ("fork" ∷ tid ∷ []) ("You now own child node " ++ˢ name ++ˢ ". Reply READY.") >>= λ r →
      readIORef ref >>= λ s → writeIORef ref (rememberDurable (AIReply.threadId r) s) >> IO.return r

scriptedService : List String → IO.IO (RunningIO AIReq AIReply (⊤ × ⊤))
scriptedService replies = newIORef replies >>= λ ref → IO.return (record
  { onCall = scripted ref
  ; onStop = IO.return (tt , tt) })
  where
    scripted : IORef (List String) → AIReq → IO.IO AIReply
    scripted ref (bindNode n _) = IO.return (aiReply "bound" ("scripted/" ++ˢ n))
    scripted ref (propose _ _ _) = readIORef ref >>= λ where
      [] → failIO "ScriptedBackend exhausted before a valid verdict/finish"
      (r ∷ rs) → writeIORef ref rs >> IO.return (aiReply r "scripted")
    scripted ref (accept _) = IO.return (aiReply "accepted" "scripted")
    scripted ref (forkNode n) = IO.return (aiReply "" ("scripted/" ++ˢ n))

httpService : String → List String → PromptHeader → RunningIO AIReq AIReply (⊤ × ⊤)
httpService endpoint headers header = record
  { onCall = request
  ; onStop = IO.return (tt , tt) }
  where
    request : AIReq → IO.IO AIReply
    request (bindNode n _) = IO.return (aiReply "bound" n)
    request (propose prompt _ _) = readProcessAt "" 120000 "curl"
      ("--fail-with-body" ∷ "--silent" ∷ "--show-error" ∷ "-H" ∷ "Content-Type: application/json" ∷ concatMap (λ h → "-H" ∷ h ∷ []) headers ++
       ("--data-binary" ∷ "@-" ∷ endpoint ∷ []))
      ("{\"input\":\"" ++ˢ escape (header ++ˢ "\n" ++ˢ prompt) ++ˢ "\"}") >>= λ where
        (procResult zero out _) → IO.return (aiReply (jsonString "output_text" out) "http")
        (procResult (suc _) out err) → IO.return (aiReply (out ++ˢ err) "http")
    request (accept _) = IO.return (aiReply "accepted" "http")
    request (forkNode _) = IO.return (aiReply "" "http")

aiService : Backend → IO.IO (RunningIO AIReq AIReply (⊤ × ⊤))
aiService (CodexCLIBackend cfg) = codexService cfg
aiService (ScriptedBackend rs) = scriptedService rs
aiService (ServiceBackend service) = service
aiService (ParallelServiceBackend service) = service
aiService (RawHTTPBackend endpoint headers header) = IO.return (httpService endpoint headers header)

-- Scope threads by tree, including offline backends, without changing node
-- semantics. Each bind is recorded, including inherited child forks.
trackedService : String → Backend → IO.IO (RunningIO AIReq AIReply (⊤ × ⊤))
trackedService dir backend = aiService (scoped backend) >>= λ srv → IO.return (record
  { onCall = λ req → OwnershipIO.onCall srv req >>= recordReply req
  ; onStop = OwnershipIO.onStop srv })
  where
    scoped : Backend → Backend
    scoped (CodexCLIBackend cfg) = CodexCLIBackend (record cfg { sessions = dir })
    scoped b = b
    recordReply : AIReq → AIReply → IO.IO AIReply
    recordReply (bindNode n _) reply = mkdirP dir >>
      F.writeFile (dir ++ˢ "/" ++ˢ n ++ˢ ".id") (AIReply.threadId reply) >> IO.return reply
    recordReply _ reply = IO.return reply
