{-# OPTIONS --guardedness #-}
module Code.SessionRunner where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; concatMap; map; take; reverse; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; wordsBy; unlines; intersperse; lines; toList; fromList) renaming (_++_ to _++ˢ_)
open import Agda.Builtin.Char using (primCharEquality)
import Data.Char as Char
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership using (Prog; Dir)
open import OwnershipIO hiding (ext)
open import OwnershipIO.FFI
open import Code.Transport using (Verdict; ok; contradiction)
open import Code.Harness using (NodeΨ; NodeTask; nodeAgent; HomeShape; HomeSt; ChildS)
open import Code.Codecs using (HomeValue; storeHome)
open import Code.Driver using (writeSource; moduleNameOf; nodeEnvironmentWith; nodeEnvironmentForBackend)

-- The sole unbounded loop is an outer IO observer. Each call remains a finite
-- ownership transaction, and stop always returns the dynamically indexed home.
{-# NON_TERMINATING #-}
awaitNode : OfferIO ChildS → IO.IO Verdict
awaitNode srv = onCall srv tt IO.>>= λ where
  nothing → awaitNode srv
  (just v) → IO.return v

runNode : EnvIO NodeΨ → NodeTask → HomeValue → IO.IO (Verdict × HomeValue)
runNode env task (sh , home) = provideIO env (nodeAgent sh) home IO.>>= λ receive →
  receive task IO.>>= λ srv → awaitNode srv IO.>>= λ verdict →
  onStop srv IO.>>= λ next → IO.return (verdict , next)

runAndStore : String → EnvIO NodeΨ → NodeTask → HomeValue → IO.IO Verdict
runAndStore path env task home = runNode env task home IO.>>= λ { (v , next) →
  storeHome path next IO.>>= λ _ → IO.return v }

-- An open-world session may evaluate any typed Prog selected from its Registry.
runProbe : ∀ {Ψ Γ A} → EnvIO Ψ → Prog Ψ (Dir Γ) (Dir Γ) A → ModelsIO Γ → IO.IO (ModelsIO Γ × A)
runProbe = evalIO

open import Code hiding (Name; set)
open import Code.Transport using (nullᵇ; specΔ; stubOf; specCheckOf; specImplOK; specProblem; newIface; child; keep; _⇝_)
open import Code.Tree using (node; codeOf; codesOf)
open import Code.Codecs using (loadHome; homeNoChan)
open import Code.Protocol
import Code.PolyTransport as PT
import Code.NodeTransport as NT
import Code.Namespace as NS
open import Code.TreeSnapshot using (freezeHome)
import Meta.Boundary as Boundary
import Meta.Sandbox as Sandbox
import Store.CAS as CAS
open import Store.Verify using (verifyCommitDAG)
open import OwnershipIO.MetaFFI using (catchIO; replaceDuring; withTreeLock)
open import Code.Lift using (LiftSpec; ChildLift; EndpointLift; baseMod; upperMod; childLifts; endpoints; baseChild; upperChild; subLift; baseUnit; LiftProblem; wrongBase; wrongUpper; missingChildMap; missingBaseUnit) renaming (liftSpec to mkLiftSpec)
open import Code.Parse using (parseLift)
open import Code.Render using (render)
open import Code.AgdaTool using (writeCodes; modulePath)
open import Code.AI using (Backend; trackedService; isConcurrentBackend; withBackendAncestors)
open import Code.Prompt using (sessionTemplate; sessionTransportHelp; showLiftProblem; showImplProblem)
open import Code.SExpr using (list; str; sym; showSExpr)
open import Code.SessionProtocol
open import Code.SessionWorkspace
open import Backend.Switch using (leanPrism; resolveBackendMode; switchDump; switchCheck; switchSessionCompileExe; checkCandidateEntrySafe)

private
  infixl 1 _>>=_ _>>_
  _>>=_ = IO._>>=_
  _>>_ : ∀ {a b} {A : Set a} {B : Set b} → IO.IO A → IO.IO B → IO.IO B
  m >> n = m >>= λ _ → n

record SessionConfig : Set where
  constructor sessionConfig
  field
    repository workspace goal : String
    reference : RefSpec
    sessionBackend : Backend
    treeBackend : String → Backend
open SessionConfig public

lastPart : List String → String
lastPart [] = "Main"
lastPart (s ∷ []) = s
lastPart (_ ∷ ss) = lastPart ss

executableName : String → String
executableName src with moduleNameOf src
... | nothing = "Main"
... | just n = lastPart (wordsBy ('.' Char.≟_) n)

-- Compile all four static C relays (`term-relay`, `fs-relay`, `net-relay`, `git-relay`)
-- once into `tmp/term-build/` so `SessionEnv` has the full sandboxed tool suite.
private
  buildRelayC : String → String → String → IO.IO Bool
  buildRelayC repo src bin = fileExists bin >>= λ built →
    if built then IO.return true else
      mkdirP (repo ++ˢ "/tmp/term-build") >> readProcessAt repo 120000 "cc"
        ("-std=c11" ∷ "-O2" ∷ "-Wall" ∷ "-Wextra" ∷ "-Werror" ∷ "-static"
        ∷ src ∷ "-o" ∷ bin ∷ []) "" >>= λ where
          (procResult zero _ _) → IO.return true
          _ → IO.return false

ensureRelay : String → IO.IO (Maybe String)
ensureRelay repo = do
  let base = repo ++ˢ "/tmp/term-build"
      tBin = base ++ˢ "/term-relay"
      fBin = base ++ˢ "/fs-relay"
      nBin = base ++ˢ "/net-relay"
      gBin = base ++ˢ "/git-relay"
      wBin = base ++ˢ "/web-relay"
  okT ← buildRelayC repo "runtime/term-relay.c"       tBin
  okF ← buildRelayC repo "runtime/tools/fs-relay.c"   fBin
  okN ← buildRelayC repo "runtime/tools/net-relay.c"  nBin
  okG ← buildRelayC repo "runtime/tools/git-relay.c"  gBin
  okW ← buildRelayC repo "runtime/tools/web-relay.c"  wBin
  if okT ∧ okF ∧ okN ∧ okG ∧ okW then IO.return (just tBin) else IO.return nothing

compileInWith : Bool → String → String → String → List String → String → IO.IO ProcResult
compileInWith staticLink ghcObjDir repo dir incs file = do
  cliHostC ← absolutePath (repo ++ˢ "/runtime/cli_host.c")
  let outDir = if ghcObjDir ==ˢ "" then "build" else ghcObjDir
      staticFlags = if staticLink then ("--ghc-flag=-optl-static" ∷ "--ghc-flag=-optl-pthread" ∷ []) else []
  mkdirP outDir
  readProcessAt dir 0 "agda"
    ("--compile" ∷ "--ghc-flag=-O0"
     ∷ "--ghc-flag=-iruntime" ∷ "--ghc-flag=-iruntime/tools"
     ∷ ("--ghc-flag=-i" ++ˢ repo ++ˢ "/runtime")
     ∷ ("--ghc-flag=-i" ++ˢ repo ++ˢ "/runtime/tools")
     ∷ ("--ghc-flag=" ++ˢ cliHostC)
     ∷ staticFlags
     ++ ("--compile-dir=build" ∷ "--ghc-flag=-outputdir" ∷ ("--ghc-flag=" ++ˢ outDir)
         ∷ includeArgs ("." ∷ incs) ++ (file ∷ []))) ""

compileIn : String → String → List String → String → IO.IO ProcResult
compileIn = compileInWith false ""

quoted : String → String
quoted s = showSExpr (str s)

sessionEnvSource : RefSpec → String → String → String → String
sessionEnvSource ref candidate relay scratch = unlines
  ("{-# OPTIONS --guardedness #-}" ∷ "module SessionEnv where"
  ∷ "open import Data.List using ([]; _∷_)"
  ∷ "open import Data.Maybe using (just; nothing)"
  ∷ "open import Code.SessionProtocol using (RefSpec; refSpec; local; docker; parseRefSpec)"
  ∷ "open import Code.SessionTools using (sessionTools)"
  ∷ "open import Code.SessionTools public using (SessionΨ)"
  ∷ "open import Code.Driver public using (ProcReq; ProcOut; procReq; outText; ProcSpec; Registry; Pick; SubT; select; all-nil; all-cons)"
  ∷ "open import Code.TermTool public using (ptySpec; TermFiles)"
  ∷ "open import Code.Tools.FsTool public using (fsSpec; FsOwnedCtx)"
  ∷ "open import Code.Tools.NetTool public using (netSpec; NetOwnedCtx)"
  ∷ "open import Code.Tools.GitTool public using (gitSpec; GitOwnedCtx)"
  ∷ "open import Context.Terminal public using (Byte; Bytes; bytes; Key; textKey; enter; escape; backspace; tab; up; down; right; left; ctrl; encodeKey; TermTopology; allTTY; pipeStdioWithTTY; SandboxTarget; localSandbox; dockerSandbox; TermConfig; termConfig; Signal; sigINT; sigTERM; sigHUP; sigQUIT; sigKILL; TermStep; writeStdin; writeTTY; closeStdin; sleepMs; resizeTTY; sendSignal; drainRaw; RawTermObs; rawObs; ttyOut; stdoutOut; stderrOut; exitStatus; emptyObs; appendObs; Screen; blankScreen; stepANSI; screenLines)"
  ∷ "open import Context.Tools.FsSandbox public using (FsNodeKind; regularNode; dirNode; symlinkNode; FsFixture; fixDir; fixFile; fixSymlink; FsConfig; fsConfig; FsStep; runCmd; writeFileStep; mkdirStep; symlinkStep; chmodStep; unlinkStep; snapshotStep; FsEntryObs; fsEntry; RawFsObs; rawFsObs; emptyFsObs; VirtualFs; virtualFs; initVirtualFs; stepVirtualFs; traceVirtualFs; FsDiff; added; modified; removed; diffSnapshot)"
  ∷ "open import Context.Tools.NetSandbox public using (HttpRoute; httpRoute; RawStubRule; rawStubRule; NetTopology; httpStubMode; tcpStubMode; udpStubMode; daemonProbeMode; httpDelayedStubMode; tcpDelayedStubMode; NetConfig; netConfig; encodeHttpReq; encodeHttpResp; HttpReqView; httpReqView; HttpRespView; httpRespView; parseHttpReq; parseHttpResp; NetStep; runClient; waitPortReady; tcpProbe; httpProbe; udpProbe; sleepNetMs; drainNet; RawNetObs; rawNetObs; emptyNetObs; wireReply; capturedReqs; timedOut; evalStubExchange)"
  ∷ "open import Context.Tools.GitSandbox public using (GitConfig; gitConfig; GitStep; gitWriteFile; gitRemoveFile; gitStageAll; gitStagePaths; gitCommit; gitSwitchBranch; gitCreateTag; gitStatus; gitRunTarget; GitRepoSummary; gitSummary; RawGitObs; rawGitObs; commitHash; summary; PureGitRepo; initPureGit)"
  ∷ "open import Context.Tools.FuzzGen public using (Seed; mkSeed; nextNat; Gen; runGen; genPure; genMap; genBind; genPair; genBounded; genBool; genByte; genList; genBytes; genChoose; sampleMany; Shrinker; shrinkNat; shrinkByte; shrinkList; shrinkBytes; firstFailure; minimize; fuzzCheck)"
  ∷ "open import Context.World public using (Cap; clockCap; envCap; ttyCap; fsCap; netCap; gitCap; webCap; CliCaps; AllCaps; WorldProg; CliApp; ReactiveApp; SimWorld; defaultSimWorld; cliSimWorld; runWorldPure; runCliPure; runReactivePure)"
  ∷ "open import Ownership public using (≡-inst; withEphemeral)"
  ∷ "open import OwnershipIO public using (EnvIO; RunningIO; OfferIO; evalIO; provideIO)"
  ∷ "reference : RefSpec"
  ∷ ("reference = decode (parseRefSpec " ++ˢ quoted (showSExpr (encodeRefSpec ref)) ++ˢ ")")
  ∷ "  where"
  ∷ "    decode : Data.Maybe.Maybe RefSpec → RefSpec"
  ∷ "    decode (just r) = r"
  ∷ "    decode nothing = refSpec (local \"/bin/false\") [] 30000"
  ∷ "sessionEnv : EnvIO SessionΨ"
  ∷ ("sessionEnv = sessionTools reference " ++ˢ quoted candidate ++ˢ " " ++ˢ quoted relay ++ˢ " " ++ˢ quoted scratch)
  ∷ [])

runInWithCache : String → String → String → List String → String → IO.IO ProcResult
runInWithCache ghcObjDir repo dir incs src = writeSource dir src >>= λ where
  nothing → IO.return (procResult 2 "" "script: missing or unsafe module name")
  (just file) → withoutSource (dir ++ˢ "/includes") file incs >>= λ masked →
    checkIOSource repo (dir ++ˢ "/dump") incs src >>= λ where
      (sourceFailed e) → IO.return (procResult 2 "" e)
      (sourceOK _) → compileInWith false ghcObjDir repo dir masked file >>= λ where
        (procResult (suc c) out err) → IO.return (procResult (suc c) (stripStdlibWarnings out) (stripStdlibWarnings err))
        (procResult zero _ _) → readProcessAt dir 120000 ("./build/" ++ˢ executableName src) [] ""

runIn : String → String → List String → String → IO.IO ProcResult
runIn = runInWithCache ""

-- Bracketed cleanup includes runtime failures and exceptions, as well as dump
-- and compiler rejection. Neither scripts nor their compiler products persist.
runScript : String → List String → String → IO.IO ProcResult
runScript scratch includes source = currentDirectory >>= λ repo → ensureRelay repo >>= λ where
  nothing → IO.return (procResult 2 "" "cannot build sandbox relays")
  (just _) → withTempDirectory scratch λ dir → runIn repo dir includes source

runSessionScript : SessionConfig → String → IO.IO ProcResult
runSessionScript cfg src = ensureRelay (repository cfg) >>= λ where
    nothing → IO.return (procResult 2 "" "cannot build sandbox relays")
    (just relay) → withTreeLock ws (withTempDirectory (ws ++ˢ "/tmp/scripts") λ dir → do
      let scratch  = dir ++ˢ "/resources"
          ghcCache = ws ++ˢ "/tmp/ghc-script-cache"
      mkdirP (dir ++ˢ "/env")
      mkdirP ghcCache
      F.writeFile (dir ++ˢ "/env/SessionEnv.agda")
        (sessionEnvSource (reference cfg) candidate relay scratch)
      result ← withOpenIncludes (repository cfg) ws λ incs →
        runInWithCache ghcCache (repository cfg) dir ((dir ++ˢ "/env") ∷ incs) src
      recordReplay scratch result)
  where
    ws = workspace cfg
    candidate = ws ++ˢ "/bin/candidate"

    -- Keep the build and exported inputs fixed from execution through publication.
    recordReplay : String → ProcResult → IO.IO ProcResult
    recordReplay scratch r@(procResult zero _ _) = do
      usedRef ← fileExists (scratch ++ˢ "/used-ref")
      usedCand ← fileExists (scratch ++ˢ "/used-cand")
      exists ← fileExists candidate
      if usedRef ∧ usedCand ∧ exists then (do
        candHash ← shaFile candidate
        inpHash ← fingerprint ws
        atomicText (ws ++ˢ "/bin/replayed.sha256") (candHash ++ˢ "\n" ++ˢ inpHash)
        IO.return r) else IO.return r
    recordReplay _ r = IO.return r

data ActionResult : Set where
  rejected : String → ActionResult
  accepted : String → ActionResult
  finished : String → ActionResult


chooseLift : List Code → Maybe String → Maybe (Maybe (Code × LiftSpec))
chooseLift cs nothing = just nothing
chooseLift cs (just src) with parseLift src
... | nothing = nothing
... | just l = find cs
  where
    find : List Code → Maybe (Maybe (Code × LiftSpec))
    find [] = nothing
    find (c ∷ cs) = if modName c ==ᴺ baseMod l then just (just (c , l)) else find cs

matchesUpper : Code → Maybe (Code × LiftSpec) → Bool
matchesUpper c nothing = true
matchesUpper c (just (_ , l)) = modName c ==ᴺ upperMod l

-- Validate LiftSpec fields owned by SESSION_ROOT before entering runNode, so a
-- closed-world node is never trapped by a missing base child-map or base unit.
precheckLift : ℕ → List Code → Code → QName → LiftSpec → List LiftProblem
precheckLift zero cs base expectedUpper l = []
precheckLift (suc fuel) cs base expectedUpper l =
  (if modName base ==ᴺ baseMod l then [] else wrongBase ∷ [])
  ++ (if expectedUpper ==ᴺ upperMod l then [] else wrongUpper ∷ [])
  ++ concatMap checkKid reqKids
  ++ concatMap checkEp (endpoints l)
  where
    reqKids : List QName
    reqKids = nubᵇ _==ᴺ_ (map imod (filterᵇ (λ i → not (nullᵇ (assumes i))) (imports base)) ++ map baseChild (childLifts l))
    findCode : QName → List Code → Maybe Code
    findCode q [] = nothing
    findCode q (c ∷ rest) = if modName c ==ᴺ q then just c else findCode q rest
    checkKid : QName → List LiftProblem
    checkKid q with filterᵇ (λ c → baseChild c ==ᴺ q) (childLifts l)
    ... | [] = missingChildMap q ∷ []
    ... | entry ∷ _ with findCode q cs | subLift entry
    ...   | nothing | _ = missingBaseUnit q ∷ []
    ...   | just childBase | just sub = precheckLift fuel cs childBase (upperChild entry) sub
    ...   | just childBase | nothing =
            if anyᵇ (λ c → modName c ==ᴺ upperChild entry) cs then []
            else precheckLift fuel cs childBase (upperChild entry) (mkLiftSpec (baseChild entry) (upperChild entry) [] [])
    checkEp : EndpointLift → List LiftProblem
    checkEp e = if anyᵇ (λ u → uname u ==ᴺ baseUnit e) (units base ++ extUnits base)
      then [] else missingBaseUnit (baseUnit e) ∷ []

chooseTransport : List SealedTree → Maybe String → Maybe NT.Bindings
chooseTransport bs nothing = just []
chooseTransport bs (just src) = PT.parsePolyTransport src Data.Maybe.>>= λ s →
  selectSource s (filterᵇ (λ b → modName (NT.implementation (snapshot b)) ==ᴺ PT.oldModOf s) bs)
  where
    selectSource : PT.TransportSpec → List SealedTree → Maybe NT.Bindings
    selectSource s (b ∷ []) = Data.Maybe.when (NT.validSource (snapshot b) s) ((snapshot b , s) ∷ [])
    selectSource _ _ = nothing

-- A single deduplicated include tree is materialized from the selected sealed
-- commits. Only in-flight interfaces/implementations go into the tool's work
-- directory, so a local stub cannot shadow an ancestor (including a keep).
driveTreeWith : SessionConfig → String → String → String → List String →
                Maybe String → Maybe String → IO.IO ActionResult
driveTreeWith cfg name reason src bases liftSrc transportSrc = catchIO (withTreeLock (workspace cfg) action) (λ e → IO.return (rejected e))
  where
    ws = workspace cfg
    repo = repository cfg
    path = ws ++ˢ "/trees/" ++ˢ name
    storeDir = ws ++ˢ "/store"
    scratch = ws ++ˢ "/tmp/nodes/" ++ˢ name
    dumpBin = repo ++ˢ "/dump/dump"

    publish : BaseClosure → HomeValue → IO.IO ActionResult
    publish b result@(sh , h) = do
      let allCodes = NT.exported (freezeHome sh (dropModel (homeNoChan sh) h))
          codes = uniqueCodes allCodes
      agree ← exportsAgree ws name codes
      if agree ∧ NS.disjointPaths allCodes ∧ consistentCodes (allCodes ++ baseCodes b) then save codes else
        IO.return (rejected "namespace: conflicting implementations at the same module path")
      where
        save : List Code → IO.IO ActionResult
        save codes = do
          prev ← CAS.readRef storeDir (treeRef name)
          let ps = nubᵇ _==ˢ_ (directTips b ++ Data.Maybe.maybe′ (λ k → k ∷ []) [] prev)
          key ← CAS.storeTreeCommit storeDir ps name reason result
          valid ← verifyCommitDAG storeDir key
          if valid then complete codes key else IO.return (rejected "drive-tree: invalid commit DAG")
          where
            complete : List Code → CAS.Hash → IO.IO ActionResult
            complete codes key = publishGeneration ws path bases "ok" result λ stage → do
              inventory ← exportCodes ws name codes
              writeCodes (stage ++ˢ "/generated") codes
              F.writeFile (stage ++ˢ "/modules.tsv") inventory
              replaceDuring (stage ++ˢ "/generated") (ws ++ˢ "/generated/" ++ˢ name)
                (replaceDuring (stage ++ˢ "/modules.tsv") (path ++ˢ "/modules.tsv")
                  (CAS.writeRef storeDir (treeRef name) key))
              IO.return (accepted ("ok " ++ˢ name ++ˢ "\n" ++ˢ unlines (map moduleSummary codes)))

    dispatch : BaseClosure → List String → Maybe (Maybe (Code × LiftSpec)) → Maybe NT.Bindings → IO.IO ActionResult
    dispatch b dirs nothing _ = IO.return (rejected "drive-tree: invalid LiftSpec or baseMod absent from baseTrees")
    dispatch b dirs _ nothing = IO.return (rejected "drive-tree: invalid TransportSpec, source snapshot or nested child mapping")
    dispatch b dirs (just lifting) (just transports′) =
      resolveBackendMode leanPrism >>= λ mode →
      switchDump mode dumpBin repo scratch dirs (dumpReq src [] []) >>= λ where
        (dumpFailed e) → IO.return (rejected e)
        (dumped spec) → validateSpec spec (specProblem (decls spec))
      where
        cs = baseCodes b
        ancestors = map modName cs
        localDeps : List Code → List Code
        localDeps = filterᵇ (λ c → not (elemᵇ _==ᴺ_ (modName c) ancestors))

        liftIssues : Code → Maybe (Code × LiftSpec) → List LiftProblem
        liftIssues spec nothing = []
        liftIssues spec (just (base , l)) = precheckLift (suc (length cs)) cs base (modName spec) l
        validateSpec : Code → Maybe String → IO.IO ActionResult
        execute : Code → Maybe HomeValue → IO.IO ActionResult
        resume : Code → IO.IO ActionResult
        resume spec = readIfExists (path ++ˢ "/verdict") >>= λ v → if v ==ˢ "ok" then
          (entries (ws ++ˢ "/trees") >>= λ trees → resolveTree ws (suc (length trees)) name >>= λ where
            nothing → IO.return (rejected "drive-tree: invalid previous tree ref")
            (just key) → verifyCommitDAG storeDir key >>= λ valid → if valid then
              (CAS.newCommitHomeReader storeDir >>= λ read → (CAS.getCommit storeDir key CAS.>>=? read) >>= λ where
                nothing → IO.return (rejected "drive-tree: missing previous home")
                (just h) → execute spec (just h))
              else IO.return (rejected "drive-tree: invalid previous commit DAG"))
          else loadHome path >>= execute spec
        validateSpec spec (just e) = IO.return (rejected e)
        validateSpec spec nothing with liftIssues spec lifting
        ... | ps@(_ ∷ _) = IO.return (rejected ("drive-tree: invalid LiftSpec for base tree (every base child subpackage must appear in LiftSpec child-map):\n" ++ˢ unlines (map showLiftProblem ps)))
        ... | [] with NS.checkTaskImports (NS.namespaceOf (modName spec)) [] ancestors spec
        ...   | ps@(_ ∷ _) = IO.return (rejected ("namespace: " ++ˢ unlines (map NS.showNamespaceProblem ps)))
        ...   | [] with specImplOK [] spec
        ...     | ps@(_ ∷ _) = IO.return (rejected ("drive-tree: specification closedImplOK:\n" ++ˢ unlines (map showImplProblem ps)))
        ...     | [] = if NS.canonicalRootOK name (modName spec) ∧ flagsOK [] (flagsOf spec) ∧ matchesUpper spec lifting
          ∧ allᵇ (λ e → PT.newModOf (proj₂ e) ==ᴺ modName spec) transports′
          ∧ not (elemᵇ _==ᴺ_ (modName spec) ancestors)
          then (resolveBackendMode leanPrism >>= λ mode →
                switchCheck mode repo scratch dirs
                 (agdaCheck (specCheckOf (specΔ (modName spec) (decls spec) [])) []) >>= λ where
                   Code.Transport.pass → resume spec
                   (Code.Transport.fail e) → IO.return (rejected ("drive-tree: specification failed Agda typecheck:\n" ++ˢ e)))
          else IO.return (rejected "drive-tree: unsafe flags, namespace collision or wrong target module")
        execute spec saved = start (chosen saved)
          where
            d = specΔ (modName spec) (decls spec) []
            chosen : Maybe HomeValue → HomeValue
            chosen nothing = node [] , stubOf d , [] , newIface d , tt
            chosen (just h) = h
            ancestorText : Code → String
            ancestorText c = if anyᵇ (λ i → imod i ==ᴺ modName c) (imports spec)
                              then render c else moduleSummary c
            start : HomeValue → IO.IO ActionResult
            start home@(sh , m) =
              let old = codeOf sh (dropModel (homeNoChan sh) m)
                  seed = map (λ u → if elemᵇ _==ᴼ_ (unit (uname u)) (objects old)
                    then keep (ext (uname u)) else Code.⊥ ⇝ ext (uname u)) (units (stubOf d))
                  task = record (nodeTask (record d { δarrows = seed }) (flagsOf spec) lifting)
                    { baseModules = cs ; transports = transports′ ; allowedAncestors = just ancestors
                    ; contextText = goal cfg ++ˢ "\nANCESTOR MODULES\n" ++ˢ unlines (map ancestorText cs) }
              in if modName old ==ᴺ modName spec then
                (let treeBack = withBackendAncestors repo dirs (treeBackend cfg name) in
                 nodeEnvironmentForBackend (isConcurrentBackend treeBack)
                   (trackedService (ws ++ˢ "/threads/" ++ˢ name) treeBack)
                   (λ req → resolveBackendMode leanPrism >>= λ mode → switchDump mode dumpBin repo scratch dirs (record req { codeDeps = localDeps (codeDeps req) }))
                   (λ req → resolveBackendMode leanPrism >>= λ mode → switchCheck mode repo scratch dirs (record req { dependencies = localDeps (dependencies req) }))
                 >>= λ env → runNode env task home >>= λ where
                   (ok , result) → publish b result
                   (contradiction c , result) → publishGeneration ws path bases "contradiction" result λ _ →
                     IO.return (accepted ("contradiction " ++ˢ name ++ˢ "\n" ++ˢ render c)))
                else IO.return (rejected "drive-tree: saved ownership root differs from specSrc")

    runTree : BaseClosure → IO.IO ActionResult
    runTree b = if elemᵇ _==ˢ_ name (map treeEpoch (sealedBases b))
                   ∨ not (allᵇ (Sandbox.checkObjectModuleSafe false) (baseCodes b))
      then IO.return (rejected "drive-tree: cyclic or unsafe ancestor")
      else withTempDirectory (ws ++ˢ "/tmp/ancestors") λ dir → do
        writeCodes dir (baseCodes b)
        dispatch b (dir ∷ []) (chooseLift (baseCodes b) liftSrc) (chooseTransport (sealedBases b) transportSrc)

    action : IO.IO ActionResult
    action = if safeTree name ∧ not (elemᵇ _==ˢ_ name bases) then
      (loadClosure ws bases >>= λ where
        nothing → IO.return (rejected "baseTrees: missing, conflicting or invalid ancestor")
        (just b) → runTree b)
      else IO.return (rejected "drive-tree: unsafe treeName or direct self-dependency")

driveTree : SessionConfig → String → String → List String → Maybe String → IO.IO ActionResult
driveTree cfg name src bases lifting = driveTreeWith cfg name "" src bases lifting nothing

private
  splitOnDot : String → List String
  splitOnDot s = map fromList (go (toList s))
    where
      consHead : Char.Char → List (List Char.Char) → List (List Char.Char)
      consHead x [] = (x ∷ []) ∷ []
      consHead x (seg ∷ segs) = (x ∷ seg) ∷ segs

      go : List Char.Char → List (List Char.Char)
      go [] = [] ∷ []
      go (c ∷ cs) = if primCharEquality c '.'
                      then [] ∷ go cs
                      else consHead c (go cs)

  splitInitLast : List String → Maybe (List String × String)
  splitInitLast [] = nothing
  splitInitLast (_ ∷ []) = nothing
  splitInitLast (x ∷ y ∷ []) = just (x ∷ [] , y)
  splitInitLast (x ∷ rest@(_ ∷ _ ∷ _)) with splitInitLast rest
  ... | nothing = nothing
  ... | just (ms , lastSeg) = just (x ∷ ms , lastSeg)

  parseEntryTarget : String → Maybe (List String × String)
  parseEntryTarget entry with splitInitLast (splitOnDot entry)
  ... | nothing = nothing
  ... | just (modParts , ident) =
    if Boundary.objectNamespace false modParts ∧ Boundary.validPart ident ∧ not (ident ==ˢ "_")
      then just (modParts , ident)
      else nothing

  synthesizeMainSource : ExeMode → String → String → String
  synthesizeMainSource mode modFull ident =
    let runner = runnerOf mode in
    unlines
      ( "{-# OPTIONS --guardedness #-}"
      ∷ "module Main where"
      ∷ "open import Agda.Builtin.IO using (IO)"
      ∷ "open import Agda.Builtin.Unit using (⊤)"
      ∷ ("open import OwnershipIO.WorldRunner using (" ++ˢ runner ++ˢ ")")
      ∷ ("import " ++ˢ modFull ++ˢ " as Target")
      ∷ "main : IO ⊤"
      ∷ ("main = " ++ˢ runner ++ˢ " Target." ++ˢ ident)
      ∷ [] ) ++ˢ "\n"
    where
      runnerOf : ExeMode → String
      runnerOf cliMode      = "runCliIO"
      runnerOf reactiveMode = "runReactiveIO"

buildExeWithMode : SessionConfig → ExeMode → String → IO.IO ActionResult
buildExeWithMode cfg mode entry = withTreeLock ws (dispatchTarget (parseEntryTarget entry))
  where
    ws = workspace cfg
    exportFilesOf : List String → IO.IO (List String)
    exportFilesOf [] = IO.return []
    exportFilesOf (d ∷ _) = sourcesIn d

    anyTreeExports : String → List String → IO.IO Bool
    anyTreeExports _ [] = IO.return false
    anyTreeExports relMod (t ∷ ts) =
      fileExists (ws ++ˢ "/generated/" ++ˢ t ++ˢ "/" ++ˢ relMod) >>= λ ex →
      if ex then IO.return true else anyTreeExports relMod ts

    compileSynthesized : String → IO.IO ActionResult
    compileSynthesized src = withOpenIncludes (repository cfg) ws λ incs →
      withTempDirectory (ws ++ˢ "/tmp/build") λ dir → writeSource dir src >>= λ where
        nothing → IO.return (rejected "source: missing or unsafe module name")
        (just file) → withoutSource (dir ++ˢ "/includes") file incs >>= λ masked →
          exportFilesOf masked >>= λ expFiles →
          mkdirP (ws ++ˢ "/bin") >>
          let candStage = ws ++ˢ "/bin/candidate.new"
              entryPath = dir ++ˢ "/" ++ˢ file
              binary    = dir ++ˢ "/build/" ++ˢ executableName src
              checkEntry : IO.IO SourceResult
              checkEntry = checkIOSource (repository cfg) (ws ++ˢ "/tmp/entry-dump") incs src >>= λ where
                (sourceFailed e) → IO.return (sourceFailed e)
                (sourceOK c) → IO.return (Data.Maybe.maybe′ sourceFailed (sourceOK c) (checkCandidateEntrySafe c))
              auditCheck = checkEntry >>= λ where
                (sourceOK _)     → IO.return nothing
                (sourceFailed e) → IO.return (just e)
              legacyBuild = checkEntry >>= λ where
                (sourceFailed e) → IO.return (Code.Transport.fail e)
                (sourceOK _) → compileInWith true "" (repository cfg) dir masked file >>= λ where
                  (procResult (suc _) out err) → IO.return (Code.Transport.fail (stripStdlibWarnings (out ++ˢ err)))
                  (procResult zero _ _) → fileExists binary >>= λ exists →
                    if exists then (readProcessAt dir 10000 "chmod" ("0755" ∷ binary ∷ []) "" >>
                                    atomicRename binary candStage >> IO.return Code.Transport.pass)
                    else IO.return (Code.Transport.fail "build-exe: module must export an executable main")
          in
          removeAll candStage >>
          resolveBackendMode leanPrism >>= λ bmode →
          switchSessionCompileExe bmode (repository cfg) (ws ++ˢ "/tmp/prism-exe") candStage entryPath expFiles auditCheck legacyBuild >>= λ where
            (Code.Transport.fail e) → removeAll candStage >> IO.return (rejected e)
            Code.Transport.pass → fileExists candStage >>= λ exists →
              if exists then (atomicRename candStage (ws ++ˢ "/bin/candidate") >>
                removeAll (ws ++ˢ "/bin/replayed.sha256") >>
                shaFile (ws ++ˢ "/bin/candidate") >>= λ hash → fingerprint ws >>= λ inputs →
                atomicText (ws ++ˢ "/bin/candidate.sha256") hash >> atomicText (ws ++ˢ "/bin/inputs.sha256") inputs >>
                atomicText (ws ++ˢ "/bin/Main.agda.source") src >>
                IO.return (accepted ("candidate sha256=" ++ˢ hash)))
              else IO.return (rejected "build-exe: module must export an executable main")

    dispatchTarget : Maybe (List String × String) → IO.IO ActionResult
    dispatchTarget nothing =
      IO.return (rejected ("build-exe: invalid or forbidden entry '" ++ˢ entry ++ˢ "' (expected '<VerifiedModule>.<app>' in Gen.* object namespace)"))
    dispatchTarget (just (modParts , ident)) =
      let modFull = intersperse "." modParts
          relMod  = intersperse "/" modParts ++ˢ ".agda"
      in successfulTrees ws >>= anyTreeExports relMod >>= λ exported →
      if not exported then
        IO.return (rejected ("build-exe: entry module '" ++ˢ modFull ++ˢ "' is not exported by any verified (ok) Dialectica tree; verify it via drive-tree first"))
      else
        compileSynthesized (synthesizeMainSource mode modFull ident)

buildExe : SessionConfig → String → IO.IO ActionResult
buildExe cfg = buildExeWithMode cfg cliMode

-- Recheck every exported module, including trees unused by Main, so a stale
-- tree proof cannot enter the manifest after an ancestor changes.
auditTrees : SessionConfig → List String → IO.IO (Maybe String)
auditTrees cfg names = loadTrees names >>= λ where
    nothing → IO.return (just "finish: missing or invalid sealed tree")
    (just trees) → let cs = concatMap owned trees in
      if consistentCodes cs then auditAll (uniqueCodes cs) trees else IO.return (just "finish: conflicting exported modules")
  where
    ws = workspace cfg
    Tree = String × BaseClosure
    loadTrees : List String → IO.IO (Maybe (List Tree))
    loadTrees [] = IO.return (just [])
    loadTrees (n ∷ ns) = loadClosure ws (n ∷ []) CAS.>>=? λ b →
      loadTrees ns CAS.>>=? λ ts → IO.return (just ((n , b) ∷ ts))
    owned : Tree → List Code
    owned (_ , b) = concatMap (λ t → NT.exported (snapshot t))
      (filterᵇ (λ t → elemᵇ _==ˢ_ (tip t) (directTips b)) (sealedBases b))

    audit : String → List Code → List Code → IO.IO (Maybe String)
    audit name current [] = IO.return nothing
    audit name current (c ∷ cs) = readIfExists file >>= λ src →
      if (src ==ˢ render c) ∧ nullᵇ (closedImplOK [] c) then
        (resolveBackendMode leanPrism >>= λ mode →
         switchCheck mode (repository cfg) (ws ++ˢ "/tmp/audit") []
          (agdaCheck c (filterᵇ (λ d → not (modName c ==ᴺ modName d)) current)) >>= λ where
            Code.Transport.pass → audit name current cs
            (Code.Transport.fail e) → IO.return (just ("finish: exported module no longer typechecks\n" ++ˢ e)))
      else IO.return (just ("finish: exported source differs from verified tree: " ++ˢ file))
      where file = ws ++ˢ "/generated/" ++ˢ name ++ˢ "/" ++ˢ modulePath c

    -- Check against the versions Main actually sees. A sealed proof can
    -- survive an in-place ancestor revision only if it still typechecks.
    auditAll : List Code → List Tree → IO.IO (Maybe String)
    auditAll current [] = IO.return nothing
    auditAll current (t@(n , b) ∷ ts) = audit n
      (filterᵇ (λ d → elemᵇ _==ᴺ_ (modName d) (map modName (baseCodes b))) current) (owned t) >>= λ where
        nothing → auditAll current ts
        (just err) → IO.return (just err)

finishSession : SessionConfig → String → IO.IO ActionResult
finishSession cfg summary = withTreeLock ws (successfulTrees ws >>= λ trees → fileExists (ws ++ˢ "/bin/candidate") >>= λ exists →
  if not (nullᵇ trees) ∧ exists then
    (fingerprint ws >>= λ current → readIfExists (ws ++ˢ "/bin/inputs.sha256") >>= λ built →
    shaFile (ws ++ˢ "/bin/candidate") >>= λ hash → readIfExists (ws ++ˢ "/bin/candidate.sha256") >>= λ recorded →
    catchIO (readIfExists (ws ++ˢ "/bin/replayed.sha256")) (λ _ → IO.return "") >>= λ replayed →
    if not (replayed ==ˢ (hash ++ˢ "\n" ++ˢ current)) then
      IO.return (rejected "finish: mandatory real replay missing or stale for current bin/candidate; run a passing run-script that compares both \"ref\" and \"cand\" after the latest build-exe") else
    if (current ==ˢ built) ∧ (hash ==ˢ recorded) then
      (auditTrees cfg trees >>= λ where
        nothing → IO.return (finished summary)
        (just err) → IO.return (rejected err))
    else IO.return (rejected "finish: source or executable changed since build-exe; rebuild and replay"))
  else IO.return (rejected "finish requires at least one ok Dialectica tree and bin/candidate; drive-tree and build-exe first"))
  where
    ws = workspace cfg

executeAction : SessionConfig → SessionAction → IO.IO ActionResult
executeAction cfg (run-script why src) = runSessionScript cfg src >>= λ where
  (procResult zero out err) → IO.return (accepted ("observation:\n" ++ˢ out ++ˢ err))
  (procResult (suc n) out err) → IO.return (rejected ("run-script exited " ++ˢ show (suc n) ++ˢ "\n" ++ˢ out ++ˢ err))
executeAction cfg (drive-tree-with name why src bases lifting transport) = driveTreeWith cfg name why src bases lifting transport
executeAction cfg (build-exe-mode mode why entry) = catchIO (buildExeWithMode cfg mode entry) (λ e → IO.return (rejected e))
executeAction cfg (finish summary) = finishSession cfg summary

actionReason : SessionAction → String
actionReason (run-script why _) = "run-script: " ++ˢ why
actionReason (drive-tree-with name why _ _ _ _) = "drive-tree " ++ˢ name ++ˢ ": " ++ˢ why
actionReason (build-exe-mode _ why _) = "build-exe: " ++ˢ why
actionReason (finish summary) = "finish: " ++ˢ summary

persistFinish : SessionConfig → String → IO.IO ⊤
persistFinish cfg summary = successfulTrees ws >>= λ trees → treeManifests ws trees >>= λ modules →
  shaFile (ws ++ˢ "/bin/candidate") >>= λ hash → threadManifest ws >>= λ threads →
  atomicText (ws ++ˢ "/MANIFEST.tsv") ("kind\tname\tcanonical_sha256_or_thread_id\tsource_sha256\n" ++ˢ modules ++ˢ
    "candidate\tbin/candidate\t" ++ˢ hash ++ˢ "\n" ++ˢ threads) >>
  atomicText (ws ++ˢ "/SUMMARY.md") summary
  where
    ws = workspace cfg

-- Durable history contains accepted semantic turns only. Rejections live in
-- the next ephemeral proposal's diagnostic, never in accept or memory.
{-# NON_TERMINATING #-}
sessionLoop : SessionConfig → RunningIO AIReq AIReply (⊤ × ⊤) → List String → String → IO.IO ⊤
sessionLoop cfg ai memory diagnostic =
  onCall ai (propose prompt (not (diagnostic ==ˢ ""))) >>= λ reply →
  respond (parseSessionAction (AIReply.text reply))
  where
    prompt = unlines (sessionTemplate ∷ sessionTransportHelp ∷ "GOAL" ∷ goal cfg ∷ "REFERENCE TARGET" ∷ showSExpr (encodeRefSpec (reference cfg))
      ∷ "ACCEPTED SESSION MEMORY" ∷ showSExpr (list (map str memory)) ∷ "TRANSIENT DIAGNOSTIC" ∷ diagnostic ∷ [])
    commit : String → IO.IO (List String)
    commit semantic = onCall ai (accept semantic) >>= λ _ →
      let next = memory ++ (semantic ∷ []) in recordFiles (workspace cfg ++ˢ "/session-memory.sexp") next >> IO.return next
    continue : SessionAction → ActionResult → IO.IO ⊤
    continue action (rejected e) = let detail = unlines (reverse (take 80 (reverse (lines e)))) in
      F.putStrLn ("Session retry: " ++ˢ detail) >> sessionLoop cfg ai memory detail
    continue action (accepted observation) = commit (actionReason action ++ˢ "\n" ++ˢ observation) >>= λ next → sessionLoop cfg ai next ""
    continue action (finished summary) = commit (actionReason action) >>= λ _ → persistFinish cfg summary
    respond : Maybe SessionAction → IO.IO ⊤
    respond nothing = sessionLoop cfg ai memory "session-action: malformed envelope or source block"
    respond (just action) = executeAction cfg action >>= continue action

runAutonomousSession : SessionConfig → IO.IO ⊤
runAutonomousSession cfg = enableLineBuffering >> trackedService (workspace cfg ++ˢ "/threads") (sessionBackend cfg) >>= λ ai →
  onCall ai (bindNode "SESSION_ROOT" nothing) >>= λ _ →
  readNames (workspace cfg ++ˢ "/session-memory.sexp") >>= λ saved →
  sessionLoop cfg ai (restore saved) "" >> onStop ai >>= λ _ → IO.return tt
  where
    restore : Maybe (List String) → List String
    restore nothing = []
    restore (just m) = m
