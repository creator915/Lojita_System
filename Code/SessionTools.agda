{-# OPTIONS --guardedness #-}
module Code.SessionTools where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; reverse)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; wordsBy; intersperse) renaming (_++_ to _++ˢ_)
import Data.Char as Char
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership using (Spec)
open import OwnershipIO using (EnvIO; RunningIO; ⟦_⟧IO; onCall; onStop)
open import OwnershipIO.FFI
open import Code using (_==ˢ_)
open import Code.Driver using (ProcSpec; ProcReq; ProcOut; procReq)
open import Code.SessionProtocol using (RefSpec; RefTarget; local; docker)
import Code.SessionProtocol as Ref
open import Code.TermTool using (ptySpec; ptyToolWithCand)
open import Code.Tools.FsTool using (fsSpec; fsToolWithCand)
open import Code.Tools.NetTool using (netSpec; netToolWithCand)
open import Code.Tools.GitTool using (gitSpec; gitToolWithCand)
open import Context.Terminal
open import Context.Tools.FsSandbox using (FsConfig; fsConfig; FsFixture; fixDir; fixFile; fixSymlink; FsStep; runCmd; symlinkStep; RawFsObs)
open import Context.Tools.NetSandbox using (NetConfig; netConfig; NetTopology; daemonProbeMode; NetStep; runClient; RawNetObs)
open import Context.Tools.GitSandbox using (GitConfig; gitConfig; GitStep; gitRunTarget; RawGitObs)

-- Unified open-world session tool palette: batch process execution, raw PTY
-- terminal, managed filesystem sandbox (`fsbox`), loopback network stub/probe
-- sandbox (`netbox`), and deterministic Git repository sandbox (`gitbox`).
SessionΨ : List Spec
SessionΨ = ProcSpec ∷ ptySpec ∷ fsSpec ∷ netSpec ∷ gitSpec ∷ []

lastPart : List String → String
lastPart [] = "session"
lastPart (s ∷ []) = s
lastPart (_ ∷ ss) = lastPart ss

private
  initParts : List String → List String
  initParts [] = []
  initParts (_ ∷ []) = []
  initParts (x ∷ xs) = x ∷ initParts xs

  dirOf : String → String
  dirOf path with initParts (wordsBy ('/' Char.≟_) path)
  ... | [] = "."
  ... | ps = "/" ++ˢ intersperse "/" ps

  siblingRelay : String → String → String
  siblingRelay termRelay name =
    let parts = wordsBy ('/' Char.≟_) termRelay
        initP = initParts parts
        lead  = case Data.String.toList termRelay of λ { ('/' ∷ _) → "/" ; _ → "" }
    in case initP of λ where
         [] → lead ++ˢ name
         ps → lead ++ˢ intersperse "/" ps ++ˢ "/" ++ˢ name
    where open import Function.Base using (case_of_)

  markUse : String → String → IO.IO ⊤
  markUse scratch alias = if (alias ==ˢ "ref") ∨ (alias ==ˢ "cand") then
    (mkdirP scratch IO.>>= λ _ → F.writeFile (scratch ++ˢ "/used-" ++ˢ alias) "") else IO.return tt

  refExeInTarget : RefTarget → String
  refExeInTarget (local exe)      = exe
  refExeInTarget (docker _ exe)   = exe

  candExeInTarget : RefTarget → String → String
  candExeInTarget (local _)    candidate = candidate
  candExeInTarget (docker _ _) _         = "/codetransport-cand"

  sandboxForRef : RefTarget → SandboxTarget → SandboxTarget
  sandboxForRef (local _)        t = t
  sandboxForRef (docker image _) localSandbox = dockerSandbox image
  sandboxForRef (docker _ _)     t@(dockerSandbox _) = t

  resolveAliasPath : RefTarget → String → String → String
  resolveAliasPath rt cand s =
    if s ==ˢ "ref" then refExeInTarget rt
    else if s ==ˢ "cand" then candExeInTarget rt cand
    else s

  stripDotSlash : String → String
  stripDotSlash s with Data.String.toList s
  ... | '.' ∷ '/' ∷ rest = Data.String.fromList rest
  ... | _                = s

  lookupLinkAlias : String → List (String × String) → String
  lookupLinkAlias _ [] = ""
  lookupLinkAlias cmd ((linkName , tag) ∷ rest) =
    if stripDotSlash cmd ==ˢ stripDotSlash linkName then tag else lookupLinkAlias cmd rest

batch : RefSpec → String → String → RunningIO ProcReq ProcOut (⊤ × ⊤)
batch ref candidate scratch = record
  { onCall = λ q → markUse scratch (ProcReq.command q) IO.>>= λ _ → request q
  ; onStop = IO.return (tt , tt) }
  where
    work = scratch ++ˢ "/proc"
    executeLocal : String → List String → String → IO.IO ProcResult
    executeLocal exe args inp = withTempDirectory work λ dir →
      readProcessAt dir (Ref.timeoutMs ref) "/usr/bin/env"
        ("-i" ∷ "LC_ALL=C.UTF-8" ∷ exe ∷ args) inp

    executeDockerRef : String → String → List String → String → IO.IO ProcResult
    executeDockerRef image exe args inp = withTempDirectory work λ dir →
      let name = "proc-" ++ˢ lastPart (wordsBy ('/' Char.≟_) dir) in
      readProcessAt dir (Ref.timeoutMs ref) "docker"
        ("run" ∷ "--rm" ∷ "-i" ∷ "--pull=never" ∷ "--network=none" ∷ "--cap-drop=ALL"
        ∷ "--security-opt=no-new-privileges" ∷ "--user" ∷ "65534:65534" ∷ "--read-only"
        ∷ "--pids-limit=128" ∷ "--tmpfs" ∷ "/tmp:rw,nosuid,noexec,size=64m"
        ∷ "--name" ∷ name ∷ "--workdir" ∷ "/tmp" ∷ "--entrypoint" ∷ "/usr/bin/env"
        ∷ image ∷ "-i" ∷ "LC_ALL=C.UTF-8" ∷ exe ∷ args) inp IO.>>= λ r →
      readProcessAt dir 10000 "docker" ("rm" ∷ "-f" ∷ name ∷ []) "" IO.>>= λ _ → IO.return r

    -- Execute `cand` inside the exact same cleanroom Docker image as `ref` so
    -- GLIBC ABI, isolated network (`--network=none`), UID 65534, and locale match.
    executeDockerCand : String → List String → String → IO.IO ProcResult
    executeDockerCand image args inp = fileExists candidate IO.>>= λ exists →
      if exists then
        (withTempDirectory work λ dir →
          let name = "cand-" ++ˢ lastPart (wordsBy ('/' Char.≟_) dir)
              staged = dir ++ˢ "/cand-bin"
          in
          readProcessAt dir 10000 "cp" (candidate ∷ staged ∷ []) "" IO.>>= λ _ →
          readProcessAt dir 10000 "chmod" ("0755" ∷ dir ∷ staged ∷ []) "" IO.>>= λ _ →
          readProcessAt dir (Ref.timeoutMs ref) "docker"
            ("run" ∷ "--rm" ∷ "-i" ∷ "--pull=never" ∷ "--network=none" ∷ "--cap-drop=ALL"
            ∷ "--security-opt=no-new-privileges" ∷ "--user" ∷ "65534:65534" ∷ "--read-only"
            ∷ "--pids-limit=128" ∷ "--tmpfs" ∷ "/tmp:rw,nosuid,noexec,size=64m"
            ∷ "--mount" ∷ ("type=bind,src=" ++ˢ staged ++ˢ ",dst=/codetransport-cand,readonly")
            ∷ "--name" ∷ name ∷ "--workdir" ∷ "/tmp" ∷ "--entrypoint" ∷ "/usr/bin/env"
            ∷ image ∷ "-i" ∷ "LC_ALL=C.UTF-8" ∷ "/codetransport-cand" ∷ args) inp IO.>>= λ r →
          readProcessAt dir 10000 "docker" ("rm" ∷ "-f" ∷ name ∷ []) "" IO.>>= λ _ → IO.return r)
      else
        IO.return (procResult 127 "" ("procExec: candidate binary does not exist at " ++ˢ candidate))

    request : ProcReq → IO.IO ProcResult
    request (procReq "ref" args inp) with Ref.target ref
    ... | local exe        = executeLocal exe (Ref.arguments ref ++ args) inp
    ... | docker image exe = executeDockerRef image exe (Ref.arguments ref ++ args) inp
    request (procReq "cand" args inp) with Ref.target ref
    ... | local _          = executeLocal candidate args inp
    ... | docker image _   = executeDockerCand image args inp
    request _ = IO.return (procResult 127 "" "procExec: use the registered aliases ref or cand")

terminal : RefSpec → String → String → String → ⟦ ptySpec ⟧IO
terminal ref candidate relay scratch cfg owned = markUse scratch (executable cfg) IO.>>= λ _ →
  ptyToolWithCand relay candidate (scratch ++ˢ "/pty") (record cfg
    { target = target resolved ; executable = executable resolved ; arguments = arguments resolved }) owned
  where
    resolveRef : RefTarget → TermConfig
    resolveRef (local exe) = record cfg
      { target = localSandbox ; executable = exe ; arguments = Ref.arguments ref ++ arguments cfg }
    resolveRef (docker image exe) = record cfg
      { target = dockerSandbox image ; executable = exe ; arguments = Ref.arguments ref ++ arguments cfg }
    resolveCand : RefTarget → TermConfig
    resolveCand (local _) = record cfg
      { target = localSandbox ; executable = candidate }
    resolveCand (docker image _) = record cfg
      { target = dockerSandbox image ; executable = "/codetransport-cand" }
    resolved : TermConfig
    resolved = if executable cfg ==ˢ "ref" then resolveRef (Ref.target ref) else
      (if executable cfg ==ˢ "cand" then resolveCand (Ref.target ref) else cfg)

filesystem : RefSpec → String → String → String → ⟦ fsSpec ⟧IO
filesystem ref candidate fsRelay scratch cfg owned =
  newIORef initialLinks IO.>>= λ linkRef →
  fsToolWithCand fsRelay candidate (scratch ++ˢ "/fs") resolvedCfg owned IO.>>= λ srv →
  IO.return (record
    { onCall = λ step → stepHook linkRef step IO.>>= λ step′ → onCall srv step′
    ; onStop = onStop srv })
  where
    rt = Ref.target ref
    initLink : FsFixture → List (String × String)
    initLink (fixSymlink p dest) =
      if (dest ==ˢ "ref") ∨ (dest ==ˢ "cand") then (p , dest) ∷ [] else []
    initLink _ = []

    collectInitLinks : List FsFixture → List (String × String)
    collectInitLinks [] = []
    collectInitLinks (f ∷ fs) = initLink f ++ collectInitLinks fs

    initialLinks : List (String × String)
    initialLinks = collectInitLinks (FsConfig.fixtures cfg)

    rewriteFixture : FsFixture → FsFixture
    rewriteFixture (fixSymlink p dest) = fixSymlink p (resolveAliasPath rt candidate dest)
    rewriteFixture f = f

    resolvedCfg : FsConfig
    resolvedCfg = record cfg
      { target = sandboxForRef rt (FsConfig.target cfg)
      ; fixtures = map rewriteFixture (FsConfig.fixtures cfg) }

    stepHook : IORef (List (String × String)) → FsStep → IO.IO FsStep
    stepHook linkRef (symlinkStep p dest) =
      (if (dest ==ˢ "ref") ∨ (dest ==ˢ "cand")
         then (readIORef linkRef IO.>>= λ ls → writeIORef linkRef ((p , dest) ∷ ls))
         else IO.return tt) IO.>>= λ _ →
      IO.return (symlinkStep p (resolveAliasPath rt candidate dest))
    stepHook linkRef (runCmd exe args inp ms) =
      readIORef linkRef IO.>>= λ ls →
      let viaLink = lookupLinkAlias exe ls
          tag     = if (exe ==ˢ "ref") ∨ (exe ==ˢ "cand") then exe else viaLink
          exe′    = if exe ==ˢ "ref" then refExeInTarget rt
                    else if exe ==ˢ "cand" then candExeInTarget rt candidate
                    else exe
          args′   = if exe ==ˢ "ref" then Ref.arguments ref ++ args else args
      in markUse scratch tag IO.>>= λ _ → IO.return (runCmd exe′ args′ inp ms)
    stepHook _ s = IO.return s

network : RefSpec → String → String → String → ⟦ netSpec ⟧IO
network ref candidate netRelay scratch cfg owned =
  markDaemon (NetConfig.topology cfg) IO.>>= λ _ →
  netToolWithCand netRelay candidate (scratch ++ˢ "/net") resolvedCfg owned IO.>>= λ srv →
  IO.return (record
    { onCall = λ step → stepHook step IO.>>= λ step′ → onCall srv step′
    ; onStop = onStop srv })
  where
    rt = Ref.target ref
    markDaemon : NetTopology → IO.IO ⊤
    markDaemon (daemonProbeMode exe _) = markUse scratch exe
    markDaemon _ = IO.return tt

    rewriteTop : NetTopology → NetTopology
    rewriteTop (daemonProbeMode exe args) =
      let exe′  = resolveAliasPath rt candidate exe
          args′ = if exe ==ˢ "ref" then Ref.arguments ref ++ args else args
      in daemonProbeMode exe′ args′
    rewriteTop top = top

    resolvedCfg : NetConfig
    resolvedCfg = record cfg
      { target = sandboxForRef rt (NetConfig.target cfg)
      ; topology = rewriteTop (NetConfig.topology cfg) }

    stepHook : NetStep → IO.IO NetStep
    stepHook (runClient exe args inp ms) =
      markUse scratch exe IO.>>= λ _ →
      let exe′  = resolveAliasPath rt candidate exe
          args′ = if exe ==ˢ "ref" then Ref.arguments ref ++ args else args
      in IO.return (runClient exe′ args′ inp ms)
    stepHook s = IO.return s

gitSandbox : RefSpec → String → String → String → ⟦ gitSpec ⟧IO
gitSandbox ref candidate gitRelay scratch cfg owned =
  gitToolWithCand gitRelay candidate (scratch ++ˢ "/git") resolvedCfg owned IO.>>= λ srv →
  IO.return (record
    { onCall = λ step → stepHook step IO.>>= λ step′ → onCall srv step′
    ; onStop = onStop srv })
  where
    rt = Ref.target ref
    resolvedCfg : GitConfig
    resolvedCfg = record cfg
      { target = sandboxForRef rt (GitConfig.target cfg) }

    stepHook : GitStep → IO.IO GitStep
    stepHook (gitRunTarget exe args inp ms) =
      markUse scratch exe IO.>>= λ _ →
      let exe′  = resolveAliasPath rt candidate exe
          args′ = if exe ==ˢ "ref" then Ref.arguments ref ++ args else args
      in IO.return (gitRunTarget exe′ args′ inp ms)
    stepHook s = IO.return s

sessionTools : RefSpec → String → String → String → EnvIO SessionΨ
sessionTools ref candidate termRelay scratch =
  (λ _ _ → IO.return (batch ref candidate scratch))
  ∷ terminal ref candidate termRelay scratch
  ∷ filesystem ref candidate (siblingRelay termRelay "fs-relay") scratch
  ∷ network ref candidate (siblingRelay termRelay "net-relay") scratch
  ∷ gitSandbox ref candidate (siblingRelay termRelay "git-relay") scratch
  ∷ []
