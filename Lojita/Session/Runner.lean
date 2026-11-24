import Lojita.Session.AI
import Lojita.Session.Prompt
import Lojita.Session.Probe

namespace Lojita.Session
open System Lojita.Kernel Lojita.Harness Lojita.Transport Lojita.Store

structure SessionConfig where
  repo : FilePath
  workspace : FilePath
  goal : String
  reference : RefSpec
  backend : Backend
  requireBuild : Bool := true
  maxSessionTurns : Option Nat := none
  maxNodePolls : Option Nat := none

inductive ActionResult where
  | accepted (outcome : String)
  | rejected (diagnostic : String)
  | finished (summary : String)
  deriving Repr

def runNode (cfg : SessionConfig) (dir : FilePath) (task : NodeTask) (home : Frozen) : IO (Verdict × Frozen) := do
  let active ← IO.mkRef ({} : Std.HashSet String)
  let propose : Proposer := fun req => do
    let owner := toString req.task.delta.child
    let ctx := dir / "ai" / owner
    writeContext ctx req
    if let some cert := req.diagnostic then logNarrowing (cfg.workspace / "narrowing-events.jsonl") "node" cert
    active.modify (·.insert owner)
    let reply ← cfg.backend.propose ⟨owner,ctx,nodePrompt req,req.diagnostic.isSome,some req⟩
    let drafts ← loadDrafts ctx
    return (resolveNodeReply reply drafts).toOption.getD reply
  let accept : AcceptNode := fun t semantic => do
    let owner := toString t.delta.child
    cfg.backend.accept owner semantic
    active.modify (·.erase owner)
  try
    IO.FS.createDirAll (dir / "ai")
    withNodeEnvIO propose (fun env => do
      let v := thawHome home
      let start ← Lojita.Ownership.evalProcIO env (nodeAgent v.1) v.2
      let (some verdict, stopped) ← Lojita.Ownership.WorkerIO.awaitIO (← start task)
        | fail "node stopped without a verdict"
      return (verdict, freezeHome stopped.1 stopped.2)) accept
  finally
    for owner in ← active.get do cfg.backend.retire owner

def driveTree (cfg : SessionConfig) (name why src : String) (bases : List String)
    (lifting transport : Option String) : IO String := withWorkspaceLock cfg.workspace do
  let p ← prepareSpec cfg.workspace name src bases lifting transport
  let (v,f) ← runNode cfg (cfg.workspace / "trees" / name) p.task p.home
  if v == .ok then verifyClosure p.closure.modules f
  let outcome ← publishTree cfg.workspace name why bases p.closure.directTips v f
  if let .liftObstruction reason culprits _ := v then
    logNarrowing (cfg.workspace / "narrowing-events.jsonl") "drive-tree"
      ⟨"liftObstruction",String.intercalate ", " (culprits.map toString),reason,s!"Repair the base and re-drive {name}."⟩
  return outcome

private def finishSession (cfg : SessionConfig) (summary : String) : IO ActionResult := withWorkspaceLock cfg.workspace do
  let ws := cfg.workspace
  discard <| auditTrees ws
  if cfg.requireBuild || (← (ws / "bin/candidate").pathExists) then
    unless ← (ws / "bin/candidate").pathExists do fail "REPLAY_REQUIRED: build-exe and replay ref and cand before finish"
    let expected ← buildIdentity ws
    unless (← readOptional (ws / "bin/build.sexp")) == some expected.canonical do fail "STALE_BUILD: rebuild and replay"
    let receipt ← readOptional (ws / "replay-receipt.sexp")
    let some (.list [r,.str scriptHash]) := receipt >>= SExpr.parseSExpr | fail "REPLAY_REQUIRED: missing replay receipt"
    unless validHash scriptHash && r.canonical == (← replayIdentity ws cfg.reference).canonical do
      fail "REPLAY_REQUIRED: stale receipt for this candidate, reference or tree"
  atomicText (ws / "SUMMARY.md") summary
  return .finished summary

def executeAction (cfg : SessionConfig) (action : SessionAction) : IO ActionResult := do
  try
    match action with
    | .runScript why src =>
      let r ← runScript cfg.repo cfg.workspace cfg.reference src
      if r.exitCode != 0 then return .rejected s!"probe exit {r.exitCode}\n{r.stdout}{r.stderr}"
      return .accepted s!"run-script {why}\n{r.stdout}{r.stderr}"
    | .driveTree n why src bs l t =>
      return .accepted s!"drive-tree {n}: {← driveTree cfg n why src bs l t}\n{why}"
    | .buildExe mode why entry => withWorkspaceLock cfg.workspace do
      let ws := cfg.workspace
      let name := qualified entry
      let modules ← entryModules ws name
      discard <| auditTrees ws
      compileVerifiedExe modules name mode (ws / "bin/candidate")
      let receipt := ws / "replay-receipt.sexp"
      if ← receipt.pathExists then IO.FS.removeFile receipt
      atomicText (ws / "bin/build.sexp") (← buildIdentity ws).canonical
      return .accepted s!"build-exe {entry}: {why}"
    | .finish summary => finishSession cfg summary
  catch e => return .rejected (toString e)

/-- A rejected proposal supplies only a transient diagnostic. The durable
    conversation and semantic memory advance after the authoritative action gate. -/
private def sessionLoop (cfg : SessionConfig) : IO String := do
  let ws := cfg.workspace
  withWorkspaceLock ws (initWorkspace ws)
  let file := ws / "session-memory.sexp"
  let some (.list saved) := SExpr.parseSExpr (← IO.FS.readFile file) | fail "corrupt session memory"
  let mut memory := (← IO.ofExcept (stringList saved)).toArray
  let mut diagnostic := ""
  let mut count := 0
  let owner := "SESSION_ROOT"
  let ctx := ws / "ai" / owner
  IO.FS.createDirAll ctx
  try
    repeat
      if cfg.maxSessionTurns.any (count ≥ ·) then fail s!"session turn limit: {diagnostic}"
      count := count + 1
      let sealed ← withWorkspaceLock ws do loadCurrentClosure ws (← sealedNames ws)
      let summaries := sealed.trees.map fun t =>
        t.name ++ " " ++ t.tip ++ "\n" ++ renderLeanMod t.home.spec ++
          String.intercalate "\n" ((exported t.home).map fun m =>
            s!"{m.modName}: " ++ String.intercalate ", " ((publicNames m).map toString))
      let prompt := sessionPrompt cfg.goal cfg.reference summaries memory.toList diagnostic
      let reply ← cfg.backend.propose ⟨owner,ctx,prompt,!diagnostic.isEmpty,none⟩
      let drafts ← loadDrafts ctx
      let result ← match parseSessionAction reply drafts with
        | .error e => pure (.rejected e)
        | .ok act => executeAction cfg act
      match result with
      | .rejected e =>
        diagnostic := e
        logNarrowing (ws / "narrowing-events.jsonl") "session" ⟨"action_rejected",owner,e,"Revise the action and retry."⟩
      | .accepted msg | .finished msg =>
        memory := memory.push msg
        atomicText file (SExpr.list (memory.toList.map .str)).canonical
        cfg.backend.accept owner msg
        if result matches .finished _ then return msg
        diagnostic := ""
    fail "session stopped without finish"
  finally cfg.backend.retire owner

def runSession (cfg : SessionConfig) : IO String := do
  IO.FS.createDirAll cfg.workspace
  let lock ← IO.FS.Handle.mk (cfg.workspace / "session.lock") .append
  unless ← lock.tryLock do fail "another SESSION_ROOT is driving this workspace"
  try sessionLoop cfg finally lock.unlock

end Lojita.Session
