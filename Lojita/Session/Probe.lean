import Lojita.Session.SessionEnv
import Lojita.Session.Workspace

namespace Lojita.Session
open System Lojita.Kernel Lojita.Store Lojita.Ownership Lojita.Ownership.Tools
open LojitaCtx.Terminal LojitaCtx.FsSandbox LojitaCtx.NetSandbox LojitaCtx.GitSandbox
open SessionEnv

structure ProbeReport where
  exitCode : Nat
  stdout : String
  stderr : String
  usedRef : Bool := false
  usedCand : Bool := false
  deriving Lean.ToJson, Lean.FromJson

private structure RelayHost where
  ref : RefSpec
  candidate : Option FilePath
  bin : FilePath
  scratch : FilePath
  used : IO.Ref (Std.HashSet String)

private def RelayHost.target (h : RelayHost) : SandboxTarget := match h.ref.target with
  | .local _ => .localSandbox
  | .docker img _ => .dockerSandbox img

private def RelayHost.command (h : RelayHost) (alias : String) (args : List String) : IO (String × List String) := do
  match alias with
  | "ref" =>
    let path := match h.ref.target with | .local b | .docker _ b => b
    return (path, h.ref.arguments ++ args)
  | "cand" =>
    let some p := h.candidate | fail "candidate has not been built"
    return (if h.ref.target matches .docker .. then "/lojita-candidate" else p.toString, args)
  | _ => fail s!"unknown executable alias {alias}. Use ref or cand"

private def RelayHost.observed (h : RelayHost) (alias : String) (code : Option Nat) : IO Unit := do
  if code.any (fun n => n != 126 && n != 127) then h.used.modify (·.insert alias)

private def RelayHost.ms (h : RelayHost) (ms : Nat) := max 1 (min ms h.ref.timeoutMs)

private def terminalHost (h : RelayHost) : HandlerIO Term.ptySpec := fun cfg files => do
  let (exe,args) ← h.command cfg.executable cfg.arguments
  let srv ← Term.ptyToolWithMount (h.bin / "term-relay") h.scratch h.candidate
    {cfg with target := h.target, executable := exe, arguments := args} files
  -- READY follows the close-on-exec handshake. An interactive target can
  -- remain alive throughout a valid replay and be stopped by its owner.
  h.used.modify (·.insert cfg.executable)
  let forward := fun (step : TermStep) =>
    srv.callIO (match step with | .sleepMs ms => .sleepMs (h.ms ms) | s => s)
  return {srv with callIO := forward}

private def fsHost (h : RelayHost) : HandlerIO Fs.fsSpec := fun cfg files => do
  let srv ← Fs.fsToolWithMount (h.bin / "fs-relay") h.scratch h.candidate {cfg with target := h.target} files
  return {srv with callIO := fun step => do
    match step with
    | .runCmd alias args input ms =>
      let (exe,args) ← h.command alias args
      let o ← srv.callIO (.runCmd exe args input (h.ms ms))
      unless o.timedOut do h.observed alias o.exitStatus
      return o
    | s => srv.callIO s}

private def netHost (h : RelayHost) : HandlerIO Net.netSpec := fun cfg files => do
  let topology ← match cfg.topology with
    | .daemonProbeMode alias args => do
      let (exe,args) ← h.command alias args
      pure (.daemonProbeMode exe args)
    | t => pure t
  let srv ← Net.netToolWithMount (h.bin / "net-relay") h.scratch h.candidate {cfg with target := h.target,topology} files
  return {srv with callIO := fun step => do
    match step with
    | .runClient alias args input ms =>
      let (exe,args) ← h.command alias args
      let o ← srv.callIO (.runClient exe args input (h.ms ms))
      unless o.timedOut do h.observed alias o.exitStatus
      return o
    | s =>
      let o ← srv.callIO s
      if let .daemonProbeMode alias _ := cfg.topology then
        if !o.timedOut && !o.wireReply.isEmpty then h.used.modify (·.insert alias)
      return o}

private def gitHost (h : RelayHost) : HandlerIO Git.gitSpec := fun cfg files => do
  let srv ← Git.gitToolWithMount (h.bin / "git-relay") h.scratch h.candidate {cfg with target := h.target} files
  return {srv with callIO := fun step => do
    match step with
    | .gitRunTarget alias args input ms =>
      let (exe,args) ← h.command alias args
      let o ← srv.callIO (.gitRunTarget exe args input (h.ms ms))
      unless o.timedOut do h.observed alias o.exitStatus
      return o
    | s => srv.callIO s}

private def probeEnv (h : RelayHost) : EnvIO SessionΨ :=
  EnvIO.cons (terminalHost h) (EnvIO.cons (fsHost h) (EnvIO.cons (netHost h) (EnvIO.cons (gitHost h)
    (EnvIO.cons (fun (cfg : Web.WebConfig) files => Web.webTool (h.bin / "web-relay") h.scratch {cfg with target := h.target} files)
      EnvIO.nil))))

private instance : Nonempty Probe := ⟨Prog.done {}⟩

/-- The disposable worker evaluates only a kernel-audited value of the exact
    indexed program type. Its tool environment comes from the host. -/
def probeWorker (repo ws scratch : FilePath) (ref : RefSpec) (source : String) : IO ProbeReport := do
  preload (repo / ".lake/build/lib/lean")
  let (env,n) ← elaborateProbe source
  let some c := env.find? n | fail "missing probe"
  unless Lean.Kernel.isDefEqGuarded env {} c.type (Lean.mkConst ``Probe) do fail "probe must have type SessionEnv.Probe"
  let boxed ← IO.ofExcept (unsafe env.evalConst NonScalar {} n (checkMeta := false))
  let prog : Probe := (unsafe unsafeCast boxed)
  let used ← IO.mkRef {}
  let candidate := ws / "bin/candidate"
  let mount := if ← candidate.pathExists then some candidate else none
  let (_,r) ← evalIO (probeEnv ⟨ref,mount,repo / ".lake/build/relays",scratch,used⟩) prog ()
  let seen ← used.get
  return ⟨r.exitCode,r.stdout,r.stderr,seen.contains "ref",seen.contains "cand"⟩

def buildIdentity (ws : FilePath) : IO SExpr := do
  let candidate ← IO.FS.readBinFile (ws / "bin/candidate")
  return .list [.sym "build", .str (sha256 candidate), .str (← treeFingerprint ws)]

private def pinnedReference (ref : RefSpec) : IO RefSpec := do
  match ref.target with
  | .local bin => return {ref with target := .local (← IO.FS.realPath bin).toString}
  | .docker image bin =>
    let out ← IO.Process.output {cmd := "docker", args := #["image","inspect","--format","{{.Id}}","--",image]}
    let id := out.stdout.trimAscii.toString
    unless out.exitCode == 0 && id.startsWith "sha256:" && validHash (id.drop 7).toString do
      fail s!"cannot identify cleanroom Docker image {image}: {out.stderr}"
    return {ref with target := .docker id bin}

private def replayStamp (ws : FilePath) (ref pinned : RefSpec) : IO SExpr := do
  let fingerprint ← match pinned.target with
    | .local p => sha256 <$> IO.FS.readBinFile p
    | .docker id _ => pure id
  return .list [.sym "replay", ← buildIdentity ws, encodeRefSpec ref, .str fingerprint]

def replayIdentity (ws : FilePath) (ref : RefSpec) : IO SExpr := do
  replayStamp ws ref (← pinnedReference ref)

def runScript (repo ws : FilePath) (ref : RefSpec) (src : String) : IO ProbeReport :=
  withWorkspaceLock ws do
    let ws ← IO.FS.realPath ws
    let repo ← IO.FS.realPath repo
    let pinned ← pinnedReference ref
    let before ← if ← (ws / "bin/candidate").pathExists then some <$> replayStamp ws ref pinned else pure none
    IO.FS.withTempDir fun dir => do
      let dir ← IO.FS.realPath dir
      IO.FS.writeFile (dir / "probe.lean") src
      IO.FS.writeFile (dir / "ref.sexp") (encodeRefSpec pinned).canonical
      let out ← IO.Process.output {
        cmd := "timeout", cwd := some dir
        args := #["-k","2","120",(repo / "lojita").toString,"probe-worker",repo.toString,ws.toString,dir.toString]}
      if out.exitCode != 0 then return ⟨out.exitCode.toNat,out.stdout,out.stderr,false,false⟩
      let r : ProbeReport ← IO.ofExcept (Lean.Json.parse out.stdout >>= Lean.fromJson?)
      if r.usedRef && r.usedCand then
        let file := ws / "replay-receipt.sexp"
        if r.exitCode == 0 then
          let receipt ← replayIdentity ws ref
          unless before.any (·.canonical == receipt.canonical) do fail "build or reference changed during replay"
          atomicText file (SExpr.list [receipt,.str (sha256 src.toUTF8)]).canonical
        else if ← file.pathExists then IO.FS.removeFile file
      return {r with stderr := out.stderr ++ r.stderr}

end Lojita.Session
