import Lojita.Session.Context

namespace Lojita.Session
open System Lean Lojita.Kernel Lojita.Harness Lojita.Store

structure TurnRequest where
  owner : String
  ctxDir : FilePath
  prompt : String
  retry : Bool
  node : Option AIRequest := none
  stopping : BaseIO Bool := pure false

structure Backend where
  propose : TurnRequest → IO String
  accept : String → String → IO Unit := fun _ _ => pure ()
  retire : String → IO Unit := fun _ => pure ()
  cancel : String → IO Unit := fun _ => pure ()

def ScriptedBackend (f : TurnRequest → IO String) : Backend := {propose := f}

structure CodexConfig where
  repo : FilePath
  workspace : FilePath
  refFile : FilePath
  executable : Option String := none
  rolloutDir : Option FilePath := none

private def envOr (name fallback : String) : IO String := do
  let some s ← IO.getEnv name | return fallback
  return if s.isEmpty then fallback else s

private def uuid (s : String) : Bool :=
  let groups := s.splitOn "-"
  groups.map String.length == [8,4,4,4,12] && groups.all (fun g => g.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')))

private def threadStarted (events : String) : Option String := Id.run do
  for line in events.splitOn "\n" do
    if let .ok event := Json.parse line then
      if (event.getObjValAs? String "type").toOption == some "thread.started" then
        if let .ok id := event.getObjValAs? String "thread_id" then
          if uuid id then return some id
  return none

private abbrev ProcessKills := Std.Mutex (Std.HashMap String (IO Unit))

private def codexOutput (kills : ProcessKills) (owner : String) (stopping : BaseIO Bool)
    (args : IO.Process.SpawnArgs) (prompt : String) : IO (IO.Process.Output × Except IO.Error Unit) := do
  if ← stopping then fail s!"cancelled {owner}"
  let (stdin, child) ← (← IO.Process.spawn {args with
    stdin := .piped, stdout := .piped, stderr := .piped, setsid := true}).takeStdin
  let kill : IO Unit := try child.kill catch | .noSuchThing .. => pure () | e => throw e
  try
    kills.atomically do
      if ← stopping then kill else modify (·.insert owner kill)
    let stdout ← IO.asTask (readPipe child.stdout) .dedicated
    let stderr ← IO.asTask (readPipe child.stderr) .dedicated
    -- Dropping the extracted handle after flush sends EOF even while the kill hook owns child.
    let sent ← (stdin.putStr prompt *> stdin.flush).toBaseIO
    if !sent.isOk then kill
    let output ← IO.wait stdout
    let errors ← IO.wait stderr
    let exitCode ← child.wait
    return (⟨exitCode, ← EIO.ofExcept output, ← EIO.ofExcept errors⟩, sent)
  finally
    kills.atomically (modify (·.erase owner))
where
  readPipe (h : IO.FS.Handle) : IO String := do
    let bytes ← h.readBinToEnd
    if let some text := String.fromUTF8? bytes then return text
    -- SIGTERM can truncate a later JSON line after a complete thread.started event.
    if ← stopping then return String.fromUTF8Lossy bytes
    fail "codex pipe contained invalid UTF-8"

private def invokeCodex (cfg : CodexConfig) (kills : ProcessKills) (req : TurnRequest)
    (stopping : BaseIO Bool) (mode : List String) (prompt : String) (toolsEnabled : Bool)
    (onThread : String → IO Unit := fun _ => pure ()) : IO (String × Option String) := do
  let model ← envOr "CODETRANSPORT_MODEL" "gpt-6.2-sol"
  let effort ← envOr "CODETRANSPORT_EFFORT" "max"
  let tier := (← IO.getEnv "CODETRANSPORT_SERVICE_TIER").getD "ultrafast"
  let isolated := req.ctxDir / "work"
  IO.FS.createDirAll isolated
  let toml := fun (s : String) => (Json.str s).compress
  let mut args := #["exec","--skip-git-repo-check","-s","read-only","-C",isolated.toString,
    "-m",model,"-c","model_reasoning_effort=" ++ toml effort]
  if !tier.isEmpty then args := args ++ #["-c","service_tier=" ++ toml tier]
  args := args ++ #["-c","approval_policy=\"never\"","-c","features.shell_tool=false",
    "-c","features.unified_exec=false","-c","features.multi_agent=false"]
  if toolsEnabled then
    let kind := if req.node.isSome then "node" else "session"
    let mut flags := ["mcp","--mode",kind,"--repo",cfg.repo.toString,"--ctx-dir",req.ctxDir.toString,
      "--narrow-log",(cfg.workspace / "narrowing-events.jsonl").toString]
    if kind == "session" then flags := flags ++ ["--workspace",cfg.workspace.toString,"--ref-file",cfg.refFile.toString]
    let server := "mcp_servers.lojita={command=" ++ toml (cfg.repo / "lojita").toString ++
      ",args=" ++ (toJson flags).compress ++ ",startup_timeout_sec=30,tool_timeout_sec=180,default_tools_approval_mode=\"approve\"}"
    args := args ++ #["-c",server]
  let last := req.ctxDir / "last-message"
  try
    let bin ← match cfg.executable with
      | some path => pure path
      | none => do
        let installed : FilePath := "/root/.local/bin/codex"
        envOr "CODETRANSPORT_CODEX_BIN" (if ← installed.pathExists then installed.toString else "codex")
    let (out, sent) ← codexOutput kills req.owner stopping {
      cmd := bin, args := args ++ #["--json","-o",last.toString] ++ mode.toArray ++ #["-"], cwd := some isolated} prompt
    let tid := threadStarted out.stdout
    -- A terminated fork may already have published its rollout and thread.started event.
    if let some id := tid then onThread id
    if let some dir ← IO.getEnv "CODETRANSPORT_CODEX_TRACE_DIR" then
      let call := String.intercalate "-" (if mode.isEmpty then ["new"] else mode)
      atomicText (FilePath.mk dir / req.owner / s!"{← IO.monoNanosNow}-{call}.jsonl") out.stdout
    if ← stopping then fail s!"cancelled {req.owner}"
    unless out.exitCode == 0 do fail s!"codex exec ({out.exitCode}): {out.stderr}\n{out.stdout}"
    EIO.ofExcept sent
    return (← IO.FS.readFile last,tid)
  finally
    if ← last.pathExists then IO.FS.removeFile last

private structure ThreadState where
  mainThread : String
  scratchThread : Option String
  request : TurnRequest
  generation : Nat

/-- Only a validated ID reported by our own fork may be retired.
    Durable IDs and unrelated session files never enter the removal set. -/
private def retireScratch (cfg : CodexConfig) (s : ThreadState) : IO Unit := do
  if let some tid := s.scratchThread then
    unless uuid tid && tid != s.mainThread do fail "invalid scratch thread identity"
    let sessions ← match cfg.rolloutDir with
      | some dir => pure dir
      | none => do
        let home ← envOr "HOME" ""
        let dir : FilePath := ← envOr "CODEX_HOME" (home ++ "/.codex")
        pure (dir / "sessions")
    if ← sessions.isDir then
      let result ← IO.Process.output {cmd := "find", args := #["-P",sessions.toString,"-ignore_readdir_race",
        "-type","f","(","-name","rollout-????-??-??T??-??-??-" ++ tid ++ ".jsonl","-o","-name",tid ++ ".jsonl",
        "-o","-name",tid ++ ".thread",")","-delete"]}
      unless result.exitCode == 0 do fail result.stderr
  let drafts := s.request.ctxDir / "drafts"
  if ← drafts.isDir then IO.FS.removeDirAll drafts

private structure OwnerThread where
  state : Std.Mutex (Option ThreadState)
  generation : IO.Ref Nat

private def OwnerThread.stopping (slot : OwnerThread) (generation : Nat) (req : TurnRequest) : BaseIO Bool := do
  return (← slot.generation.get) != generation || (← req.stopping)

private def OwnerThread.retire (slot : OwnerThread) (cfg : CodexConfig) (through : Option Nat := none) : IO Unit :=
  slot.state.atomically do
    if let some s ← get then
      if through.all (s.generation ≤ ·) then
        retireScratch cfg s
        set (none : Option ThreadState)

def CodexCLIBackend (cfg : CodexConfig) : IO Backend := do
  let owners ← Std.Mutex.new ({} : Std.HashMap String OwnerThread)
  let kills : ProcessKills ← Std.Mutex.new {}
  let propose := fun (req : TurnRequest) => do
    unless safeDraftName req.owner do fail "invalid thread slot"
    let slot ← owners.atomically do
      if let some slot := (← get)[req.owner]? then return slot
      let slot : OwnerThread := ⟨← Std.Mutex.new none, ← IO.mkRef 0⟩
      modify (·.insert req.owner slot)
      return slot
    let generation ← slot.generation.get
    let stopping := slot.stopping generation req
    slot.state.atomically fun state => do
      if ← stopping then fail s!"cancelled {req.owner}"
      proposeTurn cfg kills req generation stopping state
  let findOwner := fun (owner : String) => owners.atomically (return (← get)[owner]?)
  let retire := fun owner => do
    if let some slot ← findOwner owner then slot.retire cfg
  let cancel := fun owner => do
    if let some slot ← findOwner owner then
      -- Invalidate pending spawns as well as the process currently registered for this owner.
      let (generation, result) ← kills.atomically do
        let generation ← slot.generation.modifyGet fun n => (n, n + 1)
        let kill : Option (IO Unit) ← modifyGet fun m => (m[owner]?, m.erase owner)
        return (generation, ← (kill.getD (pure ())).toBaseIO)
      try EIO.ofExcept result finally slot.retire cfg generation
  let accept := fun owner semantic => do
    if let some slot ← findOwner owner then
      slot.state.atomically do
        if let some s ← get then
          discard <| invokeCodex cfg kills s.request (slot.stopping s.generation s.request) ["resume",s.mainThread]
            ("Accepted semantic turn:\n" ++ semantic ++ "\nAcknowledge only.") false
          retireScratch cfg s
          set (none : Option ThreadState)
  return {propose,accept,retire,cancel}
where
  proposeTurn (cfg : CodexConfig) (kills : ProcessKills) (req : TurnRequest) (generation : Nat)
      (stopping : BaseIO Bool) (state : IO.Ref (Option ThreadState)) : IO String := do
    let idFile := cfg.workspace / "threads" / (req.owner ++ ".id")
    let main ← match ← readOptional idFile with
      | some tid => pure tid
      | none => do
        let (_,some tid) ← invokeCodex cfg kills req stopping [] "You are a Lojita ownership agent. Reply READY." false
          | fail "Codex did not return a durable thread ID"
        atomicText idFile tid
        pure tid
    unless uuid main do fail "invalid durable thread ID"
    let previous ← state.get
    let scratch := (previous.filter (·.generation == generation)).bind (·.scratchThread)
    let resume := req.retry && scratch.isSome
    unless resume do
      if let some old := previous then retireScratch cfg old
    let current : ThreadState := ⟨main, if resume then scratch else none, req, generation⟩
    state.set (some current)
    let mode := if resume then ["resume",scratch.getD ""] else ["fork",main]
    atomicText (req.ctxDir / "latest-prompt") req.prompt
    let stdout ← IO.getStdout
    stdout.putStrLn (if resume then s!"Retrying {req.owner} on scratch ({scratch.getD ""})"
      else s!"Planning {req.owner} ({main})")
    stdout.flush
    let remember := fun tid => do
      unless tid != main && (!resume || some tid == scratch) do fail "unexpected proposal thread identity"
      for file in ← namesAt (cfg.workspace / "threads") do
        if file.endsWith ".id" && (← readOptional (cfg.workspace / "threads" / file)) == some tid then
          fail "proposal fork identifies a durable thread"
      state.set (some {current with scratchThread := some tid})
    let (reply,tid) ← invokeCodex cfg kills req stopping mode req.prompt true remember
    unless resume || tid.isSome do fail "Codex did not identify the proposal fork"
    atomicText (req.ctxDir / "latest-reply") reply
    return reply

/-- Resolve the actual envelope after the tool turn; a draft may have been
    created or patched after the request was constructed. A reply consisting of
    a single `@draft` is replaced by the submission held in that draft. Missing
    inner drafts stay as bare symbols so `parseSubmission` names them exactly. -/
def resolveNodeReply (reply : String) (drafts : DraftStore) : Except String String := do
  let (expr, sources) ← submissionEnvelope reply drafts
  return (resolve expr sources).canonical
where
  resolve (e : SExpr) (ds : DraftStore) : SExpr :=
    match e with
    | .sym n => match draftRef? ds n with
      | some src => .str src
      | none => e
    | .list xs => .list (xs.attach.map fun ⟨x, _⟩ => resolve x ds)
    | _ => e
  termination_by sizeOf e
  decreasing_by
    have := List.sizeOf_lt_of_mem ‹x ∈ xs›
    simp_wf; omega

end Lojita.Session
