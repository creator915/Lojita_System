import Lojita.Session.Context

namespace Lojita.Session
open System Lean Lojita.Kernel Lojita.Harness Lojita.Store

structure TurnRequest where
  owner : String
  ctxDir : FilePath
  prompt : String
  retry : Bool
  node : Option AIRequest := none

structure Backend where
  propose : TurnRequest → IO String
  accept : String → String → IO Unit := fun _ _ => pure ()
  retire : String → IO Unit := fun _ => pure ()

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

private def invokeCodex (cfg : CodexConfig) (req : TurnRequest) (mode : List String) (prompt : String)
    (toolsEnabled : Bool) : IO (String × Option String) := do
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
    let out ← IO.Process.output {cmd := bin, args := args ++ #["--json","-o",last.toString] ++ mode.toArray ++ #["-"],
                                 cwd := some isolated} (some prompt)
    if let some dir ← IO.getEnv "CODETRANSPORT_CODEX_TRACE_DIR" then
      let call := String.intercalate "-" (if mode.isEmpty then ["new"] else mode)
      atomicText (FilePath.mk dir / req.owner / s!"{← IO.monoNanosNow}-{call}.jsonl") out.stdout
    unless out.exitCode == 0 do fail s!"codex exec ({out.exitCode}): {out.stderr}\n{out.stdout}"
    return (← IO.FS.readFile last,threadStarted out.stdout)
  finally
    if ← last.pathExists then IO.FS.removeFile last

private structure ThreadState where
  mainThread : String
  scratchThread : Option String
  request : TurnRequest

/-- Only a validated ID obtained from our own successful fork may be retired.
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

def CodexCLIBackend (cfg : CodexConfig) : IO Backend := do
  let states ← IO.mkRef ({} : Std.HashMap String ThreadState)
  let retire := fun owner => do
    if let some s := (← states.get)[owner]? then
      retireScratch cfg s
      states.modify (·.erase owner)
  let propose := fun (req : TurnRequest) => do
    unless safeDraftName req.owner do fail "invalid thread slot"
    let idFile := cfg.workspace / "threads" / (req.owner ++ ".id")
    let main ← match ← readOptional idFile with
      | some tid => pure tid
      | none => do
        let (_,some tid) ← invokeCodex cfg req [] "You are a Lojita ownership agent. Reply READY." false
          | fail "Codex did not return a durable thread ID"
        atomicText idFile tid
        pure tid
    unless uuid main do fail "invalid durable thread ID"
    let scratch := (← states.get)[req.owner]?.bind (·.scratchThread)
    let resume := req.retry && scratch.isSome
    unless resume do retire req.owner
    let mode := if resume then ["resume",scratch.getD ""] else ["fork",main]
    atomicText (req.ctxDir / "latest-prompt") req.prompt
    let stdout ← IO.getStdout
    stdout.putStrLn (if resume then s!"Retrying {req.owner} on scratch ({scratch.getD ""})"
      else s!"Planning {req.owner} ({main})")
    stdout.flush
    let (reply,tid) ← invokeCodex cfg req mode req.prompt true
    atomicText (req.ctxDir / "latest-reply") reply
    let some tid := tid <|> (if resume then scratch else none) | fail "Codex did not identify the proposal fork"
    unless tid != main && (!resume || some tid == scratch) do fail "unexpected proposal thread identity"
    for slot in ← namesAt (cfg.workspace / "threads") do
      if slot.endsWith ".id" && (← readOptional (cfg.workspace / "threads" / slot)) == some tid then
        fail "proposal fork identifies a durable thread"
    states.modify (·.insert req.owner ⟨main,some tid,req⟩)
    return reply
  let accept := fun owner semantic => do
    if let some s := (← states.get)[owner]? then
      discard <| invokeCodex cfg s.request ["resume",s.mainThread] ("Accepted semantic turn:\n" ++ semantic ++ "\nAcknowledge only.") false
      retire owner
  return {propose,accept,retire}

/-- Resolve the actual envelope after the tool turn; a draft may have been
    created or patched after the request was constructed. -/
def resolveNodeReply (reply : String) (drafts : DraftStore) : Except String String := do
  let (text, sources) ← extractBlocks reply drafts
  let some expr := SExpr.parseSExpr text | throw "INVALID_SUBMISSION"
  return (← resolve expr sources).canonical
where
  resolve (e : SExpr) (ds : DraftStore) : Except String SExpr := do
    match e with
    | .sym n => if n.startsWith "@" then return .str (← sourceValue ds e) else return e
    | .list xs => return .list (← xs.mapM (resolve · ds))
    | _ => return e
  termination_by sizeOf e

end Lojita.Session
