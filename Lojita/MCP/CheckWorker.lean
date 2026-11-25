import Lean

namespace Lojita.MCP.CheckWorker
open Lean System

abbrev Child := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }
inductive State where
  | idle
  | running (child : Child)
  | reaping (exitCode : Task (Except IO.Error UInt32))

abbrev Slot := IO.Ref State

private def limit (key : String) (maximum : Nat) : IO Nat := do
  let some raw ← IO.getEnv key | return maximum
  let some n := raw.toNat? | throw (IO.userError s!"invalid {key}: expected a positive integer")
  if n == 0 then throw (IO.userError s!"invalid {key}: expected a positive integer")
  return min n maximum

-- Applied inside the checker after exec and before loading Lean modules.
@[extern "lojita_protect_check_worker"]
opaque protect : IO Unit

@[extern "lojita_kill_check_worker"]
private opaque killWorker (pid : UInt32) : IO Unit

private def getChild (slot : Slot) (exe : FilePath) (args : Array String) : IO Child := do
  match ← slot.get with
  | .running child => return child
  | .reaping exitCode =>
    unless ← IO.hasFinished exitCode do
      throw (IO.userError "CHECK_WORKER_STOPPING: prior checker is still exiting")
    discard <| EIO.ofExcept (← IO.wait exitCode)
  | .idle => pure ()
  let child : Child ← IO.Process.spawn {
    cmd := "setpriv", args := #["--pdeathsig", "KILL", exe.toString] ++ args
    -- Each owner already has its own process; avoid a pool of large reserved stacks per owner.
    env := #[("LEAN_NUM_THREADS", some "1")],
    stdin := .piped, stdout := .piped, stderr := .inherit }
  slot.set (.running child)
  return child

def stop (slot : Slot) : IO Unit := do
  let .running child ← slot.get | return
  -- The PID belongs to us until wait reaps it. SIGKILL also handles a stopped checker.
  killWorker child.pid
  let reap ← IO.asTask child.wait .dedicated
  slot.set (.reaping reap)
  -- A task in uninterruptible I/O can outlast SIGKILL. Leave its reaper
  -- running and refuse to stack more checkers behind it.
  for _ in [:20] do
    if ← IO.hasFinished reap then
      discard <| EIO.ofExcept (← IO.wait reap)
      slot.set .idle
      return
    IO.sleep 5

private def rssKiB (pid : UInt32) : IO Nat := do
  let status ← IO.FS.readFile s!"/proc/{pid}/status"
  -- A zombie has no VmRSS. Its closed pipe reports the worker failure.
  let some row := (status.splitOn "\n").find? (·.startsWith "VmRSS:") | return 0
  let some kb := ((row.drop "VmRSS:".length).toString.splitOn " ").findSome? (fun s => s.trimAscii.toString.toNat?)
    | throw (IO.userError "cannot parse checker VmRSS")
  return kb

def request (slot : Slot) (exe : FilePath) (args : Array String) (req : Json) : IO Json := do
  let timeout ← limit "LOJITA_CHECK_TIMEOUT_MS" 120000
  let memory ← limit "LOJITA_CHECK_RSS_MIB" 1536
  let started ← IO.monoMsNow
  let child ← getChild slot exe args
  try
    -- Include pipe writes in the deadline: a wedged worker may stop reading a large draft.
    let exchange ← IO.asTask (prio := .dedicated) do
      child.stdin.putStrLn req.compress
      child.stdin.flush
      child.stdout.getLine
    let mut nextSample := started
    let mut lastRSS := 0
    repeat
      let now ← IO.monoMsNow
      if now >= started + timeout then
        throw (IO.userError s!"CHECK_TIMEOUT: checker {child.pid} exceeded {timeout} ms (last RSS {lastRSS} KiB)")
      if now >= nextSample then
        lastRSS ← rssKiB child.pid
        if lastRSS > memory * 1024 then
          throw (IO.userError s!"CHECK_MEMORY_LIMIT: checker {child.pid} RSS {lastRSS} KiB exceeded {memory} MiB")
        nextSample := now + 50
      if ← IO.hasFinished exchange then
        let line ← EIO.ofExcept (← IO.wait exchange)
        if line.isEmpty then throw (IO.userError "CHECK_WORKER_EXIT: checker closed its output")
        return ← IO.ofExcept <| (← IO.ofExcept (Json.parse line)).getObjVal? "result"
      IO.sleep 5
    throw (IO.userError "CHECK_WORKER_EXIT: missing reply")
  catch e =>
    stop slot
    throw e

end Lojita.MCP.CheckWorker
