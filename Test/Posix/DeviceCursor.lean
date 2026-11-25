import LojitaCtx.Io.CanonicalRecords

open LojitaCtx.Posix LojitaCtx.Io

namespace DeviceTwin

private structure Trace where
  m : Machine := {}
  values : Array Int := #[]

private abbrev Run := StateT Trace IO

private def emit (n : Int) : Run Unit := modify fun s => {s with values := s.values.push n}

private def step (op : SysOp) : Run (Ret op.Result) := do
  let (result,m) := stepSyscall (← get).m canonicalSlice op
  modify fun s => {s with m}
  return result

private def ok (op : SysOp) : Run op.Result := do
  match ← step op with
  | .ok x => return x
  | .err e => throw <| IO.userError s!"{repr op}: {repr e}"
  | .wouldBlock _ => throw <| IO.userError s!"blocked: {repr op}"

private def record {α} (encode : α → Nat) : Ret α → Run Unit
  | .ok x => emit (Int.ofNat (encode x))
  | .err e => emit (-(Int.ofNat e.code))
  | .wouldBlock _ => throw <| IO.userError "nonblocking operation blocked"

private def write (fd : Nat) (bs : Bytes) := do record id (← step (.write fd bs.toByteArray))
private def read (fd n : Nat) := do
  record (fun (bs : ByteArray) => bs.data.foldl (fun (a : Nat) (b : UInt8) => a*257+b.toNat+1) 0) (← step (.read fd n))
private def poll (fd mask : Nat) := do
  let masks ← ok (.ppoll [⟨fd,mask⟩] (some 0) false)
  match masks with
  | [n] => emit n
  | _ => throw <| IO.userError "poll size"

private def pair (attrs : Termios) : Run (Fd × Fd) := do
  let initial := ({} : Machine).setPty 1 {attrs}
  let flags : OpenFlags := {access := .readWrite, nonblock := true}
  let .ok (master,m) := initial.allocate (.pty 1 true) flags | throw <| IO.userError "allocate master"
  let .ok (slave,m) := m.allocate (.pty 1 false) flags | throw <| IO.userError "allocate slave"
  modify fun s => {s with m := m.account}
  return (master,slave)

private def slaveHangup : Run Unit := do
  let (master,slave) ← pair rawTermios
  let alias ← ok (.dup2 master 10)
  discard <| ok (.close master)
  write alias [97,98,99]
  read slave 1
  poll slave 5
  discard <| ok (.dup2 slave alias)
  poll slave 5
  read slave 2
  read alias 2
  write slave []
  write slave [120]
  discard <| ok (.close alias)
  discard <| ok (.close slave)
  unless (← get).m.kernel.ptys.isEmpty do throw <| IO.userError "last close retained PTY"

private def masterHangup : Run Unit := do
  let (master,slave) ← pair rawTermios
  let alias ← ok (.dup2 slave 10)
  discard <| ok (.close slave)
  read master 1
  write alias [97,98,99]
  discard <| ok (.close alias)
  poll master 5
  read master 1
  read master 4
  poll master 5
  read master 4
  read master 4
  write master [120]
  discard <| ok (.close master)

private def checkBuffered (start : Machine) (fd : Fd) : IO Unit := do
  let depth := 32
  let plan := List.replicate depth canonicalSlice
  let cap : Cap.fdIoCap ∈ [Cap.fdIoCap] := by simp
  for chunk in [1,32] do
    let r : BufReader := {fd,chunkSize := chunk}
    let (.done (.ok bs,reader),afterAll) := runPrefix ((readAll cap r).observe depth) start plan
      | throw <| IO.userError "canonical readAll suspended or failed"
    let (.done (.ok lines),afterLines) := runPrefix ((readLines cap r).observe depth) start plan
      | throw <| IO.userError "canonical readLines suspended or failed"
    unless reader.eof && lines == [[97,98,99,10],[49,50,10]] && bs == lines.flatten do
      throw <| IO.userError "canonical framing across short reads"
    for after in [afterAll,afterLines] do
      unless (show Ret ByteArray from (stepSyscall after canonicalSlice (.read fd 32)).1) = .ok ⟨#[122,10]⟩ do
        throw <| IO.userError "VEOF did not preserve the following record"

private def canonicalRecord : Run Unit := do
  let (master,slave) ← pair canonTermios
  write master [97,98,99,13,49,50,10,4,122,10]
  checkBuffered (← get).m slave
  read slave 1
  read slave 32
  read slave 32
  poll slave 1
  read slave 3
  poll slave 1
  read slave 1
  read slave 3
  poll slave 1
  read slave 3
  discard <| ok (.close master)
  discard <| ok (.close slave)

private def peerFin : Run Unit := do
  let peer : SocketState := {input := {pendingBytes := [97,0,98], writers := 0}}
  let m : Machine := {kernel := {listeners := ({} : Table SocketState).insert 1234 peer}}
  modify fun s => {s with m}
  let fd ← ok (.socketStream true false)
  discard <| ok (.connectLoopback fd 1234)
  read fd 2
  read fd 2
  poll fd 5
  read fd 1
  read fd 1

def run : IO Unit := do
  let (_,s) ← (slaveHangup *> masterHangup *> canonicalRecord *> peerFin).run {}
  let linux ← IO.Process.output {cmd := "python3", args := #["Test/Posix/device_cursor.py"]}
  let simulated := String.intercalate "," (s.values.toList.map toString)
  unless linux.exitCode == 0 do throw <| IO.userError linux.stderr
  unless simulated == linux.stdout.trimAscii.toString do
    throw <| IO.userError s!"simulated {simulated}\nLinux {linux.stdout}"
  IO.println s!"Linux/Lean matched {s.values.size} PTY and TCP observations."

end DeviceTwin

def main := DeviceTwin.run
