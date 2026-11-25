import LojitaCtx.Posix.Program

namespace Gen.SignalPoll
open LojitaCtx.Posix

theorem fdCap : Cap.fdIoCap ∈ CoreCaps := by simp [CoreCaps]
theorem envCap : Cap.envCap ∈ CoreCaps := by simp [CoreCaps]

private def b (s : String) : Bytes := s.toUTF8.data.toList

/-- The host test injects signals into this verified program while it is blocked
    inside the requested syscall. Single-byte markers delimit the wait phases. -/
def app : PosixMachine CoreCaps Unit UInt32 := PosixMachine.ofFree do
  let .ok [mode] ← FreeSys.call .getArgs envCap | return 20
  let _ ← FreeSys.call (.write 1 (ByteArray.mk #[82])) fdCap
  if mode == b "pending" then
    let .ok _ ← FreeSys.call (.read 0 1) fdCap | return 21
  if mode == b "defer" then
    let .ok [] ← FreeSys.call (.ppoll [] (some 300) false) fdCap | return 22
  let timeout := if mode == b "timeout" then 25 else 3500
  let r ← FreeSys.call (.ppoll [] (some timeout) (mode != b "plain")) fdCap
  match r with
  | .err .EINTR =>
    let _ ← FreeSys.call (.write 1 (ByteArray.mk #[69])) fdCap
    pure ()
  | .ok [] =>
    let _ ← FreeSys.call (.write 1 (ByteArray.mk #[84])) fdCap
    pure ()
  | _ => return 23
  if mode == b "restore" || mode == b "timeout" || mode == b "ignored" then
    let .ok _ ← FreeSys.call (.read 0 1) fdCap | return 24
  return 0

end Gen.SignalPoll
