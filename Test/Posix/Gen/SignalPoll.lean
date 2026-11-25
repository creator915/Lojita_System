import LojitaCtx.Posix.Program

namespace Gen.SignalPoll
open LojitaCtx.Posix

private def b (s : String) : Bytes := s.toUTF8.data.toList

/-- The host test injects signals into this verified program while it is blocked
    inside the requested syscall. Single-byte markers delimit the wait phases. -/
def app : PosixProg CoreCaps UInt32 := do
  let .ok [mode] ← PosixProg.call .getArgs (by decide) | return 20
  let _ ← PosixProg.call (.write 1 [82]) (by decide)
  if mode == b "pending" then
    let .ok _ ← PosixProg.call (.read 0 1) (by decide) | return 21
  if mode == b "defer" then
    let .ok [] ← PosixProg.call (.ppoll [] (some 300) false) (by decide) | return 22
  let timeout := if mode == b "timeout" then 25 else 3500
  let r ← PosixProg.call (.ppoll [] (some timeout) (mode != b "plain")) (show Cap.fdIoCap ∈ CoreCaps from by decide)
  match r with
  | .err .EINTR =>
    let _ ← PosixProg.call (.write 1 [69]) (by decide)
    pure ()
  | .ok [] =>
    let _ ← PosixProg.call (.write 1 [84]) (by decide)
    pure ()
  | _ => return 23
  if mode == b "restore" || mode == b "timeout" || mode == b "ignored" then
    let .ok _ ← PosixProg.call (.read 0 1) (by decide) | return 24
  return 0

end Gen.SignalPoll
