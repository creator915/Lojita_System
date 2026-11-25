import LojitaCtx.Posix.Program

namespace Gen.CopyBytes
open LojitaCtx.Posix

inductive CopyState where
  | reading
  | writing (bytes : ByteArray)
  | finished (code : UInt32)

theorem fdCap : Cap.fdIoCap ∈ CoreCaps := by simp [CoreCaps]

def copyStep : CopyState → Request CoreCaps UInt32 CopyState
  | .reading => .ask (.read 0 4096) fdCap fun
    | .ok bytes => if bytes.isEmpty then .finished 0 else .writing bytes
    | .err .EINTR => .reading
    | _ => .finished 1
  | .writing bytes => .ask (.write 1 bytes) fdCap fun (reply : Ret Nat) => match reply with
    | .ok n =>
      if n == bytes.size then .reading
      else if n == 0 || n > bytes.size then .finished 2
      else .writing (bytes.extract n bytes.size)
    | .err .EINTR => .writing bytes
    | _ => .finished 2
  | .finished code => .done code

def app : PosixMachine CoreCaps CopyState UInt32 :=
  PosixMachine.unfold .reading copyStep

end Gen.CopyBytes
