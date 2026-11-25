import LojitaCtx.Posix.Program

namespace Lojita.Runtime.PosixNative
open LojitaCtx.Posix

structure Reply where
  error : Nat
  value : Nat
  data : ByteArray
  deriving Inhabited

@[extern "lojita_posix_call"]
private opaque raw (op : UInt32) (a b c : UInt64) (x y : @& ByteArray) : IO Reply

def invoke (op : UInt32) (a b c : Nat := 0) (x y : ByteArray := .empty) : IO Reply :=
  raw op a.toUInt64 b.toUInt64 c.toUInt64 x y

def Reply.result {α : Type} (r : Reply) (f : Reply → α) : Ret α :=
  if r.error = 0 then .ok (f r) else .err (Errno.decode r.error)

def Reply.unit (r : Reply) : Ret Unit := r.result (fun _ => ())
def Reply.number (r : Reply) : Ret Nat := r.result Reply.value
def Reply.packed (r : Reply) : Ret ByteArray := r.result Reply.data
def Reply.bytes (r : Reply) : Ret Bytes := r.result (fun s => s.data.data.toList)

def word (bytes : ByteArray) (start width : Nat) : Nat :=
  (List.range width).foldl (fun n i => n + (bytes[start+i]!.toNat <<< (8*i))) 0

def encodeWord (n width : Nat) : Bytes :=
  (List.range width).map fun i => (n >>> (8*i)).toUInt8

def fdArg (n : Fd) : Nat := min n 2147483647
def dirArg : DirFd → Nat
  | none => 4294967196 -- AT_FDCWD (-100)
  | some n => fdArg n

def flags (f : OpenFlags) : Nat :=
  let access := match f.access with | .readOnly => 0 | .writeOnly => 1 | .readWrite => 2
  access + f.create.toNat*64 + f.excl.toNat*128 + f.trunc.toNat*512 + f.append.toNat*1024 +
    f.nonblock.toNat*2048 + f.directory.toNat*65536 + f.nofollow.toNat*131072 + f.cloexec.toNat*524288

def ttyBits (t : Termios) := t.icanon.toNat + 2*t.echo.toNat + 4*t.isig.toNat + 8*t.icrnl.toNat + 16*t.opost.toNat

def fromBits (v : Nat) : Termios :=
  ⟨v.testBit 0, v.testBit 1, v.testBit 2, v.testBit 3, v.testBit 4⟩

def stat (r : Reply) : Ret StatObs := Id.run do
  if r.error != 0 then return .err (Errno.decode r.error)
  let w := fun i => word r.data (8*i) 8
  let kind : FileKind ← match w 1 with
    | 32768 => pure .regular | 16384 => pure .directory | 40960 => pure .symlink
    | 4096 => pure .fifo | 8192 => pure .tty | 49152 => pure .socket
    | _ => return .err .EOPNOTSUPP
  return .ok ⟨w 0,kind,w 2,w 3,w 4⟩

def pathCall (op : UInt32) (a : Nat) (path : Bytes) (b c : Nat := 0) (other : Bytes := []) : IO Reply :=
  if path.contains 0 || other.contains 0 then pure ⟨22,0,.empty⟩
  else invoke op a b c ((path ++ [0]).toByteArray) ((other ++ [0]).toByteArray)

end Lojita.Runtime.PosixNative
