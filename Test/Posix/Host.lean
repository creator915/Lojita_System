import Lojita.Runtime.WorldRunner

open LojitaCtx.Posix

private instance : Repr ByteArray where
  reprPrec b prec := reprPrec b.data prec

private def call (op : SysOp) := Lojita.Runtime.WorldRunner.perform [] op

private def expect {α : Type} [DecidableEq α] [Repr α] (label : String) (actual expected : α) : IO Unit :=
  unless actual = expected do throw (IO.userError s!"{label}: got {repr actual}, expected {repr expected}")

private def ok (op : SysOp) : IO op.Result := do
  match ← call op with
  | .ok x => return x
  | .err e => throw (IO.userError s!"{repr op}: errno {e.code}")
  | .wouldBlock _ => throw (IO.userError s!"{repr op}: unexpected blocked result")

def main : IO Unit := IO.FS.withTempDir fun dir => do
  let name : Bytes := [102,255]
  let link : Bytes := [108]
  let moved : Bytes := [109]
  let parent ← ok (.openat none dir.toString.toUTF8.data.toList {directory := true} 0)
  let fd ← ok (.openat (some parent) name {create := true,access := .readWrite} 0o600)
  let data : Bytes := [0,255,10,9]
  expect (α := Nat) "write" (← ok (.write fd data.toByteArray)) 4
  expect (α := Nat) "pwrite" (← ok (.pwrite fd ⟨#[42]⟩ 1)) 1
  expect (α := Nat) "offset after pwrite" (← ok (.lseek fd 0 .cur)) 4
  expect (α := ByteArray) "pread" (← ok (.pread fd 4 0)) ⟨#[0,42,10,9]⟩
  let st ← ok (.fstat fd)
  expect (α := FileKind) "file kind" st.kind .regular
  expect (α := Nat) "file size" st.size 4
  expect (α := Nat) "mode" st.mode 0o600
  let _ ← ok (.symlinkat name (some parent) link)
  expect (α := Bytes) "raw symlink target" (← ok (.readlinkat (some parent) link)) name
  expect (α := FileKind) "raw symlink stat" (← ok (.fstatat (some parent) link false)).kind .symlink
  let _ ← ok (.renameat (some parent) name (some parent) moved)
  expect (α := Ret StatObs) "dangling link" (← call (.fstatat (some parent) link true)) (.err .ENOENT)
  expect (α := Ret Nat) "embedded NUL" (← call (.openat (some parent) [102,0,120] {} 0)) (.err .EINVAL)
  let _ ← ok (.unlinkat (some parent) moved false)
  expect (α := Nat) "unlinked inode" (← ok (.fstat fd)).nlink 0
  expect (α := Nat) "alias" (← ok (.dup2 fd 47)) 47
  let _ ← ok (.lseek fd 1 .set)
  expect (α := ByteArray) "alias reads" (← ok (.read 47 2)) ⟨#[42,10]⟩
  expect (α := Nat) "alias offset" (← ok (.lseek fd 0 .cur)) 3
  let (reader,writer) ← ok (.pipe2 true true)
  expect (α := Ret ByteArray) "would block" (← call (.read reader 1)) (.err .EAGAIN)
  expect (α := List Nat) "poll" (← ok (.ppoll [⟨reader,1⟩,⟨writer,4⟩] (some 0) false)) [0,4]
  expect (α := Nat) "pipe write" (← ok (.write writer ⟨#[255]⟩)) 1
  let _ ← ok (.close writer)
  expect (α := List Nat) "poll after close" (← ok (.ppoll [⟨reader,1⟩] (some 0) false)) [17]
  expect (α := ByteArray) "pipe data" (← ok (.read reader 10)) ⟨#[255]⟩
  expect (α := ByteArray) "EOF" (← ok (.read reader 10)) ⟨#[]⟩
  expect (α := Bool) "ordinary fd isatty" (← ok (.isatty reader)) false
  expect (α := Ret Termios) "termios error" (← call (.tcgetattr reader)) (.err .ENOTTY)
  let _ ← ok (.setNonblock reader false)
  let _ ← ok (.setCloexec fd true)
  for n in [reader,47,fd,parent] do discard <| ok (.close n)
  let now : Nat ← ok .clockGettime
  let _ ← ok (.nanosleep 1000000)
  let later : Nat ← ok .clockGettime
  unless later ≥ now + 1000000 do throw (IO.userError "monotonic clock did not advance")
  IO.println "Native POSIX ABI passed file, link, fd, pipe, poll, tty-error and clock checks."
