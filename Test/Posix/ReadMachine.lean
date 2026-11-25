import LojitaCtx.Io.PipeCursor
import LojitaCtx.Io.RegularCursor

open LojitaCtx.Posix LojitaCtx.Io

private theorem cap : Cap.fdIoCap ∈ CoreCaps := by decide

/-- Preserve both the key and the shape; TreeMap lookup alone misses the
    two-node flip caused by recomputing reference accounting on every read. -/
private def treeKeys {α : Type} : Std.DTreeMap.Internal.Impl Nat (fun _ => α) → List (Option Nat)
  | .leaf => [none]
  | .inner _ k _ l r => some k :: (treeKeys l ++ treeKeys r)

private def shape {α : Type} (t : Table α) := treeKeys t.inner.inner

private def payload : Bytes := [65,10,10,0,255,66,67]
private def base (target : KernelTarget) (off : Nat) : Machine :=
  let e : FdEntry := {ofd := 5}
  let d : OpenFileDesc := {target,flags := {},offset := off,refcnt := 2}
  let vfs := InodeTable.empty.put 8 {payload := .reg payload.toByteArray,nlink := 1}
  {proc := {fds := ({} : Table FdEntry).insert 3 e |>.insert 9 e}
   kernel := {ofds := ({} : Table OpenFileDesc).insert 5 d,vfs,clock := 123}}

private def readPair (m : Machine) (size : Nat) (ss : List StepSlice) (expected : Bytes)
    (lines : List Bytes) : IO (Machine × Machine) := do
  let r : BufReader := {fd := 3,chunkSize := size}
  let (.done (.ok bs,_),a) := runPrefix ((readAll cap r).observe ss.length) m ss
    | throw (IO.userError "readAll failed to reach EOF")
  let (.done (.ok got),b) := runPrefix ((readLines cap r).observe ss.length) m ss
    | throw (IO.userError "readLines failed to reach EOF")
  unless bs == expected && got == lines do throw (IO.userError "read values depend on slice schedule")
  for z in [a,b] do
    unless shape z.kernel.vfs.nodes == shape m.kernel.vfs.nodes &&
        z.proc.fds.toList == m.proc.fds.toList && z.kernel.clock == 123 do
      throw (IO.userError "read modified unrelated state or balanced-tree shape")
  return (a,b)

def main : IO Unit := do
  let x : StepSlice := {maxBytes := 7}
  let y : StepSlice := {maxBytes := 4}
  let intr : StepSlice := {intrBefore := true}
  let lines : List Bytes := [[65,10],[10],[0,255,66,67]]
  let pipe : StreamBuf := {pendingBytes := payload,readers := 1,writers := 0}
  let old := (base (.pipe 11 false) 0).setPipe 11 pipe
  for initial in [old,old.setPages 11 [⟨3,4096⟩,⟨4,4⟩],old.setPages 11 [⟨0,10⟩,⟨7,19⟩]] do
    let (a,b) ← readPair initial 7 [x,x] payload lines
    let (c,d) ← readPair initial 4 [intr,y,intr,y,y] payload lines
    for z in [a,b,c,d] do
      unless (z.kernel.pipes[11]?).any (fun s => s.pendingBytes.isEmpty) &&
          (z.kernel.pipePages[11]?).any List.isEmpty do
        throw (IO.userError "pipe bytes or page layout survived EOF")
  for off in [0,3,16] do
    let m := base (.inode 8) off
    let suffix := payload.drop off
    let remainingLines := (({} : Framing).chunk suffix).lines
    let (a,b) ← readPair m 7 [x,x] suffix remainingLines
    let (c,d) ← readPair m 4 [intr,y,intr,y,y] suffix remainingLines
    for z in [a,b,c,d] do
      let .ok (_,desc) := z.lookup 9 | throw (IO.userError "read lost the alias")
      unless desc.offset == off+suffix.length do throw (IO.userError "incorrect final shared offset")
  IO.println "Whole-machine read twins passed for closed pipes, uncached pages, aliasing, and seeks past EOF."
