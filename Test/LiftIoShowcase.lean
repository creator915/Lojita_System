import Gen.LiftIo
import LojitaCtx.Io.LineRefinement
import Lojita.Kernel.Driver

namespace Test.LiftIoShowcase
open Gen.LiftIo LojitaCtx.Posix LojitaCtx.Io LojitaCtx.Io.FsLib

/-- Two reads of the same stationary inode may have unrelated short-read and
    interrupt schedules. Project those actual file replies into T15; T16 fixes
    T0's result and descriptor table. T1 executes the buffered line loop at size 3. -/
theorem lift_square {m opened before₀ before₁ end₀ end₁ : Machine}
    {fd ino : Nat} {bytes : ByteArray} {openSlice close₀ close₁ s₀ s₁ q₀ q₁}
    (openedFd : stepSyscall m openSlice (.openat none input {} 0) = (.ok fd,opened))
    (high : FileReads fd ino 65536 bytes 0 opened s₀ q₀ before₀)
    (low : FileReads fd ino 3 bytes 0 opened s₁ q₁ before₁)
    (closed₀ : stepSyscall before₀ close₀ (.close fd) = (.ok (),end₀))
    (closed₁ : stepSyscall before₁ close₁ (.close fd) = (.ok (),end₁)) :
    runPrefix (whole.observe q₀.length) m (openSlice :: (s₀ ++ [close₀])) =
      (.done (.ok bytes.data.toList),end₀) ∧
    runPrefix (streamed.observe q₁.length) m (openSlice :: (s₁ ++ [close₁])) =
      (.done (.ok bytes.data.toList),end₁) ∧
    sameDescriptors end₀ m ∧ sameDescriptors end₁ m ∧
    ∃ lines final, LineRun fdCap (.ready {fd,chunkSize := 65536}) q₀ lines final ∧
      LineRun fdCap (.ready {fd,chunkSize := 65536}) q₁ lines final := by
  have baseResult := readFileAll_refines_spec fdCap pathCap openedFd high closed₀
  have lowContents := low.contents
  obtain ⟨_,a⟩ := shadowFile high 65536 (by decide)
  obtain ⟨_,b⟩ := shadowFile low 65536 (by decide)
  have common : delivered q₁ = delivered q₀ := lowContents.1.trans high.contents.1.symm
  rw [common] at b
  have both := ioBuf_chunk_confluence fdCap ({fd,chunkSize := 65536} : BufReader) rfl a b
  refine ⟨baseResult.1,Executes.run ?_,baseResult.2,
    close_restores (open_fresh openedFd) lowContents.2 (close_fds closed₁),_,_,both.2.2.1,both.2.2.2.1⟩
  let r : BufReader := {fd,chunkSize := 3}
  let lines := (r.frame.chunk (delivered q₁)).lines
  have readRun : Executes ((readLines fdCap r).observe q₁.length) opened s₁ (.ok lines) before₁ :=
    lineKernel fdCap low r [] rfl rfl rfl
  have bytesEq : lines.flatten = bytes.data.toList := by
    simp [lines, Framing.flatten_lines, chunk_preserves, r, BufReader.pending, lowContents.1]
  let use := FsLib.andThen (readLines fdCap r) fun xs => pure (Ret.ok xs.flatten)
  have used : Executes (use.observe q₁.length) opened s₁ (.ok bytes.data.toList) before₁ := by
    rw [← List.append_nil s₁, ← bytesEq]
    exact readRun.bind (.done _ _)
  apply Executes.ask openedFd
  exact used.bind (.ask closed₁ (.done _ _))

/-- Instantiate both sides on a concrete inode. Keep an unrelated descriptor
    open to exercise close restoration in addition to empty-table startup. -/
def modelCheck : IO Unit := do
  let data : Bytes := [65,10,10,0,255,13,10,90]
  let setupSlices := List.replicate 20 canonicalSlice
  let (.done (.ok ()),dirs) := runPrefix
      ((mkdirP pathCap [47,102,105,120,116,117,114,101,115]).observe 20) {} setupSlices
    | throw (IO.userError "model fixture directory")
  let (.done (.ok ()),files) := runPrefix ((writeFileTrunc fdCap pathCap input data).observe 20) dirs setupSlices
    | throw (IO.userError "model fixture file")
  let (.ok _,held) := stepSyscall files canonicalSlice (.openat none input {} 0)
    | throw (IO.userError "model unrelated descriptor")
  for (program,width) in [(whole,7),(streamed,1)] do
    let progress : StepSlice := {maxBytes := width}
    let schedule := canonicalSlice :: (List.replicate 24 [{intrBefore := true},progress]).flatten
    let (.done (.ok got),after) := runPrefix (program.observe 64) held schedule
      | throw (IO.userError "model did not reach EOF and close")
    unless got == data && held.fds.toList == after.fds.toList do
      throw (IO.userError "model returned different file bytes or changed a descriptor binding")
  let exhausted := {held with proc := {held.proc with limit := 0}}
  let (.done (.err .EMFILE),failed) := runPrefix (whole.observe 1) exhausted [canonicalSlice]
    | throw (IO.userError "model open did not report EMFILE")
  unless exhausted.fds.toList == failed.fds.toList do throw (IO.userError "failed open changed descriptors")

end Test.LiftIoShowcase

open Lojita.Kernel

def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "expected directory for static showcase executables")
  Test.LiftIoShowcase.modelCheck
  let source ← IO.FS.readFile "Test/Posix/Gen/LiftIo.lean"
  let checked ← IO.ofExcept (parseLeanMod source)
  let wrong := ["Gen","LiftIo","wrongCaps"]
  let rejected ← try
    checkVerifiedEntry [checked] ⟨wrong⟩ .posix
    pure false
  catch e =>
    unless (toString e).startsWith "ENTRY_TYPE_MISMATCH:" do throw e
    pure true
  unless rejected do throw (IO.userError "POSIX checker accepted an entry with the wrong capabilities")
  for entry in ["base", "refined", "argvEcho"] do
    compileVerifiedExe [checked] ⟨["Gen","LiftIo",entry]⟩ .posix (System.FilePath.mk dir / entry)
