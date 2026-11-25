import Gen.LiftIo
import LojitaCtx.Io.RegularCursor
import LojitaCtx.Io.KernelConfluence
import Lojita.Kernel.Driver

namespace Test.LiftIoShowcase
open Gen.LiftIo LojitaCtx.Posix LojitaCtx.Io LojitaCtx.Io.FsLib

private theorem regularReads {fd ino size off slices qs} {data : ByteArray} {atOff : Nat → Machine}
    (law : CursorLaw data.data.toList fd atOff)
    (regular : ∀ i, AtRegular (atOff i) fd ino data i)
    (progress : Progressing data.data.toList size off slices qs) :
    FileReads fd ino size data off (atOff off) slices qs (atOff data.data.toList.length) := by
  induction progress with
  | @eof sl awake =>
    exact .eof (regular _) (by simpa only [awake,Bool.false_eq_true,ite_false,nextChunk,List.drop_length,List.take_nil,List.length_nil,Nat.add_zero] using law data.data.toList.length size sl)
  | @data off sl b chunk slices answers awake piece tail ih =>
    exact .data (regular _) (by simpa [awake,piece] using law off size sl) ih
  | @interrupted off sl slices answers intr tail ih =>
    exact .interrupted (by simpa [intr] using law off size sl) ih

/-- Two progressing schedules start from one stationary inode. T15 supplies the
    common state at EOF, and T16 supplies the file result and FD restoration. -/
theorem lift_square {m opened closed : Machine} {fd ino : Nat} {e : FdEntry}
    {d : OpenFileDesc} {node : Inode} {bytes : ByteArray} {openSlice close₀ close₁ s₀ s₁ q₀ q₁}
    (openedFd : stepSyscall m openSlice (.openat none input {} 0) = (.ok fd,opened))
    (backed : fdLinks opened.proc opened.kernel.ofds) (entry : opened.fds[fd]? = some e)
    (desc : opened.kernel.ofds[e.ofd]? = some d) (reg : d.target = .inode ino)
    (access : d.flags.access ≠ .writeOnly) (start : d.offset = 0)
    (found : opened.kernel.vfs.node ino = .ok node) (contents : node.payload = .reg bytes)
    (high : Progressing bytes.data.toList 65536 0 s₀ q₀)
    (low : Progressing bytes.data.toList 3 0 s₁ q₁)
    (release : stepSyscall (fileCursor opened e.ofd d bytes.data.toList.length) close₀ (.close fd) = (.ok (),closed)) :
    runPrefix (whole.observe (q₀.length+2)) m (openSlice :: (s₀ ++ [close₀])) =
      (.done (.ok bytes.data.toList),closed) ∧
    runPrefix (streamed.observe (q₁.length+2)) m (openSlice :: (s₁ ++ [close₁])) =
      (.done (.ok bytes.data.toList),closed) ∧ sameDescriptors closed m := by
  let atOff := fileCursor opened e.ofd d
  have law := regular_cursor_law opened fd e d ino node bytes backed entry desc reg access found contents
  have initial : atOff 0 = opened := start ▸ fileCursor_initial opened e.ofd d desc
  have regular (i : Nat) : AtRegular (atOff i) fd ino bytes i := by
    have fe : (atOff i).fds[fd]? = some e := entry
    let current := {d with offset := i}
    have ofd : (atOff i).kernel.ofds[e.ofd]? = some current := Std.TreeMap.getElem?_insert_self
    exact ⟨e.ofd,current,node,by simp [Machine.lookup,fe,ofd]; rfl,reg,access,rfl,found,contents⟩
  have highTrace := regularReads (atOff := atOff) law regular high
  rw [initial] at highTrace
  have base := readFileAll_refines_spec fdCap pathCap openedFd highTrace release
  have firstStep : CursorStep bytes.data.toList fd atOff 0 opened := initial ▸ law 0
  obtain ⟨trace,_⟩ := low.startReplay law firstStep
  have highAt : MachineReads fd 65536 (atOff 0) s₀ q₀ (atOff bytes.data.toList.length) := by
    rw [initial]; exact highTrace.machineReads
  have lowAt : MachineReads fd 3 (atOff 0) s₁ q₁ (atOff bytes.data.toList.length) := by
    rw [initial]; exact trace
  have both := ioBuf_chunk_confluence fdCap (cursor_finite_law (cursor := atOff) law) (Nat.zero_le _) highAt lowAt
  have expected := both.2.2.2
  rw [initial] at expected
  let r : BufReader := {fd,chunkSize := 3}
  let lines := (r.frame.chunk (delivered q₁)).lines
  have lineRun : Executes ((readLines fdCap r).observe q₁.length) opened s₁ (.ok lines) (atOff bytes.data.toList.length) :=
    by simpa only [readLines,PosixMachine.observe_unfold,List.reverse_nil,List.nil_append,lines] using
        linesMachineReads fdCap trace r [] rfl rfl rfl
  have sameRun := lineRun.run.symm.trans expected
  have sameLines : lines = (({} : Framing).chunk bytes.data.toList).lines := by
    simpa using Ret.ok.inj (SimOutcome.done.inj (congrArg Prod.fst sameRun))
  have dataEq : lines.flatten = bytes.data.toList := by
    rw [sameLines, Framing.flatten_lines, chunk_preserves]
    rfl
  let use (i : Fd) := (readLines fdCap {fd := i,chunkSize := 3}).map (Ret.map List.flatten)
  have used : Executes ((use fd).observe q₁.length) opened s₁ (.ok bytes.data.toList) (atOff bytes.data.toList.length) := by
    rw [show (use fd).observe q₁.length = ((readLines fdCap r).observe q₁.length).bind
      (fun x => .done (x.map List.flatten)) from PosixMachine.observe_map _ _ _, ← List.append_nil s₁]
    conv => arg 4; rw [← dataEq]
    exact lineRun.bind (.done _ _)
  have released : stepSyscall (atOff bytes.data.toList.length) close₁ (.close fd) = (.ok (),closed) := release
  refine ⟨base.1,Executes.run ?_,base.2⟩
  apply Executes.ask openedFd
  exact used.withFd_body fdCap (FreeSys.call (.openat none input {} 0) pathCap) use released

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
  let check {S : Type} (program : PosixMachine CoreCaps S (Ret Bytes)) (width : Nat) : IO Unit := do
    let progress : StepSlice := {maxBytes := width}
    let schedule := canonicalSlice :: (List.replicate 24 [{intrBefore := true},progress]).flatten
    let (.done (.ok got),after) := runPrefix (program.observe 64) held schedule
      | throw (IO.userError "model did not reach EOF and close")
    unless got == data && held.fds.toList == after.fds.toList do
      throw (IO.userError "model returned different file bytes or changed a descriptor binding")
  check whole 7
  check streamed 1
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
    checkVerifiedEntry [checked] ⟨wrong⟩
    pure false
  catch e =>
    unless (toString e).startsWith "ENTRY_TYPE_MISMATCH:" do throw e
    pure true
  unless rejected do throw (IO.userError "POSIX checker accepted an entry with the wrong capabilities")
  for entry in ["base", "refined", "argvEcho"] do
    compileVerifiedExe [checked] ⟨["Gen","LiftIo",entry]⟩ (System.FilePath.mk dir / entry)
  let signals ← IO.ofExcept (parseLeanMod (← IO.FS.readFile "Test/Posix/Gen/SignalPoll.lean"))
  compileVerifiedExe [signals] ⟨["Gen","SignalPoll","app"]⟩ (System.FilePath.mk dir / "signalPoll")

  let stream ← IO.ofExcept (parseLeanMod (← IO.FS.readFile "Test/Posix/Gen/CopyBytes.lean"))
  compileVerifiedExe [stream] ⟨["Gen","CopyBytes","app"]⟩ (System.FilePath.mk dir / "copyBytes")
