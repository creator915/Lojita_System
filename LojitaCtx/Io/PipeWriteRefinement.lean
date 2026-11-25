import LojitaCtx.Io.FileRefinement

namespace LojitaCtx.Io
open LojitaCtx.Posix LojitaCtx.Io.FsLib


/-- Kernel runs with a finite number of interrupted or successful write steps.
    Success sizes come from stepSyscall; no constructor assumes conservation. -/
inductive MachineWrites : BufWriter → Machine → List StepSlice → Machine → Prop where
  | done {w m} (empty : w.remaining = []) : MachineWrites w m [] m
  | data {w m sl n next rest z} (nonempty : w.remaining ≠ [])
    (step : stepSyscall m sl (.write w.fd w.remaining) = (.ok n,next))
    (tail : MachineWrites (w.advance n) next rest z) : MachineWrites w m (sl :: rest) z
  | interrupt {w m sl next rest z} (nonempty : w.remaining ≠ [])
    (step : stepSyscall m sl (.write w.fd w.remaining) = (.err .EINTR,next))
    (tail : MachineWrites w next rest z) : MachineWrites w m (sl :: rest) z

/-- The descriptor initially holds a writable open description of the pipe. -/
def PipeWriterAt (m : Machine) (fd id : Nat) : Prop :=
  ∃ (e : FdEntry) (d : OpenFileDesc), m.fds[fd]? = some e ∧
    m.kernel.ofds[e.ofd]? = some d ∧ d.target = .pipe id true ∧ d.flags.access ≠ .readOnly

private def Transfer (input before after : Bytes) : Ret Nat → Prop
  | .ok n => 0 < n ∧ n ≤ input.length ∧ after = before ++ input.take n
  | .err .EINTR => after = before
  | _ => True

private theorem stream_transfer (s : StreamBuf) (sl : StepSlice) (nb : Bool)
    (bs : Bytes) (nonempty : bs ≠ []) :
    let (r,next) := streamWrite sl nb bs s
    Transfer bs s.pendingBytes next.pendingBytes r := by
  have hn : bs.isEmpty = false := by simpa using nonempty
  simp only [streamWrite, hn, Bool.false_eq_true, ite_false]
  split
  · trivial
  split
  · rfl
  split
  · cases nb <;> trivial
  · rename_i room
    have free : s.freeSpace > 0 := by
      by_cases hz : s.freeSpace = 0
      · simp [hz] at room
      · omega
    have positive := List.length_pos_iff.mpr nonempty
    split <;> simp [Transfer] <;> omega

private theorem page_transfer (s : StreamBuf) (ps : PipePages) (sl : StepSlice) (nb : Bool)
    (bs : Bytes) (nonempty : bs ≠ []) :
    let (r,next,_) := PipePages.write ps sl nb bs s
    Transfer bs s.pendingBytes next.pendingBytes r := by
  unfold PipePages.write
  simp only [Id.run, Pure.pure]
  split
  · cases nb <;> trivial
  · exact stream_transfer s _ nb bs nonempty

private theorem publish_pipe {m : Machine} {fd i : Nat}
    (held : PipeWriterAt m fd i) (s : StreamBuf) (ps : PipePages) :
    let n := ((m.setPipe i s).setPages i ps).account
    PipeWriterAt n fd i ∧ ∃ out, n.kernel.pipes[i]? = some out ∧ out.pendingBytes = s.pendingBytes := by
  obtain ⟨e,d,hfd,hdesc,target,allowed⟩ := held
  have mem := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hfd
  have refs : 0 < fdCount m.proc e.ofd := List.countP_pos_iff.mpr ⟨(fd,e),mem,by simp⟩
  let ds := liveOfds m.proc m.kernel.ofds
  let live := {d with refcnt := fdCount m.proc e.ofd}
  have found : ds[e.ofd]? = some live := by simp [ds,liveOfds,hdesc,Nat.ne_of_gt refs,live]
  have writes : 0 < targetCount ds (.pipe i true) :=
    List.countP_pos_iff.mpr ⟨(e.ofd,live),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr found,by simp [live,target]⟩
  refine ⟨⟨e,live,hfd,found,target,allowed⟩,?_⟩
  let out := {s with readers := targetCount ds (.pipe i false), writers := targetCount ds (.pipe i true)}
  refine ⟨out,?_,rfl⟩
  change (livePipes (m.kernel.pipes.insert i s) ds)[i]? = some out
  simp [livePipes,out,Nat.ne_of_gt writes]


private theorem actual_transfer {m after : Machine} {fd i : Nat} {sl : StepSlice}
    {s : StreamBuf} {bs : Bytes} {r : Ret Nat}
    (held : PipeWriterAt m fd i) (pipe : m.kernel.pipes[i]? = some s) (nonempty : bs ≠ [])
    (notIo : r ≠ .err .EIO) (notPipe : r ≠ .err .EPIPE)
    (step : stepSyscall m sl (.write fd bs) = (r,after)) :
    PipeWriterAt after fd i ∧ ∃ out, after.kernel.pipes[i]? = some out ∧
      Transfer bs s.pendingBytes out.pendingBytes r := by
  obtain ⟨e,d,hfd,hdesc,target,allowed⟩ := held
  have lookup : m.lookup fd = .ok (e.ofd,d) := by
    simp [Machine.lookup,hfd,hdesc,Pure.pure,Except.pure]
  generalize hr : PipePages.write (m.pages i s) sl d.flags.nonblock bs s = result
  obtain ⟨actual,next,ps⟩ := result
  let updated := (m.setPipe i next).setPages i ps
  let published := if actual = .err .EPIPE then updated.signal .pipe else updated
  have raw : dispatchSyscall m sl (.write fd bs) = .ok (actual,published) := by
    simp [dispatchSyscall, fdWrite, lookup, target, allowed, pipe, hr,
      Bind.bind, Except.bind, Pure.pure, Except.pure, updated, published] <;> rfl
  cases hl : fdLinks published.proc published.kernel.ofds with
  | false =>
    simp only [stepSyscall,raw,hl,Bool.false_eq_true,ite_false] at step
    change ((Ret.err .EIO : Ret Nat),m) = (r,after) at step
    exact False.elim (notIo (Prod.mk.inj step).1.symm)
  | true =>
    have same : actual = r := by simpa [stepSyscall,raw,hl] using congrArg (fun pair : Ret Nat × Machine => pair.1) step
    subst actual
    have hp : published = updated := by simp [published,notPipe]
    have okLinks : fdLinks updated.proc updated.kernel.ofds = true := hp ▸ hl
    have state : updated.account = after := by
      simpa [stepSyscall,raw,hp,okLinks] using congrArg Prod.snd step
    subst after
    obtain ⟨stable,out,existsOut,bytes⟩ :=
      publish_pipe (m := m) (fd := fd) (i := i) ⟨e,d,hfd,hdesc,target,allowed⟩ next ps
    refine ⟨stable,out,existsOut,?_⟩
    rw [bytes]
    have theory := page_transfer s (m.pages i s) sl d.flags.nonblock bs nonempty
    simpa [hr] using theory

/-- For any schedule of successful or interrupted kernel writes, the executable
    user program terminates at exactly the recorded machine. The complete input
    occurs once in that pipe, including after short writes and retries. -/
theorem writeAll_pipe_refines {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {w : BufWriter} {m z : Machine} {slices : List StepSlice} {i : PipeId} {s : StreamBuf}
    (held : PipeWriterAt m w.fd i) (pipe : m.kernel.pipes[i]? = some s)
    (trace : MachineWrites w m slices z) :
    runPrefix ((writeAll cap w).observe slices.length) m slices =
        (.done (.ok (),{w with remaining := [], written := w.written + w.remaining.length}),z) ∧
    ∃ out, z.kernel.pipes[i]? = some out ∧ out.pendingBytes = s.pendingBytes ++ w.remaining := by
  induction trace generalizing s with
  | @done w m empty =>
    constructor
    · simp only [writeAll,PosixProg.unfold,PosixProg.unfoldPrefix,writeStep,empty,
                 List.isEmpty_nil,ite_true,runPrefix,List.length_nil,Nat.add_zero]
      cases w; simp_all
    · exact ⟨s,pipe,by simp [empty]⟩
  | @data w m sl n next rest z nonempty step tail ih =>
    obtain ⟨live,buf,present,positive,bounded,bytes⟩ :=
      actual_transfer (r := .ok n) held pipe nonempty (by intro h; cases h) (by intro h; cases h) step
    obtain ⟨ran,out,existsOut,final⟩ := ih live present
    have hn : w.remaining.isEmpty = false := by simpa using nonempty
    have resume : w.receive (.ok n) = .ready (w.advance n) := by
      simp [BufWriter.receive,Nat.ne_of_gt positive,Nat.not_lt.mpr bounded]
    constructor
    · change runPrefix (PosixProg.unfoldPrefix (writeStep cap) (rest.length+1) (.ready w)) m _ = _
      rw [PosixProg.unfoldPrefix]
      simp only [writeStep,hn,Bool.false_eq_true,ite_false,runPrefix,step]
      change runPrefix (PosixProg.unfoldPrefix (writeStep cap) rest.length (w.receive (.ok n))) next rest = _
      rw [resume]
      simpa [writeAll,PosixProg.unfold,BufWriter.advance,Nat.add_assoc,Nat.add_sub_of_le bounded] using ran
    · refine ⟨out,existsOut,?_⟩
      rw [final,bytes]
      simp [BufWriter.advance,List.append_assoc]
  | @interrupt w m sl next rest z nonempty step tail ih =>
    obtain ⟨live,buf,present,bytes⟩ :=
      actual_transfer (r := .err .EINTR) held pipe nonempty (by intro h; cases h) (by intro h; cases h) step
    obtain ⟨ran,out,existsOut,final⟩ := ih live present
    have hn : w.remaining.isEmpty = false := by simpa using nonempty
    constructor
    · change runPrefix (PosixProg.unfoldPrefix (writeStep cap) (rest.length+1) (.ready w)) m _ = _
      rw [PosixProg.unfoldPrefix]
      simp only [writeStep,hn,Bool.false_eq_true,ite_false,runPrefix,step,BufWriter.receive]
      exact ran
    · exact ⟨out,existsOut,final.trans (by rw [show buf.pendingBytes = s.pendingBytes from bytes])⟩

/-- Two progressing schedules agree on the public writer result and every byte
    retained by the actual pipe. Internal page allocation can depend on where a
    write stopped. -/
theorem writeAll_pipe_schedule_confluence {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {w : BufWriter} {m z₁ z₂ : Machine} {a b : List StepSlice} {i : PipeId} {s : StreamBuf}
    (held : PipeWriterAt m w.fd i) (pipe : m.kernel.pipes[i]? = some s)
    (one : MachineWrites w m a z₁) (two : MachineWrites w m b z₂) :
    (runPrefix ((writeAll cap w).observe a.length) m a).1 =
      (runPrefix ((writeAll cap w).observe b.length) m b).1 ∧
    (z₁.kernel.pipes[i]?).map StreamBuf.pendingBytes = (z₂.kernel.pipes[i]?).map StreamBuf.pendingBytes := by
  obtain ⟨run₁,s₁,lookup₁,bytes₁⟩ := writeAll_pipe_refines cap held pipe one
  obtain ⟨run₂,s₂,lookup₂,bytes₂⟩ := writeAll_pipe_refines cap held pipe two
  simp [run₁,run₂,lookup₁,lookup₂,bytes₁,bytes₂]

end LojitaCtx.Io
