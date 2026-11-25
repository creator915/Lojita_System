import LojitaCtx.Io.MachineConfluence
import LojitaCtx.Posix.Kernel.InsertMapping

namespace LojitaCtx.Io
open LojitaCtx.Posix FsLib

private theorem drop_take_length (xs : Bytes) (n : Nat) : xs.drop (xs.take n).length = xs.drop n := by
  apply List.append_cancel_left (as := xs.take n)
  rw [prefix_remaining, List.take_append_drop]

theorem closed_stream (s : StreamBuf) (closed : s.writers = 0) (nb : Bool)
    (sl : StepSlice) (n : Nat) (positive : 0 < n) :
    streamRead {sl with maxBytes := n} nb s =
      if sl.intrBefore then (.err .EINTR,s)
      else let bs := s.pendingBytes.take n; (.ok bs,{s with pendingBytes := s.pendingBytes.drop bs.length}) := by
  cases hi : sl.intrBefore
  · simp only [Bool.false_eq_true,ite_false]
    rw [drop_take_length]
    cases n with
    | zero => omega
    | succ k =>
      cases hp : s.pendingBytes with
      | nil => simp [streamRead,hp,closed]; cases s; simp_all
      | cons b bs => simp [streamRead,hp]
  · simp [streamRead]

private theorem pipe_read (m : Machine) (fd id i size : Nat) (d : OpenFileDesc)
    (s : StreamBuf) (sl : StepSlice) (look : m.lookup fd = .ok (id,d))
    (r : d.flags.access ≠ .writeOnly) (pipe : d.target = .pipe i false)
    (present : m.kernel.pipes[i]? = some s) (closed : s.writers = 0)
    (backed : fdLinks m.proc m.kernel.ofds) :
    let ps := m.pages i s
    let n := min (max 1 size) (max 1 sl.maxBytes)
    stepSyscall m sl (.read fd (max 1 size)) =
      if sl.intrBefore then (.err .EINTR, (m.setPipe i s).setPages i ps)
      else let bs := s.pendingBytes.take n
           (.ok bs, (m.setPipe i {s with pendingBytes := s.pendingBytes.drop bs.length}).setPages i
              (PipePages.consume ps bs.length)) := by
  intro ps n
  have stream := closed_stream s closed d.flags.nonblock sl n (by dsimp [n]; omega)
  have nonzero : max 1 size ≠ 0 := by omega
  cases hi : sl.intrBefore
  · let bs := s.pendingBytes.take n
    let next := (m.setPipe i {s with pendingBytes := s.pendingBytes.drop bs.length}).setPages i (PipePages.consume ps bs.length)
    have raw : dispatchSyscall m sl (.read fd (max 1 size)) = .ok (.ok bs,next) := by
      simp only [hi,Bool.false_eq_true,ite_false,n] at stream
      simp [dispatchSyscall,fdRead,look,r,pipe,present,nonzero,hi,stream,
        Bind.bind,Except.bind,Pure.pure,Except.pure,bs,next,ps,n] <;> rfl
    simp only [stepSyscall,raw,show fdLinks next.proc next.kernel.ofds from backed,
      ite_true,SysOp.publishesRead,Bool.false_eq_true,ite_false] <;> rfl
  · let next := (m.setPipe i s).setPages i ps
    have raw : dispatchSyscall m sl (.read fd (max 1 size)) = .ok (.err .EINTR,next) := by
      simp only [hi,ite_true,n] at stream
      simp [dispatchSyscall,fdRead,look,r,pipe,present,nonzero,hi,stream,Bind.bind,Except.bind,
        Pure.pure,Except.pure,next,ps] <;> rfl
    simp only [stepSyscall,raw,show fdLinks next.proc next.kernel.ofds from backed,SysOp.publishesRead,ite_true] <;> rfl

def pipeCursor (m : Machine) (i : PipeId) (s : StreamBuf) (ps : PipePages) (off : Nat) : Machine :=
  (m.setPipe i {s with pendingBytes := s.pendingBytes.drop off}).setPages i (PipePages.consume ps off)

theorem pipe_cursor_law (m : Machine) (fd id i : Nat) (d : OpenFileDesc) (s : StreamBuf) (ps : PipePages)
    (backed : fdLinks m.proc m.kernel.ofds) (look : m.lookup fd = .ok (id,d))
    (pipe : d.target = .pipe i false) (readable : d.flags.access ≠ .writeOnly)
    (closed : s.writers = 0) : CursorLaw s.pendingBytes fd (pipeCursor m i s ps) := by
  intro off size sl
  let here := pipeCursor m i s ps off
  let stream := {s with pendingBytes := s.pendingBytes.drop off}
  have seen : here.kernel.pipes[i]? = some stream := Std.TreeMap.getElem?_insert_self
  have cached : here.pages i stream = PipePages.consume ps off := by
    simp [here,pipeCursor,Machine.pages,Machine.setPages]
  have read := pipe_read here fd id i size d stream sl look readable pipe seen closed backed
  change stepSyscall here sl _ = _
  rw [read]
  simp only [cached]
  cases hi : sl.intrBefore <;>
    simp [here,pipeCursor,Machine.setPipe,Machine.setPages,table_insert_overwrite,stream,nextChunk,PipePages.consume_add,List.drop_drop]

/-- All closed read ends, including older machines with no cached page layout.
    The first read obtains the layout via Machine.pages, whether it returns
    bytes, EOF, or EINTR; subsequent reads preserve its exact physical shape. -/
theorem closed_pipe_confluence {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    (m : Machine) (fd id i : Nat) (d : OpenFileDesc) (s : StreamBuf)
    (backed : fdLinks m.proc m.kernel.ofds) (look : m.lookup fd = .ok (id,d))
    (pipe : d.target = .pipe i false) (readable : d.flags.access ≠ .writeOnly)
    (present : m.kernel.pipes[i]? = some s) (closed : s.writers = 0)
    {n₁ n₂ ss₁ ss₂ qs₁ qs₂}
    (first : Progressing s.pendingBytes n₁ 0 ss₁ qs₁) (second : Progressing s.pendingBytes n₂ 0 ss₂ qs₂) :
    let final := pipeCursor m i s (m.pages i s) s.pendingBytes.length
    BufferedObservations cap fd n₁ s.pendingBytes ss₁ qs₁.length m final ∧
    BufferedObservations cap fd n₂ s.pendingBytes ss₂ qs₂.length m final := by
  let ps := m.pages i s
  let ready := (m.setPipe i s).setPages i ps
  let atOff := pipeCursor m i s ps
  have cursor := pipe_cursor_law m fd id i d s ps backed look pipe readable closed
  have start : AttemptStep s.pendingBytes fd atOff 0 m ready := by
    intro size sl
    simpa only [atOff,pipeCursor,ps,ready,nextChunk,List.drop_zero,Nat.zero_add]
      using pipe_read m fd id i size d s sl look readable pipe present closed backed
  have prepared : AttemptStep s.pendingBytes fd atOff 0 ready ready := by
    intro size sl
    have entry : ready.kernel.pipes[i]? = some s := Std.TreeMap.getElem?_insert_self
    have cached : ready.pages i s = ps := by simp [Machine.pages,ready,Machine.setPages]
    have read := pipe_read ready fd id i size d s sl look readable pipe entry closed backed
    dsimp only at read
    rw [cached] at read
    rw [read]
    simp only [atOff,pipeCursor,ready,nextChunk,List.drop_zero,Nat.zero_add,Machine.setPages,
      Machine.setPipe,table_insert_overwrite]
  have a := first.preparedReplay cursor start prepared
  have b := second.preparedReplay cursor start prepared
  exact ⟨buffered_observations cap a.1 a.2,buffered_observations cap b.1 b.2⟩

end LojitaCtx.Io
