import LojitaCtx.Io.Lines
import LojitaCtx.Io.FileRefinement

namespace LojitaCtx.Io
open LojitaCtx.Posix FsLib

private theorem batchEof {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (r : BufReader) (rev : List Bytes) :
    lineBatchStep cap (.ready {r with eof := true}, rev) = .done (.ok (rev.reverse ++ r.frame.lines)) := by
  cases hx : r.buf.data.toList.drop r.pos <;>
    simp [lineBatchStep, readStep, BufReader.inspect, hx, BufReader.frame, Framing.lines, List.append_assoc]

private def unqueued (r : BufReader) : BufReader := {r with ready := []}

private theorem oneLineRead {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {r : BufReader} {rev : List Bytes} {m sl q next rest n result z}
    (awake : r.eof = false) (step : stepSyscall m sl (.read r.fd (max 1 r.chunkSize)) = (q.map List.toByteArray,next))
    (tail : Executes (PosixMachine.unfoldPrefix (lineBatchStep cap) n
      ((unqueued r).receive q, r.ready.reverse ++ rev)) next rest result z) :
    Executes (PosixMachine.unfoldPrefix (lineBatchStep cap) (n+1) (.ready r,rev)) m (sl::rest) result z := by
  rw [PosixMachine.unfoldPrefix]
  simp only [lineBatchStep, readStep, BufReader.inspect, awake, Bool.false_eq_true, ite_false]
  apply Executes.ask step
  let rr : BufReader := {fd := r.fd, chunkSize := r.chunkSize, buf := r.buf, pos := r.pos}
  change Executes (PosixMachine.unfoldPrefix (lineBatchStep cap) n (rr.receivePacked (q.map List.toByteArray), r.ready.reverse ++ rev)) next rest result z
  rw [BufReader.receivePacked_list]
  simpa only [unqueued,awake,rr] using tail

theorem linesMachineReads {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {fd size m slices qs z} (t : MachineReads fd size m slices qs z)
    (r : BufReader) (rev : List Bytes) (desc : r.fd = fd) (count : r.chunkSize = size) (awake : r.eof = false) :
    Executes (PosixMachine.unfoldPrefix (lineBatchStep cap) qs.length (.ready r,rev))
      m slices (.ok (rev.reverse ++ (r.frame.chunk (delivered qs)).lines)) z := by
  induction t generalizing r rev with
  | @eof m sl z step =>
    apply oneLineRead cap (n := 0) (q := .ok []) (next := z) awake (by rw [desc,count] <;> exact step)
    change Executes (PosixMachine.unfoldPrefix (lineBatchStep cap) 0
      (.ready {(unqueued r) with eof := true}, _)) _ _ _ _
    rw [PosixMachine.unfoldPrefix, batchEof, queue_frame r (delivered [.ok []])]
    simp [unqueued, delivered, Framing.chunk, List.append_assoc]
    exact .done _ _
  | @data m sl next slices qs z b bs step rest ih =>
    apply oneLineRead cap (n := qs.length) (q := .ok (b::bs)) (next := next) awake (by rw [desc,count] <;> exact step)
    have tail := ih ((unqueued r).ingest (b::bs)) (r.ready.reverse ++ rev) desc count awake
    change Executes _ _ _ (Ret.ok (rev.reverse ++ (r.frame.chunk ((b::bs) ++ delivered qs)).lines)) _
    rw [queue_frame]
    simpa only [List.reverse_append, List.reverse_reverse, List.append_assoc, chunk_append,
      unqueued, BufReader.ingest, frame_withFrame, BufReader.receive] using tail
  | @interrupted m sl next slices qs z step rest ih =>
    apply oneLineRead cap (n := qs.length) (q := .err .EINTR) (next := next) awake (by rw [desc,count] <;> exact step)
    have tail := ih (unqueued r) (r.ready.reverse ++ rev) desc count awake
    rw [queue_frame]
    simpa only [List.reverse_append, List.reverse_reverse, List.append_assoc, unqueued, delivered,
      BufReader.receive] using tail

theorem lineKernel {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {fd ino size bytes off m slices qs z} (t : FileReads fd ino size bytes off m slices qs z)
    (r : BufReader) (rev : List Bytes) (desc : r.fd = fd) (count : r.chunkSize = size) (awake : r.eof = false) :
    Executes (PosixMachine.unfoldPrefix (lineBatchStep cap) qs.length (.ready r,rev))
      m slices (.ok (rev.reverse ++ (r.frame.chunk (delivered qs)).lines)) z :=
  linesMachineReads cap t.machineReads r rev desc count awake

def closedInput (xs : Bytes) : StreamBuf := {pendingBytes := xs, writers := 0}

/-- Project actual file completions onto a closed pipe. Matching chunk
    boundaries witness the stream theorem on the same reply transcript. -/
theorem shadowFile {fd ino size bytes off m slices qs z}
    (trace : FsLib.FileReads fd ino size bytes off m slices qs z) (cap : Nat)
    (bound : size ≤ cap) : ∃ ss, ReadTrace cap (closedInput (delivered qs)) ss qs (closedInput []) := by
  induction trace with
  | eof _ _ =>
    refine ⟨[canonicalSlice],ReadTrace.eof ?_⟩
    rfl
  | @data off m sl next slices qs z b bs file step rest ih =>
    obtain ⟨ss,tail⟩ := ih
    obtain ⟨hx,_⟩ := inode_chunk file step
    have l := congrArg List.length hx
    simp only [List.length_cons, List.length_take] at l
    have bounded : bs.length + 1 ≤ max 1 cap := by omega
    let chunk : StepSlice := {maxBytes := bs.length+1}
    refine ⟨chunk::ss, ReadTrace.data (next := closedInput (delivered qs)) ?_ tail⟩
    simp [closedInput, delivered, streamRead, chunk, Nat.min_eq_left bounded]
  | @interrupted off m sl slices qs z step rest ih =>
    obtain ⟨ss,tail⟩ := ih
    let interrupt : StepSlice := {intrBefore := true}
    exact ⟨interrupt::ss, ReadTrace.interrupted (sl := interrupt) rfl tail⟩

end LojitaCtx.Io
