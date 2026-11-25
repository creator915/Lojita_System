import LojitaCtx.Io.Confluence

namespace LojitaCtx.Io
open LojitaCtx.Posix

private theorem write_success (s : StreamBuf) (sl : StepSlice) (bs : Bytes) (n : Nat)
    (next : StreamBuf) (nonempty : bs ≠ []) (h : streamWrite sl false bs s = (.ok n, next)) :
    0 < n ∧ n ≤ bs.length ∧ next.pendingBytes = s.pendingBytes ++ bs.take n := by
  have hn : bs.isEmpty = false := by cases bs <;> simp_all
  unfold streamWrite at h
  simp only [hn, Bool.false_eq_true, ite_false] at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h
  · cases h
  · split at h
    · obtain ⟨hnat,rfl⟩ := Prod.mk.inj h
      cases Ret.ok.inj hnat
      exact ⟨List.length_pos_iff.mpr nonempty, Nat.le_refl _, rfl⟩
    · obtain ⟨hnat,rfl⟩ := Prod.mk.inj h
      cases Ret.ok.inj hnat
      have bl := List.length_pos_iff.mpr nonempty
      have free : 0 < s.freeSpace := by
        by_cases zero : s.freeSpace = 0
        · simp [zero] at *
        · omega
      exact ⟨by omega, by omega, rfl⟩

private theorem write_intr (s : StreamBuf) (sl : StepSlice) (bs : Bytes) (next : StreamBuf)
    (h : streamWrite sl false bs s = (.err .EINTR, next)) : next = s := by
  unfold streamWrite at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h
  · exact (Prod.mk.inj h).2.symm
  · split at h <;> cases h

inductive WriteTrace : BufWriter → StreamBuf → List StepSlice → List (Ret Nat) → StreamBuf → Prop where
  | done {w s} (empty : w.remaining = []) : WriteTrace w s [] [] s
  | data {w s sl n next slices qs z} (nonempty : w.remaining ≠ [])
    (step : streamWrite sl false w.remaining s = (.ok n,next))
    (tail : WriteTrace (w.advance n) next slices qs z) :
    WriteTrace w s (sl::slices) (.ok n :: qs) z
  | interrupt {w s sl next slices qs z} (nonempty : w.remaining ≠ [])
    (step : streamWrite sl false w.remaining s = (.err .EINTR,next))
    (tail : WriteTrace w next slices qs z) : WriteTrace w s (sl::slices) (.err .EINTR :: qs) z

def writeAnswers (qs : List (Ret Nat)) : List Answer := qs.map fun q => ⟨.nat,q⟩

/-- A successful writeAll under any progressing Linux write trace commits each
    input byte once, including after arbitrary short writes and interrupts. -/
theorem writeAll_chunk_confluence {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {w s slices qs z} (t : WriteTrace w s slices qs z) :
    Finishes ((writeAll cap w).observe qs.length) (writeAnswers qs)
      (.ok (), {w with remaining := [], written := w.written + w.remaining.length}) ∧
    z.pendingBytes = s.pendingBytes ++ w.remaining := by
  induction t with
  | @done w s empty =>
    constructor
    · change Finishes (PosixProg.unfoldPrefix (writeStep cap) 0 (.ready w)) [] _
      rw [PosixProg.unfoldPrefix]
      simp only [writeStep, empty, List.isEmpty_nil, ite_true, List.length_nil, Nat.add_zero]
      cases w; simp_all; exact .done _
    · simp [empty]
  | @data w s sl n next slices qs z nonempty step tail ih =>
    obtain ⟨positive,bounded,pending⟩ := write_success _ _ _ _ _ nonempty step
    have hn : w.remaining.isEmpty = false := by simpa using nonempty
    have hnext : w.receive (.ok n) = .ready (w.advance n) := by
      simp [BufWriter.receive, Nat.ne_of_gt positive, Nat.not_lt.mpr bounded]
    constructor
    · change Finishes (PosixProg.unfoldPrefix (writeStep cap) (qs.length+1) (.ready w)) _ _
      rw [PosixProg.unfoldPrefix]
      simp only [writeStep, hn, Bool.false_eq_true, ite_false]
      apply Finishes.ask
      change Finishes (PosixProg.unfoldPrefix (writeStep cap) qs.length (w.receive (.ok n))) _ _
      rw [hnext]
      simpa [writeAnswers, writeAll, PosixProg.unfold, BufWriter.advance, Nat.add_assoc, Nat.add_sub_of_le bounded]
        using ih.1
    · rw [ih.2, pending]
      simp [BufWriter.advance, List.append_assoc]
  | @interrupt w s sl next slices qs z nonempty step tail ih =>
    have hn : w.remaining.isEmpty = false := by simpa using nonempty
    constructor
    · change Finishes (PosixProg.unfoldPrefix (writeStep cap) (qs.length+1) (.ready w)) _ _
      rw [PosixProg.unfoldPrefix]
      simp only [writeStep, hn, Bool.false_eq_true, ite_false]
      exact .ask ih.1
    · exact write_intr _ _ _ _ step ▸ ih.2

end LojitaCtx.Io
