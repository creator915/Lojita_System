import LojitaCtx.Io.Buf

namespace LojitaCtx.Io
open LojitaCtx.Posix

def Framing.bytes (f : Framing) : Bytes :=
  f.completeRev.reverse.flatten ++ f.tailRev.reverse

theorem byte_preserves (s : Framing) (b : UInt8) :
    (s.byte b).bytes = s.bytes ++ [b] := by
  by_cases h : b = lf <;> simp [Framing.byte, h, Framing.bytes, List.append_assoc]

theorem chunk_preserves (s : Framing) (bs : Bytes) :
    (s.chunk bs).bytes = s.bytes ++ bs := by
  induction bs generalizing s with
  | nil => simp [Framing.chunk]
  | cons b rest ih =>
    change ((s.byte b).chunk rest).bytes = _
    simp [ih, byte_preserves, List.append_assoc]

@[simp] theorem pending_frame (r : BufReader) : r.frame.bytes = r.pending := by
  simp [BufReader.frame, Framing.bytes, BufReader.pending]

@[simp] theorem pending_ingest (r : BufReader) (bs : Bytes) :
    (r.ingest bs).pending = r.pending ++ bs := by
  rw [← pending_frame, BufReader.ingest, frame_withFrame, chunk_preserves, pending_frame]

def endStream (s : StreamBuf) : StreamBuf := {s with pendingBytes := []}

private theorem read_preserves_metadata (sl : StepSlice) (s : StreamBuf) :
    endStream (streamRead sl false s).2 = endStream s := by
  cases hi : sl.intrBefore <;> cases hp : s.pendingBytes <;> simp [streamRead, hi, hp, endStream]

private theorem read_zero_end (sl : StepSlice) (s z : StreamBuf)
    (h : streamRead sl false s = (.ok [], z)) :
    s.pendingBytes = [] ∧ z = endStream s := by
  cases hi : sl.intrBefore <;> cases hp : s.pendingBytes with
  | nil =>
    simp [streamRead, hi, hp] at h
    all_goals obtain ⟨_, rfl⟩ := h; cases s; simp_all [endStream]
  | cons b bs => simp [streamRead, hi, hp] at h

/-- A completed positive-size Linux read trace. The evidence is the *actual*
    stream transition at each observed slice, including pre-transfer interrupts. -/
inductive ReadTrace (size : Nat) :
    StreamBuf → List StepSlice → List (Ret Bytes) → StreamBuf → Prop where
  | eof {s z sl} (step : streamRead {sl with maxBytes := min sl.maxBytes (max 1 size)}
        false s = (.ok [], z)) : ReadTrace size s [sl] [.ok []] z
  | data {s z next sl ss replies b bs}
      (step : streamRead {sl with maxBytes := min sl.maxBytes (max 1 size)}
        false s = (.ok (b :: bs), next))
      (rest : ReadTrace size next ss replies z) :
      ReadTrace size s (sl :: ss) (.ok (b :: bs) :: replies) z
  | interrupted {s z next sl ss replies}
      (step : streamRead {sl with maxBytes := min sl.maxBytes (max 1 size)}
        false s = (.err .EINTR, next))
      (rest : ReadTrace size next ss replies z) :
      ReadTrace size s (sl :: ss) (.err .EINTR :: replies) z

def delivered : List (Ret Bytes) → Bytes
  | [] => []
  | .ok bs :: tail => bs ++ delivered tail
  | _ :: tail => delivered tail

theorem ReadTrace.contents {size s slices replies z} (t : ReadTrace size s slices replies z) :
    delivered replies = s.pendingBytes ∧ z = endStream s := by
  induction t with
  | eof step =>
    obtain ⟨h, hz⟩ := read_zero_end _ _ _ step
    simp [delivered, h, hz]
  | @data s z next sl ss replies b bs step rest ih =>
    have h := streamRead_byte_conservation _ _ _ _ _ step
    have hmeta :=  read_preserves_metadata {sl with maxBytes := min sl.maxBytes (max 1 size)} s
    rw [step] at hmeta
    exact ⟨(congrArg (_ ++ ·) ih.1).trans h, ih.2.trans hmeta⟩
  | interrupted step rest ih =>
    have h := streamRead_blocked_preserves _ _ _ (Or.inr (Or.inl (congrArg Prod.fst step)))
    rw [step] at h
    simp only at h
    simpa [h, delivered] using ih

/-- Execute the actual buffered machine on a typed sequence of read completions. -/
def readAnswers (rs : List (Ret Bytes)) : List Answer :=
  rs.map fun r => ⟨.packed, r.map List.toByteArray⟩

/-- Exact replay consumes every supplied answer. This permits compositional
    proofs across a sequence of calls, including the closing call after EOF. -/
inductive Finishes {Δ : List Cap} {A : Type} : Prefix Δ A → List Answer → A → Prop where
  | done (a : A) : Finishes (.done a) [] a
  | ask {op : SysOp} {h : op.cap ∈ Δ} {next : Ret op.Result → Prefix Δ A}
      {answer rest value} (run : Finishes (next (answer.get op)) rest value) :
      Finishes (.ask op h next) (answer :: rest) value

theorem Finishes.bind {Δ : List Cap} {A B : Type} {p : Prefix Δ A} {rs : List Answer} {a : A}
    (r : Finishes p rs a) {f : A → Prefix Δ B} {ss : List Answer} {b : B}
    (t : Finishes (f a) ss b) : Finishes (p.bind f) (rs ++ ss) b := by
  induction r with
  | done => exact t
  | ask _ ih => exact .ask (ih t)

theorem Finishes.after {Δ : List Cap} {A : Type} {p : Prefix Δ A} {rs : List Answer} {a : A}
    (r : Finishes p rs a) : p.after rs = .done a := by
  induction r with
  | done => rfl
  | ask _ ih => exact ih

inductive ReadsToEof : List (Ret Bytes) → Prop where
  | eof : ReadsToEof [.ok []]
  | data (b : UInt8) (bs : Bytes) {rest} (next : ReadsToEof rest) :
    ReadsToEof (.ok (b :: bs) :: rest)
  | interrupt {rest} (next : ReadsToEof rest) : ReadsToEof (.err .EINTR :: rest)

theorem ReadTrace.toEof {size s slices replies z} (trace : ReadTrace size s slices replies z) :
    ReadsToEof replies := by
  induction trace with
  | eof _ => exact .eof
  | data _ _ ih => exact .data _ _ ih
  | interrupted _ _ ih => exact .interrupt ih

private theorem clear_receive (r : BufReader) (bs : Bytes) :
    (r.ingest bs).clear = r.clear := rfl

private theorem read_one {Δ : List Cap} (h : .fdIoCap ∈ Δ) (mode : ReadMode) (r : BufReader)
    (needs : r.inspect mode = none) (q : Ret Bytes) (rest : List (Ret Bytes)) (value : ReadResult)
    (tail : Finishes (PosixMachine.unfoldPrefix (readStep h mode) rest.length (r.receive q))
      (readAnswers rest) value) :
    Finishes (PosixMachine.unfoldPrefix (readStep h mode) (rest.length + 1) (.ready r))
      (readAnswers (q :: rest)) value := by
  rw [PosixMachine.unfoldPrefix]
  simp only [readStep, needs]
  apply Finishes.ask
  change Finishes (PosixMachine.unfoldPrefix _ _ (r.receivePacked (q.map List.toByteArray))) _ _
  simpa only [BufReader.receivePacked_list, readAnswers] using tail

theorem readAll_core {Δ : List Cap} {rs : List (Ret Bytes)} (h : .fdIoCap ∈ Δ)
    (t : ReadsToEof rs) (r : BufReader) (awake : r.eof = false) :
    Finishes ((PosixMachine.unfold (.ready r) (readStep h .all)).observe rs.length)
      (readAnswers rs) (.ok (some (r.pending ++ delivered rs)), {r.clear with eof := true}) := by
  rw [PosixMachine.observe_unfold]
  induction t generalizing r with
  | eof =>
    apply read_one h .all r (by simp [BufReader.inspect, awake]) (.ok []) []
    simp only [delivered, List.append_nil]
    exact .done _
  | data b bs _ ih =>
    apply read_one h .all r (by simp [BufReader.inspect, awake]) (.ok (b::bs))
    simpa [delivered, List.append_assoc, clear_receive, PosixMachine.unfold, BufReader.receive] using ih (r.ingest (b::bs)) awake
  | interrupt _ ih =>
    apply read_one h .all r (by simp [BufReader.inspect, awake]) (.err .EINTR)
    exact ih r awake

theorem readAll_finishes {Δ : List Cap} {rs : List (Ret Bytes)} (h : .fdIoCap ∈ Δ)
    (t : ReadsToEof rs) (r : BufReader) (awake : r.eof = false) :
    Finishes ((readAll h r).observe rs.length) (readAnswers rs)
      (.ok (r.pending ++ delivered rs), {r.clear with eof := true}) := by
  rw [readAll, readBytes, PosixMachine.observe_map]
  have core := readAll_core h t r awake
  rw [← List.append_nil (readAnswers rs)]
  exact core.bind (.done _)

end LojitaCtx.Io
