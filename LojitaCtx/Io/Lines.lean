import LojitaCtx.Io.Confluence

namespace LojitaCtx.Io
open LojitaCtx.Posix

/-- A run of repeated calls to the readLine transition. A completed line starts
    a new call with the returned reader. A syscall reply resumes the same call. -/
inductive LineRun {Δ : List Cap} (cap : .fdIoCap ∈ Δ) :
    ReadProgress → List (Ret Bytes) → List Bytes → BufReader → Prop where
  | eof {state final} (done : readStep cap .line state = .done (.ok none, final)) :
    LineRun cap state [] [] final
  | line {state next bs replies lines final}
    (done : readStep cap .line state = .done (.ok (some bs), next))
    (rest : LineRun cap (.ready next) replies lines final) :
    LineRun cap state replies (bs :: lines) final
  | read {state fd count reply replies lines final k}
    (ask : readStep cap .line state = .ask (.read fd count) cap k)
    (rest : LineRun cap (k reply) replies lines final) :
    LineRun cap state (reply :: replies) lines final

def Framing.prepend (f : Framing) (xs : List Bytes) : Framing :=
  {f with completeRev := f.completeRev ++ xs.reverse}

private theorem byte_prepend (f : Framing) (xs : List Bytes) (b : UInt8) :
    (f.prepend xs).byte b = (f.byte b).prepend xs := by
  by_cases hb : b = lf <;> simp [Framing.byte, Framing.prepend, hb]

private theorem chunk_prepend (f : Framing) (xs : List Bytes) (bs : Bytes) :
    (f.prepend xs).chunk bs = (f.chunk bs).prepend xs := by
  induction bs generalizing f with
  | nil => rfl
  | cons x xs ih =>
    change (((f.prepend _).byte x).chunk xs) = ((f.byte x).chunk xs).prepend _
    rw [byte_prepend, ih]

private theorem lines_prepend (f : Framing) (xs : List Bytes) :
    (f.prepend xs).lines = xs ++ f.lines := by
  simp [Framing.prepend, Framing.lines, List.append_assoc]

theorem queue_frame (r : BufReader) (bs : Bytes) :
    (r.frame.chunk bs).lines = r.ready ++ (({r with ready := []} : BufReader).frame.chunk bs).lines := by
  have h : r.frame = (({r with ready := []} : BufReader).frame).prepend r.ready := by
    simp [BufReader.frame, Framing.prepend]
  conv => lhs; rw [h, chunk_prepend, lines_prepend]

private theorem drain {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (r : BufReader)
    {qs ls final} (h : LineRun cap (.ready {r with ready := []}) qs ls final) :
    LineRun cap (.ready r) qs (r.ready ++ ls) final := by
  cases r with
  | mk fd size buf pos ready eof =>
    induction ready with
    | nil => exact h
    | cons line rest ih =>
      apply LineRun.line (next := ⟨fd,size,buf,pos,rest,eof⟩)
      · rfl
      · exact ih h

private theorem consume_eof {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (r : BufReader)
    (empty : r.ready = []) :
    LineRun cap (.ready {r with eof := true}) [] r.frame.lines {r.clear with eof := true} := by
  cases hx : r.buf.data.toList.drop r.pos with
  | nil =>
    have emptyLines : r.frame.lines = [] := by simp [BufReader.frame, Framing.lines, empty, hx]
    rw [emptyLines]
    apply LineRun.eof
    simp [readStep, BufReader.inspect, empty, hx, BufReader.clear, BufReader.withFrame]
  | cons b bs =>
    have oneLine : r.frame.lines = [b :: bs] := by
      simp [BufReader.frame, Framing.lines, empty, hx]
    rw [oneLine]
    apply LineRun.line (next := {r.clear with eof := true})
    · simp [readStep, BufReader.inspect, empty, hx, BufReader.clear, BufReader.withFrame]
    · apply LineRun.eof
      rfl

theorem readLines_run {Δ : List Cap} (cap : .fdIoCap ∈ Δ) {qs}
    (t : ReadsToEof qs) (r : BufReader) (awake : r.eof = false) :
    LineRun cap (.ready r) qs (r.frame.chunk (delivered qs)).lines {r.clear with eof := true} := by
  induction t generalizing r with
  | eof =>
    rw [queue_frame]
    apply drain
    apply LineRun.read (fd := r.fd) (count := max 1 r.chunkSize)
      (k := ({r with ready := []} : BufReader).receive)
    · simp [readStep, BufReader.inspect, awake]
    · exact consume_eof cap {r with ready := []} rfl
  | @data b bs rest _ ih =>
    rw [queue_frame]
    apply drain
    let clean : BufReader := {r with ready := []}
    apply LineRun.read (fd := r.fd) (count := max 1 r.chunkSize) (k := clean.receive)
    · simp [clean, readStep, BufReader.inspect, awake]
    · have tail := ih (clean.ingest (b::bs)) awake
      change LineRun cap (.ready (clean.ingest (b::bs))) rest (clean.frame.chunk ((b::bs) ++ delivered rest)).lines _
      rw [chunk_append]
      have hc : (clean.ingest (b::bs)).clear = r.clear := rfl
      rw [hc] at tail
      simpa only [BufReader.ingest, frame_withFrame] using tail
  | interrupt _ ih =>
    rw [queue_frame]
    apply drain
    let clean : BufReader := {r with ready := []}
    apply LineRun.read (fd := r.fd) (count := max 1 r.chunkSize) (k := clean.receive)
    · simp [clean, readStep, BufReader.inspect, awake]
    · exact ih clean awake

/-- Two independent progressing slice schedules, including interrupted syscalls,
    produce the same bytes, lines and stream state. Both userland observations
    are the actual readAll / readLine transition systems. -/
theorem stream_chunk_confluence {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (r : BufReader)
    (awake : r.eof = false) {s a b q₁ q₂ z₁ z₂}
    (one : ReadTrace r.chunkSize s a q₁ z₁) (two : ReadTrace r.chunkSize s b q₂ z₂) :
    let final := {r.clear with eof := true}
    let bytes := r.pending ++ s.pendingBytes
    let lines := (r.frame.chunk s.pendingBytes).lines
    Finishes ((readAll cap r).observe q₁.length) (readAnswers q₁) (.ok bytes, final) ∧
    Finishes ((readAll cap r).observe q₂.length) (readAnswers q₂) (.ok bytes, final) ∧
    LineRun cap (.ready r) q₁ lines final ∧ LineRun cap (.ready r) q₂ lines final ∧ z₁ = z₂ := by
  obtain ⟨hb₁,hz₁⟩ := one.contents
  obtain ⟨hb₂,hz₂⟩ := two.contents
  exact ⟨hb₁ ▸ readAll_finishes cap one.toEof r awake, hb₂ ▸ readAll_finishes cap two.toEof r awake,
    hb₁ ▸ readLines_run cap one.toEof r awake, hb₂ ▸ readLines_run cap two.toEof r awake, hz₁.trans hz₂.symm⟩

theorem Framing.flatten_lines (f : Framing) : f.lines.flatten = f.bytes := by
  cases h : f.tailRev <;> simp [Framing.lines, Framing.bytes, h]

end LojitaCtx.Io
