import LojitaCtx.Io.LineRefinement

namespace LojitaCtx.Io
open LojitaCtx.Posix FsLib

/-- The bytes returned by one positive read on a stationary finite input. -/
def nextChunk (bs : Bytes) (off size : Nat) (sl : StepSlice) : Bytes :=
  (bs.drop off).take (min (max 1 size) (max 1 sl.maxBytes))

/-- Progress is determined entirely by input bytes, requested read size and
    slice schedule. No execution result or final machine is assumed. -/
inductive Progressing (bs : Bytes) (size : Nat) : Nat → List StepSlice → List (Ret Bytes) → Prop where
  | eof {sl : StepSlice} (awake : sl.intrBefore = false) :
    Progressing bs size bs.length [sl] [.ok []]
  | data {off sl b chunk slices answers} (awake : sl.intrBefore = false)
    (piece : nextChunk bs off size sl = b::chunk)
    (tail : Progressing bs size (off+(b::chunk).length) slices answers) :
    Progressing bs size off (sl::slices) (.ok (b::chunk)::answers)
  | interrupted {off sl slices answers} (intr : sl.intrBefore = true)
    (tail : Progressing bs size off slices answers) :
    Progressing bs size off (sl::slices) (.err .EINTR::answers)

def AttemptStep (bytes : Bytes) (fd : Fd) (atOffset : Nat → Machine) (off : Nat)
    (source interrupted : Machine) : Prop :=
  ∀ (size : Nat) (sl : StepSlice), stepSyscall source sl (.read fd (max 1 size)) =
    if sl.intrBefore then (.err .EINTR,interrupted)
    else let bs := nextChunk bytes off size sl; (.ok bs,atOffset (off + bs.length))

abbrev CursorStep (bytes : Bytes) (fd : Fd) (atOffset : Nat → Machine) (off : Nat) (source : Machine) : Prop :=
  AttemptStep bytes fd atOffset off source (atOffset off)

/-- A device cursor gives the whole machine at a physical offset. Implementors
    prove one actual Linux-model read for every offset, size and slice. -/
def CursorLaw (bytes : Bytes) (fd : Fd) (atOffset : Nat → Machine) : Prop :=
  ∀ off, CursorStep bytes fd atOffset off (atOffset off)

theorem Progressing.replay {bs fd atOffset size off ss qs}
    (cursor : CursorLaw bs fd atOffset) (schedule : Progressing bs size off ss qs) :
    MachineReads fd size (atOffset off) ss qs (atOffset bs.length) ∧ delivered qs = bs.drop off := by
  induction schedule with
  | @eof sl awake =>
    refine ⟨.eof ?_,by simp [delivered]⟩
    simpa [awake,nextChunk] using cursor bs.length size sl
  | @data off sl b chunk slices answers awake piece tail ih =>
    refine ⟨.data (by simpa [awake,piece] using cursor off size sl) ih.1,?_⟩
    change (b::chunk) ++ delivered answers = _
    rw [ih.2, ← List.drop_drop, ← piece]
    exact prefix_remaining _ _
  | @interrupted off sl slices answers intr tail ih =>
    exact ⟨.interrupted (by simpa [intr] using cursor off size sl) ih.1,ih.2⟩

/-- Some kernel objects initialize accounting metadata on the first read.
    A source may therefore enter the cursor family on its first transition. -/
theorem Progressing.startReplay {bs fd atOffset size off ss qs source}
    (cursor : CursorLaw bs fd atOffset) (initial : CursorStep bs fd atOffset off source)
    (schedule : Progressing bs size off ss qs) :
    MachineReads fd size source ss qs (atOffset bs.length) ∧ delivered qs = bs.drop off := by
  refine ⟨?_,(schedule.replay cursor).2⟩
  cases schedule with
  | @eof sl awake => exact .eof (by simpa [awake,nextChunk] using initial size sl)
  | @data off sl b chunk slices answers awake piece tail =>
    exact .data (by simpa [awake,piece] using initial size sl) (tail.replay cursor).1
  | @interrupted off sl slices answers intr tail =>
    exact .interrupted (by simpa [intr] using initial size sl) (tail.replay cursor).1

/-- An interrupted first read can cache device metadata before transferring
    any bytes. Arbitrarily many such interruptions lead to the same EOF state. -/
theorem Progressing.preparedReplay {bs fd atOffset size off ss qs}
    (cursor : CursorLaw bs fd atOffset) (schedule : Progressing bs size off ss qs)
    {source prepared : Machine} (first : AttemptStep bs fd atOffset off source prepared)
    (again : AttemptStep bs fd atOffset off prepared prepared) :
    MachineReads fd size source ss qs (atOffset bs.length) ∧ delivered qs = bs.drop off := by
  refine ⟨?_,(schedule.replay cursor).2⟩
  induction schedule generalizing source prepared with
  | @eof sl awake => exact .eof (by simpa [awake,nextChunk] using first size sl)
  | @data off sl b chunk slices answers awake piece tail ih =>
    exact .data (by simpa [awake,piece] using first size sl) (tail.replay cursor).1
  | @interrupted off sl slices answers intr tail ih =>
    exact .interrupted (by simpa [intr] using first size sl) (ih again again)

def BufferedObservations {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (fd size : Nat) (payload : Bytes)
    (slices : List StepSlice) (depth : Nat) (start final : Machine) : Prop :=
  let r : BufReader := {fd,chunkSize := size}
  runPrefix ((readAll cap r).observe depth) start slices =
    (.done (.ok payload,{r.clear with eof := true}),final) ∧
  runPrefix ((readLines cap r).observe depth) start slices =
    (.done (.ok (({} : Framing).chunk payload).lines),final)

theorem BufferedObservations.append_unused {Δ : List Cap} {cap : .fdIoCap ∈ Δ}
    {fd size payload slices depth start final}
    (run : BufferedObservations cap fd size payload slices depth start final) (unused : List StepSlice) :
    BufferedObservations cap fd size payload (slices ++ unused) depth start final :=
  ⟨runPrefix_done_append run.1 unused,runPrefix_done_append run.2 unused⟩

theorem buffered_observations {Δ : List Cap} (cap : .fdIoCap ∈ Δ) {size fd start final ss qs payload}
    (steps : MachineReads fd size start ss qs final) (content : delivered qs = payload) :
    BufferedObservations cap fd size payload ss qs.length start final := by
  let r : BufReader := {fd,chunkSize := size}
  have whole := readKernel cap steps r rfl rfl rfl
  have lines := linesMachineReads cap steps r [] rfl rfl rfl
  have w : r.pending ++ delivered qs = payload := by simpa [r,BufReader.pending] using content
  rw [w] at whole
  rw [content] at lines
  constructor
  · apply Executes.run
    rw [← List.append_nil ss]
    exact whole.bind (.done _ _)
  · exact Executes.run lines

/-- Four real runPrefix evaluations, two input schedules and read sizes, one
    shared structural Machine value. readLines drives the readLine machine,
    preserving delimited lines and the final unterminated tail. -/
theorem machine_chunk_confluence {Δ : List Cap} (cap : .fdIoCap ∈ Δ) {bytes fd atOffset off source}
    (cursor : CursorLaw bytes fd atOffset) (initial : CursorStep bytes fd atOffset off source) {n₁ n₂ ss₁ ss₂ qs₁ qs₂}
    (first : Progressing bytes n₁ off ss₁ qs₁) (second : Progressing bytes n₂ off ss₂ qs₂) :
    BufferedObservations cap fd n₁ (bytes.drop off) ss₁ qs₁.length source (atOffset bytes.length) ∧
    BufferedObservations cap fd n₂ (bytes.drop off) ss₂ qs₂.length source (atOffset bytes.length) := by
  obtain ⟨run₁,bs₁⟩ := first.startReplay cursor initial
  obtain ⟨run₂,bs₂⟩ := second.startReplay cursor initial
  exact ⟨buffered_observations cap run₁ bs₁,buffered_observations cap run₂ bs₂⟩

end LojitaCtx.Io
