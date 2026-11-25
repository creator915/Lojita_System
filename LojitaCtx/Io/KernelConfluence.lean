import LojitaCtx.Io.MachineConfluence

namespace LojitaCtx.Io
open LojitaCtx.Posix FsLib

/-- A finite deterministic input until its next observable EOF. Each clause is
    a one-syscall device law. Nonempty transfers may stop before the requested
    count (for instance at a canonical record boundary). EOF has its own
    post-state, which need not produce EOF if the program reads again. -/
structure FiniteReadLaw (bytes : Bytes) (fd : Fd) (cursor : Nat → Machine) (afterEof : Machine) : Prop where
  input : ∀ (off size : Nat) (sl : StepSlice) (b : UInt8) (bs : Bytes) (next : Machine), off ≤ bytes.length →
    stepSyscall (cursor off) sl (.read fd (max 1 size)) = (.ok (b::bs),next) →
    let advance := off+(b::bs).length
    (b::bs) ++ bytes.drop advance = bytes.drop off ∧ next = cursor advance
  interrupt : ∀ (off size : Nat) (sl : StepSlice) (next : Machine), off ≤ bytes.length →
    stepSyscall (cursor off) sl (.read fd (max 1 size)) = (.err .EINTR,next) → next = cursor off
  eof : ∀ (off size : Nat) (sl : StepSlice) (next : Machine), off ≤ bytes.length →
    stepSyscall (cursor off) sl (.read fd (max 1 size)) = (.ok [],next) →
    bytes.drop off = [] ∧ next = afterEof

/-- A source that fills each requested slice also satisfies the general finite-input law. -/
theorem cursor_finite_law {bytes fd cursor} (law : CursorLaw bytes fd cursor) :
    FiniteReadLaw bytes fd cursor (cursor bytes.length) := by
  constructor
  · intro off size sl b bs next within step
    rw [law off size sl] at step
    cases hi : sl.intrBefore <;> simp [hi] at step
    obtain ⟨piece,rfl⟩ := step
    have bytesEq := Ret.ok.inj piece
    dsimp only
    rw [← bytesEq, ← List.drop_drop]
    exact ⟨prefix_remaining _ _,rfl⟩
  · intro off size sl next within step
    rw [law off size sl] at step
    cases hi : sl.intrBefore <;> simp [hi] at step
    exact step.symm
  · intro off size sl next within step
    rw [law off size sl] at step
    cases hi : sl.intrBefore <;> simp [hi] at step
    obtain ⟨empty,rfl⟩ := step
    have len := congrArg List.length (Ret.ok.inj empty)
    simp [nextChunk,List.length_drop] at len
    have pos : 0 < min (max 1 size) (max 1 sl.maxBytes) := by omega
    have last : off = bytes.length := by omega
    simp [last,nextChunk]

theorem FiniteReadLaw.completed {bytes fd cursor afterEof} (law : FiniteReadLaw bytes fd cursor afterEof)
    {m n size ss qs} (trace : MachineReads fd size m ss qs n) {off} (start : m = cursor off) (within : off ≤ bytes.length) :
    delivered qs = bytes.drop off ∧ n = afterEof := by
  induction trace generalizing off with
  | @eof m sl n step =>
    subst m
    obtain ⟨empty,fin⟩ := law.eof off size sl n within step
    exact ⟨empty.symm,fin⟩
  | @data m sl next ss qs n b bs step rest ih =>
    subst m
    obtain ⟨piece,advance⟩ := law.input off size sl b bs next within step
    have len := congrArg List.length piece
    simp only [List.length_append, List.length_drop] at len
    obtain ⟨tail,fin⟩ := ih advance (by omega)
    exact ⟨(congrArg ((b::bs) ++ ·) tail).trans piece,fin⟩
  | @interrupted m sl next ss qs n step rest ih =>
    subst m
    exact ih (law.interrupt off size sl next within step) within

/-- Two *actual* completed read traces of possibly different sizes, cut at
    arbitrary kernel-selected boundaries. The number and timing of interrupts
    may differ. All four buffered runs reach the very same whole machine. -/
theorem ioBuf_chunk_confluence {Δ : List Cap} (cap : .fdIoCap ∈ Δ) {bytes fd cursor afterEof off}
    (law : FiniteReadLaw bytes fd cursor afterEof) (within : off ≤ bytes.length) {n₁ n₂ ss₁ ss₂ qs₁ qs₂ z₁ z₂}
    (one : MachineReads fd n₁ (cursor off) ss₁ qs₁ z₁)
    (two : MachineReads fd n₂ (cursor off) ss₂ qs₂ z₂) :
    z₁ = z₂ ∧ BufferedObservations cap fd n₁ (bytes.drop off) ss₁ qs₁.length (cursor off) afterEof ∧
    BufferedObservations cap fd n₂ (bytes.drop off) ss₂ qs₂.length (cursor off) afterEof := by
  obtain ⟨b₁,h₁⟩ := law.completed one rfl within
  obtain ⟨b₂,h₂⟩ := law.completed two rfl within
  exact ⟨h₁.trans h₂.symm, h₁ ▸ buffered_observations cap one b₁, h₂ ▸ buffered_observations cap two b₂⟩

end LojitaCtx.Io
