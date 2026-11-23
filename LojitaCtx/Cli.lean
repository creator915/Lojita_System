import LojitaCtx.WorldLaws

namespace LojitaCtx.Cli

open Terminal PosixChannel World

def scanStdinLoopW {Δ : List Cap} {S A : Type} (h : CapMem .stdioCap Δ) (sc : ByteScanner S A) :
    Nat → S → WorldProg Δ (Option A)
  | 0, _ => .pure none
  | fuel + 1, s => worldBind (readStdinByteW h) fun
    | none => .pure (some (sc.onEOF s))
    | some b => match sc.onByte s b with
      | .done a => .pure (some a)
      | .more next => scanStdinLoopW h sc fuel next
termination_by structural fuel _ => fuel

/-- Bound the number of stdin pulls. A pull yielding `none` calls the scanner's EOF handler. -/
def scanStdinFuelW {Δ : List Cap} {S A : Type} (h : CapMem .stdioCap Δ) (fuel : Nat)
    (sc : ByteScanner S A) : WorldProg Δ (Option A) :=
  scanStdinLoopW h sc fuel sc.init

private theorem run_bind_readStdinByteW {Δ : List Cap} {A : Type} (h : CapMem .stdioCap Δ)
    (k : Option Byte → WorldProg Δ A) (w : SimWorld) {ch : InChan} (input : w.stdio.stdin = ch) :
    runWorldPure (worldBind (readStdinByteW h) k) w =
      runWorldPure (k (popChanByte ch).1) { w with stdio := { w.stdio with stdin := (popChanByte ch).2 } } := by
  subst ch
  rfl

private theorem run_scanStdinLoopW_emit_prefix {Δ : List Cap} {S A : Type} (h : CapMem .stdioCap Δ)
    (sc : ByteScanner S A) (s : S) (p rem extra : Bytes) (a : A) (fuel : Nat)
    (closed waited : Bool) (w : SimWorld)
    (emits : runScannerFrom sc s p false false = (.emit a, InChan.inChan rem false false))
    (enough : p.length ≤ fuel) (input : w.stdio.stdin = InChan.inChan (p ++ extra) closed waited) :
    runWorldPure (scanStdinLoopW h sc fuel s) w =
      (some a, { w with stdio := { w.stdio with stdin := InChan.inChan (rem ++ extra) closed waited } }) := by
  induction p generalizing s fuel w with
  | nil => simp [runScannerFrom] at emits
  | cons b bs ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      rw [scanStdinLoopW, run_bind_readStdinByteW h _ w input]
      simp only [List.cons_append, popChanByte]
      cases step : sc.onByte s b with
      | done value =>
        simp [runScannerFrom, step] at emits
        obtain ⟨rfl, rfl⟩ := emits
        rfl
      | more next =>
        simp only [runScannerFrom, step] at emits
        exact ih next fuel _ emits (Nat.le_of_succ_le_succ enough) rfl

/-- Only the emitting prefix needs fuel, regardless of the length or closure of the remaining input. -/
theorem run_scanStdinFuelW_emit_prefix {Δ : List Cap} {S A : Type} (h : CapMem .stdioCap Δ)
    (sc : ByteScanner S A) (p rem extra : Bytes) (a : A) (fuel : Nat) (closed waited : Bool) (w : SimWorld)
    (emits : evalScanner sc (openPipe p) = (.emit a, InChan.inChan rem false false))
    (enough : p.length ≤ fuel) (input : w.stdio.stdin = InChan.inChan (p ++ extra) closed waited) :
    runWorldPure (scanStdinFuelW h fuel sc) w =
      (some a, { w with stdio := { w.stdio with stdin := InChan.inChan (rem ++ extra) closed waited } }) :=
  run_scanStdinLoopW_emit_prefix h sc sc.init p rem extra a fuel closed waited w emits enough input

private theorem run_scanStdinLoopW_closed_eof {Δ : List Cap} {S A : Type} (h : CapMem .stdioCap Δ)
    (sc : ByteScanner S A) (s : S) (p : Bytes) (a : A) (fuel : Nat) (waited : Bool) (w : SimWorld)
    (ended : runScannerFrom sc s p true false = (.ended a, emptyClosedPipe))
    (enough : p.length < fuel) (input : w.stdio.stdin = InChan.inChan p true waited) :
    runWorldPure (scanStdinLoopW h sc fuel s) w =
      (some a, { w with stdio := { w.stdio with stdin := InChan.inChan [] true waited } }) := by
  induction p generalizing s fuel w with
  | nil =>
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ enough).elim
    | succ fuel =>
      have value : sc.onEOF s = a := by simpa [runScannerFrom, emptyClosedPipe, closedPipe] using ended
      rw [scanStdinLoopW, run_bind_readStdinByteW h _ w input, ← value]
      rfl
  | cons b bs ih =>
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ enough).elim
    | succ fuel =>
      rw [scanStdinLoopW, run_bind_readStdinByteW h _ w input]
      simp only [popChanByte]
      cases step : sc.onByte s b with
      | done value => simp [runScannerFrom, step] at ended
      | more next =>
        simp only [runScannerFrom, step] at ended
        exact ih next fuel _ ended (Nat.lt_of_succ_lt_succ enough) rfl

/-- A scanner that finishes at EOF needs one additional pull after the last byte. -/
theorem run_scanStdinFuelW_closed_eof {Δ : List Cap} {S A : Type} (h : CapMem .stdioCap Δ)
    (sc : ByteScanner S A) (p : Bytes) (a : A) (fuel : Nat) (waited : Bool) (w : SimWorld)
    (ended : evalScanner sc (closedPipe p) = (.ended a, emptyClosedPipe))
    (enough : p.length < fuel) (input : w.stdio.stdin = InChan.inChan p true waited) :
    runWorldPure (scanStdinFuelW h fuel sc) w =
      (some a, { w with stdio := { w.stdio with stdin := InChan.inChan [] true waited } }) :=
  run_scanStdinLoopW_closed_eof h sc sc.init p a fuel waited w ended enough input

private def readExactLoopW {Δ : List Cap} (h : CapMem .stdioCap Δ) : Nat → Bytes → WorldProg Δ Bytes
  | 0, revAcc => .pure revAcc.reverse
  | n + 1, revAcc => worldBind (readStdinByteW h) fun
    | none => .pure revAcc.reverse
    | some b => readExactLoopW h n (b :: revAcc)
termination_by structural n _ => n

/-- Read up to `n` bytes, returning the collected prefix if a pull yields `none`. -/
def readExactBytesW {Δ : List Cap} (h : CapMem .stdioCap Δ) (n : Nat) : WorldProg Δ Bytes :=
  readExactLoopW h n []

private theorem run_readExactLoopW_prefix {Δ : List Cap} (h : CapMem .stdioCap Δ)
    (p extra revAcc : Bytes) (w : SimWorld) (input : w.stdio.stdin = openPipe (p ++ extra)) :
    runWorldPure (readExactLoopW h p.length revAcc) w =
      (revAcc.reverse ++ p, { w with stdio := { w.stdio with stdin := openPipe extra } }) := by
  induction p generalizing revAcc w with
  | nil =>
    simp only [List.nil_append] at input
    rw [← input, List.append_nil]
    rfl
  | cons b bs ih =>
    rw [List.length_cons, readExactLoopW, run_bind_readStdinByteW h _ w input]
    simp only [List.cons_append, openPipe, popChanByte]
    rw [show revAcc.reverse ++ b :: bs = (b :: revAcc).reverse ++ bs by simp]
    exact ih (b :: revAcc) _ rfl

theorem run_readExactBytesW_open_prefix {Δ : List Cap} (h : CapMem .stdioCap Δ)
    (n : Nat) (p extra : Bytes) (w : SimWorld) (size : p.length = n)
    (input : w.stdio.stdin = openPipe (p ++ extra)) :
    runWorldPure (readExactBytesW h n) w =
      (p, { w with stdio := { w.stdio with stdin := openPipe extra } }) := by
  subst n
  exact run_readExactLoopW_prefix h p extra [] w input

structure StreamReply : Type where
  stdout : Bytes
  stderr : Bytes
  exitCode : ExitCode

def feedScannerChunk {S : Type} (sc : ByteScanner S StreamReply) : S → Bytes → ScanDecision S StreamReply
  | s, [] => .more s
  | s, b :: bs => match sc.onByte s b with
    | .more next => feedScannerChunk sc next bs
    | .done r => .done r
termination_by structural _ chunk => chunk

def emitStreamReply {Δ : List Cap} (hStdio : CapMem .stdioCap Δ) (r : StreamReply) : WorldProg Δ ExitCode :=
  worldSeq (writeStdoutW hStdio r.stdout) <|
    worldSeq (writeStderrW hStdio r.stderr) (.pure r.exitCode)

/-- Carry the scanner state between chunks. An explicit stdin EOF event calls its EOF handler. -/
def streamScannerApp {Δ : List Cap} {S : Type} (hStdio : CapMem .stdioCap Δ)
    (sc : ByteScanner S StreamReply) : ReactiveApp Δ S where
  init := .pure sc.init
  onStep
    | ⟨_, .evStdinBytes chunk⟩, s => match feedScannerChunk sc s chunk with
      | .more next => .pure (.inl next)
      | .done r => mapWorld Sum.inr (emitStreamReply hStdio r)
    | ⟨_, .evStdinEOF⟩, s => mapWorld Sum.inr (emitStreamReply hStdio (sc.onEOF s))
    | _, s => .pure (.inl s)

private theorem feedScannerChunk_append {S : Type} (sc : ByteScanner S StreamReply) (s : S) (pre post : Bytes) :
    feedScannerChunk sc s (pre ++ post) =
      match feedScannerChunk sc s pre with
      | .more next => feedScannerChunk sc next post
      | .done r => .done r := by
  induction pre generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.cons_append, feedScannerChunk]
    cases sc.onByte s b with
    | more next => exact ih next
    | done r => rfl

private theorem runScannerFrom_chunk_outcome {S : Type} (sc : ByteScanner S StreamReply)
    (s : S) (bs : Bytes) (closed : Bool) :
    (runScannerFrom sc s bs closed false).1 =
      match feedScannerChunk sc s bs with
      | .done r => .emit r
      | .more next => if closed then .ended (sc.onEOF next) else .wouldBlock := by
  induction bs generalizing s with
  | nil => cases closed <;> rfl
  | cons b bs ih =>
    simp only [runScannerFrom, feedScannerChunk]
    cases sc.onByte s b with
    | more next => exact ih next
    | done r => rfl

/-- A completed chunk exits before any remaining chunks or trailing events are inspected. -/
private theorem run_streamScannerApp_chunks {Δ : List Cap} {S : Type} (hStdio : CapMem .stdioCap Δ)
    (sc : ByteScanner S StreamReply) (s : S) (chunks : List Bytes) (tail : List (Event Δ)) (w : SimWorld) :
    runReactiveSteps (streamScannerApp hStdio sc) s
      (chunks.map (Event.mkEvent hStdio ∘ EventPayload.evStdinBytes) ++ tail) w =
      match feedScannerChunk sc s chunks.flatten with
      | .more next => runReactiveSteps (streamScannerApp hStdio sc) next tail w
      | .done r => (.inr r.exitCode, (runWorldPure (emitStreamReply hStdio r) w).2) := by
  induction chunks generalizing s with
  | nil => rfl
  | cons chunk chunks ih =>
    simp only [List.map_cons, List.cons_append, List.flatten_cons, feedScannerChunk_append,
      runReactiveSteps, Function.comp_apply, streamScannerApp]
    cases feedScannerChunk sc s chunk with
    | more next => exact ih next
    | done r => rfl

/-- A byte-triggered reply exits on an open stream and appends both outputs exactly once. -/
theorem streamScannerApp_early_exit {Δ : List Cap} {S : Type} (hStdio : CapMem .stdioCap Δ)
    (sc : ByteScanner S StreamReply) (chunks : List Bytes) (r : StreamReply) (rest : InChan) (w : SimWorld)
    (emits : evalScanner sc (openPipe chunks.flatten) = (.emit r, rest)) :
    runReactivePure (streamScannerApp hStdio sc)
      (chunks.map (Event.mkEvent hStdio ∘ EventPayload.evStdinBytes)) w =
      (.inr r.exitCode, { w with stdio := { w.stdio with
        stdout := writeOut r.stdout w.stdio.stdout, stderr := writeOut r.stderr w.stdio.stderr } }) := by
  have outcome := congrArg Prod.fst emits
  change (runScannerFrom sc sc.init chunks.flatten false false).1 = .emit r at outcome
  rw [runScannerFrom_chunk_outcome] at outcome
  have run := run_streamScannerApp_chunks hStdio sc sc.init chunks [] w
  rw [List.append_nil] at run
  cases step : feedScannerChunk sc sc.init chunks.flatten with
  | more next => simp [step] at outcome
  | done value =>
    simp [step] at outcome
    subst value
    rw [step] at run
    exact run

/-- Delivering EOF after any partition of the bytes produces the closed scanner's reply. -/
theorem streamScannerApp_closed_eof {Δ : List Cap} {S : Type} (hStdio : CapMem .stdioCap Δ)
    (sc : ByteScanner S StreamReply) (chunks : List Bytes) (r : StreamReply) (w : SimWorld)
    (ended : evalScanner sc (closedPipe chunks.flatten) = (.ended r, emptyClosedPipe)) :
    runReactivePure (streamScannerApp hStdio sc)
      (chunks.map (Event.mkEvent hStdio ∘ EventPayload.evStdinBytes) ++ [Event.mkEvent hStdio .evStdinEOF]) w =
      (.inr r.exitCode, { w with stdio := { w.stdio with
        stdout := writeOut r.stdout w.stdio.stdout, stderr := writeOut r.stderr w.stdio.stderr } }) := by
  have outcome := congrArg Prod.fst ended
  change (runScannerFrom sc sc.init chunks.flatten true false).1 = .ended r at outcome
  rw [runScannerFrom_chunk_outcome] at outcome
  have run := run_streamScannerApp_chunks hStdio sc sc.init chunks [Event.mkEvent hStdio .evStdinEOF] w
  cases step : feedScannerChunk sc sc.init chunks.flatten with
  | done value => simp [step] at outcome
  | more next =>
    simp [step] at outcome
    subst r
    rw [step] at run
    exact run

theorem streamScannerApp_eof_confluent {Δ : List Cap} {S : Type} (hStdio : CapMem .stdioCap Δ)
    (sc : ByteScanner S StreamReply) (chunks : List Bytes) (r : StreamReply) (w : SimWorld)
    (ended : evalScanner sc (closedPipe chunks.flatten) = (.ended r, emptyClosedPipe)) :
    runReactivePure (streamScannerApp hStdio sc)
      (chunks.map (Event.mkEvent hStdio ∘ EventPayload.evStdinBytes) ++ [Event.mkEvent hStdio .evStdinEOF]) w =
    runReactivePure (streamScannerApp hStdio sc)
      [Event.mkEvent hStdio (.evStdinBytes chunks.flatten), Event.mkEvent hStdio .evStdinEOF] w := by
  apply (streamScannerApp_closed_eof hStdio sc chunks r w ended).trans
  apply (streamScannerApp_closed_eof hStdio sc [chunks.flatten] r w _).symm
  simpa using ended

inductive TuiInput : Type where
  | stdinChunk : Bytes → TuiInput
  | stdinEOF   : TuiInput
  | ttyBytes   : Bytes → TuiInput
  | ttyEOF     : TuiInput
  | ttyResize  : Nat → Nat → TuiInput
  | signal     : TermSignal → TuiInput
  | tickMs     : Nat → TuiInput

def TuiInput.ctorIdx : TuiInput → Nat
  | .stdinChunk _ => 0
  | .stdinEOF     => 1
  | .ttyBytes _   => 2
  | .ttyEOF       => 3
  | .ttyResize .. => 4
  | .signal _     => 5
  | .tickMs _     => 6

def classifyEvent {Δ : List Cap} : Event Δ → Option TuiInput
  | ⟨_, .evStdinBytes bs⟩   => some (.stdinChunk bs)
  | ⟨_, .evStdinEOF⟩        => some .stdinEOF
  | ⟨_, .evTTYBytes bs⟩     => some (.ttyBytes bs)
  | ⟨_, .evKey key⟩         => some (.ttyBytes (encodeKey key))
  | ⟨_, .evTTYEOF⟩          => some .ttyEOF
  | ⟨_, .evResize rows cols⟩ => some (.ttyResize rows cols)
  | ⟨_, .evSignal sig⟩      => some (.signal sig)
  | ⟨_, .evTickMs ms⟩       => some (.tickMs ms)
  | _                       => none

structure TuiSpec (S : Type) : Type where
  init : S
  /-- Each turn produces a state, a terminal frame diff, and an optional final selection and exit code. -/
  step : TuiInput → S → S × Bytes × Option (Bytes × ExitCode)

def tuiReactiveApp {Δ : List Cap} {S : Type} (hStdio : CapMem .stdioCap Δ) (hTty : CapMem .ttyCap Δ)
    (raw : Bool := true) (spec : TuiSpec S) : ReactiveApp Δ S where
  init := worldSeq (setTTYRawW hTty raw) (.pure spec.init)
  onStep ev s := match classifyEvent ev with
    | none => .pure (.inl s)
    | some inp =>
      let (next, frame, result) := spec.step inp s
      let draw := if frame.isEmpty then .pure () else writeTTYW_ hTty frame
      worldBind draw fun _ => match result with
        | none => .pure (.inl next)
        | some (selected, code) => worldSeq (writeStdoutW hStdio selected) (.pure (.inr code))

/-- A continuing turn applies exactly its frame diff to the controlling terminal. -/
theorem tuiReactiveApp_nonExit {Δ : List Cap} {S : Type} (hStdio : CapMem .stdioCap Δ) (hTty : CapMem .ttyCap Δ)
    (raw : Bool) (spec : TuiSpec S) (ev : Event Δ) (inp : TuiInput) (s : S) (w : SimWorld)
    (classified : classifyEvent ev = some inp) (running : (spec.step inp s).2.2 = none) :
    runWorldPure ((tuiReactiveApp hStdio hTty raw spec).onStep ev s) w =
      (.inl (spec.step inp s).1, { w with tty := (writeCtrlTTY (spec.step inp s).2.1 w.tty).2 }) := by
  generalize turn : spec.step inp s = t at running ⊢
  obtain ⟨next, frame, result⟩ := t
  change result = none at running
  subst result
  simp only [tuiReactiveApp, classified, turn]
  cases frame with
  | nil =>
    cases attached : w.tty.hasTTY with
    | false => rw [writeCtrlTTY_noTTY [] w.tty attached]; rfl
    | true => rw [writeCtrlTTY_nil w.tty attached]; rfl
  | cons b bs => rfl

theorem tuiReactiveApp_nonExit_preserves_stdout {Δ : List Cap} {S : Type}
    (hStdio : CapMem .stdioCap Δ) (hTty : CapMem .ttyCap Δ)
    (raw : Bool) (spec : TuiSpec S) (ev : Event Δ) (inp : TuiInput) (s : S) (w : SimWorld)
    (classified : classifyEvent ev = some inp) (running : (spec.step inp s).2.2 = none) :
    let w' := (runWorldPure ((tuiReactiveApp hStdio hTty raw spec).onStep ev s) w).2
    w'.stdio.stdout = w.stdio.stdout ∧ w'.stdio.stderr = w.stdio.stderr := by
  rw [tuiReactiveApp_nonExit hStdio hTty raw spec ev inp s w classified running]
  exact ⟨rfl, rfl⟩

end LojitaCtx.Cli
