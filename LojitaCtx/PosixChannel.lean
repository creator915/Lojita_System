import LojitaCtx.Terminal

namespace LojitaCtx.PosixChannel

open LojitaCtx.Terminal

inductive ScanDecision (S A : Type) : Type where
  | more : S → ScanDecision S A
  | done : A → ScanDecision S A

def ScanDecision.ctorIdx {S A : Type} : ScanDecision S A → Nat
  | .more _ => 0
  | .done _ => 1

/-- A scanner can finish on a byte, finish at EOF, or exhaust an open channel. -/
inductive ReadOutcome (A : Type) : Type where
  | emit       : A → ReadOutcome A
  | ended      : A → ReadOutcome A
  | wouldBlock : ReadOutcome A

def ReadOutcome.ctorIdx {A : Type} : ReadOutcome A → Nat
  | .emit _     => 0
  | .ended _    => 1
  | .wouldBlock => 2

def ReadOutcome.value? {A : Type} : ReadOutcome A → Option A
  | .emit a | .ended a => some a
  | .wouldBlock        => none

def ReadOutcome.isBlocked {A : Type} : ReadOutcome A → Bool
  | .wouldBlock => true
  | _           => false

structure InChan : Type where
  inChan ::
  pending : Bytes
  closed  : Bool
  /-- Records whether a read has ever exhausted the open channel. -/
  waited  : Bool := false

def closedPipe (bs : Bytes) : InChan := InChan.inChan bs true false
def openPipe (bs : Bytes) : InChan := InChan.inChan bs false false
def emptyClosedPipe : InChan := closedPipe []
def emptyOpenPipe : InChan := openPipe []

def readChanByte (ch : InChan) : ReadOutcome (Option Byte) × InChan :=
  match ch.pending with
  | b :: bs => (.emit (some b), { ch with pending := bs })
  | [] => if ch.closed then (.ended none, ch) else (.wouldBlock, { ch with waited := true })

def popChanByte (ch : InChan) : Option Byte × InChan :=
  match ch.pending with
  | b :: bs => (some b, { ch with pending := bs })
  | [] => (none, if ch.closed then ch else { ch with waited := true })

structure ByteScanner (S A : Type) : Type where
  byteScanner ::
  init   : S
  onByte : S → Byte → ScanDecision S A
  onEOF  : S → A

def runScannerFrom {S A : Type} (sc : ByteScanner S A) :
    S → Bytes → Bool → Bool → ReadOutcome A × InChan
  | s, [], true, waited => (.ended (sc.onEOF s), InChan.inChan [] true waited)
  | _, [], false, _     => (.wouldBlock, InChan.inChan [] false true)
  | s, b :: bs, closed, waited =>
    match sc.onByte s b with
    | .done a  => (.emit a, InChan.inChan bs closed waited)
    | .more s' => runScannerFrom sc s' bs closed waited
termination_by structural _ bs _ _ => bs

def evalScanner {S A : Type} (sc : ByteScanner S A) (ch : InChan) : ReadOutcome A × InChan :=
  runScannerFrom sc sc.init ch.pending ch.closed ch.waited

def oneByteScanner : ByteScanner Unit (Option Byte) where
  init := ()
  onByte _ b := .done (some b)
  onEOF _ := none

def lineScanner : ByteScanner Bytes (Option Bytes) where
  init := []
  onByte revAcc b := if b == 10 then .done (some (b :: revAcc).reverse) else .more (b :: revAcc)
  onEOF revAcc := if revAcc.isEmpty then none else some revAcc.reverse

def allScanner : ByteScanner Bytes Bytes where
  init := []
  onByte revAcc b := .more (b :: revAcc)
  onEOF revAcc := revAcc.reverse

def readChanLine (ch : InChan) : Option Bytes × InChan :=
  let r := evalScanner lineScanner ch
  match r.1 with
  | .emit l | .ended l => (l, r.2)
  | .wouldBlock        => (none, r.2)

/-- Drain the pending bytes, marking a wait when the channel is still open. -/
def readChanAll (ch : InChan) : Bytes × InChan :=
  (ch.pending, InChan.inChan [] ch.closed (if ch.closed then ch.waited else true))

structure OutChan : Type where
  outChan ::
  written : ByteArray
  isTTY   : Bool

def emptyOutChan (isTTY : Bool := false) : OutChan :=
  OutChan.outChan .empty isTTY

def writeOut (bs : Bytes) (c : OutChan) : OutChan :=
  { c with written := bs.foldl ByteArray.push c.written }

def projectOutScreen (rows cols : Nat) (c : OutChan) : Option Screen :=
  if c.isTTY then some (stepANSI (blankScreen rows cols) c.written.data.toList) else none

structure StdioChannels : Type where
  stdioChannels ::
  stdin      : InChan
  stdinIsTTY : Bool
  stdout     : OutChan
  stderr     : OutChan

def pipeStdio (inp : Bytes := []) (closed : Bool := true) (isTtyOut : Bool := false) : StdioChannels :=
  StdioChannels.stdioChannels (InChan.inChan inp closed false) false
    (emptyOutChan isTtyOut) (emptyOutChan false)

def interactiveStdio (inp : Bytes := []) (closed : Bool := false) : StdioChannels :=
  StdioChannels.stdioChannels (InChan.inChan inp closed false) true
    (emptyOutChan true) (emptyOutChan true)

/-- The controlling terminal has its own input, output, and ANSI parser state. -/
structure CtrlTTY : Type where
  ctrlTTY ::
  hasTTY    : Bool
  rawMode   : Bool
  ttyIn     : InChan
  ttyOut    : ByteArray
  ttyScreen : Screen

def noCtrlTTY (rows : Nat := 24) (cols : Nat := 80) : CtrlTTY :=
  CtrlTTY.ctrlTTY false false emptyClosedPipe .empty (blankScreen rows cols)

def mkCtrlTTY (rows cols : Nat) (keys : Bytes := []) (closed : Bool := false) (raw : Bool := true) :
    CtrlTTY :=
  CtrlTTY.ctrlTTY true raw (InChan.inChan keys closed false) .empty (blankScreen rows cols)

def setCtrlTTYRaw (raw : Bool) (t : CtrlTTY) : Bool × CtrlTTY :=
  if t.hasTTY then (true, { t with rawMode := raw }) else (false, t)

def popCtrlTTYByte (t : CtrlTTY) : Option Byte × CtrlTTY :=
  if t.hasTTY then
    let r := popChanByte t.ttyIn
    (r.1, { t with ttyIn := r.2 })
  else
    (none, t)

def writeCtrlTTY (bs : Bytes) (t : CtrlTTY) : Bool × CtrlTTY :=
  if t.hasTTY then
    (true, { t with
      ttyOut := bs.foldl ByteArray.push t.ttyOut
      ttyScreen := stepANSI t.ttyScreen bs })
  else
    (false, t)

def resizeCtrlTTY (rows cols : Nat) (t : CtrlTTY) : CtrlTTY :=
  if t.hasTTY then
    { t with ttyScreen := { t.ttyScreen with height := max 1 rows, width := max 1 cols } }
  else
    t

def foldChunk {S : Type} (step : S → Byte → S) (s : S) (chunk : Bytes) : S :=
  chunk.foldl step s

def feedChunks {S : Type} (step : S → Byte → S) (s : S) (chunks : List Bytes) : S :=
  chunks.foldl (foldChunk step) s

-- Emission consumes only a prefix and preserves the incoming channel flags.
private theorem runScannerFrom_emit_prefix {S A : Type} (sc : ByteScanner S A)
    (s : S) (p : Bytes) (a : A) (rest : InChan)
    (h : runScannerFrom sc s p false false = (.emit a, rest)) :
    rest.waited = false ∧ ∀ (extra : Bytes) (closed waited : Bool),
      runScannerFrom sc s (p ++ extra) closed waited =
        (.emit a, InChan.inChan (rest.pending ++ extra) closed waited) := by
  induction p generalizing s with
  | nil => simp [runScannerFrom] at h
  | cons b bs ih =>
    simp only [List.cons_append, runScannerFrom] at h ⊢
    cases step : sc.onByte s b with
    | more next =>
      rw [step] at h
      exact ih next h
    | done value =>
      simp [step] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, fun _ _ _ => rfl⟩

theorem evalScanner_prefix_causal {S A : Type} (sc : ByteScanner S A)
    (p rem extra : Bytes) (a : A) (closed waited : Bool)
    (h : evalScanner sc (openPipe p) = (.emit a, InChan.inChan rem false false)) :
    evalScanner sc (InChan.inChan (p ++ extra) closed waited) =
      (.emit a, InChan.inChan (rem ++ extra) closed waited) :=
  (runScannerFrom_emit_prefix sc sc.init p a _ h).2 extra closed waited

theorem evalScanner_emit_never_waits {S A : Type} (sc : ByteScanner S A) (p : Bytes) (a : A)
    (h : (evalScanner sc (openPipe p)).1 = .emit a) :
    (evalScanner sc (openPipe p)).2.waited = false := by
  have emit : evalScanner sc (openPipe p) = (.emit a, (evalScanner sc (openPipe p)).2) := by
    rw [← h]
  exact (runScannerFrom_emit_prefix sc sc.init p a _ emit).1

theorem evalScanner_seq_cut {S₁ A₁ S₂ A₂ : Type} (sc₁ : ByteScanner S₁ A₁) (sc₂ : ByteScanner S₂ A₂)
    (p rem extra : Bytes) (a : A₁) (closed waited : Bool)
    (h : evalScanner sc₁ (openPipe p) = (.emit a, InChan.inChan rem false false)) :
    evalScanner sc₂ (evalScanner sc₁ (InChan.inChan (p ++ extra) closed waited)).2 =
      evalScanner sc₂ (InChan.inChan (rem ++ extra) closed waited) := by
  rw [evalScanner_prefix_causal sc₁ p rem extra a closed waited h]

theorem evalScanner_oneByte (ch : InChan) : evalScanner oneByteScanner ch = readChanByte ch := by
  obtain ⟨bs, closed, waited⟩ := ch
  cases bs with
  | nil => cases closed <;> rfl
  | cons b bs => rfl

theorem evalScanner_oneByte_popChanByte (ch : InChan) :
    (evalScanner oneByteScanner ch).1.value?.join = (popChanByte ch).1 ∧
    (evalScanner oneByteScanner ch).2 = (popChanByte ch).2 := by
  rw [evalScanner_oneByte]
  obtain ⟨bs, closed, waited⟩ := ch
  cases bs with
  | nil => cases closed <;> exact ⟨rfl, rfl⟩
  | cons b bs => exact ⟨rfl, rfl⟩

-- Both collecting scanners prepend each accepted byte to the same reverse accumulator.
private theorem runScannerFrom_collect_prefix {A : Type} (sc : ByteScanner Bytes A)
    (pre post revAcc : Bytes) (closed waited : Bool)
    (h : ∀ b ∈ pre, ∀ acc, sc.onByte acc b = .more (b :: acc)) :
    runScannerFrom sc revAcc (pre ++ post) closed waited =
      runScannerFrom sc (pre.reverseAux revAcc) post closed waited := by
  induction pre generalizing revAcc with
  | nil => rfl
  | cons b pre ih =>
    rw [List.cons_append, runScannerFrom, h b List.mem_cons_self revAcc]
    exact ih (b :: revAcc) (fun x hx => h x (List.mem_cons_of_mem b hx))

theorem evalScanner_allScanner_readChanAll (ch : InChan) :
    evalScanner allScanner ch =
      (if ch.closed then .ended (readChanAll ch).1 else .wouldBlock, (readChanAll ch).2) := by
  obtain ⟨bs, closed, waited⟩ := ch
  have collect := runScannerFrom_collect_prefix allScanner bs [] [] closed waited (fun _ _ _ => rfl)
  cases closed <;> simpa [evalScanner, readChanAll, runScannerFrom, allScanner] using collect

theorem evalScanner_allScanner_closed (bs : Bytes) :
    evalScanner allScanner (closedPipe bs) = (.ended bs, closedPipe []) :=
  evalScanner_allScanner_readChanAll (closedPipe bs)

theorem evalScanner_allScanner_open_blocks (bs : Bytes) :
    evalScanner allScanner (openPipe bs) = (.wouldBlock, InChan.inChan [] false true) :=
  evalScanner_allScanner_readChanAll (openPipe bs)

theorem readChanAll_open_waited (bs : Bytes) : (readChanAll (openPipe bs)).2.waited = true := rfl

private theorem evalScanner_line_prefix (pre post : Bytes) (closed waited : Bool)
    (h : pre.all (fun b => b != 10) = true) :
    evalScanner lineScanner (InChan.inChan (pre ++ post) closed waited) =
      runScannerFrom lineScanner pre.reverse post closed waited := by
  apply runScannerFrom_collect_prefix lineScanner pre post [] closed waited
  intro b hb acc
  have hne : b ≠ 10 := by simpa using List.all_eq_true.mp h b hb
  simp [lineScanner, hne]

theorem evalScanner_lineScanner_newline (pre post : Bytes) (closed waited : Bool)
    (h : pre.all (fun b => b != 10) = true) :
    evalScanner lineScanner (InChan.inChan (pre ++ (10 :: post)) closed waited) =
      (.emit (some (pre ++ [10])), InChan.inChan post closed waited) := by
  rw [evalScanner_line_prefix pre (10 :: post) closed waited h, runScannerFrom]
  simp [lineScanner]

theorem readChanLine_newline (pre post : Bytes) (closed : Bool)
    (h : pre.all (fun b => b != 10) = true) :
    readChanLine (InChan.inChan (pre ++ (10 :: post)) closed false) =
      (some (pre ++ [10]), InChan.inChan post closed false) := by
  rw [readChanLine, evalScanner_lineScanner_newline pre post closed false h]

theorem evalScanner_lineScanner_open_no_newline_blocks (bs : Bytes)
    (h : bs.all (fun b => b != 10) = true) :
    evalScanner lineScanner (openPipe bs) = (.wouldBlock, InChan.inChan [] false true) := by
  simpa [openPipe, runScannerFrom] using evalScanner_line_prefix bs [] false false h

theorem readChanLine_open_no_newline_blocks (bs : Bytes) (h : bs.all (fun b => b != 10) = true) :
    readChanLine (openPipe bs) = (none, InChan.inChan [] false true) := by
  rw [readChanLine, evalScanner_lineScanner_open_no_newline_blocks bs h]

theorem evalScanner_lineScanner_closed_no_newline (bs : Bytes)
    (h : bs.all (fun b => b != 10) = true) (hne : bs ≠ []) :
    evalScanner lineScanner (closedPipe bs) = (.ended (some bs), closedPipe []) := by
  simpa [closedPipe, runScannerFrom, lineScanner, hne] using evalScanner_line_prefix bs [] true false h

theorem readChanLine_closed_no_newline (bs : Bytes)
    (h : bs.all (fun b => b != 10) = true) (hne : bs ≠ []) :
    readChanLine (closedPipe bs) = (some bs, closedPipe []) := by
  rw [readChanLine, evalScanner_lineScanner_closed_no_newline bs h hne]

theorem evalScanner_lineScanner_closed_empty :
    evalScanner lineScanner emptyClosedPipe = (.ended none, emptyClosedPipe) := rfl

theorem foldChunk_nil {S : Type} (step : S → Byte → S) (s : S) : foldChunk step s [] = s := rfl

theorem foldChunk_append {S : Type} (step : S → Byte → S) (s : S) (c₁ c₂ : Bytes) :
    foldChunk step s (c₁ ++ c₂) = foldChunk step (foldChunk step s c₁) c₂ :=
  List.foldl_append

theorem feedChunks_flatten_eq {S : Type} (step : S → Byte → S) (s : S) (chunks : List Bytes) :
    feedChunks step s chunks = foldChunk step s chunks.flatten :=
  List.foldl_flatten.symm

theorem writeOut_nil (c : OutChan) : writeOut [] c = c := rfl

theorem writeOut_append (a b : Bytes) (c : OutChan) : writeOut (a ++ b) c = writeOut b (writeOut a c) := by
  simp [writeOut]

theorem writeOut_isTTY (bs : Bytes) (c : OutChan) : (writeOut bs c).isTTY = c.isTTY := rfl

theorem writeCtrlTTY_noTTY (bs : Bytes) (t : CtrlTTY) (h : t.hasTTY = false) :
    writeCtrlTTY bs t = (false, t) := by simp [writeCtrlTTY, h]

theorem popCtrlTTYByte_noTTY (t : CtrlTTY) (h : t.hasTTY = false) :
    popCtrlTTYByte t = (none, t) := by simp [popCtrlTTYByte, h]

theorem writeCtrlTTY_nil (t : CtrlTTY) (h : t.hasTTY = true) :
    writeCtrlTTY [] t = (true, t) := by
  rw [writeCtrlTTY, ite_eq_left h]
  rfl

theorem writeCtrlTTY_append (a b : Bytes) (t : CtrlTTY) (h : t.hasTTY = true) :
    writeCtrlTTY (a ++ b) t = (true, (writeCtrlTTY b (writeCtrlTTY a t).2).2) := by
  simp [writeCtrlTTY, h, stepANSI]

end LojitaCtx.PosixChannel
