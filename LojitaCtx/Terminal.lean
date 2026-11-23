import LojitaCtx.Utf8
namespace LojitaCtx.Terminal

abbrev Byte := UInt8
abbrev Bytes := List UInt8
abbrev byte := UInt8.ofNat
def bytes (s : String) : Bytes := s.toUTF8.data.toList
def utf8Char := String.utf8EncodeChar

inductive Key : Type where
  | textKey   : String → Key
  | enter     : Key
  | escape    : Key
  | backspace : Key
  | tab       : Key
  | up        : Key
  | down      : Key
  | right     : Key
  | left      : Key
  | home      : Key
  | end       : Key
  | delete    : Key
  | ctrl      : Char → Key

def encodeKey : Key → Bytes
  | .textKey s => bytes s
  | .enter => [byte 13]
  | .escape => [byte 27]
  | .backspace => [byte 127]
  | .tab => [byte 9]
  | .up => bytes "\x1b[A"
  | .down => bytes "\x1b[B"
  | .right => bytes "\x1b[C"
  | .left => bytes "\x1b[D"
  | .home => bytes "\x1b[H"
  | .end => bytes "\x1b[F"
  | .delete => bytes "\x1b[3~"
  | .ctrl c => [byte (Char.toNat c % 32)]

inductive TermTopology : Type where
  | allTTY           : TermTopology
  | pipeStdioWithTTY : TermTopology
  | pipesNoTTY       : TermTopology

def TermTopology.ctorIdx : TermTopology → Nat
  | .allTTY           => 0
  | .pipeStdioWithTTY => 1
  | .pipesNoTTY       => 2

inductive SandboxTarget : Type where
  | localSandbox  : SandboxTarget
  | dockerSandbox : String → SandboxTarget

structure TermConfig : Type where termConfig ::
  target : SandboxTarget
  topology : TermTopology
  executable : String
  arguments : List String
  envVars : List (String × String)
  rows : Nat
  cols : Nat
  files : List String

inductive TermSignal : Type where
  | sigINT  : TermSignal
  | sigTERM : TermSignal
  | sigHUP  : TermSignal
  | sigQUIT : TermSignal
  | sigKILL : TermSignal

inductive TermStep : Type where
  | writeStdin : Bytes → TermStep
  | writeTTY   : Bytes → TermStep
  | closeStdin : TermStep
  | sleepMs    : Nat → TermStep
  | resizeTTY  : Nat → Nat → TermStep
  | sendSignal : TermSignal → TermStep
  | drainRaw   : TermStep

structure RawTermObs : Type where
  rawObs ::
  ttyOut     : Bytes
  stdoutOut  : Bytes
  stderrOut  : Bytes
  exitStatus : Option Nat

def emptyObs : RawTermObs :=
  RawTermObs.rawObs [] [] [] .none

def latest (previous : Unit → Option Nat) (current : Option Nat) : Option Nat :=
  current.orElse previous

def appendObs (a b : RawTermObs) : RawTermObs :=
  RawTermObs.rawObs (a.ttyOut ++ b.ttyOut) (a.stdoutOut ++ b.stdoutOut) (a.stderrOut ++ b.stderrOut)
    (latest (fun _ => a.exitStatus) b.exitStatus)

inductive TimerEdit (E : Type) : Type where
  | arm    : Nat → Nat → E → TimerEdit E
  | cancel : Nat → TimerEdit E

structure Timer (E : Type) : Type where
  timer ::
  slot     : Nat
  deadline : Nat
  payload  : E

inductive TermEvent (E : Type) : Type where
  | input   : TermStep → TermEvent E
  | timeout : E → TermEvent E

structure Effect (S E : Type) : Type where
  effect ::
  nextState : S
  output    : RawTermObs
  edits     : List (TimerEdit E)

/-- Bytes received since the last observation, in reverse arrival order. -/
structure PendingOutput where
  ttyRev : Bytes := []
  stdoutRev : Bytes := []
  stderrRev : Bytes := []
  exitStatus : Option Nat := none

def PendingOutput.add (p : PendingOutput) (o : RawTermObs) : PendingOutput :=
  ⟨o.ttyOut.reverseAux p.ttyRev, o.stdoutOut.reverseAux p.stdoutRev, o.stderrOut.reverseAux p.stderrRev,
   latest (fun _ => p.exitStatus) o.exitStatus⟩

def PendingOutput.toObs (p : PendingOutput) : RawTermObs :=
  ⟨p.ttyRev.reverse, p.stdoutRev.reverse, p.stderrRev.reverse, p.exitStatus⟩

structure TimedMachine (S E : Type) where
  now : Nat
  state : S
  timers : List (Timer E)
  buffer : PendingOutput

def TimedMachine.timed {S E : Type} (now : Nat) (state : S) (timers : List (Timer E)) (pending : RawTermObs) :
    TimedMachine S E := ⟨now, state, timers, ({} : PendingOutput).add pending⟩

def TimedMachine.pending {S E : Type} (m : TimedMachine S E) := m.buffer.toObs

abbrev Handler (S E : Type) : Type :=
  TermEvent E → S → Effect S E

def removeTimer {E : Type} (n : Nat) : List (Timer E) → List (Timer E)
  | [] => []
  | t :: ts => if n == t.slot then removeTimer n ts else t :: removeTimer n ts
termination_by structural ts => ts

def insertTimer {E : Type} (t : Timer E) : List (Timer E) → List (Timer E)
  | [] => [t]
  | u :: us => if t.deadline < u.deadline then t :: u :: us else u :: insertTimer t us
termination_by structural us => us

def editTimers {E : Type} (n : Nat) : List (TimerEdit E) → List (Timer E) → List (Timer E)
  | [], ts => ts
  | .cancel k :: es, ts => editTimers n es (removeTimer k ts)
  | .arm k delay e :: es, ts =>
    editTimers n es (insertTimer (Timer.timer k (n + max 1 delay) e) (removeTimer k ts))
termination_by structural es _ => es

def applyEffect {S E : Type} (e : Effect S E) (m : TimedMachine S E) : TimedMachine S E :=
  {m with state := e.nextState, timers := editTimers m.now e.edits m.timers, buffer := m.buffer.add e.output}

def fireDue {S E : Type} : Nat → Handler S E → TimedMachine S E → TimedMachine S E
  | 0, _, m => m
  | Nat.succ fuel, h, m =>
    match m.timers with
    | [] => m
    | t :: ts =>
      if t.deadline ≤ m.now then
        fireDue fuel h (applyEffect (h (.timeout t.payload) m.state) { m with timers := ts })
      else m
termination_by structural fuel _ _ => fuel

def advance {S E : Type} : Nat → Handler S E → TimedMachine S E → TimedMachine S E
  | 0, _, m => m
  | Nat.succ n, h, m =>
      advance n h (fireDue (List.length m.timers) h { m with now := Nat.succ m.now })
termination_by structural n _ _ => n

def perform {S E : Type} (h : Handler S E) : TermStep → TimedMachine S E → TimedMachine S E
  | .sleepMs n, m => advance n h m
  | q, m          => applyEffect (h (.input q) m.state) m

def observe {S E : Type} (m : TimedMachine S E) : TimedMachine S E × RawTermObs :=
  ({m with buffer := {exitStatus := m.buffer.exitStatus}}, m.pending)

def stepTimed {S E : Type} (h : Handler S E) (q : TermStep) (m : TimedMachine S E) :
    TimedMachine S E × RawTermObs :=
  observe (perform h q m)

def traceTimed {S E : Type} (h : Handler S E) : List TermStep → TimedMachine S E → List RawTermObs
  | [], _ => []
  | q :: qs, m =>
      let r := stepTimed h q m
      r.2 :: traceTimed h qs r.1
termination_by structural qs _ => qs

inductive Colour : Type where
  | defaultColour : Colour
  | indexed       : Nat → Colour
  | rgb           : Nat → Nat → Nat → Colour

structure Rendition : Type where
  rendition ::
  foreground : Colour
  background : Colour
  bold       : Bool
  underline  : Bool
  inverse    : Bool

def plain : Rendition :=
  Rendition.rendition .defaultColour .defaultColour false false false

structure Cell : Type where
  cell ::
  glyph : Char
  style : Rendition

structure Surface : Type where
  surface ::
  grid        : List (List Cell)
  row         : Nat
  col         : Nat
  ink         : Rendition
  wrapPending : Bool

inductive TermParser : Type where
  | ground    : TermParser
  | escaped   : TermParser
  | osc       : TermParser
  | oscEscape : TermParser
  | csi       : Bool → List Nat → Nat → TermParser
  | utf       : Nat → Nat → TermParser

structure Screen : Type where
  screen ::
  height  : Nat
  width   : Nat
  active  : Surface
  primary : Option Surface
  parser  : TermParser

def blankSurface (h w : Nat) : Surface :=
  Surface.surface (List.replicate h (List.replicate w (Cell.cell ' ' plain))) 0 0 plain false

def blankScreen (h w : Nat) : Screen :=
  let h' := max 1 h
  let w' := max 1 w
  Screen.screen h' w' (blankSurface h' w') .none .ground

def putAt {A : Type} : Nat → A → List A → List A
  | _, _, [] => []
  | 0, x, _ :: xs => x :: xs
  | Nat.succ n, x, y :: ys => y :: putAt n x ys
termination_by structural _ _ xs => xs

def getAt {A : Type} (d : A) : Nat → List A → A
  | _, [] => d
  | 0, x :: _ => x
  | Nat.succ n, _ :: xs => getAt d n xs
termination_by structural _ xs => xs

def move (r c : Nat) (s : Screen) : Screen :=
  { s with
    active :=
      { s.active with
        row := min r (s.height - 1)
        col := min c (s.width - 1)
        wrapPending := false } }

def lineFeed (s : Screen) : Screen :=
  let scroll : List (List Cell) → List (List Cell)
    | [] => []
    | _ :: xs => xs ++ [List.replicate s.width (Cell.cell ' ' s.active.ink)]
  if Nat.succ s.active.row < s.height then move (Nat.succ s.active.row) s.active.col s
  else { s with active := { s.active with grid := scroll s.active.grid, wrapPending := false } }

def printGlyph (c : Char) (s : Screen) : Screen :=
  let draw (t : Screen) : Screen :=
    { t with
      active :=
        {
          t.active with
          grid :=
            putAt t.active.row
              (putAt t.active.col (Cell.cell c t.active.ink) (getAt [] t.active.row t.active.grid))
              t.active.grid
          col := min (Nat.succ t.active.col) (t.width - 1)
          wrapPending := Nat.succ t.active.col == t.width } }
  draw (if s.active.wrapPending then lineFeed (move s.active.row 0 s) else s)

def mapIndexedGo {A B : Type} (f : Nat → A → B) (n : Nat) : List A → List B
  | [] => []
  | x :: rest => f n x :: mapIndexedGo f (Nat.succ n) rest
termination_by structural xs => xs

def mapIndexed {A B : Type} (f : Nat → A → B) (xs : List A) : List B :=
  mapIndexedGo f 0 xs

def erase (whole : Bool) (mode : Nat) (s : Screen) : Screen :=
  let r := s.active.row
  let c := s.active.col
  let chosen (y x : Nat) : Bool :=
    if whole then
      mode == 2 || mode == 0 && (r < y || r == y && c ≤ x) ||
        mode == 1 && (y < r || r == y && x ≤ c)
    else y == r && (mode == 2 || (mode == 0 && c ≤ x || mode == 1 && x ≤ c))
  let line (y : Nat) : List Cell → List Cell :=
    mapIndexed fun x v => if chosen y x then Cell.cell ' ' s.active.ink else v
  { s with active := { s.active with grid := mapIndexed line s.active.grid } }

def sgrOne (n : Nat) (a : Rendition) : Rendition :=
  if n == 0 then plain
  else
    if n == 1 then { a with bold := true }
    else
      if n == 22 then { a with bold := false }
      else
        if n == 4 then { a with underline := true }
        else
          if n == 24 then { a with underline := false }
          else
            if n == 7 then { a with inverse := true }
            else
              if n == 27 then { a with inverse := false }
              else
                if n == 39 then { a with foreground := .defaultColour }
                else
                  if n == 49 then { a with background := .defaultColour }
                  else
                    if 30 ≤ n && n ≤ 37 then { a with foreground := .indexed (n - 30) }
                    else
                      if 40 ≤ n && n ≤ 47 then { a with background := .indexed (n - 40) }
                      else
                        if 90 ≤ n && n ≤ 97 then { a with foreground := .indexed (8 + (n - 90)) }
                        else
                          if 100 ≤ n && n ≤ 107 then
                            { a with background := .indexed (8 + (n - 100)) }
                          else a

def setColour (n : Nat) (c : Colour) (a : Rendition) : Rendition :=
  if n == 38 then { a with foreground := c } else { a with background := c }

def sgrFuel : Nat → List Nat → Rendition → Rendition
  | 0, _, a => a
  | Nat.succ _, [], a => a
  | Nat.succ fuel, n :: 5 :: c :: ns, a =>
    if n == 38 || n == 48 then sgrFuel fuel ns (setColour n (.indexed c) a)
    else sgrFuel fuel (5 :: c :: ns) (sgrOne n a)
  | Nat.succ fuel, n :: 2 :: r :: g :: b :: ns, a =>
    if n == 38 || n == 48 then sgrFuel fuel ns (setColour n (.rgb r g b) a)
    else sgrFuel fuel (2 :: r :: g :: b :: ns) (sgrOne n a)
  | Nat.succ fuel, n :: ns, a => sgrFuel fuel ns (sgrOne n a)
termination_by structural fuel _ _ => fuel

def sgr (ns : List Nat) : Rendition → Rendition :=
  sgrFuel (List.length ns) ns

def altScreen : Bool → Screen → Screen
  | true, s =>
      match s.primary with
      | .some _  => s
      | .none => { s with active := blankSurface s.height s.width, primary := .some s.active }
  | false, s =>
      match s.primary with
      | .none => s
      | .some a  => { s with active := a, primary := .none }

def dispatchCSI : Bool → List Nat → Nat → Screen → Screen
  | true, ns, cmd, s =>
    if getAt 0 0 ns == 1049 then
      if cmd == 104 then altScreen true s else if cmd == 108 then altScreen false s else s
    else s
  | false, ns, cmd, s =>
    if cmd == 65 then move (s.active.row - max 1 (getAt 0 0 ns)) s.active.col s
    else
      if cmd == 66 then move (s.active.row + max 1 (getAt 0 0 ns)) s.active.col s
      else
        if cmd == 67 then move s.active.row (s.active.col + max 1 (getAt 0 0 ns)) s
        else
          if cmd == 68 then move s.active.row (s.active.col - max 1 (getAt 0 0 ns)) s
          else
            if cmd == 71 then move s.active.row (getAt 0 0 ns - 1) s
            else
              if cmd == 72 || cmd == 102 then move (getAt 0 0 ns - 1) (getAt 0 1 ns - 1) s
              else
                if cmd == 74 then erase true (getAt 0 0 ns) s
                else
                  if cmd == 75 then erase false (getAt 0 0 ns) s
                  else
                    if cmd == 109 then
                      { s with active := { s.active with ink := sgr ns s.active.ink } }
                    else s

def groundByte (n : Nat) (s : Screen) : Screen :=
  if n == 27 then { s with parser := .escaped }
  else
    if n == 13 then move s.active.row 0 s
    else
      if n == 10 then lineFeed s
      else
        if n == 8 then move s.active.row (s.active.col - 1) s
        else
          if n == 9 then move s.active.row ((1 + s.active.col / 8) * 8) s
          else
            if 32 ≤ n && n < 127 then printGlyph (Char.ofNat n) s
            else
              if 194 ≤ n && n < 224 then { s with parser := .utf 1 (n - 192) }
              else
                if 224 ≤ n && n < 240 then { s with parser := .utf 2 (n - 224) }
                else if 240 ≤ n && n < 245 then { s with parser := .utf 3 (n - 240) } else s

def ansiByte (b : Byte) (s : Screen) : Screen :=
  let ob := UInt8.toNat b
  match s.parser with
  | .ground => groundByte ob s
  | .escaped =>
    { s with parser := if ob == 91 then .csi false [] 0 else if ob == 93 then .osc else .ground }
  | .osc => { s with parser := if ob == 7 then .ground else if ob == 27 then .oscEscape else .osc }
  | .oscEscape => { s with parser := if ob == 92 then .ground else .osc }
  | .csi priv ns n =>
    if 48 ≤ ob && ob ≤ 57 then { s with parser := .csi priv ns (10 * n + (ob - 48)) }
    else
      if ob == 59 then { s with parser := .csi priv (n :: ns) 0 }
      else
        if ob == 63 then { s with parser := .csi true ns n }
        else
          if 64 ≤ ob && ob ≤ 126 then
            dispatchCSI priv (List.reverse (n :: ns)) ob { s with parser := .ground }
          else if ob == 27 then { s with parser := .escaped } else s
  | .utf 0 _ => groundByte ob { s with parser := .ground }
  | .utf (Nat.succ remaining) n =>
    if 128 ≤ ob && ob < 192 then
      if remaining == 0 then
        printGlyph (Char.ofNat (64 * n + (ob - 128))) { s with parser := .ground }
      else { s with parser := .utf remaining (64 * n + (ob - 128)) }
    else groundByte ob { s with parser := .ground }

def stepANSI : Screen → Bytes → Screen :=
  List.foldl (fun s b => ansiByte b s)

def screenLines (s : Screen) : List String :=
  List.map (fun line => String.ofList (List.map Cell.glyph line)) s.active.grid

end LojitaCtx.Terminal
