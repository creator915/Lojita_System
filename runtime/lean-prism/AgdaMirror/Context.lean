import AgdaMirror.Core

-- Sparse pattern compilation uses Nat.hasNotBit, which depends on propext.
set_option backward.match.sparseCases false
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `AgdaMirror.Context`: Exact Mirror of `Context.Blueprint`, `Context.PolyTransport`, and `Context.Terminal`
-/

namespace AgdaMirror.Context

open AgdaMirror

universe u v w

-- §1 `Context.Blueprint`

structure PortLift (Base Upper : Type) : Type 1 where
  portLift ::
  project : Upper → Base

abbrev keepPort (A : Type) : PortLift A A :=
  PortLift.portLift (fun a => a)

abbrev fromEl {Base : Type} (El : Base → Type) : PortLift Base (AgdaSigma Base El) :=
  PortLift.portLift AgdaSigma.proj₁

abbrev FiberOf {B U : Type} (p : PortLift B U) (b : B) : Type :=
  AgdaSigma U (fun (u : U) => AgdaId (p.project u) b)

abbrev composeLift {A B C : Type} (p : PortLift A B) (q : PortLift B C) : PortLift A C :=
  PortLift.portLift (fun c => p.project (q.project c))

abbrev Commutes₁ {A B U V : Type} (p : PortLift A U) (q : PortLift B V)
    (Dom : U → Type) (Rel : B → B → Type) (f : A → B) (g : U → V) : Type :=
  ∀ (u : U), Dom u → Rel (q.project (g u)) (f (p.project u))

abbrev Commutes₂ {A B C U V W : Type} (p : PortLift A U) (q : PortLift B V) (r : PortLift C W)
    (Dom : U → V → Type) (Rel : C → C → Type) (f : A → B → C) (g : U → V → W) : Type :=
  ∀ (u : U) (v : V), Dom u v → Rel (r.project (g u v)) (f (p.project u) (q.project v))

abbrev Commutes₃ {A B C D U V W X : Type}
    (p : PortLift A U) (q : PortLift B V) (r : PortLift C W) (s : PortLift D X)
    (Dom : U → V → W → Type) (Rel : D → D → Type)
    (f : A → B → C → D) (g : U → V → W → X) : Type :=
  ∀ (u : U) (v : V) (w : W), Dom u v w →
    Rel (s.project (g u v w)) (f (p.project u) (q.project v) (r.project w))

-- §2 `Context.PolyTransport`

structure PortRel (A B : Type) : Type 1 where
  portRel ::
  rel : A → B → Type

abbrev idPort (A : Type) : PortRel A A :=
  PortRel.portRel AgdaId

abbrev equivPort {A : Type} (r : A → A → Type) : PortRel A A :=
  PortRel.portRel r

abbrev graphPort {A B : Type} (f : A → B) : PortRel A B :=
  PortRel.portRel (fun a b => AgdaId (f a) b)

abbrev cographPort {A B : Type} (g : B → A) : PortRel A B :=
  PortRel.portRel (fun a b => AgdaId a (g b))

abbrev tensorPort {A₁ B₁ A₂ B₂ : Type} (P : PortRel A₁ B₁) (Q : PortRel A₂ B₂) :
    PortRel (AgdaProd A₁ A₂) (AgdaProd B₁ B₂) :=
  PortRel.portRel (fun x y => AgdaProd (P.rel x.proj₁ y.proj₁) (Q.rel x.proj₂ y.proj₂))

abbrev splitPort {A B₁ B₂ : Type} (f : A → AgdaProd B₁ B₂) : PortRel A (AgdaProd B₁ B₂) :=
  graphPort f

abbrev mergePort {A₁ A₂ B : Type} (f : AgdaProd A₁ A₂ → B) : PortRel (AgdaProd A₁ A₂) B :=
  graphPort f

abbrev introPort (B : Type) : PortRel AgdaTop B :=
  PortRel.portRel (fun _ _ => AgdaTop)

abbrev elimPort (A : Type) : PortRel A AgdaTop :=
  PortRel.portRel (fun _ _ => AgdaTop)

abbrev compPort {A B C : Type} (P : PortRel A B) (Q : PortRel B C) : PortRel A C :=
  PortRel.portRel (fun a c => AgdaSigma B (fun (b : B) => AgdaProd (P.rel a b) (Q.rel b c)))

abbrev cut₁ {A B C D : Type} (f : A → AgdaProd B C) (g : B → D) (a : A) : AgdaProd D C :=
  prodMap1 g (f a)

abbrev cutRel {A B C D : Type} (R : A → B → C → Type) (S : B → D → Type)
    (a : A) (d : D) (c : C) : Type :=
  AgdaSigma B (fun (b : B) => AgdaProd (R a b c) (S b d))

abbrev TransportsPoly {Aᵢ Aₒ Bᵢ Bₒ : Type} (Rin : PortRel Aᵢ Bᵢ) (Rout : PortRel Aₒ Bₒ)
    (Dom : Aᵢ → Type) (f : Aᵢ → Aₒ) (g : Bᵢ → Bₒ) : Type :=
  ∀ (x : Aᵢ) (y : Bᵢ), Dom x → Rin.rel x y → Rout.rel (f x) (g y)

abbrev Transports₁ {A B C D : Type} : PortRel A B → PortRel C D → (A → Type) → (A → C) → (B → D) → Type :=
  TransportsPoly

abbrev Transports₂ {A₁ B₁ A₂ B₂ C D : Type}
    (R₁ : PortRel A₁ B₁) (R₂ : PortRel A₂ B₂) (Rout : PortRel C D)
    (Dom : A₁ → A₂ → Type) (f : A₁ → A₂ → C) (g : B₁ → B₂ → D) : Type :=
  ∀ (x₁ : A₁) (x₂ : A₂) (y₁ : B₁) (y₂ : B₂),
    Dom x₁ x₂ → R₁.rel x₁ y₁ → R₂.rel x₂ y₂ → Rout.rel (f x₁ x₂) (g y₁ y₂)

def composeTransportsCut
    {A A' B B' C C' D D' : Type}
    {Rin : PortRel A A'} {Rmid : PortRel B B'} {Rc : PortRel C C'} {Rd : PortRel D D'}
    {f : A → AgdaProd B C} {f' : A' → AgdaProd B' C'} {g : B → D} {g' : B' → D'}
    (first : TransportsPoly Rin (tensorPort Rmid Rc) (fun _ => AgdaTop) f f')
    (second : TransportsPoly Rmid Rd (fun _ => AgdaTop) g g') :
    TransportsPoly Rin (tensorPort Rd Rc) (fun _ => AgdaTop) (cut₁ f g) (cut₁ f' g') :=
  fun x y _ related =>
    let p := first x y AgdaTop.tt related
    AgdaSigma.mk (second (f x).proj₁ (f' y).proj₁ AgdaTop.tt p.proj₁) p.proj₂

def transportLiftCube
    {A B U V : Type} (p : U → A) (q : V → B)
    {Dom : U → Type} {b₀ b₀' : A → B} {u : U → V}
    (base : TransportsPoly (idPort A) (idPort B) (fun _ => AgdaTop) b₀ b₀')
    (upper : ∀ (x : U), Dom x → AgdaId (q (u x)) (b₀ (p x))) :
    ∀ (x : U), Dom x → AgdaId (q (u x)) (b₀' (p x)) :=
  fun x dom => idTrans (upper x dom) (base (p x) (p x) AgdaTop.tt AgdaId.refl)

-- §3 Core `Context.Terminal`

abbrev Byte : Type := AgdaFin 256
abbrev Bytes : Type := List Byte

def byte (n : Nat) : Byte :=
  agdaFinFromNatMod n 255

def utf8Char (c : Char) : Bytes :=
  let n := agdaCharToNat c
  agdaIte (agdaNatLt n 128) [byte n]
    (agdaIte (agdaNatLt n 2048) [byte (agdaAdd 192 (agdaDiv n 64)), byte (agdaAdd 128 (agdaModNat n 64))]
      (agdaIte (agdaNatLt n 65536)
        [byte (agdaAdd 224 (agdaDiv n 4096)), byte (agdaAdd 128 (agdaModNat (agdaDiv n 64) 64)), byte (agdaAdd 128 (agdaModNat n 64))]
        [byte (agdaAdd 240 (agdaDiv n 262144)), byte (agdaAdd 128 (agdaModNat (agdaDiv n 4096) 64)),
         byte (agdaAdd 128 (agdaModNat (agdaDiv n 64) 64)), byte (agdaAdd 128 (agdaModNat n 64))]))

def bytes (s : String) : Bytes :=
  agdaFoldl (fun acc c => agdaAppend acc (utf8Char c)) [] (agdaToList s)

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
  | .enter     => [byte 13]
  | .escape    => [byte 27]
  | .backspace => [byte 127]
  | .tab       => [byte 9]
  | .up        => bytes "\x1b[A"
  | .down      => bytes "\x1b[B"
  | .right     => bytes "\x1b[C"
  | .left      => bytes "\x1b[D"
  | .home      => bytes "\x1b[H"
  | .end       => bytes "\x1b[F"
  | .delete    => bytes "\x1b[3~"
  | .ctrl c    => [byte (agdaModNat (agdaCharToNat c) 32)]

inductive TermTopology : Type where
  | allTTY           : TermTopology
  | pipeStdioWithTTY : TermTopology

inductive SandboxTarget : Type where
  | localSandbox  : SandboxTarget
  | dockerSandbox : String → SandboxTarget

structure TermConfig : Type where
  termConfig ::
  target     : SandboxTarget
  topology   : TermTopology
  executable : String
  arguments  : List String
  envVars    : List (AgdaPair String String)
  rows       : Nat
  cols       : Nat
  files      : List String

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
  exitStatus : AgdaMaybe Nat

def emptyObs : RawTermObs :=
  RawTermObs.rawObs [] [] [] .nothing

def latest : AgdaMaybe Nat → AgdaMaybe Nat → AgdaMaybe Nat
  | a, .nothing => a
  | _, .just n  => .just n

def appendObs (a b : RawTermObs) : RawTermObs :=
  RawTermObs.rawObs
    (agdaAppend a.ttyOut b.ttyOut)
    (agdaAppend a.stdoutOut b.stdoutOut)
    (agdaAppend a.stderrOut b.stderrOut)
    (latest a.exitStatus b.exitStatus)

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

structure TimedMachine (S E : Type) : Type where
  timed ::
  now     : Nat
  state   : S
  timers  : List (Timer E)
  pending : RawTermObs

abbrev Handler (S E : Type) : Type :=
  TermEvent E → S → Effect S E

def removeTimer {E : Type} (n : Nat) : List (Timer E) → List (Timer E)
  | [] => []
  | t :: ts => agdaIte (agdaNatEq n t.slot) (removeTimer n ts) (t :: removeTimer n ts)
termination_by structural ts => ts

def insertTimer {E : Type} (t : Timer E) : List (Timer E) → List (Timer E)
  | [] => [t]
  | u :: us => agdaIte (agdaNatLt t.deadline u.deadline) (t :: u :: us) (u :: insertTimer t us)
termination_by structural us => us

def editTimers {E : Type} (n : Nat) : List (TimerEdit E) → List (Timer E) → List (Timer E)
  | [], ts => ts
  | .cancel k :: es, ts => editTimers n es (removeTimer k ts)
  | .arm k delay e :: es, ts =>
      editTimers n es (insertTimer (Timer.timer k (agdaAdd n (agdaMax 1 delay)) e) (removeTimer k ts))
termination_by structural es _ => es

def applyEffect {S E : Type} (e : Effect S E) (m : TimedMachine S E) : TimedMachine S E :=
  TimedMachine.timed m.now e.nextState (editTimers m.now e.edits m.timers) (appendObs m.pending e.output)

def fireDue {S E : Type} : Nat → Handler S E → TimedMachine S E → TimedMachine S E
  | 0, _, m => m
  | Nat.succ fuel, h, m =>
      match m.timers with
      | [] => m
      | t :: ts =>
          agdaIte (agdaNatLe t.deadline m.now)
            (fireDue fuel h (applyEffect (h (.timeout t.payload) m.state) { m with timers := ts }))
            m
termination_by structural fuel _ _ => fuel

def advance {S E : Type} : Nat → Handler S E → TimedMachine S E → TimedMachine S E
  | 0, _, m => m
  | Nat.succ n, h, m =>
      advance n h (fireDue (agdaLength m.timers) h { m with now := Nat.succ m.now })
termination_by structural n _ _ => n

def perform {S E : Type} (h : Handler S E) : TermStep → TimedMachine S E → TimedMachine S E
  | .sleepMs n, m => advance n h m
  | q, m          => applyEffect (h (.input q) m.state) m

def observe {S E : Type} (m : TimedMachine S E) : AgdaPair (TimedMachine S E) RawTermObs :=
  AgdaPair.mk { m with pending := RawTermObs.rawObs [] [] [] m.pending.exitStatus } m.pending

def observeSigma {S E : Type} (m : TimedMachine S E) : AgdaProd (TimedMachine S E) RawTermObs :=
  AgdaSigma.mk { m with pending := RawTermObs.rawObs [] [] [] m.pending.exitStatus } m.pending

def stepTimed {S E : Type} (h : Handler S E) (q : TermStep) (m : TimedMachine S E) :
    AgdaPair (TimedMachine S E) RawTermObs :=
  observe (perform h q m)

def stepTimedSigma {S E : Type} (h : Handler S E) (q : TermStep) (m : TimedMachine S E) :
    AgdaProd (TimedMachine S E) RawTermObs :=
  observeSigma (perform h q m)

def traceTimed {S E : Type} (h : Handler S E) : List TermStep → TimedMachine S E → List RawTermObs
  | [], _ => []
  | q :: qs, m =>
      let r := stepTimed h q m
      r.proj₂ :: traceTimed h qs r.proj₁
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
  primary : AgdaMaybe Surface
  parser  : TermParser

def blankSurface (h w : Nat) : Surface :=
  Surface.surface (agdaReplicate h (agdaReplicate w (Cell.cell ' ' plain))) 0 0 plain false

def blankScreen (h w : Nat) : Screen :=
  let h' := agdaMax 1 h
  let w' := agdaMax 1 w
  Screen.screen h' w' (blankSurface h' w') .nothing .ground

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
  { s with active := { s.active with
      row := agdaMin r (agdaSub s.height 1)
      col := agdaMin c (agdaSub s.width 1)
      wrapPending := false } }

def lineFeed (s : Screen) : Screen :=
  let scroll : List (List Cell) → List (List Cell)
    | [] => []
    | _ :: xs => agdaAppend xs [agdaReplicate s.width (Cell.cell ' ' s.active.ink)]
  agdaIte (agdaNatLt (Nat.succ s.active.row) s.height)
    (move (Nat.succ s.active.row) s.active.col s)
    { s with active := { s.active with grid := scroll s.active.grid, wrapPending := false } }

def printGlyph (c : Char) (s : Screen) : Screen :=
  let draw (t : Screen) : Screen :=
    { t with active := { t.active with
        grid := putAt t.active.row
          (putAt t.active.col (Cell.cell c t.active.ink) (getAt [] t.active.row t.active.grid))
          t.active.grid
        col := agdaMin (Nat.succ t.active.col) (agdaSub t.width 1)
        wrapPending := agdaNatEq (Nat.succ t.active.col) t.width } }
  draw (agdaIte s.active.wrapPending (lineFeed (move s.active.row 0 s)) s)

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
    agdaIte whole
      (agdaOr (agdaOr (agdaNatEq mode 2)
        (agdaAnd (agdaNatEq mode 0) (agdaOr (agdaNatLt r y) (agdaAnd (agdaNatEq r y) (agdaNatLe c x)))))
        (agdaAnd (agdaNatEq mode 1) (agdaOr (agdaNatLt y r) (agdaAnd (agdaNatEq r y) (agdaNatLe x c)))))
      (agdaAnd (agdaNatEq y r)
        (agdaOr (agdaNatEq mode 2)
          (agdaOr (agdaAnd (agdaNatEq mode 0) (agdaNatLe c x))
            (agdaAnd (agdaNatEq mode 1) (agdaNatLe x c)))))
  let line (y : Nat) : List Cell → List Cell :=
    mapIndexed (fun x v => agdaIte (chosen y x) (Cell.cell ' ' s.active.ink) v)
  { s with active := { s.active with grid := mapIndexed line s.active.grid } }

def sgrOne (n : Nat) (a : Rendition) : Rendition :=
  agdaIte (agdaNatEq n 0) plain
    (agdaIte (agdaNatEq n 1) { a with bold := true }
      (agdaIte (agdaNatEq n 22) { a with bold := false }
        (agdaIte (agdaNatEq n 4) { a with underline := true }
          (agdaIte (agdaNatEq n 24) { a with underline := false }
            (agdaIte (agdaNatEq n 7) { a with inverse := true }
              (agdaIte (agdaNatEq n 27) { a with inverse := false }
                (agdaIte (agdaNatEq n 39) { a with foreground := .defaultColour }
                  (agdaIte (agdaNatEq n 49) { a with background := .defaultColour }
                    (agdaIte (agdaAnd (agdaNatLe 30 n) (agdaNatLe n 37)) { a with foreground := .indexed (agdaSub n 30) }
                      (agdaIte (agdaAnd (agdaNatLe 40 n) (agdaNatLe n 47)) { a with background := .indexed (agdaSub n 40) }
                        (agdaIte (agdaAnd (agdaNatLe 90 n) (agdaNatLe n 97)) { a with foreground := .indexed (agdaAdd 8 (agdaSub n 90)) }
                          (agdaIte (agdaAnd (agdaNatLe 100 n) (agdaNatLe n 107)) { a with background := .indexed (agdaAdd 8 (agdaSub n 100)) }
                            a))))))))))))

def setColour (n : Nat) (c : Colour) (a : Rendition) : Rendition :=
  agdaIte (agdaNatEq n 38) { a with foreground := c } { a with background := c }

def sgrFuel : Nat → List Nat → Rendition → Rendition
  | 0, _, a => a
  | Nat.succ _, [], a => a
  | Nat.succ fuel, n :: 5 :: c :: ns, a =>
      agdaIte (agdaOr (agdaNatEq n 38) (agdaNatEq n 48))
        (sgrFuel fuel ns (setColour n (.indexed c) a))
        (sgrFuel fuel (5 :: c :: ns) (sgrOne n a))
  | Nat.succ fuel, n :: 2 :: r :: g :: b :: ns, a =>
      agdaIte (agdaOr (agdaNatEq n 38) (agdaNatEq n 48))
        (sgrFuel fuel ns (setColour n (.rgb r g b) a))
        (sgrFuel fuel (2 :: r :: g :: b :: ns) (sgrOne n a))
  | Nat.succ fuel, n :: ns, a =>
      sgrFuel fuel ns (sgrOne n a)
termination_by structural fuel _ _ => fuel

def sgr (ns : List Nat) : Rendition → Rendition :=
  sgrFuel (agdaLength ns) ns

def altScreen : Bool → Screen → Screen
  | true, s =>
      match s.primary with
      | .just _  => s
      | .nothing => { s with active := blankSurface s.height s.width, primary := .just s.active }
  | false, s =>
      match s.primary with
      | .nothing => s
      | .just a  => { s with active := a, primary := .nothing }

def dispatchCSI : Bool → List Nat → Nat → Screen → Screen
  | true, ns, cmd, s =>
      agdaIte (agdaNatEq (getAt 0 0 ns) 1049)
        (agdaIte (agdaNatEq cmd 104) (altScreen true s)
          (agdaIte (agdaNatEq cmd 108) (altScreen false s) s))
        s
  | false, ns, cmd, s =>
      agdaIte (agdaNatEq cmd 65) (move (agdaSub s.active.row (agdaMax 1 (getAt 0 0 ns))) s.active.col s)
        (agdaIte (agdaNatEq cmd 66) (move (agdaAdd s.active.row (agdaMax 1 (getAt 0 0 ns))) s.active.col s)
          (agdaIte (agdaNatEq cmd 67) (move s.active.row (agdaAdd s.active.col (agdaMax 1 (getAt 0 0 ns))) s)
            (agdaIte (agdaNatEq cmd 68) (move s.active.row (agdaSub s.active.col (agdaMax 1 (getAt 0 0 ns))) s)
              (agdaIte (agdaNatEq cmd 71) (move s.active.row (agdaSub (getAt 0 0 ns) 1) s)
                (agdaIte (agdaOr (agdaNatEq cmd 72) (agdaNatEq cmd 102))
                  (move (agdaSub (getAt 0 0 ns) 1) (agdaSub (getAt 0 1 ns) 1) s)
                  (agdaIte (agdaNatEq cmd 74) (erase true (getAt 0 0 ns) s)
                    (agdaIte (agdaNatEq cmd 75) (erase false (getAt 0 0 ns) s)
                      (agdaIte (agdaNatEq cmd 109) { s with active := { s.active with ink := sgr ns s.active.ink } }
                        s))))))))

def groundByte (n : Nat) (s : Screen) : Screen :=
  agdaIte (agdaNatEq n 27) { s with parser := .escaped }
    (agdaIte (agdaNatEq n 13) (move s.active.row 0 s)
      (agdaIte (agdaNatEq n 10) (lineFeed s)
        (agdaIte (agdaNatEq n 8) (move s.active.row (agdaSub s.active.col 1) s)
          (agdaIte (agdaNatEq n 9) (move s.active.row (agdaMul (agdaAdd 1 (agdaDiv s.active.col 8)) 8) s)
            (agdaIte (agdaAnd (agdaNatLe 32 n) (agdaNatLt n 127)) (printGlyph (agdaCharFromNat n) s)
              (agdaIte (agdaAnd (agdaNatLe 194 n) (agdaNatLt n 224)) { s with parser := .utf 1 (agdaSub n 192) }
                (agdaIte (agdaAnd (agdaNatLe 224 n) (agdaNatLt n 240)) { s with parser := .utf 2 (agdaSub n 224) }
                  (agdaIte (agdaAnd (agdaNatLe 240 n) (agdaNatLt n 245)) { s with parser := .utf 3 (agdaSub n 240) }
                    s))))))))

def ansiByte (b : Byte) (s : Screen) : Screen :=
  let ob := agdaFinToNat b
  match s.parser with
  | .ground    => groundByte ob s
  | .escaped   => { s with parser := agdaIte (agdaNatEq ob 91) (.csi false [] 0) (agdaIte (agdaNatEq ob 93) .osc .ground) }
  | .osc       => { s with parser := agdaIte (agdaNatEq ob 7) .ground (agdaIte (agdaNatEq ob 27) .oscEscape .osc) }
  | .oscEscape => { s with parser := agdaIte (agdaNatEq ob 92) .ground .osc }
  | .csi priv ns n =>
      agdaIte (agdaAnd (agdaNatLe 48 ob) (agdaNatLe ob 57)) { s with parser := .csi priv ns (agdaAdd (agdaMul 10 n) (agdaSub ob 48)) }
        (agdaIte (agdaNatEq ob 59) { s with parser := .csi priv (n :: ns) 0 }
          (agdaIte (agdaNatEq ob 63) { s with parser := .csi true ns n }
            (agdaIte (agdaAnd (agdaNatLe 64 ob) (agdaNatLe ob 126)) (dispatchCSI priv (agdaReverse (n :: ns)) ob { s with parser := .ground })
              (agdaIte (agdaNatEq ob 27) { s with parser := .escaped } s))))
  | .utf 0 _ => groundByte ob { s with parser := .ground }
  | .utf (Nat.succ remaining) n =>
      agdaIte (agdaAnd (agdaNatLe 128 ob) (agdaNatLt ob 192))
        (agdaIte (agdaNatEq remaining 0)
          (printGlyph (agdaCharFromNat (agdaAdd (agdaMul 64 n) (agdaSub ob 128))) { s with parser := .ground })
          { s with parser := .utf remaining (agdaAdd (agdaMul 64 n) (agdaSub ob 128)) })
        (groundByte ob { s with parser := .ground })

def stepANSI : Screen → Bytes → Screen :=
  agdaFoldl (fun s b => ansiByte b s)

def screenLines (s : Screen) : List String :=
  agdaMap (fun line => agdaFromList (agdaMap Cell.glyph line)) s.active.grid

-- §4 `Context.Filter`

namespace Filter

inductive Mode : Type where
  | sensitive   : Mode
  | insensitive : Mode

inductive Kind : Type where
  | prefix  : Kind
  | suffix  : Kind
  | exclude : Kind

structure Signal : Type where
  signal ::
  kind   : Kind
  exact  : Bool
  folded : Bool

structure Input : Type where
  input ::
  operation : Kind
  needle    : String
  text      : String

def starts : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, c :: cs => agdaAnd (agdaCharEq p c) (starts ps cs)
termination_by structural ps _ => ps

def contains : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | ps, c :: cs => agdaOr (starts ps (c :: cs)) (contains ps cs)
termination_by structural _ cs => cs

def hit : Kind → List Char → List Char → Bool
  | .prefix,  p, s => starts p s
  | .suffix,  p, s => starts (agdaReverse p) (agdaReverse s)
  | .exclude, p, s => contains p s

def classify : Input → Signal
  | .input k p s =>
    .signal k (hit k (agdaToList p) (agdaToList s))
      (hit k (agdaMap agdaToLower (agdaToList p)) (agdaMap agdaToLower (agdaToList s)))

def choose : Mode → Signal → Bool
  | .sensitive,   s => s.exact
  | .insensitive, s => s.folded

def combine : Kind → Bool → Bool
  | .prefix,  b => b
  | .suffix,  b => b
  | .exclude, b => agdaNot b

def expected0 (mode : Mode) (s : Signal) : Bool :=
  combine s.kind (choose mode s)

def expected1 (mode : Mode) (i : Input) : Bool :=
  expected0 mode (classify i)

def inputPort : PortLift Signal Input :=
  PortLift.portLift classify

end Filter

inductive SafeTaboo : Type where
  | bottom : AgdaBot → SafeTaboo
  | primStrRefl : ((s : String) → AgdaId (agdaStrEq s s) true) → SafeTaboo
  | primCharRefl : ((c : Char) → AgdaId (agdaCharEq c c) true) → SafeTaboo
  | strRoundtrip : ((s : String) → AgdaId (agdaFromList (agdaToList s)) s) → SafeTaboo
  | listRoundtrip : ((cs : List Char) → AgdaId (agdaToList (agdaFromList cs)) cs) → SafeTaboo
  | funExtBool : ((f g : Nat → Bool) → ((n : Nat) → AgdaId (f n) (g n)) → AgdaId f g) → SafeTaboo
  | wlpo : ((f : Nat → Bool) → AgdaSum ((n : Nat) → AgdaId (f n) false)
      (AgdaSigma Nat (fun n => AgdaId (f n) true))) → SafeTaboo
  | markov : ((f : Nat → Bool) → (((n : Nat) → AgdaId (f n) false) → AgdaBot) →
      AgdaSigma Nat (fun n => AgdaId (f n) true)) → SafeTaboo

end AgdaMirror.Context
