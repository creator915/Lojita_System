import AgdaMirror.Core
import AgdaMirror.Context

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
# `AgdaMirror.World`: Native Constructive Mirror of `Context.Tools.*`, `Context.World`, and `*Laws`

Mirrors `Clock`, `ClockLaws`, `TermLaws`, `FuzzGen`, `FsSandbox`, `NetSandbox`, `GitSandbox`,
`WebOperad` (`Set₀` core), `Context.World`, `FsLaws`, `GitLaws`, `NetLaws`, and `WorldLaws`
with 100% definitional alignment (`refl` cross-tool Frame Laws) and zero axioms.
-/

namespace AgdaMirror

open AgdaMirror.Context

/-! ## §1 `Context.Tools.Clock` & `Context.Tools.ClockLaws` -/
namespace Clock

structure SimClock : Type where
  simClock ::
  monoMs      : Nat
  wallEpochMs : Nat
  autoTicks   : List Nat

def initClock (mono wall : Nat) (ticks : List Nat) : SimClock :=
  SimClock.simClock mono wall ticks

def zeroClock : SimClock :=
  SimClock.simClock 0 0 []

def fixedStepClock (mono wall count delta : Nat) : SimClock :=
  SimClock.simClock mono wall (agdaReplicate count delta)

def popTick : List Nat → AgdaPair Nat (List Nat)
  | []      => AgdaPair.mk 0 []
  | d :: ds => AgdaPair.mk d ds

def advanceClock (d : Nat) (c : SimClock) : SimClock :=
  { c with
    monoMs      := agdaAdd d c.monoMs
    wallEpochMs := agdaAdd d c.wallEpochMs }

def tickClock (c : SimClock) : SimClock :=
  let dt := popTick c.autoTicks
  let d  := dt.proj₁
  { c with
    monoMs      := agdaAdd d c.monoMs
    wallEpochMs := agdaAdd d c.wallEpochMs
    autoTicks   := dt.proj₂ }

def readMonoMs (c : SimClock) : AgdaPair Nat SimClock :=
  let c' := tickClock c
  AgdaPair.mk c'.monoMs c'

def readMonoMsSigma (c : SimClock) : AgdaProd Nat SimClock :=
  let c' := tickClock c
  AgdaSigma.mk c'.monoMs c'

def readWallMs (c : SimClock) : AgdaPair Nat SimClock :=
  let c' := tickClock c
  AgdaPair.mk c'.wallEpochMs c'

def readWallMsSigma (c : SimClock) : AgdaProd Nat SimClock :=
  let c' := tickClock c
  AgdaSigma.mk c'.wallEpochMs c'

def sleepClockMs : Nat → SimClock → SimClock :=
  advanceClock

def deadlineReached (deadline : Nat) (c : SimClock) : Bool :=
  agdaNatLe deadline c.monoMs

def remainingMs (deadline : Nat) (c : SimClock) : Nat :=
  agdaSub deadline c.monoMs

def withTimeoutClock {A : Type} (timeoutMs costMs : Nat) (result : A) (c : SimClock) :
    AgdaPair (AgdaMaybe A) SimClock :=
  let effTimeout := agdaIte (agdaNatEq timeoutMs 0) 30000 timeoutMs
  let timedOut   := agdaNatLe effTimeout costMs
  let spent      := agdaIte timedOut effTimeout costMs
  let val        := agdaIte timedOut .nothing (.just result)
  AgdaPair.mk val (advanceClock spent c)

inductive ClockStep : Type where
  | stepNowMono       : ClockStep
  | stepNowWall       : ClockStep
  | stepSleepMs       : Nat → ClockStep
  | stepCheckDeadline : Nat → ClockStep

structure RawClockObs : Type where
  rawClockObs ::
  observedMs : Nat
  expired    : Bool

def stepSimClock : ClockStep → SimClock → AgdaPair SimClock RawClockObs
  | .stepNowMono, c =>
      let r := readMonoMs c
      AgdaPair.mk r.proj₂ (RawClockObs.rawClockObs r.proj₁ false)
  | .stepNowWall, c =>
      let r := readWallMs c
      AgdaPair.mk r.proj₂ (RawClockObs.rawClockObs r.proj₁ false)
  | .stepSleepMs d, c =>
      let c' := sleepClockMs d c
      AgdaPair.mk c' (RawClockObs.rawClockObs c'.monoMs false)
  | .stepCheckDeadline dl, c =>
      AgdaPair.mk c (RawClockObs.rawClockObs c.monoMs (deadlineReached dl c))

def traceSimClock : List ClockStep → SimClock → List RawClockObs
  | [], _ => []
  | s :: ss, c =>
      let r := stepSimClock s c
      r.proj₂ :: traceSimClock ss r.proj₁
termination_by structural ss _ => ss

private theorem agdaAdd_assoc : ∀ (a b c : Nat), agdaAdd (agdaAdd a b) c = agdaAdd a (agdaAdd b c)
  | 0, _, _          => rfl
  | Nat.succ a, b, c => congrArg Nat.succ (agdaAdd_assoc a b c)

private theorem agdaAdd_zero_r : ∀ (a : Nat), agdaAdd a 0 = a
  | 0          => rfl
  | Nat.succ a => congrArg Nat.succ (agdaAdd_zero_r a)

private theorem agdaAdd_succ_r : ∀ (a b : Nat), agdaAdd a (Nat.succ b) = Nat.succ (agdaAdd a b)
  | 0, _          => rfl
  | Nat.succ a, b => congrArg Nat.succ (agdaAdd_succ_r a b)

private theorem agdaAdd_comm : ∀ (a b : Nat), agdaAdd a b = agdaAdd b a
  | 0, b          => Eq.symm (agdaAdd_zero_r b)
  | Nat.succ a, b => Eq.trans (congrArg Nat.succ (agdaAdd_comm a b)) (Eq.symm (agdaAdd_succ_r b a))

def advanceClockZero (c : SimClock) : AgdaId (advanceClock 0 c) c :=
  .refl

def advanceClockAdd (a b : Nat) (c : SimClock) :
    AgdaId (advanceClock (agdaAdd a b) c) (advanceClock a (advanceClock b c)) :=
  agdaEqToId (by
    cases c
    simp only [advanceClock, agdaAdd_assoc])

def advanceClockComm (a b : Nat) (c : SimClock) :
    AgdaId (advanceClock a (advanceClock b c)) (advanceClock b (advanceClock a c)) :=
  idTrans (idSym (advanceClockAdd a b c))
    (idTrans (idCong (fun k => advanceClock k c) (agdaEqToId (agdaAdd_comm a b)))
      (advanceClockAdd b a c))

def advanceClockMonoLe (d : Nat) (c : SimClock) :
    AgdaNatLeRel c.monoMs (advanceClock d c).monoMs :=
  agdaNatMLeNM c.monoMs d

def advanceClockWallLe (d : Nat) (c : SimClock) :
    AgdaNatLeRel c.wallEpochMs (advanceClock d c).wallEpochMs :=
  agdaNatMLeNM c.wallEpochMs d

def advanceClockTicks (d : Nat) (c : SimClock) :
    AgdaId (advanceClock d c).autoTicks c.autoTicks :=
  .refl

def readMonoMonotonic (c : SimClock) :
    AgdaNatLeRel c.monoMs (readMonoMs c).proj₁ :=
  agdaNatMLeNM c.monoMs (popTick c.autoTicks).proj₁

def readWallMonotonic (c : SimClock) :
    AgdaNatLeRel c.wallEpochMs (readWallMs c).proj₁ :=
  agdaNatMLeNM c.wallEpochMs (popTick c.autoTicks).proj₁

def readMonoIdle (m w : Nat) :
    AgdaId (readMonoMs (SimClock.simClock m w [])) (AgdaPair.mk m (SimClock.simClock m w [])) :=
  .refl

def sleepClockZero (c : SimClock) : AgdaId (sleepClockMs 0 c) c :=
  .refl

def sleepClockAdd (a b : Nat) (c : SimClock) :
    AgdaId (sleepClockMs (agdaAdd a b) c) (sleepClockMs a (sleepClockMs b c)) :=
  advanceClockAdd a b c

def foldClockSteps : List ClockStep → SimClock → SimClock
  | [], st      => st
  | s :: ss, st => foldClockSteps ss (stepSimClock s st).proj₁
termination_by structural ss _ => ss

def traceSimClockAppend : (xs ys : List ClockStep) → (c : SimClock) →
    AgdaId (traceSimClock (agdaAppend xs ys) c)
           (agdaAppend (traceSimClock xs c) (traceSimClock ys (foldClockSteps xs c)))
  | [], _, _      => .refl
  | s :: xs, ys, c =>
      idCong ((stepSimClock s c).proj₂ :: ·)
        (traceSimClockAppend xs ys (stepSimClock s c).proj₁)

end Clock

/-! ## §2 `Context.Tools.TermLaws` -/
namespace TermLaws

def foldlAppend {A B : Type} (f : B → A → B) :
    (acc : B) → (xs ys : List A) →
    AgdaId (agdaFoldl f acc (agdaAppend xs ys)) (agdaFoldl f (agdaFoldl f acc xs) ys)
  | _, [], _        => .refl
  | acc, x :: xs, ys => foldlAppend f (f acc x) xs ys

def stepANSINil (s : Screen) : AgdaId (stepANSI s []) s := .refl

def stepANSICons (s : Screen) (b : Byte) (bs : Bytes) :
    AgdaId (stepANSI s (b :: bs)) (stepANSI (ansiByte b s) bs) := .refl

def stepANSIAppend (s : Screen) (a b : Bytes) :
    AgdaId (stepANSI s (agdaAppend a b)) (stepANSI (stepANSI s a) b) :=
  foldlAppend (fun t b' => ansiByte b' t) s a b

def latestNothingLeft : (x : AgdaMaybe Nat) → AgdaId (latest .nothing x) x
  | .nothing => .refl
  | .just _  => .refl

def latestNothingRight (x : AgdaMaybe Nat) : AgdaId (latest x .nothing) x := .refl

def latestAssoc : (a b c : AgdaMaybe Nat) →
    AgdaId (latest (latest a b) c) (latest a (latest b c))
  | _, _, .just _         => .refl
  | _, .nothing, .nothing => .refl
  | _, .just _,  .nothing => .refl

private theorem agdaAppend_nil_r {A : Type} : ∀ (xs : List A), agdaAppend xs [] = xs
  | []      => rfl
  | x :: xs => congrArg (x :: ·) (agdaAppend_nil_r xs)

private theorem agdaAppend_assoc {A : Type} : ∀ (xs ys zs : List A),
    agdaAppend (agdaAppend xs ys) zs = agdaAppend xs (agdaAppend ys zs)
  | [], _, _       => rfl
  | x :: xs, ys, zs => congrArg (x :: ·) (agdaAppend_assoc xs ys zs)

def appendObsEmptyLeft : (o : RawTermObs) → AgdaId (appendObs emptyObs o) o
  | .rawObs _ _ _ .nothing  => .refl
  | .rawObs _ _ _ (.just _) => .refl

def appendObsEmptyRight : (o : RawTermObs) → AgdaId (appendObs o emptyObs) o
  | .rawObs t so se ex =>
      agdaEqToId (by simp only [appendObs, emptyObs, latest, agdaAppend_nil_r])

def appendObsAssoc : (a b c : RawTermObs) →
    AgdaId (appendObs (appendObs a b) c) (appendObs a (appendObs b c))
  | .rawObs t₁ o₁ e₁ x₁, .rawObs t₂ o₂ e₂ x₂, .rawObs t₃ o₃ e₃ x₃ =>
      agdaEqToId (by
        have hLat := agdaIdToEq (latestAssoc x₁ x₂ x₃)
        simp only [appendObs, agdaAppend_assoc, hLat])

def advanceZero {S E : Type} (h : Handler S E) (m : TimedMachine S E) :
    AgdaId (advance 0 h m) m := .refl

def advanceAdd {S E : Type} : (a b : Nat) → (h : Handler S E) → (m : TimedMachine S E) →
    AgdaId (advance (agdaAdd a b) h m) (advance b h (advance a h m))
  | 0, _, _, _          => .refl
  | Nat.succ a, b, h, m =>
      advanceAdd a b h (fireDue (agdaLength m.timers) h { m with now := Nat.succ m.now })

def altScreenRoundtrip : (s : Screen) → AgdaId s.primary .nothing →
    AgdaId (altScreen false (altScreen true s)) s
  | .screen _ _ _ .nothing _, .refl => .refl

end TermLaws

/-! ## §3 `Context.Tools.FuzzGen` -/
namespace FuzzGen

structure Seed : Type where
  seed ::
  state : Nat

def mkSeed (n : Nat) : Seed :=
  Seed.seed (agdaModNat n 4294967296)

def nextNat (s : Seed) : AgdaPair Nat Seed :=
  let n := agdaModNat (agdaAdd (agdaMul 1664525 s.state) 1013904223) 4294967296
  AgdaPair.mk n (Seed.seed n)

abbrev Gen (A : Type) : Type :=
  Seed → AgdaPair A Seed

def runGen {A : Type} (g : Gen A) (s : Seed) : AgdaPair A Seed :=
  g s

def genPure {A : Type} (a : A) (s : Seed) : AgdaPair A Seed :=
  AgdaPair.mk a s

def genMap {A B : Type} (f : A → B) (g : Gen A) (s : Seed) : AgdaPair B Seed :=
  let r := g s
  AgdaPair.mk (f r.proj₁) r.proj₂

def genBind {A B : Type} (g : Gen A) (f : A → Gen B) (s : Seed) : AgdaPair B Seed :=
  let r := g s
  f r.proj₁ r.proj₂

def genPair {A B : Type} (a : Gen A) (b : Gen B) : Gen (AgdaPair A B) :=
  genBind a (fun x => genMap (fun y => AgdaPair.mk x y) b)

def genBounded (n : Nat) : Gen Nat :=
  genMap (fun k => agdaModNat k (Nat.succ n)) nextNat

def genBool : Gen Bool :=
  genMap (fun n => agdaNatEq n 1) (genBounded 1)

def genByte : Gen Byte :=
  genMap byte (genBounded 255)

def genList {A : Type} : Nat → Gen A → Gen (List A)
  | 0, _          => genPure []
  | Nat.succ n, g => genBind g (fun x => genMap (fun xs => x :: xs) (genList n g))
termination_by structural n _ => n

def genBytes (n : Nat) : Gen Bytes :=
  genBind (genBounded n) (fun k => genList k genByte)

def chooseAt {A : Type} (d : A) : Nat → List A → A
  | _, []               => d
  | 0, x :: _           => x
  | Nat.succ n, _ :: xs => chooseAt d n xs
termination_by structural _ xs => xs

def genChoose {A : Type} (d : A) (xs : List A) : Gen A :=
  genMap (fun n => chooseAt d n (d :: xs)) (genBounded (agdaLength xs))

def sampleMany {A : Type} : Nat → Gen A → Seed → List A
  | 0, _, _          => []
  | Nat.succ n, g, s =>
      let r := g s
      r.proj₁ :: sampleMany n g r.proj₂
termination_by structural n _ _ => n

abbrev Shrinker (A : Type) : Type :=
  A → List A

def shrinkNat : Nat → List Nat
  | 0          => []
  | Nat.succ n =>
      let h := agdaDiv (Nat.succ n) 2
      0 :: agdaAppend (agdaIte (agdaNatEq h 0) [] [h])
             (agdaIte (agdaNatEq n 0) [] (agdaIte (agdaNatEq n h) [] [n]))

def shrinkByte (b : Byte) : List Byte :=
  agdaMap byte (shrinkNat (agdaFinToNat b))

def shrinkList {A : Type} (shrink : Shrinker A) : List A → List (List A)
  | []      => []
  | x :: xs =>
      xs :: agdaAppend (agdaMap (fun y => y :: xs) (shrink x))
                       (agdaMap (fun ys => x :: ys) (shrinkList shrink xs))
termination_by structural xs => xs

def shrinkBytes : Shrinker Bytes :=
  shrinkList shrinkByte

def firstFailure {A : Type} (ok : A → Bool) : List A → AgdaMaybe A
  | []      => .nothing
  | x :: xs => agdaIte (ok x) (firstFailure ok xs) (.just x)
termination_by structural xs => xs

def minimize {A : Type} : Nat → Shrinker A → (A → Bool) → A → A
  | 0, _, _, x               => x
  | Nat.succ fuel, sh, ok, x =>
      match firstFailure ok (sh x) with
      | .nothing => x
      | .just y  => minimize fuel sh ok y
termination_by structural fuel _ _ _ => fuel

def fuzzCheck {A : Type} : Nat → Nat → Gen A → Shrinker A → (A → Bool) → Seed → AgdaMaybe A
  | 0, _, _, _, _, _                    => .nothing
  | Nat.succ count, fuel, g, sh, ok, s  =>
      let r := g s
      agdaIte (ok r.proj₁) (fuzzCheck count fuel g sh ok r.proj₂) (.just (minimize fuel sh ok r.proj₁))
termination_by structural count _ _ _ _ _ => count

end FuzzGen

/-! ## §4 `Context.Tools.FsSandbox` -/
namespace FsSandbox

def eqChars : List Char → List Char → Bool
  | [], []             => true
  | c :: cs, d :: ds   => agdaAnd (agdaNatEq (agdaCharToNat c) (agdaCharToNat d)) (eqChars cs ds)
  | _, _               => false
termination_by structural cs _ => cs

def eqStr (a b : String) : Bool :=
  eqChars (agdaToList a) (agdaToList b)

def splitSegmentChars : List Char → List Char → List (List Char)
  | acc, []      => [agdaReverse acc]
  | acc, c :: cs =>
      agdaIte (agdaNatEq (agdaCharToNat c) 47)
        (agdaReverse acc :: splitSegmentChars [] cs)
        (splitSegmentChars (c :: acc) cs)
termination_by structural _ cs => cs

def segments (p : String) : List String :=
  agdaMap agdaFromList (splitSegmentChars [] (agdaToList p))

def all {A : Type} (f : A → Bool) : List A → Bool
  | []      => true
  | x :: xs => agdaAnd (f x) (all f xs)
termination_by structural xs => xs

def validSegChars (cs : List Char) : Bool :=
  agdaAnd (agdaNot (eqChars cs []))
    (agdaAnd (agdaNot (eqChars cs ['.'])) (agdaNot (eqChars cs ['.', '.'])))

def validSegment (s : String) : Bool :=
  validSegChars (agdaToList s)

def validRelPath (p : String) : Bool :=
  agdaAnd (all validSegChars (splitSegmentChars [] (agdaToList p)))
          (all (fun c => agdaNot (agdaNatEq (agdaCharToNat c) 0)) (agdaToList p))

def eqBytes : Bytes → Bytes → Bool
  | [], []           => true
  | a :: as, b :: bs => agdaAnd (agdaNatEq (agdaFinToNat a) (agdaFinToNat b)) (eqBytes as bs)
  | _, _             => false
termination_by structural as _ => as

def ltBytes : Bytes → Bytes → Bool
  | [], []           => false
  | [], _ :: _       => true
  | _ :: _, []       => false
  | a :: as, b :: bs =>
      agdaIte (agdaNatEq (agdaFinToNat a) (agdaFinToNat b))
        (ltBytes as bs)
        (agdaNatLt (agdaFinToNat a) (agdaFinToNat b))
termination_by structural as _ => as

def prefixBytes : Bytes → Bytes → Bool
  | [], _            => true
  | _ :: _, []       => false
  | a :: as, b :: bs => agdaAnd (agdaNatEq (agdaFinToNat a) (agdaFinToNat b)) (prefixBytes as bs)
termination_by structural as _ => as

def isParent (p q : String) : Bool :=
  prefixBytes (bytes (agdaStrAppend p "/")) (bytes q)

def collide (p q : String) : Bool :=
  agdaOr (eqStr p q) (agdaOr (isParent p q) (isParent q p))

def noPathCollisions : List String → Bool
  | []      => true
  | p :: ps => agdaAnd (validRelPath p) (agdaAnd (all (fun q => agdaNot (collide p q)) ps) (noPathCollisions ps))
termination_by structural ps => ps

def maskMode (n : Nat) : Nat :=
  agdaModNat n 512

inductive FsNodeKind : Type where
  | regularNode : FsNodeKind
  | dirNode     : FsNodeKind
  | symlinkNode : FsNodeKind

inductive FsFixture : Type where
  | fixDir     : String → Nat → FsFixture
  | fixFile    : String → Nat → Bytes → FsFixture
  | fixSymlink : String → String → FsFixture

structure FsConfig : Type where
  fsConfig ::
  target     : SandboxTarget
  envVars    : List (AgdaPair String String)
  ownedFiles : List String
  fixtures   : List FsFixture

inductive FsStep : Type where
  | runCmd        : String → List String → Bytes → Nat → FsStep
  | writeFileStep : String → Bytes → FsStep
  | mkdirStep     : String → Nat → FsStep
  | symlinkStep   : String → String → FsStep
  | chmodStep     : String → Nat → FsStep
  | unlinkStep    : String → FsStep
  | snapshotStep  : FsStep

structure FsEntryObs : Type where
  fsEntry ::
  entryPath  : String
  entryKind  : FsNodeKind
  entryMode  : Nat
  entryBytes : Bytes

structure RawFsObs : Type where
  rawFsObs ::
  stdoutOut  : Bytes
  stderrOut  : Bytes
  exitStatus : AgdaMaybe Nat
  timedOut   : Bool
  entries    : List FsEntryObs

def emptyFsObs : RawFsObs :=
  RawFsObs.rawFsObs [] [] .nothing false []

def rejectedFsObs : RawFsObs :=
  RawFsObs.rawFsObs [] (bytes "filesystem operation rejected") (.just 1) false []

def eqKind : FsNodeKind → FsNodeKind → Bool
  | .regularNode, .regularNode => true
  | .dirNode,     .dirNode     => true
  | .symlinkNode, .symlinkNode => true
  | _,            _            => false

def eqEntry (a b : FsEntryObs) : Bool :=
  agdaAnd (eqStr a.entryPath b.entryPath)
    (agdaAnd (eqKind a.entryKind b.entryKind)
      (agdaAnd (agdaNatEq a.entryMode b.entryMode) (eqBytes a.entryBytes b.entryBytes)))

def eqEntries : List FsEntryObs → List FsEntryObs → Bool
  | [], []           => true
  | a :: as, b :: bs => agdaAnd (eqEntry a b) (eqEntries as bs)
  | _, _             => false
termination_by structural as _ => as

def eqExit : AgdaMaybe Nat → AgdaMaybe Nat → Bool
  | .nothing, .nothing => true
  | .just a,  .just b  => agdaNatEq a b
  | _,        _        => false

def eqBool : Bool → Bool → Bool
  | true,  true  => true
  | false, false => true
  | _,     _     => false

def eqObs (a b : RawFsObs) : Bool :=
  agdaAnd (eqBytes a.stdoutOut b.stdoutOut)
    (agdaAnd (eqBytes a.stderrOut b.stderrOut)
      (agdaAnd (eqExit a.exitStatus b.exitStatus)
        (agdaAnd (eqBool a.timedOut b.timedOut) (eqEntries a.entries b.entries))))

def eqTrace : List RawFsObs → List RawFsObs → Bool
  | [], []           => true
  | a :: as, b :: bs => agdaAnd (eqObs a b) (eqTrace as bs)
  | _, _             => false
termination_by structural as _ => as

structure VirtualFs : Type where
  virtualFs ::
  fsEntries : List FsEntryObs

def lookupEntry (p : String) : List FsEntryObs → AgdaMaybe FsEntryObs
  | []      => .nothing
  | e :: es => agdaIte (eqStr p e.entryPath) (.just e) (lookupEntry p es)
termination_by structural es => es

def insertEntry (e : FsEntryObs) : List FsEntryObs → List FsEntryObs
  | []      => [e]
  | x :: xs =>
      agdaIte (eqStr e.entryPath x.entryPath)
        (e :: xs)
        (agdaIte (ltBytes (bytes e.entryPath) (bytes x.entryPath))
          (e :: x :: xs)
          (x :: insertEntry e xs))
termination_by structural xs => xs

def removeEntry (p : String) : List FsEntryObs → List FsEntryObs
  | []      => []
  | x :: xs => agdaIte (eqStr p x.entryPath) xs (x :: removeEntry p xs)
termination_by structural xs => xs

def putEntry (e : FsEntryObs) (v : VirtualFs) : VirtualFs :=
  VirtualFs.virtualFs (insertEntry e v.fsEntries)

def joinPart (p q : String) : String :=
  agdaIte (eqStr p "") q (agdaStrAppend p (agdaStrAppend "/" q))

def parentsFrom : String → List String → List String
  | _, []            => []
  | _, [_]           => []
  | p, x :: y :: xs  =>
      let px := joinPart p x
      px :: parentsFrom px (y :: xs)
termination_by structural _ xs => xs

def parentPaths (p : String) : List String :=
  parentsFrom "" (segments p)

def ensureParents (create : Bool) : List String → VirtualFs → AgdaMaybe VirtualFs
  | [], v      => .just v
  | p :: ps, v =>
      match lookupEntry p v.fsEntries with
      | .just e  => agdaIte (eqKind e.entryKind .dirNode) (ensureParents create ps v) .nothing
      | .nothing => agdaIte create (ensureParents create ps (putEntry (FsEntryObs.fsEntry p .dirNode 493 []) v)) .nothing
termination_by structural ps _ => ps

def prepare (create : Bool) (p : String) (v : VirtualFs) : AgdaMaybe VirtualFs :=
  agdaIte (validRelPath p) (ensureParents create (parentPaths p) v) .nothing

def writeLeaf (p : String) (bs : Bytes) (v : VirtualFs) : AgdaMaybe VirtualFs :=
  match lookupEntry p v.fsEntries with
  | .nothing => .just (putEntry (FsEntryObs.fsEntry p .regularNode 420 bs) v)
  | .just e  =>
      agdaIte (eqKind e.entryKind .regularNode)
        (.just (putEntry (FsEntryObs.fsEntry p .regularNode e.entryMode bs) v))
        .nothing

def mkdirLeaf (p : String) (mode : Nat) (v : VirtualFs) : AgdaMaybe VirtualFs :=
  match lookupEntry p v.fsEntries with
  | .nothing => .just (putEntry (FsEntryObs.fsEntry p .dirNode (maskMode mode) []) v)
  | .just e  =>
      agdaIte (eqKind e.entryKind .dirNode)
        (.just (putEntry (FsEntryObs.fsEntry p .dirNode (maskMode mode) []) v))
        .nothing

def linkLeaf (p dest : String) (v : VirtualFs) : AgdaMaybe VirtualFs :=
  match lookupEntry p v.fsEntries with
  | .nothing => .just (putEntry (FsEntryObs.fsEntry p .symlinkNode 511 (bytes dest)) v)
  | .just e  =>
      agdaIte (eqKind e.entryKind .dirNode)
        .nothing
        (.just (putEntry (FsEntryObs.fsEntry p .symlinkNode 511 (bytes dest)) v))

def chmodLeaf (p : String) (mode : Nat) (v : VirtualFs) : AgdaMaybe VirtualFs :=
  match lookupEntry p v.fsEntries with
  | .nothing => .nothing
  | .just e  =>
      agdaIte (eqKind e.entryKind .symlinkNode)
        .nothing
        (.just (putEntry (FsEntryObs.fsEntry p e.entryKind (maskMode mode) e.entryBytes) v))

def unlinkLeaf (p : String) (v : VirtualFs) : AgdaMaybe VirtualFs :=
  match lookupEntry p v.fsEntries with
  | .nothing => .nothing
  | .just _  =>
      agdaIte (all (fun x => agdaNot (isParent p x.entryPath)) v.fsEntries)
        (.just (VirtualFs.virtualFs (removeEntry p v.fsEntries)))
        .nothing

def bindMaybe {A B : Type} : AgdaMaybe A → (A → AgdaMaybe B) → AgdaMaybe B
  | .nothing, _ => .nothing
  | .just x,  f => f x

def applyFs : FsStep → VirtualFs → AgdaMaybe VirtualFs
  | .writeFileStep p bs, v => bindMaybe (prepare true p v) (writeLeaf p bs)
  | .mkdirStep p mode,   v => bindMaybe (prepare true p v) (mkdirLeaf p mode)
  | .symlinkStep p dest, v =>
      agdaIte (agdaAnd (all (fun c => agdaNot (agdaNatEq (agdaCharToNat c) 0)) (agdaToList dest))
                       (agdaNot (eqStr dest "")))
        (bindMaybe (prepare true p v) (linkLeaf p dest))
        .nothing
  | .chmodStep p mode,   v => bindMaybe (prepare false p v) (chmodLeaf p mode)
  | .unlinkStep p,       v => bindMaybe (prepare false p v) (unlinkLeaf p)
  | _,                   v => .just v

abbrev CmdSemantics : Type :=
  String → List String → Bytes → Nat → VirtualFs →
    AgdaPair VirtualFs (AgdaPair Bytes (AgdaPair Bytes (AgdaPair Nat Bool)))

def noopCmd : CmdSemantics :=
  fun _ _ _ _ v =>
    AgdaPair.mk v (AgdaPair.mk [] (AgdaPair.mk [] (AgdaPair.mk 0 false)))

def finishFs (old : VirtualFs) : AgdaMaybe VirtualFs → AgdaPair VirtualFs RawFsObs
  | .nothing   => AgdaPair.mk old rejectedFsObs
  | .just next => AgdaPair.mk next emptyFsObs

def stepVirtualFs (cmd : CmdSemantics) : FsStep → VirtualFs → AgdaPair VirtualFs RawFsObs
  | .runCmd exe args input ms, v =>
      let r := cmd exe args input ms v
      let next    := r.proj₁
      let out     := r.proj₂.proj₁
      let err     := r.proj₂.proj₂.proj₁
      let status  := r.proj₂.proj₂.proj₂.proj₁
      let timeout := r.proj₂.proj₂.proj₂.proj₂
      AgdaPair.mk next (RawFsObs.rawFsObs out err (.just status) timeout [])
  | .snapshotStep, v =>
      AgdaPair.mk v (RawFsObs.rawFsObs [] [] .nothing false v.fsEntries)
  | q, v =>
      finishFs v (applyFs q v)

def traceVirtualFs (cmd : CmdSemantics) : List FsStep → VirtualFs → List RawFsObs
  | [], _      => []
  | q :: qs, v =>
      let r := stepVirtualFs cmd q v
      r.proj₂ :: traceVirtualFs cmd qs r.proj₁
termination_by structural qs _ => qs

def retain (old : VirtualFs) : AgdaMaybe VirtualFs → VirtualFs
  | .nothing => old
  | .just v  => v

def initOwned : List String → List Bytes → VirtualFs → VirtualFs
  | [], _, v            => v
  | p :: ps, [], v      => initOwned ps [] (retain v (applyFs (.writeFileStep p []) v))
  | p :: ps, b :: bs, v => initOwned ps bs (retain v (applyFs (.writeFileStep p b) v))
termination_by structural ps _ _ => ps

def initDirs : List FsFixture → VirtualFs → VirtualFs
  | [], v                    => v
  | .fixDir p mode :: fs, v  => initDirs fs (retain v (applyFs (.mkdirStep p mode) v))
  | _ :: fs, v               => initDirs fs v
termination_by structural fs _ => fs

def initFixtures : List FsFixture → VirtualFs → VirtualFs
  | [], v                          => v
  | .fixFile p mode bs :: fs, v    =>
      initFixtures fs (retain v (bindMaybe (applyFs (.writeFileStep p bs) v) (chmodLeaf p mode)))
  | .fixSymlink p dest :: fs, v    =>
      initFixtures fs (retain v (applyFs (.symlinkStep p dest) v))
  | _ :: fs, v                     => initFixtures fs v
termination_by structural fs _ => fs

def initVirtualFs (cfg : FsConfig) (contents : List Bytes) : VirtualFs :=
  initFixtures cfg.fixtures
    (initOwned cfg.ownedFiles contents (initDirs cfg.fixtures (VirtualFs.virtualFs [])))

inductive FsDiff : Type where
  | added    : String → FsDiff
  | modified : String → FsDiff
  | removed  : String → FsDiff

def diffSnapshot : List FsEntryObs → List FsEntryObs → List FsDiff
  | [], ys           => agdaMap (fun y => FsDiff.added y.entryPath) ys
  | xs, []           => agdaMap (fun x => FsDiff.removed x.entryPath) xs
  | x :: xs, y :: ys =>
      if eqStr x.entryPath y.entryPath then
        agdaAppend (agdaIte (eqEntry x y) [] [FsDiff.modified x.entryPath]) (diffSnapshot xs ys)
      else if ltBytes (bytes x.entryPath) (bytes y.entryPath) then
        FsDiff.removed x.entryPath :: diffSnapshot xs (y :: ys)
      else
        FsDiff.added y.entryPath :: diffSnapshot (x :: xs) ys
termination_by xs ys => xs.length + ys.length

end FsSandbox

/-! ## §5 `Context.Tools.NetSandbox` -/
namespace NetSandbox

def digitChar : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | _ => '9'

def decCharsFuel : Nat → Nat → List Char → List Char
  | 0, _, acc          => acc
  | Nat.succ f, n, acc =>
      agdaIte (agdaNatLt n 10)
        (digitChar n :: acc)
        (decCharsFuel f (agdaDiv n 10) (digitChar (agdaModNat n 10) :: acc))
termination_by structural f _ _ => f

def showDec (n : Nat) : String :=
  agdaFromList (decCharsFuel (Nat.succ n) n [])

structure HttpRoute : Type where
  httpRoute ::
  routeMethod  : String
  routePath    : String
  routeStatus  : Nat
  routeReason  : String
  routeHeaders : List (AgdaPair String String)
  routeBody    : Bytes

structure RawStubRule : Type where
  rawStubRule ::
  matchPrefix  : Bytes
  replyPayload : Bytes

inductive NetTopology : Type where
  | httpStubMode        : List HttpRoute → NetTopology
  | tcpStubMode         : List RawStubRule → NetTopology
  | udpStubMode         : List RawStubRule → NetTopology
  | daemonProbeMode     : String → List String → NetTopology
  | httpDelayedStubMode : Nat → List HttpRoute → NetTopology
  | tcpDelayedStubMode  : Nat → List RawStubRule → NetTopology

structure NetConfig : Type where
  netConfig ::
  target     : SandboxTarget
  topology   : NetTopology
  envVars    : List (AgdaPair String String)
  ownedFiles : List String

def eqBytes : Bytes → Bytes → Bool :=
  FsSandbox.eqBytes

def eqByteLists : List Bytes → List Bytes → Bool
  | [], []           => true
  | a :: as, b :: bs => agdaAnd (eqBytes a b) (eqByteLists as bs)
  | _, _             => false
termination_by structural as _ => as

def prefixBytes : Bytes → Bytes → Bool :=
  FsSandbox.prefixBytes

def lower (s : String) : String :=
  agdaFromList (agdaMap agdaToLower (agdaToList s))

def hasHeader (key : String) : List (AgdaPair String String) → Bool
  | []             => false
  | nv :: rest     => agdaOr (FsSandbox.eqStr (lower key) (lower nv.proj₁)) (hasHeader key rest)
termination_by structural hs => hs

def headerLines : List (AgdaPair String String) → String
  | []         => ""
  | nv :: rest =>
      agdaStrAppend nv.proj₁
        (agdaStrAppend ": " (agdaStrAppend nv.proj₂ (agdaStrAppend "\r\n" (headerLines rest))))
termination_by structural hs => hs

def autoHeader (name value : String) (hs : List (AgdaPair String String)) : String :=
  agdaIte (hasHeader name hs) "" (agdaStrAppend name (agdaStrAppend ": " (agdaStrAppend value "\r\n")))

def headerBytes : List (AgdaPair String String) → Bytes
  | []         => []
  | nv :: rest =>
      agdaAppend (bytes nv.proj₁)
        (agdaAppend (bytes ": ")
          (agdaAppend (bytes nv.proj₂)
            (agdaAppend (bytes "\r\n") (headerBytes rest))))
termination_by structural hs => hs

def autoHeaderBytes (name : String) (value : Bytes) (hs : List (AgdaPair String String)) : Bytes :=
  agdaIte (hasHeader name hs) []
    (agdaAppend (bytes name) (agdaAppend (bytes ": ") (agdaAppend value (bytes "\r\n"))))

def decBytes (n : Nat) : Bytes :=
  agdaMap (fun c => byte (agdaCharToNat c)) (decCharsFuel (Nat.succ n) n [])

def encodeHttpReq (method path : String) (hs : List (AgdaPair String String)) (body : Bytes) : Bytes :=
  agdaAppend (bytes method)
    (agdaAppend (bytes " ")
      (agdaAppend (bytes path)
        (agdaAppend (bytes " HTTP/1.1\r\n")
          (agdaAppend (autoHeaderBytes "Host" (bytes "127.0.0.1") hs)
            (agdaAppend (autoHeaderBytes "Connection" (bytes "close") hs)
              (agdaAppend (autoHeaderBytes "Content-Length" (decBytes (agdaLength body)) hs)
                (agdaAppend (headerBytes hs) (agdaAppend (bytes "\r\n") body))))))))

def encodeHttpResp (status : Nat) (reason : String) (hs : List (AgdaPair String String)) (body : Bytes) : Bytes :=
  agdaAppend (bytes "HTTP/1.1 ")
    (agdaAppend (decBytes status)
      (agdaAppend (bytes " ")
        (agdaAppend (bytes reason)
          (agdaAppend (bytes "\r\n")
            (agdaAppend (autoHeaderBytes "Content-Length" (decBytes (agdaLength body)) hs)
              (agdaAppend (autoHeaderBytes "Connection" (bytes "close") hs)
                (agdaAppend (headerBytes hs) (agdaAppend (bytes "\r\n") body))))))))

structure HttpReqView : Type where
  httpReqView ::
  reqMethod : String
  reqTarget : String
  reqBody   : Bytes

structure HttpRespView : Type where
  httpRespView ::
  respCode : Nat
  respBody : Bytes

def splitMarkGo (marker : Bytes) : Bytes → Bytes → AgdaMaybe (AgdaPair Bytes Bytes)
  | _,   []      => .nothing
  | acc, b :: bs =>
      let rest := b :: bs
      agdaIte (prefixBytes marker rest)
        (.just (AgdaPair.mk (agdaReverse acc) (agdaDrop (agdaLength marker) rest)))
        (splitMarkGo marker (b :: acc) bs)
termination_by structural _ rest => rest

def splitMark (marker : Bytes) : Bytes → AgdaMaybe (AgdaPair Bytes Bytes) :=
  splitMarkGo marker []

def isAsciiSpaceByte (b : Byte) : Bool :=
  let n := agdaFinToNat b
  agdaOr (agdaNatEq n 32)
    (agdaOr (agdaNatEq n 9)
      (agdaOr (agdaNatEq n 10)
        (agdaOr (agdaNatEq n 11)
          (agdaOr (agdaNatEq n 12) (agdaNatEq n 13)))))

def flushWordAcc : Bytes → List Bytes
  | []      => []
  | x :: xs => [agdaReverse (x :: xs)]

def wordsBytesGo : Bytes → Bytes → List Bytes
  | acc, []      => flushWordAcc acc
  | acc, b :: bs =>
      agdaIte (isAsciiSpaceByte b)
        (agdaAppend (flushWordAcc acc) (wordsBytesGo [] bs))
        (wordsBytesGo (b :: acc) bs)
termination_by structural _ bs => bs

def wordsBytes : Bytes → List Bytes :=
  wordsBytesGo []

def wireText (bs : Bytes) : String :=
  agdaFromList (agdaMap (fun b => agdaCharFromNat (agdaFinToNat b)) bs)

def httpVersion (s : String) : Bool :=
  agdaOr (FsSandbox.eqStr s "HTTP/1.1") (FsSandbox.eqStr s "HTTP/1.0")

def httpVersionBytes (bs : Bytes) : Bool :=
  agdaOr (eqBytes bs (bytes "HTTP/1.1")) (eqBytes bs (bytes "HTTP/1.0"))

def requestLineBytes : List Bytes → Bytes → AgdaMaybe HttpReqView
  | [methodB, pathB, versionB], body =>
      agdaIte (httpVersionBytes versionB)
        (.just (HttpReqView.httpReqView (wireText methodB) (wireText pathB) body))
        .nothing
  | _, _ => .nothing

def requestLine : List String → Bytes → AgdaMaybe HttpReqView
  | [method, path, version], body =>
      agdaIte (httpVersion version) (.just (HttpReqView.httpReqView method path body)) .nothing
  | _, _ => .nothing

def parseHttpReq (input : Bytes) : AgdaMaybe HttpReqView :=
  match splitMark (bytes "\r\n") input, splitMark (bytes "\r\n\r\n") input with
  | .just lineRem, .just hdrBody => requestLineBytes (wordsBytes lineRem.proj₁) hdrBody.proj₂
  | _, _ => .nothing

def digitValue (b : Byte) : AgdaMaybe Nat :=
  agdaIte (agdaAnd (agdaNatLe 48 (agdaFinToNat b)) (agdaNatLt (agdaFinToNat b) 58))
    (.just (agdaSub (agdaFinToNat b) 48))
    .nothing

def statusValue : Bytes → AgdaMaybe Nat
  | [a, b, c] =>
      match digitValue a, digitValue b, digitValue c with
      | .just x, .just y, .just z => .just (agdaAdd (agdaMul 100 x) (agdaAdd (agdaMul 10 y) z))
      | _, _, _ => .nothing
  | _ => .nothing

def statusView : AgdaMaybe Nat → Bytes → AgdaMaybe HttpRespView
  | .nothing,   _    => .nothing
  | .just code, body => .just (HttpRespView.httpRespView code body)

def responseLineBytes : List Bytes → Bytes → AgdaMaybe HttpRespView
  | versionB :: codeB :: _, body =>
      agdaIte (httpVersionBytes versionB) (statusView (statusValue codeB) body) .nothing
  | _, _ => .nothing

def responseLine : List String → Bytes → AgdaMaybe HttpRespView
  | version :: code :: _, body =>
      agdaIte (httpVersion version) (statusView (statusValue (bytes code)) body) .nothing
  | _, _ => .nothing

def parseHttpResp (input : Bytes) : AgdaMaybe HttpRespView :=
  match splitMark (bytes "\r\n") input, splitMark (bytes "\r\n\r\n") input with
  | .just lineRem, .just hdrBody => responseLineBytes (wordsBytes lineRem.proj₁) hdrBody.proj₂
  | _, _ => .nothing

def routeMatch (expected actual : String) : Bool :=
  agdaOr (FsSandbox.eqStr expected "*") (FsSandbox.eqStr expected actual)

def matchHttpRoute : List HttpRoute → HttpReqView → Bytes
  | [], _        => encodeHttpResp 404 "Not Found" [] []
  | r :: rs, req =>
      agdaIte (agdaAnd (routeMatch r.routeMethod req.reqMethod) (routeMatch r.routePath req.reqTarget))
        (encodeHttpResp r.routeStatus r.routeReason r.routeHeaders r.routeBody)
        (matchHttpRoute rs req)
termination_by structural rs _ => rs

def matchRawRule : List RawStubRule → Bytes → Bytes
  | [], _          => []
  | r :: rs, input => agdaIte (prefixBytes r.matchPrefix input) r.replyPayload (matchRawRule rs input)
termination_by structural rs _ => rs

inductive NetStep : Type where
  | runClient     : String → List String → Bytes → Nat → NetStep
  | waitPortReady : Nat → NetStep
  | tcpProbe      : Bytes → Nat → NetStep
  | httpProbe     : String → String → List (AgdaPair String String) → Bytes → Nat → NetStep
  | udpProbe      : Bytes → Nat → NetStep
  | sleepNetMs    : Nat → NetStep
  | drainNet      : NetStep

structure RawNetObs : Type where
  rawNetObs ::
  stdoutOut    : Bytes
  stderrOut    : Bytes
  wireReply    : Bytes
  capturedReqs : List Bytes
  exitStatus   : AgdaMaybe Nat
  timedOut     : Bool

def emptyNetObs : RawNetObs :=
  RawNetObs.rawNetObs [] [] [] [] .nothing false

def eqExit : AgdaMaybe Nat → AgdaMaybe Nat → Bool := FsSandbox.eqExit
def eqBool : Bool → Bool → Bool := FsSandbox.eqBool

def eqObs (a b : RawNetObs) : Bool :=
  agdaAnd (eqBytes a.stdoutOut b.stdoutOut)
    (agdaAnd (eqBytes a.stderrOut b.stderrOut)
      (agdaAnd (eqBytes a.wireReply b.wireReply)
        (agdaAnd (eqByteLists a.capturedReqs b.capturedReqs)
          (agdaAnd (eqExit a.exitStatus b.exitStatus) (eqBool a.timedOut b.timedOut)))))

def eqReqView (a b : HttpReqView) : Bool :=
  agdaAnd (FsSandbox.eqStr a.reqMethod b.reqMethod)
    (agdaAnd (FsSandbox.eqStr a.reqTarget b.reqTarget) (eqBytes a.reqBody b.reqBody))

def eqReqViews : List (AgdaMaybe HttpReqView) → List (AgdaMaybe HttpReqView) → Bool
  | [], []                     => true
  | .just a :: as, .just b :: bs => agdaAnd (eqReqView a b) (eqReqViews as bs)
  | .nothing :: as, .nothing :: bs => eqReqViews as bs
  | _, _                       => false
termination_by structural as _ => as

def httpExchange (routes : List HttpRoute) : AgdaMaybe HttpReqView → Bytes
  | .nothing  => []
  | .just req => matchHttpRoute routes req

def stubReply : NetTopology → Bytes → Bytes
  | .httpStubMode routes,          input => httpExchange routes (parseHttpReq input)
  | .tcpStubMode rules,            input => matchRawRule rules input
  | .udpStubMode rules,            input => matchRawRule rules input
  | .daemonProbeMode _ _,          _     => []
  | .httpDelayedStubMode _ routes, input => httpExchange routes (parseHttpReq input)
  | .tcpDelayedStubMode _ rules,   input => matchRawRule rules input

def evalStubExchange (mode : NetTopology) (requests : List Bytes) : AgdaPair (List Bytes) (List Bytes) :=
  AgdaPair.mk requests (agdaMap (stubReply mode) requests)

structure DaemonModel : Type where
  daemonModel ::
  daemonReady   : Bool
  daemonHandler : Bytes → Bytes
  daemonOut     : Bytes
  daemonErr     : Bytes
  daemonExit    : AgdaMaybe Nat

def modelWire (model : DaemonModel) : NetStep → Bytes
  | .tcpProbe input _               => model.daemonHandler input
  | .httpProbe method path hs body _ => model.daemonHandler (encodeHttpReq method path hs body)
  | .udpProbe input _               => model.daemonHandler input
  | _                               => []

def modelTimeout (model : DaemonModel) : NetStep → Bool
  | .waitPortReady _ => agdaIte model.daemonReady false true
  | _                => false

def stepDaemonModel (model : DaemonModel) (st : NetStep) : AgdaPair DaemonModel RawNetObs :=
  AgdaPair.mk
    (DaemonModel.daemonModel model.daemonReady model.daemonHandler [] [] .nothing)
    (RawNetObs.rawNetObs model.daemonOut model.daemonErr (modelWire model st) [] model.daemonExit (modelTimeout model st))

def traceDaemonModel (model : DaemonModel) : List NetStep → List RawNetObs
  | []        => []
  | st :: sts =>
      let r := stepDaemonModel model st
      r.proj₂ :: traceDaemonModel r.proj₁ sts
termination_by structural sts => sts

end NetSandbox

/-! ## §6 `Context.Tools.GitSandbox` -/
namespace GitSandbox

structure GitConfig : Type where
  gitConfig ::
  target        : SandboxTarget
  defaultBranch : String
  authorName    : String
  authorEmail   : String
  baseEpochSec  : Nat
  envVars       : List (AgdaPair String String)
  ownedFiles    : List String

inductive GitStep : Type where
  | gitWriteFile    : String → Bytes → GitStep
  | gitRemoveFile   : String → GitStep
  | gitStageAll     : GitStep
  | gitStagePaths   : List String → GitStep
  | gitCommit       : String → Nat → GitStep
  | gitSwitchBranch : String → Bool → GitStep
  | gitCreateTag    : String → GitStep
  | gitStatus       : GitStep
  | gitRunTarget    : String → List String → Bytes → Nat → GitStep

structure GitRepoSummary : Type where
  gitSummary ::
  currentBranch  : String
  commitCount    : Nat
  branchNames    : List String
  tagNames       : List String
  stagedPaths    : List String
  modifiedPaths  : List String
  untrackedPaths : List String

structure RawGitObs : Type where
  rawGitObs ::
  stdoutOut  : Bytes
  stderrOut  : Bytes
  commitHash : String
  exitStatus : AgdaMaybe Nat
  timedOut   : Bool
  summary    : AgdaMaybe GitRepoSummary

def validGitPath (p : String) : Bool :=
  match FsSandbox.segments p with
  | []         => false
  | first :: _ => agdaAnd (FsSandbox.validRelPath p) (agdaNot (FsSandbox.eqStr first ".git"))

def refChar (c : Char) : Bool :=
  let n := agdaCharToNat c
  agdaOr (agdaAnd (agdaNatLt 47 n) (agdaNatLt n 58))
    (agdaOr (agdaAnd (agdaNatLt 64 n) (agdaNatLt n 91))
      (agdaOr (agdaAnd (agdaNatLt 96 n) (agdaNatLt n 123))
        (agdaOr (agdaNatEq n 45)
          (agdaOr (agdaNatEq n 95)
            (agdaOr (agdaNatEq n 46) (agdaNatEq n 47))))))

def noDoubleDot : List Char → Bool
  | []            => true
  | [_]           => true
  | a :: b :: cs  =>
      agdaAnd (agdaNot (agdaAnd (agdaNatEq (agdaCharToNat a) 46) (agdaNatEq (agdaCharToNat b) 46)))
              (noDoubleDot (b :: cs))
termination_by structural cs => cs

def validRefPart (p : String) : Bool :=
  match agdaToList p with
  | []     => false
  | c :: _ =>
      agdaAnd (agdaNot (agdaNatEq (agdaCharToNat c) 46))
        (agdaAnd (agdaNot (FsSandbox.prefixBytes (bytes ".") (agdaReverse (bytes p))))
                 (agdaNot (FsSandbox.prefixBytes (agdaReverse (bytes ".lock")) (agdaReverse (bytes p)))))

def validRefName (p : String) : Bool :=
  match agdaToList p with
  | []      => false
  | c :: cs =>
      agdaAnd (agdaNot (agdaNatEq (agdaCharToNat c) 45))
        (agdaAnd (FsSandbox.validRelPath p)
          (agdaAnd (FsSandbox.all refChar (c :: cs))
            (agdaAnd (noDoubleDot (c :: cs))
              (agdaAnd (FsSandbox.all validRefPart (FsSandbox.segments p))
                       (agdaNot (FsSandbox.prefixBytes (bytes ".") (agdaReverse (bytes p))))))))

def validBranch (p : String) : Bool :=
  agdaAnd (validRefName p) (agdaNot (FsSandbox.eqStr p "HEAD"))

abbrev GitTree : Type :=
  List (AgdaPair String Bytes)

structure PureCommit : Type where
  pureCommit ::
  parentIndex   : AgdaMaybe Nat
  treeSnapshot  : GitTree
  commitMessage : String
  timestamp     : Nat

structure PureGitRepo : Type where
  pureGitRepo ::
  config     : GitConfig
  worktree   : GitTree
  index      : GitTree
  commits    : List PureCommit
  branchMap  : List (AgdaPair String (AgdaMaybe Nat))
  headBranch : String
  tagMap     : List (AgdaPair String Nat)

def lookupName {A : Type} (p : String) : List (AgdaPair String A) → AgdaMaybe A
  | []       => .nothing
  | qx :: xs => agdaIte (FsSandbox.eqStr p qx.proj₁) (.just qx.proj₂) (lookupName p xs)
termination_by structural xs => xs

def putName {A : Type} (p : String) (x : A) : List (AgdaPair String A) → List (AgdaPair String A)
  | []       => [AgdaPair.mk p x]
  | qy :: xs => agdaIte (FsSandbox.eqStr p qy.proj₁) (AgdaPair.mk p x :: xs) (qy :: putName p x xs)
termination_by structural xs => xs

def removeName {A : Type} (p : String) : List (AgdaPair String A) → List (AgdaPair String A)
  | []       => []
  | qx :: xs => agdaIte (FsSandbox.eqStr p qx.proj₁) xs (qx :: removeName p xs)
termination_by structural xs => xs

def present {A : Type} : AgdaMaybe A → Bool
  | .nothing => false
  | .just _  => true

def eqMaybeBytes : AgdaMaybe Bytes → AgdaMaybe Bytes → Bool
  | .nothing, .nothing => true
  | .just a,  .just b  => FsSandbox.eqBytes a b
  | _,        _        => false

def insertPath (p : String) : List String → List String
  | []      => [p]
  | q :: qs =>
      agdaIte (FsSandbox.eqStr p q)
        (q :: qs)
        (agdaIte (FsSandbox.ltBytes (bytes p) (bytes q))
          (p :: q :: qs)
          (q :: insertPath p qs))
termination_by structural qs => qs

def sortPaths : List String → List String
  | []      => []
  | p :: ps => insertPath p (sortPaths ps)
termination_by structural ps => ps

def choosePaths (f : String → Bool) : List String → List String
  | []      => []
  | p :: ps => agdaIte (f p) (p :: choosePaths f ps) (choosePaths f ps)
termination_by structural ps => ps

def nthCommit : Nat → List PureCommit → AgdaMaybe PureCommit
  | _, []               => .nothing
  | 0, c :: _           => .just c
  | Nat.succ n, _ :: cs => nthCommit n cs
termination_by structural _ cs => cs

def headIndex (r : PureGitRepo) : AgdaMaybe Nat :=
  match lookupName r.headBranch r.branchMap with
  | .nothing => .nothing
  | .just n  => n

def treeAt : AgdaMaybe Nat → List PureCommit → GitTree
  | .nothing, _  => []
  | .just n,  cs =>
      match nthCommit n cs with
      | .nothing => []
      | .just c  => c.treeSnapshot

def headTree (r : PureGitRepo) : GitTree :=
  treeAt (headIndex r) r.commits

def countParents : Nat → AgdaMaybe Nat → List PureCommit → Nat
  | 0,          _,        _  => 0
  | Nat.succ _, .nothing, _  => 0
  | Nat.succ f, .just n,  cs =>
      match nthCommit n cs with
      | .nothing => 0
      | .just c  => Nat.succ (countParents f c.parentIndex cs)
termination_by structural f _ _ => f

def changedPaths (a b : GitTree) : List String :=
  choosePaths
    (fun p => agdaNot (eqMaybeBytes (lookupName p a) (lookupName p b)))
    (sortPaths (agdaAppend (agdaMap AgdaPair.proj₁ a) (agdaMap AgdaPair.proj₁ b)))

def liveBranches : List (AgdaPair String (AgdaMaybe Nat)) → List String
  | []                       => []
  | ⟨_, .nothing⟩ :: bs      => liveBranches bs
  | ⟨p, .just _⟩  :: bs      => p :: liveBranches bs
termination_by structural bs => bs

def projectSummary (r : PureGitRepo) : GitRepoSummary :=
  GitRepoSummary.gitSummary
    r.headBranch
    (countParents (agdaLength r.commits) (headIndex r) r.commits)
    (sortPaths (liveBranches r.branchMap))
    (sortPaths (agdaMap AgdaPair.proj₁ r.tagMap))
    (changedPaths (headTree r) r.index)
    (choosePaths (fun p => agdaNot (eqMaybeBytes (lookupName p r.worktree) (lookupName p r.index)))
      (sortPaths (agdaMap AgdaPair.proj₁ r.index)))
    (choosePaths (fun p => agdaNot (present (lookupName p r.index)))
      (sortPaths (agdaMap AgdaPair.proj₁ r.worktree)))

def initTree : List String → List Bytes → GitTree
  | [], _             => []
  | p :: ps, []       => AgdaPair.mk p [] :: initTree ps []
  | p :: ps, b :: bs  => AgdaPair.mk p b  :: initTree ps bs
termination_by structural ps _ => ps

def initPureGit (cfg : GitConfig) (bs : List Bytes) : PureGitRepo :=
  PureGitRepo.pureGitRepo
    cfg
    (agdaIte (agdaAnd (FsSandbox.all validGitPath cfg.ownedFiles) (FsSandbox.noPathCollisions cfg.ownedFiles))
      (initTree cfg.ownedFiles bs)
      [])
    []
    []
    [AgdaPair.mk cfg.defaultBranch .nothing]
    cfg.defaultBranch
    []

def writeTree (p : String) (b : Bytes) (t : GitTree) : GitTree :=
  agdaIte (agdaAnd (validGitPath p)
                   (FsSandbox.all (fun q => agdaOr (FsSandbox.eqStr p q.proj₁) (agdaNot (FsSandbox.collide p q.proj₁))) t))
    (putName p b t)
    t

def pathSelected : List String → String → Bool
  | [], _      => false
  | q :: qs, p => agdaOr (FsSandbox.eqStr p q) (agdaOr (FsSandbox.isParent q p) (pathSelected qs p))
termination_by structural qs _ => qs

private def chooseEntries (f : String → Bool) : GitTree → GitTree
  | []         => []
  | pb :: rest => agdaIte (f pb.proj₁) (pb :: chooseEntries f rest) (chooseEntries f rest)
termination_by structural rest => rest

def stageSelected (ps : List String) (w i : GitTree) : GitTree :=
  agdaAppend (chooseEntries (fun p => agdaNot (pathSelected ps p)) i)
             (chooseEntries (pathSelected ps) w)

private def hasTreePath (p : String) : GitTree → Bool
  | []         => false
  | qb :: rest => agdaOr (FsSandbox.eqStr p qb.proj₁) (agdaOr (FsSandbox.isParent p qb.proj₁) (hasTreePath p rest))
termination_by structural rest => rest

def allStagePathsExist : List String → GitTree → GitTree → Bool
  | [], _, _      => true
  | p :: ps, w, i => agdaAnd (hasTreePath p (agdaAppend w i)) (allStagePathsExist ps w i)
termination_by structural ps _ _ => ps

def checkoutSafe (old next staged working : GitTree) : Bool :=
  let safe (p : String) : Bool :=
    agdaOr (eqMaybeBytes (lookupName p old) (lookupName p next))
      (agdaOr (eqMaybeBytes (lookupName p staged) (lookupName p next))
        (agdaAnd (eqMaybeBytes (lookupName p staged) (lookupName p old))
                 (eqMaybeBytes (lookupName p working) (lookupName p staged))))
  FsSandbox.all safe
    (sortPaths (agdaAppend (agdaMap AgdaPair.proj₁ old)
                 (agdaAppend (agdaMap AgdaPair.proj₁ next) (agdaMap AgdaPair.proj₁ staged))))

def carryTree (old next staged : GitTree) : GitTree → List String → GitTree
  | working, []      => working
  | working, p :: ps =>
      let keep := agdaOr (eqMaybeBytes (lookupName p old) (lookupName p next))
                         (eqMaybeBytes (lookupName p staged) (lookupName p next))
      let working' :=
        match keep with
        | true  => working
        | false =>
            match lookupName p next with
            | .nothing => removeName p working
            | .just b  => putName p b working
      carryTree old next staged working' ps
termination_by structural _ ps => ps

def checkoutExisting (name : String) (dest : AgdaMaybe Nat) (r : PureGitRepo) : PureGitRepo :=
  let old := headTree r
  let next := treeAt dest r.commits
  let paths := sortPaths (agdaAppend (agdaMap AgdaPair.proj₁ old)
                           (agdaAppend (agdaMap AgdaPair.proj₁ next) (agdaMap AgdaPair.proj₁ r.index)))
  let nextIndex    := carryTree old next r.index r.index paths
  let nextWorktree := carryTree old next r.index r.worktree paths
  agdaIte (agdaAnd (checkoutSafe old next r.index r.worktree)
            (agdaAnd (FsSandbox.noPathCollisions (agdaMap AgdaPair.proj₁ nextIndex))
                     (FsSandbox.noPathCollisions (agdaMap AgdaPair.proj₁ nextWorktree))))
    { r with headBranch := name, index := nextIndex, worktree := nextWorktree }
    r

def newBranchMap (r : PureGitRepo) : List (AgdaPair String (AgdaMaybe Nat)) :=
  match headIndex r with
  | .nothing => removeName r.headBranch r.branchMap
  | .just _  => r.branchMap

def switchBranch (name : String) (create : Bool) (r : PureGitRepo) : PureGitRepo :=
  match validBranch name, lookupName name r.branchMap with
  | false, _         => r
  | true, .just dest => agdaIte create r (checkoutExisting name dest r)
  | true, .nothing   =>
      agdaIte (agdaAnd create (FsSandbox.all (fun p => agdaNot (FsSandbox.collide name p.proj₁)) (newBranchMap r)))
        { r with headBranch := name, branchMap := putName name (headIndex r) (newBranchMap r) }
        r

def createTag (name : String) (r : PureGitRepo) : PureGitRepo :=
  match headIndex r with
  | .nothing => r
  | .just n  =>
      agdaIte (agdaAnd (validRefName name) (FsSandbox.all (fun p => agdaNot (FsSandbox.collide name p.proj₁)) r.tagMap))
        { r with tagMap := putName name n r.tagMap }
        r

def commitTree (msg : String) (offset : Nat) (r : PureGitRepo) : PureGitRepo :=
  let changed := agdaNot (agdaNatEq (agdaLength (changedPaths (headTree r) r.index)) 0)
  agdaIte (agdaAnd (agdaNot (FsSandbox.eqStr msg ""))
            (agdaAnd (FsSandbox.all (fun c => agdaNot (agdaNatEq (agdaCharToNat c) 0)) (agdaToList msg))
                     changed))
    { r with
      commits   := agdaAppend r.commits [PureCommit.pureCommit (headIndex r) r.index msg (agdaAdd r.config.baseEpochSec offset)]
      branchMap := putName r.headBranch (.just (agdaLength r.commits)) r.branchMap }
    r

def stepPureGit : GitStep → PureGitRepo → AgdaPair PureGitRepo (AgdaMaybe GitRepoSummary)
  | .gitWriteFile p bs, r         => AgdaPair.mk { r with worktree := writeTree p bs r.worktree } .nothing
  | .gitRemoveFile p, r           => AgdaPair.mk (agdaIte (validGitPath p) { r with worktree := removeName p r.worktree } r) .nothing
  | .gitStageAll, r               => AgdaPair.mk { r with index := r.worktree } .nothing
  | .gitStagePaths ps, r          =>
      AgdaPair.mk
        (agdaIte (agdaAnd (FsSandbox.all validGitPath ps) (allStagePathsExist ps r.worktree r.index))
          { r with index := stageSelected ps r.worktree r.index }
          r)
        .nothing
  | .gitCommit msg offset, r      => AgdaPair.mk (commitTree msg offset r) .nothing
  | .gitSwitchBranch name create, r => AgdaPair.mk (switchBranch name create r) .nothing
  | .gitCreateTag name, r         => AgdaPair.mk (createTag name r) .nothing
  | .gitStatus, r                 => AgdaPair.mk r (.just (projectSummary r))
  | .gitRunTarget _ _ _ _, r      => AgdaPair.mk r .nothing

def runPureGit : List GitStep → PureGitRepo → PureGitRepo
  | [], r      => r
  | q :: qs, r => runPureGit qs (stepPureGit q r).proj₁
termination_by structural qs _ => qs

def eqStrings : List String → List String → Bool
  | [], []           => true
  | a :: as, b :: bs => agdaAnd (FsSandbox.eqStr a b) (eqStrings as bs)
  | _, _             => false
termination_by structural as _ => as

def eqGitSummary (a b : GitRepoSummary) : Bool :=
  agdaAnd (FsSandbox.eqStr a.currentBranch b.currentBranch)
    (agdaAnd (agdaNatEq a.commitCount b.commitCount)
      (agdaAnd (eqStrings a.branchNames b.branchNames)
        (agdaAnd (eqStrings a.tagNames b.tagNames)
          (agdaAnd (eqStrings a.stagedPaths b.stagedPaths)
            (agdaAnd (eqStrings a.modifiedPaths b.modifiedPaths)
                     (eqStrings a.untrackedPaths b.untrackedPaths))))))

end GitSandbox

/-! ## §7 `Context.Tools.WebOperad` (`Set₀` Scene, Geometry & Draw Stack Core) -/
namespace WebOperad

structure Point : Type where
  pt ::
  px : Int
  py : Int

structure Size : Type where
  size ::
  w : Nat
  h : Nat

structure Rect : Type where
  rect ::
  rx : Int
  ry : Int
  rw : Nat
  rh : Nat

structure QPoint : Type where
  qpt ::
  qx         : Int
  qy         : Int
  qdenMinus1 : Nat

def den (q : QPoint) : Int :=
  Int.ofNat (Nat.succ q.qdenMinus1)

def fromPixel (p : Point) : QPoint :=
  QPoint.qpt p.px p.py 0

def rightEdge (r : Rect) : Int :=
  agdaIntAdd r.rx (Int.ofNat r.rw)

def bottomEdge (r : Rect) : Int :=
  agdaIntAdd r.ry (Int.ofNat r.rh)

def inIntervalB (lo hi x : Int) (k : Nat) : Bool :=
  let scale := Int.ofNat (Nat.succ k)
  agdaAnd (agdaIntLeB (agdaIntMul lo scale) x)
          (agdaNot (agdaIntLeB (agdaIntMul hi scale) x))

def inRectQ (q : QPoint) (r : Rect) : Bool :=
  agdaAnd (inIntervalB r.rx (rightEdge r) q.qx q.qdenMinus1)
          (inIntervalB r.ry (bottomEdge r) q.qy q.qdenMinus1)

def inRect (p : Point) (r : Rect) : Bool :=
  inRectQ (fromPixel p) r

def degenerateB (r : Rect) : Bool :=
  agdaOr (agdaNatEq r.rw 0) (agdaNatEq r.rh 0)

def edgesB (a b : Rect) : Bool :=
  agdaAnd (agdaIntLeB b.rx a.rx)
    (agdaAnd (agdaIntLeB (rightEdge a) (rightEdge b))
      (agdaAnd (agdaIntLeB b.ry a.ry) (agdaIntLeB (bottomEdge a) (bottomEdge b))))

def subRect (a b : Rect) : Bool :=
  agdaOr (degenerateB a) (edgesB a b)

def disjointRect (a b : Rect) : Bool :=
  agdaOr (degenerateB a)
    (agdaOr (degenerateB b)
      (agdaOr (agdaIntLeB (rightEdge a) b.rx)
        (agdaOr (agdaIntLeB (rightEdge b) a.rx)
          (agdaOr (agdaIntLeB (bottomEdge a) b.ry)
                  (agdaIntLeB (bottomEdge b) a.ry)))))

structure Affine2D : Type where
  matrix ::
  num_1 : Nat
  den_1 : Nat
  tx    : Int
  ty    : Int

private def mulPos (a b : Nat) : Nat :=
  agdaAdd b (agdaMul a (Nat.succ b))

def affine (n d : Nat) (x y : Int) : Affine2D :=
  Affine2D.matrix n d (agdaIntMul x (Int.ofNat (Nat.succ d))) (agdaIntMul y (Int.ofNat (Nat.succ d)))

def idAffine : Affine2D :=
  Affine2D.matrix 0 0 (Int.ofNat 0) (Int.ofNat 0)

def compAffine : Affine2D → Affine2D → Affine2D
  | .matrix a b x y, .matrix c d u v =>
      Affine2D.matrix
        (mulPos a c)
        (mulPos b d)
        (agdaIntAdd (agdaIntMul (Int.ofNat (Nat.succ a)) u) (agdaIntMul x (Int.ofNat (Nat.succ d))))
        (agdaIntAdd (agdaIntMul (Int.ofNat (Nat.succ a)) v) (agdaIntMul y (Int.ofNat (Nat.succ d))))

def invAffine : Affine2D → Affine2D
  | .matrix n d x y => Affine2D.matrix d n (agdaIntNeg x) (agdaIntNeg y)

def applyFwd : Affine2D → QPoint → QPoint
  | .matrix n d x y, q =>
      QPoint.qpt
        (agdaIntAdd (agdaIntMul (Int.ofNat (Nat.succ n)) q.qx) (agdaIntMul x (den q)))
        (agdaIntAdd (agdaIntMul (Int.ofNat (Nat.succ n)) q.qy) (agdaIntMul y (den q)))
        (mulPos d q.qdenMinus1)

def applyInv (t : Affine2D) (q : QPoint) : QPoint :=
  applyFwd (invAffine t) q

inductive VisualStyle : Type where
  | fill   : Colour → VisualStyle
  | stroke : Colour → VisualStyle
  | label  : String → Colour → VisualStyle

inductive Scene (A : Type) : Type where
  | empty       : Scene A
  | decorRect   : VisualStyle → Rect → Scene A
  | occludeRect : Colour → Rect → Scene A
  | hitRect     : A → Colour → Rect → Scene A
  | decorLine   : Point → Point → Colour → Scene A
  | transform   : Affine2D → Scene A → Scene A
  | clip        : Rect → Scene A → Scene A
  | over        : Scene A → Scene A → Scene A

def mapScene {A B : Type} (f : A → B) : Scene A → Scene B
  | .empty            => .empty
  | .decorRect v r    => .decorRect v r
  | .occludeRect c r  => .occludeRect c r
  | .hitRect a c r    => .hitRect (f a) c r
  | .decorLine p q c  => .decorLine p q c
  | .transform t s    => .transform t (mapScene f s)
  | .clip r s         => .clip r (mapScene f s)
  | .over front back  => .over (mapScene f front) (mapScene f back)
termination_by structural s => s

def paint {A V : Type} (ink : AgdaMaybe A → Colour → AgdaMaybe V) :
    Scene A → QPoint → AgdaMaybe V → AgdaMaybe V
  | .empty,           _, base => base
  | .decorRect _ _,   _, base => base
  | .decorLine _ _ _, _, base => base
  | .occludeRect c r, q, base => agdaIte (inRectQ q r) (ink .nothing c) base
  | .hitRect a c r,   q, base => agdaIte (inRectQ q r) (ink (.just a) c) base
  | .transform t s,   q, base => paint ink s (applyInv t q) base
  | .clip r s,        q, base =>
      match inRectQ q r with
      | true  => paint ink s q base
      | false => base
  | .over f b,        q, base => paint ink f q (paint ink b q base)
termination_by structural s _ _ => s

def ownerInk {A : Type} (a : AgdaMaybe A) (_ : Colour) : AgdaMaybe A := a
def colourInk {A : Type} (_ : AgdaMaybe A) (c : Colour) : AgdaMaybe Colour := .just c

def paintOwner {A : Type} (s : Scene A) (q : QPoint) : AgdaMaybe A :=
  paint ownerInk s q .nothing

def paintSurfaceColour {A : Type} (s : Scene A) (q : QPoint) : AgdaMaybe Colour :=
  paint (colourInk (A := A)) s q .nothing

inductive HitResult (A : Type) : Type where
  | miss    : HitResult A
  | blocked : HitResult A
  | hit     : A → HitResult A

private def firstHit {A : Type} : HitResult A → (AgdaTop → HitResult A) → HitResult A
  | .miss,    below => below .tt
  | .blocked, _     => .blocked
  | .hit a,   _     => .hit a

def route {A : Type} : Scene A → QPoint → HitResult A
  | .empty,           _ => .miss
  | .decorRect _ _,   _ => .miss
  | .decorLine _ _ _, _ => .miss
  | .occludeRect _ r, q => agdaIte (inRectQ q r) .blocked .miss
  | .hitRect a _ r,   q => agdaIte (inRectQ q r) (.hit a) .miss
  | .transform t s,   q => route s (applyInv t q)
  | .clip r s,        q =>
      match inRectQ q r with
      | true  => route s q
      | false => .miss
  | .over front back, q => firstHit (route front q) (fun _ => route back q)
termination_by structural s _ => s

def resolve {A : Type} : HitResult A → AgdaMaybe A → AgdaMaybe A
  | .miss,    base => base
  | .blocked, _    => .nothing
  | .hit a,   _    => .just a

def hitTest {A : Type} (s : Scene A) (q : QPoint) : AgdaMaybe A :=
  resolve (route s q) .nothing

inductive DrawCmd : Type where
  | cmdSave       : DrawCmd
  | cmdRestore    : DrawCmd
  | cmdTransform  : Affine2D → DrawCmd
  | cmdClip       : Rect → DrawCmd
  | cmdFillRect   : Colour → Rect → DrawCmd
  | cmdStrokeRect : Colour → Rect → DrawCmd
  | cmdText       : String → Colour → Rect → DrawCmd
  | cmdLine       : Point → Point → Colour → DrawCmd

def styleCmd : VisualStyle → Rect → DrawCmd
  | .fill c,    r => .cmdFillRect c r
  | .stroke c,  r => .cmdStrokeRect c r
  | .label t c, r => .cmdText t c r

inductive DrawPass : Type where
  | full     : DrawPass
  | surfaces : DrawPass

def emit {A : Type} : DrawPass → Scene A → List DrawCmd → List DrawCmd
  | _,         .empty,           k => k
  | .full,     .decorRect st r,  k => styleCmd st r :: k
  | .full,     .decorLine p q c, k => .cmdLine p q c :: k
  | .surfaces, .decorRect _ _,   k => k
  | .surfaces, .decorLine _ _ _, k => k
  | _,         .occludeRect c r, k => .cmdFillRect c r :: k
  | _,         .hitRect _ c r,   k => .cmdFillRect c r :: k
  | pass,      .transform t s,   k => .cmdSave :: .cmdTransform t :: emit pass s (.cmdRestore :: k)
  | pass,      .clip r s,        k => .cmdSave :: .cmdClip r :: emit pass s (.cmdRestore :: k)
  | pass,      .over f b,        k => emit pass b (emit pass f k)
termination_by structural _ s _ => s

def compileDraw {A : Type} (s : Scene A) : List DrawCmd :=
  emit .full s []

def compileSurfaceDraw {A : Type} (s : Scene A) : List DrawCmd :=
  emit .surfaces s []

abbrev FrameState : Type := AgdaMaybe QPoint

def mask (r : Rect) : FrameState → FrameState
  | .nothing => .nothing
  | .just q  => agdaIte (inRectQ q r) (.just q) .nothing

def putColour (r : Rect) (c : Colour) : FrameState → AgdaMaybe Colour → AgdaMaybe Colour
  | .nothing, old => old
  | .just q,  old => agdaIte (inRectQ q r) (.just c) old

def run : List DrawCmd → FrameState → List FrameState → AgdaMaybe Colour → AgdaMaybe Colour
  | [],                   _,     _,             pixel => pixel
  | .cmdSave :: cs,       frame, stack,         pixel => run cs frame (frame :: stack) pixel
  | .cmdRestore :: _,     _,     [],            pixel => pixel
  | .cmdRestore :: cs,    _,     saved :: stack, pixel => run cs saved stack pixel
  | .cmdTransform t :: cs, frame, stack,        pixel => run cs (maybeMap (applyInv t) frame) stack pixel
  | .cmdClip r :: cs,     frame, stack,         pixel => run cs (mask r frame) stack pixel
  | .cmdFillRect c r :: cs, frame, stack,       pixel => run cs frame stack (putColour r c frame pixel)
  | _ :: cs,              frame, stack,         pixel => run cs frame stack pixel
termination_by structural cs _ _ _ => cs

def runDrawStack (cs : List DrawCmd) (q : QPoint) : AgdaMaybe Colour :=
  run cs (.just q) [] .nothing

inductive HostInput : Type where
  | hostClick   : Int → Int → HostInput
  | hostPanZoom : Int → Int → Nat → Nat → HostInput
  | hostKey     : Key → HostInput
  | hostResize  : Nat → Nat → HostInput
  | hostTickMs  : Nat → HostInput

private theorem dualRoutePaint {A : Type} :
    ∀ (s : Scene A) (q : QPoint) (base : AgdaMaybe A),
      resolve (route s q) base = paint ownerInk s q base
  | .empty, _, _           => rfl
  | .decorRect _ _, _, _   => rfl
  | .decorLine _ _ _, _, _ => rfl
  | .occludeRect _ r, q, base => by simp only [route, paint]; cases inRectQ q r <;> rfl
  | .hitRect _ _ r, q, base   => by simp only [route, paint]; cases inRectQ q r <;> rfl
  | .transform t s, q, base   => dualRoutePaint s (applyInv t q) base
  | .clip r s, q, base => by
      simp only [route, paint]
      cases inRectQ q r with
      | true  => exact dualRoutePaint s q base
      | false => rfl
  | .over f b, q, base => by
      simp only [route, paint]
      have hf := dualRoutePaint f q (paint ownerInk b q base)
      cases hrf : route f q with
      | miss =>
          rw [hrf] at hf
          simp only [firstHit, resolve] at hf ⊢
          exact Eq.trans (dualRoutePaint b q base) hf
      | blocked =>
          rw [hrf] at hf
          simpa [firstHit, resolve] using hf
      | hit a =>
          rw [hrf] at hf
          simpa [firstHit, resolve] using hf

def visualHitConsistent {A : Type} (s : Scene A) (q : QPoint) :
    AgdaId (hitTest s q) (paintOwner s q) :=
  agdaEqToId (dualRoutePaint s q .nothing)

private def atFrame {A : Type} (s : Scene A) : FrameState → AgdaMaybe Colour → AgdaMaybe Colour
  | .nothing, old => old
  | .just q,  old => paint (colourInk (A := A)) s q old

private theorem machinePrefix {A : Type} :
    ∀ (s : Scene A) (k : List DrawCmd) (f : FrameState) (st : List FrameState) (old : AgdaMaybe Colour),
      run (emit .surfaces s k) f st old = run k f st (atFrame s f old)
  | .empty, _, .nothing, _, _           => rfl
  | .empty, _, .just _, _, _            => rfl
  | .decorRect _ _, _, .nothing, _, _   => rfl
  | .decorRect _ _, _, .just _, _, _    => rfl
  | .decorLine _ _ _, _, .nothing, _, _ => rfl
  | .decorLine _ _ _, _, .just _, _, _  => rfl
  | .occludeRect c r, _, .nothing, _, _ => rfl
  | .occludeRect c r, k, .just q, st, old => by
      simp only [emit, run, putColour, atFrame, paint, colourInk]
  | .hitRect a c r, _, .nothing, _, _   => rfl
  | .hitRect a c r, k, .just q, st, old => by
      simp only [emit, run, putColour, atFrame, paint, colourInk]
  | .transform t s, k, .nothing, st, old =>
      machinePrefix s (.cmdRestore :: k) .nothing (.nothing :: st) old
  | .transform t s, k, .just q, st, old =>
      machinePrefix s (.cmdRestore :: k) (.just (applyInv t q)) (.just q :: st) old
  | .clip r s, k, .nothing, st, old =>
      machinePrefix s (.cmdRestore :: k) .nothing (.nothing :: st) old
  | .clip r s, k, .just q, st, old => by
      simp only [emit, run, mask, atFrame, paint]
      cases inRectQ q r with
      | false => exact machinePrefix s (.cmdRestore :: k) .nothing (.just q :: st) old
      | true  => exact machinePrefix s (.cmdRestore :: k) (.just q) (.just q :: st) old
  | .over f b, k, fr, st, old => by
      simp only [emit]
      rw [machinePrefix b (emit .surfaces f k) fr st old,
          machinePrefix f k fr st (atFrame b fr old)]
      cases fr <;> rfl

def drawMachineSound {A : Type} (s : Scene A) (q : QPoint) :
    AgdaId (runDrawStack (compileSurfaceDraw s) q) (paintSurfaceColour s q) :=
  agdaEqToId (machinePrefix s [] (.just q) [] .nothing)

end WebOperad

/-! ## §8 `Context.World` (`Cap`, `WorldProg`, `SimWorld`, `runWorldPure`) -/
namespace World

open Clock
open FsSandbox (FsNodeKind FsEntryObs VirtualFs)
open NetSandbox (HttpRoute RawStubRule NetTopology)
open GitSandbox (GitConfig GitStep GitRepoSummary PureGitRepo)
open WebOperad (Point Size Rect QPoint Scene DrawCmd HostInput)

inductive Cap : Type where
  | clockCap : Cap
  | envCap   : Cap
  | ttyCap   : Cap
  | fsCap    : Cap
  | netCap   : Cap
  | gitCap   : Cap
  | webCap   : Cap

def eqCap : Cap → Cap → Bool
  | .clockCap, .clockCap => true
  | .envCap,   .envCap   => true
  | .ttyCap,   .ttyCap   => true
  | .fsCap,    .fsCap    => true
  | .netCap,   .netCap   => true
  | .gitCap,   .gitCap   => true
  | .webCap,   .webCap   => true
  | _,         _         => false

inductive CapMem (c : Cap) : List Cap → Type where
  | here  : {cs : List Cap} → CapMem c (c :: cs)
  | there : {d : Cap} → {cs : List Cap} → CapMem c cs → CapMem c (d :: cs)

abbrev CapSub (Δ₁ Δ₂ : List Cap) : Type :=
  {c : Cap} → CapMem c Δ₁ → CapMem c Δ₂

def capSubRefl {Δ : List Cap} : CapSub Δ Δ :=
  fun h => h

def capSubTrans {Δ₁ Δ₂ Δ₃ : List Cap} (f : CapSub Δ₁ Δ₂) (g : CapSub Δ₂ Δ₃) : CapSub Δ₁ Δ₃ :=
  fun h => g (f h)

def capSubNil {Δ : List Cap} : CapSub [] Δ :=
  fun h => nomatch h

def capSubStep {d : Cap} {Δ₁ Δ₂ : List Cap} (sub : CapSub Δ₁ Δ₂) : CapSub Δ₁ (d :: Δ₂) :=
  fun h => .there (sub h)

def capSubCons {c : Cap} {Δ₁ Δ₂ : List Cap} (hc : CapMem c Δ₂) (sub : CapSub Δ₁ Δ₂) : CapSub (c :: Δ₁) Δ₂
  | _, .here    => hc
  | _, .there h => sub h

def hasCap (c : Cap) : List Cap → Bool
  | []      => false
  | d :: ds => agdaOr (eqCap c d) (hasCap c ds)
termination_by structural ds => ds

def findCapIn : (c : Cap) → (Δ : List Cap) → AgdaMaybe (CapMem c Δ)
  | _,         []             => .nothing
  | .clockCap, .clockCap :: _ => .just .here
  | .envCap,   .envCap   :: _ => .just .here
  | .ttyCap,   .ttyCap   :: _ => .just .here
  | .fsCap,    .fsCap    :: _ => .just .here
  | .netCap,   .netCap   :: _ => .just .here
  | .gitCap,   .gitCap   :: _ => .just .here
  | .webCap,   .webCap   :: _ => .just .here
  | c,         _         :: ds =>
      match findCapIn c ds with
      | .just m  => .just (.there m)
      | .nothing => .nothing
termination_by _ ds => ds.length

def PureCaps : List Cap := []

def CliCaps : List Cap :=
  [.clockCap, .envCap, .ttyCap, .fsCap, .netCap]

def AllCaps : List Cap :=
  [.clockCap, .envCap, .ttyCap, .fsCap, .netCap, .gitCap, .webCap]

def clockInCli : CapMem .clockCap CliCaps := .here
def envInCli   : CapMem .envCap   CliCaps := .there .here
def ttyInCli   : CapMem .ttyCap   CliCaps := .there (.there .here)
def fsInCli    : CapMem .fsCap    CliCaps := .there (.there (.there .here))
def netInCli   : CapMem .netCap   CliCaps := .there (.there (.there (.there .here)))

def clockInAll : CapMem .clockCap AllCaps := .here
def envInAll   : CapMem .envCap   AllCaps := .there .here
def ttyInAll   : CapMem .ttyCap   AllCaps := .there (.there .here)
def fsInAll    : CapMem .fsCap    AllCaps := .there (.there (.there .here))
def netInAll   : CapMem .netCap   AllCaps := .there (.there (.there (.there .here)))
def gitInAll   : CapMem .gitCap   AllCaps := .there (.there (.there (.there (.there .here))))
def webInAll   : CapMem .webCap   AllCaps := .there (.there (.there (.there (.there (.there .here)))))

def cliSubAll : CapSub CliCaps AllCaps :=
  capSubCons clockInAll (capSubCons envInAll (capSubCons ttyInAll (capSubCons fsInAll (capSubCons netInAll capSubNil))))

private def isUtf8Cont (x : Nat) : Bool :=
  agdaAnd (agdaNatLe 128 x) (agdaNatLt x 192)

private def mapMaybeChars (c : Char) : AgdaMaybe (List Char) → AgdaMaybe (List Char)
  | .nothing => .nothing
  | .just cs => .just (c :: cs)

def decodeUtf8Chars : List Nat → AgdaMaybe (List Char)
  | []         => .just []
  | b₁ :: rest =>
      if agdaNatLt b₁ 128 then
        mapMaybeChars (agdaCharFromNat b₁) (decodeUtf8Chars rest)
      else if agdaAnd (agdaNatLe 194 b₁) (agdaNatLt b₁ 224) then
        match rest with
        | []        => .nothing
        | b₂ :: rs  =>
            agdaIte (isUtf8Cont b₂)
              (mapMaybeChars (agdaCharFromNat (agdaAdd (agdaMul (agdaSub b₁ 192) 64) (agdaSub b₂ 128))) (decodeUtf8Chars rs))
              .nothing
      else if agdaAnd (agdaNatLe 224 b₁) (agdaNatLt b₁ 240) then
        match rest with
        | b₂ :: b₃ :: rs =>
            let cp := agdaAdd (agdaMul (agdaSub b₁ 224) 4096) (agdaAdd (agdaMul (agdaSub b₂ 128) 64) (agdaSub b₃ 128))
            let surrogate := agdaAnd (agdaNatLe 55296 cp) (agdaNatLt cp 57344)
            agdaIte (agdaAnd (isUtf8Cont b₂) (agdaAnd (isUtf8Cont b₃) (agdaAnd (agdaNatLe 2048 cp) (agdaNot surrogate))))
              (mapMaybeChars (agdaCharFromNat cp) (decodeUtf8Chars rs))
              .nothing
        | _ => .nothing
      else if agdaAnd (agdaNatLe 240 b₁) (agdaNatLt b₁ 245) then
        match rest with
        | b₂ :: b₃ :: b₄ :: rs =>
            let cp := agdaAdd (agdaMul (agdaSub b₁ 240) 262144)
                        (agdaAdd (agdaMul (agdaSub b₂ 128) 4096)
                          (agdaAdd (agdaMul (agdaSub b₃ 128) 64) (agdaSub b₄ 128)))
            agdaIte (agdaAnd (isUtf8Cont b₂) (agdaAnd (isUtf8Cont b₃) (agdaAnd (isUtf8Cont b₄)
                      (agdaAnd (agdaNatLe 65536 cp) (agdaNatLt cp 1114112)))))
              (mapMaybeChars (agdaCharFromNat cp) (decodeUtf8Chars rs))
              .nothing
        | _ => .nothing
      else .nothing
termination_by xs => xs.length

def decodeUtf8 (bs : Bytes) : AgdaMaybe String :=
  match decodeUtf8Chars (agdaMap agdaFinToNat bs) with
  | .nothing => .nothing
  | .just cs => .just (agdaFromList cs)

def decodeUtf8LossyChars : List Nat → List Char
  | []         => []
  | b₁ :: rest =>
      if agdaNatLt b₁ 128 then
        agdaCharFromNat b₁ :: decodeUtf8LossyChars rest
      else if agdaAnd (agdaNatLe 194 b₁) (agdaNatLt b₁ 224) then
        match rest with
        | []       => [agdaCharFromNat 65533]
        | b₂ :: rs =>
            if isUtf8Cont b₂ then
              agdaCharFromNat (agdaAdd (agdaMul (agdaSub b₁ 192) 64) (agdaSub b₂ 128)) :: decodeUtf8LossyChars rs
            else
              agdaCharFromNat 65533 :: decodeUtf8LossyChars (b₂ :: rs)
      else if agdaAnd (agdaNatLe 224 b₁) (agdaNatLt b₁ 240) then
        match rest with
        | []        => [agdaCharFromNat 65533]
        | [b₂]      => agdaCharFromNat 65533 :: decodeUtf8LossyChars [b₂]
        | b₂ :: b₃ :: rs =>
            let cp := agdaAdd (agdaMul (agdaSub b₁ 224) 4096) (agdaAdd (agdaMul (agdaSub b₂ 128) 64) (agdaSub b₃ 128))
            let surrogate := agdaAnd (agdaNatLe 55296 cp) (agdaNatLt cp 57344)
            if agdaAnd (isUtf8Cont b₂) (agdaAnd (isUtf8Cont b₃) (agdaAnd (agdaNatLe 2048 cp) (agdaNot surrogate))) then
              agdaCharFromNat cp :: decodeUtf8LossyChars rs
            else
              agdaCharFromNat 65533 :: decodeUtf8LossyChars (b₂ :: b₃ :: rs)
      else if agdaAnd (agdaNatLe 240 b₁) (agdaNatLt b₁ 245) then
        match rest with
        | []             => [agdaCharFromNat 65533]
        | [b₂]           => agdaCharFromNat 65533 :: decodeUtf8LossyChars [b₂]
        | [b₂, b₃]       => agdaCharFromNat 65533 :: decodeUtf8LossyChars [b₂, b₃]
        | b₂ :: b₃ :: b₄ :: rs =>
            let cp := agdaAdd (agdaMul (agdaSub b₁ 240) 262144)
                        (agdaAdd (agdaMul (agdaSub b₂ 128) 4096)
                          (agdaAdd (agdaMul (agdaSub b₃ 128) 64) (agdaSub b₄ 128)))
            if agdaAnd (isUtf8Cont b₂) (agdaAnd (isUtf8Cont b₃) (agdaAnd (isUtf8Cont b₄)
                 (agdaAnd (agdaNatLe 65536 cp) (agdaNatLt cp 1114112)))) then
              agdaCharFromNat cp :: decodeUtf8LossyChars rs
            else
              agdaCharFromNat 65533 :: decodeUtf8LossyChars (b₂ :: b₃ :: b₄ :: rs)
      else
        agdaCharFromNat 65533 :: decodeUtf8LossyChars rest
termination_by xs => xs.length

def decodeUtf8Lossy (bs : Bytes) : String :=
  agdaFromList (decodeUtf8LossyChars (agdaMap agdaFinToNat bs))

inductive FsError : Type where
  | fsNotFound         : FsError
  | fsIsDirectory      : FsError
  | fsNotDirectory     : FsError
  | fsAlreadyExists    : FsError
  | fsPermissionDenied : FsError
  | fsSymlinkLoop      : FsError
  | fsInvalidPath      : FsError
  | fsIoError          : FsError

def eqFsError : FsError → FsError → Bool
  | .fsNotFound,         .fsNotFound         => true
  | .fsIsDirectory,      .fsIsDirectory      => true
  | .fsNotDirectory,     .fsNotDirectory     => true
  | .fsAlreadyExists,    .fsAlreadyExists    => true
  | .fsPermissionDenied, .fsPermissionDenied => true
  | .fsSymlinkLoop,      .fsSymlinkLoop      => true
  | .fsInvalidPath,      .fsInvalidPath      => true
  | .fsIoError,          .fsIoError          => true
  | _,                   _                   => false

def describeFsError : FsError → String
  | .fsNotFound         => "no such file or directory"
  | .fsIsDirectory      => "is a directory"
  | .fsNotDirectory     => "not a directory"
  | .fsAlreadyExists    => "file exists"
  | .fsPermissionDenied => "permission denied"
  | .fsSymlinkLoop      => "too many levels of symbolic links"
  | .fsInvalidPath      => "invalid path"
  | .fsIoError          => "input/output error"

inductive NetError : Type where
  | netConnRefused     : NetError
  | netTimedOut        : NetError
  | netInvalidEndpoint : NetError
  | netTlsError        : NetError
  | netIoError         : NetError

def eqNetError : NetError → NetError → Bool
  | .netConnRefused,     .netConnRefused     => true
  | .netTimedOut,        .netTimedOut        => true
  | .netInvalidEndpoint, .netInvalidEndpoint => true
  | .netTlsError,        .netTlsError        => true
  | .netIoError,         .netIoError         => true
  | _,                   _                   => false

def describeNetError : NetError → String
  | .netConnRefused     => "connection refused"
  | .netTimedOut        => "operation timed out"
  | .netInvalidEndpoint => "invalid host or port"
  | .netTlsError        => "tls handshake or verification failed"
  | .netIoError         => "network io error"

structure SimProcessEnv : Type where
  simProcessEnv ::
  progName   : String
  args       : List String
  envVars    : List (AgdaPair String String)
  stdinBytes : Bytes

def emptyProcessEnv : SimProcessEnv :=
  SimProcessEnv.simProcessEnv "cand" [] [] []

def cliProcessEnv (prog : String) (as : List String) (inp : Bytes) : SimProcessEnv :=
  SimProcessEnv.simProcessEnv prog as [] inp

structure SimTTY : Type where
  simTTY ::
  ttyStdin  : Bool
  ttyStdout : Bool
  ttyStderr : Bool
  stdoutBuf : Bytes
  stderrBuf : Bytes
  ttyInput  : Bytes
  ttyScreen : Screen

def pipeTTY : SimTTY :=
  SimTTY.simTTY false false false [] [] [] (blankScreen 24 80)

def interactiveTTY (rows cols : Nat) (keys : Bytes) : SimTTY :=
  SimTTY.simTTY true true true [] [] keys (blankScreen rows cols)

structure NetEndpoint : Type where
  netEndpoint ::
  epHost      : String
  epPort      : Nat
  epTls       : Bool
  epCertOk    : Bool
  epLatencyMs : Nat
  epTopology  : NetTopology

structure SimNet : Type where
  simNet ::
  endpoints    : List NetEndpoint
  capturedWire : List (AgdaPair String (AgdaPair Nat Bytes))

def emptyNet : SimNet :=
  SimNet.simNet [] []

def httpStubEndpoint (port : Nat) (routes : List HttpRoute) : NetEndpoint :=
  NetEndpoint.netEndpoint "127.0.0.1" port false true 0 (.httpStubMode routes)

structure CanvasDOM : Type where
  canvasDOM ::
  domViewport : Rect
  domCommands : List DrawCmd
  domTitle    : String
  domEvents   : List HostInput

def emptyCanvasDOM : CanvasDOM :=
  CanvasDOM.canvasDOM (Rect.rect (Int.ofNat 0) (Int.ofNat 0) 800 600) [] "" []

structure SimWorld : Type where
  simWorld ::
  clock : SimClock
  env   : SimProcessEnv
  tty   : SimTTY
  fs    : VirtualFs
  net   : SimNet
  git   : PureGitRepo
  web   : CanvasDOM

def defaultGitRepo : PureGitRepo :=
  GitSandbox.initPureGit (GitConfig.gitConfig .localSandbox "main" "CodeTransport" "ct@local" 0 [] []) []

def defaultSimWorld : SimWorld :=
  SimWorld.simWorld zeroClock emptyProcessEnv pipeTTY (VirtualFs.virtualFs []) emptyNet defaultGitRepo emptyCanvasDOM

def cliSimWorld (prog : String) (as : List String) (stdinB : Bytes) (isTtyOut : Bool) (vfs : VirtualFs) : SimWorld :=
  SimWorld.simWorld
    zeroClock
    (SimProcessEnv.simProcessEnv prog as [] stdinB)
    (SimTTY.simTTY false isTtyOut false [] [] [] (blankScreen 24 80))
    vfs
    emptyNet
    defaultGitRepo
    emptyCanvasDOM

inductive Op : Cap → Type where
  | opNowMono     : Op .clockCap
  | opNowWall     : Op .clockCap
  | opSleepMs     : Nat → Op .clockCap
  | opGetProgName : Op .envCap
  | opGetArgs     : Op .envCap
  | opLookupEnv   : String → Op .envCap
  | opReadStdinAll  : Op .envCap
  | opReadStdinLine : Op .envCap
  | opIsTTYStdin  : Op .ttyCap
  | opIsTTYStdout : Op .ttyCap
  | opIsTTYStderr : Op .ttyCap
  | opTermSize    : Op .ttyCap
  | opWriteStdout : Bytes → Op .ttyCap
  | opWriteStderr : Bytes → Op .ttyCap
  | opReadTTYByte : Op .ttyCap
  | opReadFile    : String → Op .fsCap
  | opWriteFile   : String → Bytes → Op .fsCap
  | opMkdir       : String → Nat → Op .fsCap
  | opSymlink     : String → String → Op .fsCap
  | opUnlink      : String → Op .fsCap
  | opStat        : String → Op .fsCap
  | opTcpExchange : String → Nat → Bytes → Bool → Nat → Op .netCap
  | opTlsExchange : String → Nat → String → Bool → Bytes → Bytes → Nat → Op .netCap
  | opGitStep     : GitStep → Op .gitCap
  | opGitSummary  : Op .gitCap
  | opWebViewport  : Op .webCap
  | opWebSetTitle  : String → Op .webCap
  | opWebDrawScene : Scene Nat → Op .webCap
  | opWebHitTest   : Scene Nat → QPoint → Op .webCap
  | opWebPollInput : Op .webCap

def Ret : {c : Cap} → Op c → Type
  | _, .opNowMono                 => Nat
  | _, .opNowWall                 => Nat
  | _, .opSleepMs _               => AgdaTop
  | _, .opGetProgName             => String
  | _, .opGetArgs                 => List String
  | _, .opLookupEnv _             => AgdaMaybe String
  | _, .opReadStdinAll            => Bytes
  | _, .opReadStdinLine           => AgdaMaybe Bytes
  | _, .opIsTTYStdin              => Bool
  | _, .opIsTTYStdout             => Bool
  | _, .opIsTTYStderr             => Bool
  | _, .opTermSize                => AgdaPair Nat Nat
  | _, .opWriteStdout _           => AgdaTop
  | _, .opWriteStderr _           => AgdaTop
  | _, .opReadTTYByte             => AgdaMaybe Byte
  | _, .opReadFile _              => AgdaSum FsError Bytes
  | _, .opWriteFile _ _           => AgdaSum FsError AgdaTop
  | _, .opMkdir _ _               => AgdaSum FsError AgdaTop
  | _, .opSymlink _ _             => AgdaSum FsError AgdaTop
  | _, .opUnlink _                => AgdaSum FsError AgdaTop
  | _, .opStat _                  => AgdaSum FsError FsNodeKind
  | _, .opTcpExchange _ _ _ _ _   => AgdaSum NetError Bytes
  | _, .opTlsExchange _ _ _ _ _ _ _ => AgdaSum NetError Bytes
  | _, .opGitStep _               => AgdaMaybe GitRepoSummary
  | _, .opGitSummary              => GitRepoSummary
  | _, .opWebViewport             => Rect
  | _, .opWebSetTitle _           => AgdaTop
  | _, .opWebDrawScene _          => AgdaTop
  | _, .opWebHitTest _ _          => AgdaMaybe Nat
  | _, .opWebPollInput            => AgdaMaybe HostInput

inductive WorldProg (Δ : List Cap) (A : Type) : Type where
  | pure : A → WorldProg Δ A
  | step : {c : Cap} → CapMem c Δ → (op : Op c) → (Ret op → WorldProg Δ A) → WorldProg Δ A

def worldBind {Δ : List Cap} {A B : Type} : WorldProg Δ A → (A → WorldProg Δ B) → WorldProg Δ B
  | .pure a,       k => k a
  | .step h op k₁, k => .step h op (fun r => worldBind (k₁ r) k)

def worldSeq {Δ : List Cap} {A B : Type} (m : WorldProg Δ A) (n : WorldProg Δ B) : WorldProg Δ B :=
  worldBind m (fun _ => n)

def mapWorld {Δ : List Cap} {A B : Type} (f : A → B) : WorldProg Δ A → WorldProg Δ B
  | .pure a      => .pure (f a)
  | .step h op k => .step h op (fun r => mapWorld f (k r))

def liftWorld {Δ₁ Δ₂ : List Cap} {A : Type} (sub : CapSub Δ₁ Δ₂) : WorldProg Δ₁ A → WorldProg Δ₂ A
  | .pure a      => .pure a
  | .step h op k => .step (sub h) op (fun r => liftWorld sub (k r))

def nowMonoW {Δ : List Cap} (h : CapMem .clockCap Δ) : WorldProg Δ Nat := .step h .opNowMono .pure
def nowWallW {Δ : List Cap} (h : CapMem .clockCap Δ) : WorldProg Δ Nat := .step h .opNowWall .pure
def sleepW {Δ : List Cap} (h : CapMem .clockCap Δ) (ms : Nat) : WorldProg Δ AgdaTop := .step h (.opSleepMs ms) .pure
def getProgNameW {Δ : List Cap} (h : CapMem .envCap Δ) : WorldProg Δ String := .step h .opGetProgName .pure
def getArgsW {Δ : List Cap} (h : CapMem .envCap Δ) : WorldProg Δ (List String) := .step h .opGetArgs .pure
def lookupEnvW {Δ : List Cap} (h : CapMem .envCap Δ) (k : String) : WorldProg Δ (AgdaMaybe String) := .step h (.opLookupEnv k) .pure
def readStdinAllW {Δ : List Cap} (h : CapMem .envCap Δ) : WorldProg Δ Bytes := .step h .opReadStdinAll .pure
def readStdinLineW {Δ : List Cap} (h : CapMem .envCap Δ) : WorldProg Δ (AgdaMaybe Bytes) := .step h .opReadStdinLine .pure
def isTTYStdinW {Δ : List Cap} (h : CapMem .ttyCap Δ) : WorldProg Δ Bool := .step h .opIsTTYStdin .pure
def isTTYStdoutW {Δ : List Cap} (h : CapMem .ttyCap Δ) : WorldProg Δ Bool := .step h .opIsTTYStdout .pure
def isTTYStderrW {Δ : List Cap} (h : CapMem .ttyCap Δ) : WorldProg Δ Bool := .step h .opIsTTYStderr .pure
def termSizeW {Δ : List Cap} (h : CapMem .ttyCap Δ) : WorldProg Δ (AgdaPair Nat Nat) := .step h .opTermSize .pure
def writeStdoutW {Δ : List Cap} (h : CapMem .ttyCap Δ) (bs : Bytes) : WorldProg Δ AgdaTop := .step h (.opWriteStdout bs) .pure
def writeStdoutStrW {Δ : List Cap} (h : CapMem .ttyCap Δ) (s : String) : WorldProg Δ AgdaTop := writeStdoutW h (bytes s)
def writeStderrW {Δ : List Cap} (h : CapMem .ttyCap Δ) (bs : Bytes) : WorldProg Δ AgdaTop := .step h (.opWriteStderr bs) .pure
def writeStderrStrW {Δ : List Cap} (h : CapMem .ttyCap Δ) (s : String) : WorldProg Δ AgdaTop := writeStderrW h (bytes s)
def readTTYByteW {Δ : List Cap} (h : CapMem .ttyCap Δ) : WorldProg Δ (AgdaMaybe Byte) := .step h .opReadTTYByte .pure
def readFileW {Δ : List Cap} (h : CapMem .fsCap Δ) (p : String) : WorldProg Δ (AgdaSum FsError Bytes) := .step h (.opReadFile p) .pure
def writeFileW {Δ : List Cap} (h : CapMem .fsCap Δ) (p : String) (bs : Bytes) : WorldProg Δ (AgdaSum FsError AgdaTop) := .step h (.opWriteFile p bs) .pure
def mkdirW {Δ : List Cap} (h : CapMem .fsCap Δ) (p : String) (mode : Nat) : WorldProg Δ (AgdaSum FsError AgdaTop) := .step h (.opMkdir p mode) .pure
def symlinkW {Δ : List Cap} (h : CapMem .fsCap Δ) (p dst : String) : WorldProg Δ (AgdaSum FsError AgdaTop) := .step h (.opSymlink p dst) .pure
def unlinkW {Δ : List Cap} (h : CapMem .fsCap Δ) (p : String) : WorldProg Δ (AgdaSum FsError AgdaTop) := .step h (.opUnlink p) .pure
def statW {Δ : List Cap} (h : CapMem .fsCap Δ) (p : String) : WorldProg Δ (AgdaSum FsError FsNodeKind) := .step h (.opStat p) .pure
def tcpExchangeW {Δ : List Cap} (h : CapMem .netCap Δ) (host : String) (port : Nat) (req : Bytes) (hc : Bool) (tms : Nat) :
    WorldProg Δ (AgdaSum NetError Bytes) := .step h (.opTcpExchange host port req hc tms) .pure
def tlsExchangeW {Δ : List Cap} (h : CapMem .netCap Δ) (host : String) (port : Nat) (sni : String) (ins : Bool) (tun req : Bytes) (tms : Nat) :
    WorldProg Δ (AgdaSum NetError Bytes) := .step h (.opTlsExchange host port sni ins tun req tms) .pure
def gitStepW {Δ : List Cap} (h : CapMem .gitCap Δ) (s : GitStep) : WorldProg Δ (AgdaMaybe GitRepoSummary) := .step h (.opGitStep s) .pure
def gitSummaryW {Δ : List Cap} (h : CapMem .gitCap Δ) : WorldProg Δ GitRepoSummary := .step h .opGitSummary .pure
def webViewportW {Δ : List Cap} (h : CapMem .webCap Δ) : WorldProg Δ Rect := .step h .opWebViewport .pure
def webSetTitleW {Δ : List Cap} (h : CapMem .webCap Δ) (t : String) : WorldProg Δ AgdaTop := .step h (.opWebSetTitle t) .pure
def webDrawSceneW {Δ : List Cap} (h : CapMem .webCap Δ) (sc : Scene Nat) : WorldProg Δ AgdaTop := .step h (.opWebDrawScene sc) .pure
def webHitTestW {Δ : List Cap} (h : CapMem .webCap Δ) (sc : Scene Nat) (q : QPoint) : WorldProg Δ (AgdaMaybe Nat) := .step h (.opWebHitTest sc q) .pure
def webPollInputW {Δ : List Cap} (h : CapMem .webCap Δ) : WorldProg Δ (AgdaMaybe HostInput) := .step h .opWebPollInput .pure

abbrev ExitCode : Type := Nat
abbrev CliApp (Δ : List Cap) : Type := WorldProg Δ ExitCode

inductive EventPayload : Cap → Type where
  | evTickMs   : Nat → EventPayload .clockCap
  | evSignal   : TermSignal → EventPayload .envCap
  | evKey      : Key → EventPayload .ttyCap
  | evResize   : Nat → Nat → EventPayload .ttyCap
  | evTTYBytes : Bytes → EventPayload .ttyCap
  | evFsWatch  : String → EventPayload .fsCap
  | evNetConn  : Bytes → EventPayload .netCap
  | evGitHook  : String → EventPayload .gitCap
  | evWebInput : HostInput → EventPayload .webCap

structure Event (Δ : List Cap) : Type where
  mkEvent ::
  {evCap    : Cap}
  evHasCap  : CapMem evCap Δ
  evPayload : EventPayload evCap

def liftEvent {Δ₁ Δ₂ : List Cap} (sub : CapSub Δ₁ Δ₂) (e : Event Δ₁) : Event Δ₂ :=
  Event.mkEvent (sub e.evHasCap) e.evPayload

structure ReactiveApp (Δ : List Cap) (S : Type) : Type where
  reactiveApp ::
  init   : WorldProg Δ S
  onStep : Event Δ → S → WorldProg Δ (AgdaSum S ExitCode)

def lookupEnvVar (k : String) : List (AgdaPair String String) → AgdaMaybe String
  | []       => .nothing
  | nv :: xs => agdaIte (FsSandbox.eqStr k nv.proj₁) (.just nv.proj₂) (lookupEnvVar k xs)
termination_by structural xs => xs

private def scanLineBytes : Byte → Bytes → AgdaPair Bytes Bytes
  | cur, []      => AgdaPair.mk [cur] []
  | cur, x :: xs =>
      agdaIte (agdaNatEq (agdaFinToNat cur) 10)
        (AgdaPair.mk [cur] (x :: xs))
        (let r := scanLineBytes x xs
         AgdaPair.mk (cur :: r.proj₁) r.proj₂)
termination_by structural _ xs => xs

def takeLineBytes : Bytes → AgdaPair (AgdaMaybe Bytes) Bytes
  | []      => AgdaPair.mk .nothing []
  | b :: bs =>
      let r := scanLineBytes b bs
      AgdaPair.mk (.just r.proj₁) r.proj₂

def popByte : Bytes → AgdaPair (AgdaMaybe Byte) Bytes
  | []      => AgdaPair.mk .nothing []
  | b :: bs => AgdaPair.mk (.just b) bs

def hasDotSlashPrefix : List Char → Bool
  | c₁ :: c₂ :: _ => agdaAnd (agdaNatEq (agdaCharToNat c₁) 46) (agdaNatEq (agdaCharToNat c₂) 47)
  | _             => false

def stripDotSlashChars : List Char → List Char
  | c₁ :: c₂ :: cs =>
      if agdaAnd (agdaNatEq (agdaCharToNat c₁) 46) (agdaNatEq (agdaCharToNat c₂) 47) then
        stripDotSlashChars cs
      else
        c₁ :: c₂ :: cs
  | cs => cs
termination_by cs => cs.length

def normalizeRelPath (p : String) : String :=
  agdaIte (hasDotSlashPrefix (agdaToList p))
    (agdaFromList (stripDotSlashChars (agdaToList p)))
    p

def readVirtualFileFuel : Nat → String → VirtualFs → AgdaSum FsError Bytes
  | 0, _, _            => .inj₁ .fsSymlinkLoop
  | Nat.succ fuel, rawP, v =>
      let p := normalizeRelPath rawP
      agdaIte (FsSandbox.eqStr p ".")
        (.inj₁ .fsIsDirectory)
        (agdaIte (agdaNot (FsSandbox.validRelPath p))
          (.inj₁ .fsInvalidPath)
          (match FsSandbox.lookupEntry p v.fsEntries with
           | .nothing => .inj₁ .fsNotFound
           | .just e  =>
               agdaIte (FsSandbox.eqKind e.entryKind .regularNode)
                 (.inj₂ e.entryBytes)
                 (agdaIte (FsSandbox.eqKind e.entryKind .dirNode)
                   (.inj₁ .fsIsDirectory)
                   (readVirtualFileFuel fuel (NetSandbox.wireText e.entryBytes) v))))
termination_by structural f _ _ => f

def readVirtualFile : String → VirtualFs → AgdaSum FsError Bytes :=
  readVirtualFileFuel 8

def writeVirtualFileFuel : Nat → String → Bytes → VirtualFs → AgdaPair (AgdaSum FsError AgdaTop) VirtualFs
  | 0, _, _, v            => AgdaPair.mk (.inj₁ .fsSymlinkLoop) v
  | Nat.succ fuel, rawP, bs, v =>
      let p := normalizeRelPath rawP
      agdaIte (FsSandbox.eqStr p ".")
        (AgdaPair.mk (.inj₁ .fsIsDirectory) v)
        (agdaIte (agdaNot (FsSandbox.validRelPath p))
          (AgdaPair.mk (.inj₁ .fsInvalidPath) v)
          (match FsSandbox.ensureParents true (FsSandbox.parentPaths p) v with
           | .nothing => AgdaPair.mk (.inj₁ .fsNotDirectory) v
           | .just v₁ =>
               match FsSandbox.lookupEntry p v₁.fsEntries with
               | .nothing =>
                   AgdaPair.mk (.inj₂ .tt) (FsSandbox.putEntry (FsEntryObs.fsEntry p .regularNode 420 bs) v₁)
               | .just e =>
                   agdaIte (FsSandbox.eqKind e.entryKind .regularNode)
                     (AgdaPair.mk (.inj₂ .tt) (FsSandbox.putEntry (FsEntryObs.fsEntry p .regularNode e.entryMode bs) v₁))
                     (agdaIte (FsSandbox.eqKind e.entryKind .dirNode)
                       (AgdaPair.mk (.inj₁ .fsIsDirectory) v)
                       (writeVirtualFileFuel fuel (NetSandbox.wireText e.entryBytes) bs v))))
termination_by structural f _ _ _ => f

def writeVirtualFile : String → Bytes → VirtualFs → AgdaPair (AgdaSum FsError AgdaTop) VirtualFs :=
  writeVirtualFileFuel 8

def writeVirtualFileSigma (p : String) (bs : Bytes) (v : VirtualFs) : AgdaProd (AgdaSum FsError AgdaTop) VirtualFs :=
  let r := writeVirtualFile p bs v
  AgdaSigma.mk r.proj₁ r.proj₂

def mkdirVirtual (rawP : String) (mode : Nat) (v : VirtualFs) : AgdaPair (AgdaSum FsError AgdaTop) VirtualFs :=
  let p := normalizeRelPath rawP
  agdaIte (FsSandbox.eqStr p ".")
    (AgdaPair.mk (.inj₂ .tt) v)
    (agdaIte (agdaNot (FsSandbox.validRelPath p))
      (AgdaPair.mk (.inj₁ .fsInvalidPath) v)
      (match FsSandbox.ensureParents true (FsSandbox.parentPaths p) v with
       | .nothing => AgdaPair.mk (.inj₁ .fsNotDirectory) v
       | .just v₁ =>
           match FsSandbox.lookupEntry p v₁.fsEntries with
           | .nothing =>
               AgdaPair.mk (.inj₂ .tt) (FsSandbox.putEntry (FsEntryObs.fsEntry p .dirNode (FsSandbox.maskMode mode) []) v₁)
           | .just e =>
               agdaIte (FsSandbox.eqKind e.entryKind .dirNode)
                 (AgdaPair.mk (.inj₂ .tt) (FsSandbox.putEntry (FsEntryObs.fsEntry p .dirNode (FsSandbox.maskMode mode) []) v₁))
                 (AgdaPair.mk (.inj₁ .fsAlreadyExists) v)))

def symlinkVirtual (rawP dest : String) (v : VirtualFs) : AgdaPair (AgdaSum FsError AgdaTop) VirtualFs :=
  let p     := normalizeRelPath rawP
  let okDst := agdaAnd (agdaNot (FsSandbox.eqStr dest ""))
                       (FsSandbox.all (fun c => agdaNot (agdaNatEq (agdaCharToNat c) 0)) (agdaToList dest))
  agdaIte (agdaOr (agdaNot okDst) (agdaOr (FsSandbox.eqStr p ".") (agdaNot (FsSandbox.validRelPath p))))
    (AgdaPair.mk (.inj₁ .fsInvalidPath) v)
    (match FsSandbox.ensureParents true (FsSandbox.parentPaths p) v with
     | .nothing => AgdaPair.mk (.inj₁ .fsNotDirectory) v
     | .just v₁ =>
         match FsSandbox.lookupEntry p v₁.fsEntries with
         | .nothing =>
             AgdaPair.mk (.inj₂ .tt) (FsSandbox.putEntry (FsEntryObs.fsEntry p .symlinkNode 511 (bytes dest)) v₁)
         | .just e =>
             agdaIte (FsSandbox.eqKind e.entryKind .dirNode)
               (AgdaPair.mk (.inj₁ .fsIsDirectory) v)
               (AgdaPair.mk (.inj₂ .tt) (FsSandbox.putEntry (FsEntryObs.fsEntry p .symlinkNode 511 (bytes dest)) v₁)))

def unlinkVirtual (rawP : String) (v : VirtualFs) : AgdaPair (AgdaSum FsError AgdaTop) VirtualFs :=
  let p := normalizeRelPath rawP
  agdaIte (agdaOr (FsSandbox.eqStr p ".") (agdaNot (FsSandbox.validRelPath p)))
    (AgdaPair.mk (.inj₁ .fsInvalidPath) v)
    (match FsSandbox.ensureParents false (FsSandbox.parentPaths p) v with
     | .nothing => AgdaPair.mk (.inj₁ .fsNotDirectory) v
     | .just _  =>
         match FsSandbox.lookupEntry p v.fsEntries with
         | .nothing => AgdaPair.mk (.inj₁ .fsNotFound) v
         | .just _  =>
             agdaIte (FsSandbox.all (fun x => agdaNot (FsSandbox.isParent p x.entryPath)) v.fsEntries)
               (AgdaPair.mk (.inj₂ .tt) (VirtualFs.virtualFs (FsSandbox.removeEntry p v.fsEntries)))
               (AgdaPair.mk (.inj₁ .fsIsDirectory) v))

def statVirtual (rawP : String) (v : VirtualFs) : AgdaSum FsError FsNodeKind :=
  let p := normalizeRelPath rawP
  agdaIte (FsSandbox.eqStr p ".")
    (.inj₂ .dirNode)
    (agdaIte (agdaNot (FsSandbox.validRelPath p))
      (.inj₁ .fsInvalidPath)
      (match FsSandbox.lookupEntry p v.fsEntries with
       | .nothing => .inj₁ .fsNotFound
       | .just e  => .inj₂ e.entryKind))

def isLoopbackHost (h : String) : Bool :=
  agdaOr (FsSandbox.eqStr h "127.0.0.1")
    (agdaOr (FsSandbox.eqStr h "localhost")
      (agdaOr (FsSandbox.eqStr h "[::1]") (FsSandbox.eqStr h "::1")))

def hostMatches (epH reqH : String) : Bool :=
  agdaOr (FsSandbox.eqStr epH "*")
    (agdaOr (FsSandbox.eqStr epH reqH) (agdaAnd (isLoopbackHost epH) (isLoopbackHost reqH)))

def findEndpoint (wantTls : Bool) (host : String) (port : Nat) : List NetEndpoint → AgdaMaybe NetEndpoint
  | []        => .nothing
  | ep :: eps =>
      let sameTls := agdaIte wantTls ep.epTls (agdaNot ep.epTls)
      agdaIte (agdaAnd sameTls (agdaAnd (agdaNatEq ep.epPort port) (hostMatches ep.epHost host)))
        (.just ep)
        (findEndpoint wantTls host port eps)
termination_by structural eps => eps

def stubDelayOf : NetTopology → Nat
  | .httpDelayedStubMode d _ => d
  | .tcpDelayedStubMode  d _ => d
  | _                        => 0

def evalNetExchange (wantTls insecure : Bool) (host : String) (port : Nat)
    (req : Bytes) (timeoutMs : Nat) (netSt : SimNet) : AgdaPair (AgdaSum NetError Bytes) SimNet :=
  let badHostPort := agdaOr (FsSandbox.eqStr host "") (agdaOr (agdaNatEq port 0) (agdaNatLt 65535 port))
  agdaIte badHostPort
    (AgdaPair.mk (.inj₁ .netInvalidEndpoint) netSt)
    (match findEndpoint wantTls host port netSt.endpoints with
     | .nothing => AgdaPair.mk (.inj₁ .netConnRefused) netSt
     | .just ep =>
         let effTimeout := agdaIte (agdaNatEq timeoutMs 0) 30000 timeoutMs
         let totalDelay := agdaAdd ep.epLatencyMs (stubDelayOf ep.epTopology)
         let certBad    := agdaAnd wantTls (agdaAnd (agdaNot insecure) (agdaNot ep.epCertOk))
         let timedOut   := agdaAnd (agdaNatLt 0 totalDelay) (agdaNatLe effTimeout totalDelay)
         let recorded   := { netSt with capturedWire := agdaAppend netSt.capturedWire [AgdaPair.mk host (AgdaPair.mk port req)] }
         agdaIte certBad
           (AgdaPair.mk (.inj₁ .netTlsError) recorded)
           (agdaIte timedOut
             (AgdaPair.mk (.inj₁ .netTimedOut) recorded)
             (AgdaPair.mk (.inj₂ (NetSandbox.stubReply ep.epTopology req)) recorded)))

def popWebEvent : List HostInput → AgdaPair (AgdaMaybe HostInput) (List HostInput)
  | []      => AgdaPair.mk .nothing []
  | e :: es => AgdaPair.mk (.just e) es

-- Exact top-level single-field record updates matching `Context.World.stepWorldPure`:
-- Every cross-tool Frame Law holds definitionally (`rfl` / `.refl`)!
def stepWorldPure {c : Cap} : (op : Op c) → SimWorld → AgdaPair (Ret op) SimWorld
  | .opNowMono, w =>
      let r := readMonoMs w.clock
      AgdaPair.mk r.proj₁ { w with clock := r.proj₂ }
  | .opNowWall, w =>
      let r := readWallMs w.clock
      AgdaPair.mk r.proj₁ { w with clock := r.proj₂ }
  | .opSleepMs ms, w =>
      AgdaPair.mk .tt { w with clock := sleepClockMs ms w.clock }
  | .opGetProgName, w =>
      AgdaPair.mk w.env.progName w
  | .opGetArgs, w =>
      AgdaPair.mk w.env.args w
  | .opLookupEnv k, w =>
      AgdaPair.mk (lookupEnvVar k w.env.envVars) w
  | .opReadStdinAll, w =>
      AgdaPair.mk w.env.stdinBytes { w with env := { w.env with stdinBytes := [] } }
  | .opReadStdinLine, w =>
      let r := takeLineBytes w.env.stdinBytes
      AgdaPair.mk r.proj₁ { w with env := { w.env with stdinBytes := r.proj₂ } }
  | .opIsTTYStdin, w  => AgdaPair.mk w.tty.ttyStdin w
  | .opIsTTYStdout, w => AgdaPair.mk w.tty.ttyStdout w
  | .opIsTTYStderr, w => AgdaPair.mk w.tty.ttyStderr w
  | .opTermSize, w =>
      AgdaPair.mk (AgdaPair.mk w.tty.ttyScreen.height w.tty.ttyScreen.width) w
  | .opWriteStdout bs, w =>
      let t := w.tty
      let nextScr := agdaIte t.ttyStdout (stepANSI t.ttyScreen bs) t.ttyScreen
      AgdaPair.mk .tt { w with tty := { t with stdoutBuf := agdaAppend t.stdoutBuf bs, ttyScreen := nextScr } }
  | .opWriteStderr bs, w =>
      let t := w.tty
      let nextScr := agdaIte t.ttyStderr (stepANSI t.ttyScreen bs) t.ttyScreen
      AgdaPair.mk .tt { w with tty := { t with stderrBuf := agdaAppend t.stderrBuf bs, ttyScreen := nextScr } }
  | .opReadTTYByte, w =>
      let t := w.tty
      let r := popByte t.ttyInput
      AgdaPair.mk r.proj₁ { w with tty := { t with ttyInput := r.proj₂ } }
  | .opReadFile p, w =>
      AgdaPair.mk (readVirtualFile p w.fs) w
  | .opWriteFile p bs, w =>
      let r := writeVirtualFile p bs w.fs
      AgdaPair.mk r.proj₁ { w with fs := r.proj₂ }
  | .opMkdir p mode, w =>
      let r := mkdirVirtual p mode w.fs
      AgdaPair.mk r.proj₁ { w with fs := r.proj₂ }
  | .opSymlink p dst, w =>
      let r := symlinkVirtual p dst w.fs
      AgdaPair.mk r.proj₁ { w with fs := r.proj₂ }
  | .opUnlink p, w =>
      let r := unlinkVirtual p w.fs
      AgdaPair.mk r.proj₁ { w with fs := r.proj₂ }
  | .opStat p, w =>
      AgdaPair.mk (statVirtual p w.fs) w
  | .opTcpExchange host port req _ tms, w =>
      let r := evalNetExchange false false host port req tms w.net
      AgdaPair.mk r.proj₁ { w with net := r.proj₂ }
  | .opTlsExchange host port _ ins _ req tms, w =>
      let r := evalNetExchange true ins host port req tms w.net
      AgdaPair.mk r.proj₁ { w with net := r.proj₂ }
  | .opGitStep gs, w =>
      let r := GitSandbox.stepPureGit gs w.git
      AgdaPair.mk r.proj₂ { w with git := r.proj₁ }
  | .opGitSummary, w =>
      AgdaPair.mk (GitSandbox.projectSummary w.git) w
  | .opWebViewport, w =>
      AgdaPair.mk w.web.domViewport w
  | .opWebSetTitle title, w =>
      AgdaPair.mk .tt { w with web := { w.web with domTitle := title } }
  | .opWebDrawScene sc, w =>
      AgdaPair.mk .tt { w with web := { w.web with domCommands := WebOperad.compileDraw sc } }
  | .opWebHitTest sc q, w =>
      AgdaPair.mk (WebOperad.hitTest sc q) w
  | .opWebPollInput, w =>
      let r := popWebEvent w.web.domEvents
      AgdaPair.mk r.proj₁ { w with web := { w.web with domEvents := r.proj₂ } }

def stepWorldPureSigma {c : Cap} (op : Op c) (w : SimWorld) : AgdaProd (Ret op) SimWorld :=
  let r := stepWorldPure op w
  AgdaSigma.mk r.proj₁ r.proj₂

def runWorldPure {Δ : List Cap} {A : Type} : WorldProg Δ A → SimWorld → AgdaPair A SimWorld
  | .pure a,      w => AgdaPair.mk a w
  | .step _ op k, w =>
      let rw := stepWorldPure op w
      runWorldPure (k rw.proj₁) rw.proj₂

def runWorldPureSigma {Δ : List Cap} {A : Type} (m : WorldProg Δ A) (w : SimWorld) : AgdaProd A SimWorld :=
  let r := runWorldPure m w
  AgdaSigma.mk r.proj₁ r.proj₂

def runCliPure {Δ : List Cap} : CliApp Δ → SimWorld → AgdaPair ExitCode SimWorld :=
  runWorldPure

def runCliPureSigma {Δ : List Cap} : CliApp Δ → SimWorld → AgdaProd ExitCode SimWorld :=
  runWorldPureSigma

def runReactiveSteps {Δ : List Cap} {S : Type} (app : ReactiveApp Δ S) :
    S → List (Event Δ) → SimWorld → AgdaPair (AgdaSum S ExitCode) SimWorld
  | s, [],      w => AgdaPair.mk (.inj₁ s) w
  | s, e :: es, w =>
      let r := runWorldPure (app.onStep e s) w
      match r.proj₁ with
      | .inj₁ s'   => runReactiveSteps app s' es r.proj₂
      | .inj₂ code => AgdaPair.mk (.inj₂ code) r.proj₂
termination_by structural _ evs _ => evs

def runReactiveStepsSigma {Δ : List Cap} {S : Type} (app : ReactiveApp Δ S)
    (s : S) (evs : List (Event Δ)) (w : SimWorld) : AgdaProd (AgdaSum S ExitCode) SimWorld :=
  let r := runReactiveSteps app s evs w
  AgdaSigma.mk r.proj₁ r.proj₂

def runReactivePure {Δ : List Cap} {S : Type} (app : ReactiveApp Δ S)
    (evs : List (Event Δ)) (w : SimWorld) : AgdaPair (AgdaSum S ExitCode) SimWorld :=
  let initRes := runWorldPure app.init w
  runReactiveSteps app initRes.proj₁ evs initRes.proj₂

def runReactivePureSigma {Δ : List Cap} {S : Type} (app : ReactiveApp Δ S)
    (evs : List (Event Δ)) (w : SimWorld) : AgdaProd (AgdaSum S ExitCode) SimWorld :=
  let r := runReactivePure app evs w
  AgdaSigma.mk r.proj₁ r.proj₂

end World

/-! ## §9 `Context.Tools.FsLaws` -/
namespace FsLaws

open FsSandbox
open World

theorem natEqB_refl : ∀ (n : Nat), agdaNatEq n n = true
  | 0          => rfl
  | Nat.succ n => natEqB_refl n

theorem natEqB_to_eq : ∀ (m n : Nat), agdaNatEq m n = true → m = n
  | 0, 0, _                   => rfl
  | Nat.succ m, Nat.succ n, h => congrArg Nat.succ (natEqB_to_eq m n h)
  | 0, Nat.succ _, h          => nomatch h
  | Nat.succ _, 0, h          => nomatch h

def eqbRefl (n : Nat) : AgdaId (agdaNatEq n n) true :=
  agdaEqToId (natEqB_refl n)

def eqbToId (m n : Nat) (h : AgdaId (agdaNatEq m n) true) : AgdaId m n :=
  agdaEqToId (natEqB_to_eq m n (agdaIdToEq h))

def neqToEqbFalse (m n : Nat) (neq : AgdaId m n → AgdaBot) : AgdaId (agdaNatEq m n) false :=
  match h : agdaNatEq m n with
  | false => .refl
  | true  => botElim (neq (agdaEqToId (natEqB_to_eq m n h)))

private theorem finToNat_inj : ∀ {k : Nat} (a b : AgdaFin k), agdaFinToNat a = agdaFinToNat b → a = b
  | Nat.succ _, .zero, .zero, _       => rfl
  | Nat.succ _, .suc a, .suc b, h     => congrArg AgdaFin.suc (finToNat_inj a b (Nat.succ.inj h))
  | Nat.succ _, .zero, .suc _, h      => nomatch h
  | Nat.succ _, .suc _, .zero, h      => nomatch h

theorem eqBytes_refl_eq : ∀ (bs : Bytes), eqBytes bs bs = true
  | []      => rfl
  | b :: bs => by simp only [eqBytes, natEqB_refl, agdaAnd, eqBytes_refl_eq bs]

private theorem list_cons_congr {α : Type} {x y : α} {xs ys : List α} (hx : x = y) (hxs : xs = ys) :
    x :: xs = y :: ys := hx ▸ hxs ▸ rfl

theorem eqBytes_to_eq : ∀ (xs ys : Bytes), eqBytes xs ys = true → xs = ys
  | [], [], _             => rfl
  | x :: xs, y :: ys, h   => by
      simp only [eqBytes, agdaAnd] at h
      cases hx : agdaNatEq (agdaFinToNat x) (agdaFinToNat y) with
      | false => rw [hx] at h; nomatch h
      | true  =>
          rw [hx] at h
          exact list_cons_congr (finToNat_inj x y (natEqB_to_eq _ _ hx)) (eqBytes_to_eq xs ys h)
  | [], _ :: _, h         => nomatch h
  | _ :: _, [], h         => nomatch h

def eqBytesRefl (bs : Bytes) : AgdaId (eqBytes bs bs) true :=
  agdaEqToId (eqBytes_refl_eq bs)

def eqBytesToId (xs ys : Bytes) (h : AgdaId (eqBytes xs ys) true) : AgdaId xs ys :=
  agdaEqToId (eqBytes_to_eq xs ys (agdaIdToEq h))

theorem eqChars_refl_eq : ∀ (cs : List Char), eqChars cs cs = true
  | []      => rfl
  | c :: cs => by simp only [eqChars, natEqB_refl, agdaAnd, eqChars_refl_eq cs]

private theorem charToNat_inj (x y : Char) (h : agdaCharToNat x = agdaCharToNat y) : x = y := by
  have h1 : Char.ofNat x.toNat = Char.ofNat y.toNat := congrArg Char.ofNat h
  simpa [Char.ofNat_toNat] using h1

theorem eqChars_to_eq : ∀ (xs ys : List Char), eqChars xs ys = true → xs = ys
  | [], [], _           => rfl
  | x :: xs, y :: ys, h => by
      simp only [eqChars, agdaAnd] at h
      cases hx : agdaNatEq (agdaCharToNat x) (agdaCharToNat y) with
      | false => rw [hx] at h; nomatch h
      | true  =>
          rw [hx] at h
          exact list_cons_congr (charToNat_inj x y (natEqB_to_eq _ _ hx)) (eqChars_to_eq xs ys h)
  | [], _ :: _, h       => nomatch h
  | _ :: _, [], h       => nomatch h

def eqCharsRefl (cs : List Char) : AgdaId (eqChars cs cs) true :=
  agdaEqToId (eqChars_refl_eq cs)

def eqCharsToId (xs ys : List Char) (h : AgdaId (eqChars xs ys) true) : AgdaId xs ys :=
  agdaEqToId (eqChars_to_eq xs ys (agdaIdToEq h))

theorem eqStr_refl_eq (s : String) : eqStr s s = true :=
  eqChars_refl_eq (agdaToList s)

theorem eqStr_to_eq (a b : String) (h : eqStr a b = true) : a = b :=
  agdaToList_inj a b (eqChars_to_eq (agdaToList a) (agdaToList b) h)

def eqStrRefl (s : String) : AgdaId (eqStr s s) true :=
  agdaEqToId (eqStr_refl_eq s)

def eqStrToId (a b : String) (h : AgdaId (eqStr a b) true) : AgdaId a b :=
  agdaEqToId (eqStr_to_eq a b (agdaIdToEq h))

def neqStrToEqStrFalse (a b : String) (neq : AgdaId a b → AgdaBot) : AgdaId (eqStr a b) false :=
  match h : eqStr a b with
  | false => .refl
  | true  => botElim (neq (agdaEqToId (eqStr_to_eq a b h)))

def neqToEqStrFalse : (a b : String) → (AgdaId a b → AgdaBot) → AgdaId (eqStr a b) false :=
  neqStrToEqStrFalse

def eqStrSym (a b : String) : AgdaId (eqStr a b) (eqStr b a) :=
  agdaEqToId (by
    cases hab : eqStr a b with
    | true =>
        have e := eqStr_to_eq a b hab
        subst e
        exact Eq.symm (eqStr_refl_eq a)
    | false =>
        cases hba : eqStr b a with
        | false => rfl
        | true =>
            have e := eqStr_to_eq b a hba
            subst e
            rw [eqStr_refl_eq b] at hab
            nomatch hab)

theorem lookup_insert_same_eq (e : FsEntryObs) :
    ∀ (es : List FsEntryObs), lookupEntry e.entryPath (insertEntry e es) = .just e
  | []      => by simp only [insertEntry, lookupEntry, eqStr_refl_eq, agdaIte]
  | x :: xs => by
      simp only [insertEntry]
      cases hex : eqStr e.entryPath x.entryPath with
      | true  => simp only [agdaIte, lookupEntry, eqStr_refl_eq]
      | false =>
          simp only [agdaIte]
          cases ltBytes (bytes e.entryPath) (bytes x.entryPath) with
          | true  => simp only [agdaIte, lookupEntry, eqStr_refl_eq]
          | false => simp only [agdaIte, lookupEntry, hex, lookup_insert_same_eq e xs]

def lookupInsertSame (e : FsEntryObs) (es : List FsEntryObs) :
    AgdaId (lookupEntry e.entryPath (insertEntry e es)) (.just e) :=
  agdaEqToId (lookup_insert_same_eq e es)

theorem lookup_insert_other_eq (q : String) (e : FsEntryObs) (neq : q ≠ e.entryPath) :
    ∀ (es : List FsEntryObs), lookupEntry q (insertEntry e es) = lookupEntry q es
  | [] => by
      simp only [insertEntry, lookupEntry]
      cases hqe : eqStr q e.entryPath with
      | false => rfl
      | true  => exact absurd (eqStr_to_eq q e.entryPath hqe) neq
  | x :: xs => by
      have hqeFalse : eqStr q e.entryPath = false := by
        cases h : eqStr q e.entryPath with
        | false => rfl
        | true  => exact absurd (eqStr_to_eq q e.entryPath h) neq
      simp only [insertEntry]
      cases hex : eqStr e.entryPath x.entryPath with
      | true =>
          have ex := eqStr_to_eq e.entryPath x.entryPath hex
          simp only [agdaIte, lookupEntry, hqeFalse, ← ex]
      | false =>
          simp only [agdaIte]
          cases ltBytes (bytes e.entryPath) (bytes x.entryPath) with
          | true  => simp only [agdaIte, lookupEntry, hqeFalse]
          | false =>
              simp only [agdaIte, lookupEntry]
              cases eqStr q x.entryPath with
              | true  => rfl
              | false => exact lookup_insert_other_eq q e neq xs

def lookupInsertOther (q : String) (e : FsEntryObs) (es : List FsEntryObs)
    (neq : AgdaId q e.entryPath → AgdaBot) :
    AgdaId (lookupEntry q (insertEntry e es)) (lookupEntry q es) :=
  agdaEqToId (lookup_insert_other_eq q e (fun h => nomatch neq (agdaEqToId h)) es)

def insertInsertSame (e₁ e₂ : FsEntryObs) (es : List FsEntryObs)
    (pEq : AgdaId e₁.entryPath e₂.entryPath) :
    AgdaId (insertEntry e₂ (insertEntry e₁ es)) (insertEntry e₂ es) :=
  agdaEqToId (by
    have hp := agdaIdToEq pEq
    induction es with
    | nil =>
        simp only [insertEntry, ← hp, eqStr_refl_eq, agdaIte]
    | cons x xs ih =>
        simp only [insertEntry, ← hp]
        cases h1x : eqStr e₁.entryPath x.entryPath with
        | true  => simp only [agdaIte, insertEntry, ← hp, eqStr_refl_eq]
        | false =>
            simp only [agdaIte]
            cases hlt : ltBytes (bytes e₁.entryPath) (bytes x.entryPath) with
            | true  => simp only [agdaIte, insertEntry, ← hp, eqStr_refl_eq]
            | false => simp only [agdaIte, insertEntry, ← hp, h1x, hlt, ih])

def noSlashOrNull : List Char → Bool
  | []      => true
  | c :: cs =>
      agdaAnd (agdaNot (agdaNatEq (agdaCharToNat c) 47))
        (agdaAnd (agdaNot (agdaNatEq (agdaCharToNat c) 0)) (noSlashOrNull cs))
termination_by structural cs => cs

def ValidFlatFile (p : String) : Bool :=
  agdaAnd (validSegChars (agdaToList p)) (noSlashOrNull (agdaToList p))

def isWritableEntry : AgdaMaybe FsEntryObs → Bool
  | .nothing => true
  | .just e  => eqKind e.entryKind .regularNode

def CanWriteReg (p : String) (v : VirtualFs) : Bool :=
  isWritableEntry (lookupEntry p v.fsEntries)

def isNotSymlinkEntry : AgdaMaybe FsEntryObs → Bool
  | .nothing => true
  | .just e  => agdaNot (eqKind e.entryKind .symlinkNode)

def NotSymlink (p : String) (v : VirtualFs) : Bool :=
  isNotSymlinkEntry (lookupEntry p v.fsEntries)

private theorem agdaReverse_cons {A : Type} (x : A) (acc : List A) :
    agdaReverse (x :: acc) = agdaAppend (agdaReverse acc) [x] := by
  have step : ∀ (ys zs : List A), agdaFoldl (fun a z => z :: a) zs ys = agdaAppend (agdaReverse ys) zs := by
    intro ys
    induction ys with
    | nil => intro zs; rfl
    | cons y ys ih =>
        intro zs
        simp only [agdaFoldl, agdaReverse]
        rw [ih (y :: zs), ih [y]]
        exact Eq.symm (TermLaws.agdaAppend_assoc (agdaFoldl (fun a z => z :: a) [] ys) [y] zs)
  simpa [agdaReverse, agdaFoldl] using step acc [x]

private theorem noSlash_split : ∀ (acc cs : List Char),
    noSlashOrNull cs = true → splitSegmentChars acc cs = [agdaAppend (agdaReverse acc) cs]
  | acc, [], _ => by simp only [splitSegmentChars, TermLaws.agdaAppend_nil_r]
  | acc, c :: cs, ok => by
      simp only [noSlashOrNull, agdaAnd, agdaNot] at ok
      cases h47 : agdaNatEq (agdaCharToNat c) 47 with
      | true  => rw [h47] at ok; nomatch ok
      | false =>
          rw [h47] at ok
          cases h0 : agdaNatEq (agdaCharToNat c) 0 with
          | true  => rw [h0] at ok; nomatch ok
          | false =>
              rw [h0] at ok
              simp only [splitSegmentChars, h47, agdaIte]
              rw [noSlash_split (c :: acc) cs ok, agdaReverse_cons c acc,
                  TermLaws.agdaAppend_assoc (agdaReverse acc) [c] cs]
              rfl

theorem and_left {a b : Bool} (h : agdaAnd a b = true) : a = true := by
  cases a <;> cases b <;> cases h <;> rfl

theorem and_right {a b : Bool} (h : agdaAnd a b = true) : b = true := by
  cases a <;> cases b <;> cases h <;> rfl

theorem not_true_eq_false {a : Bool} (h : agdaNot a = true) : a = false := by
  cases a <;> cases h <;> rfl

private theorem noSlash_noNull : ∀ (cs : List Char),
    noSlashOrNull cs = true → FsSandbox.all (fun c => agdaNot (agdaNatEq (agdaCharToNat c) 0)) cs = true
  | [], _ => rfl
  | c :: cs, ok => by
      have h0 : agdaNot (agdaNatEq (agdaCharToNat c) 0) = true := and_left (and_right ok)
      have hcs : noSlashOrNull cs = true := and_right (and_right ok)
      simp only [FsSandbox.all, h0, noSlash_noNull cs hcs, agdaAnd]

private theorem noSlash_noDotSlash : ∀ (cs : List Char),
    noSlashOrNull cs = true → hasDotSlashPrefix cs = false
  | [], _             => rfl
  | [_], _            => rfl
  | c₁ :: c₂ :: cs, ok => by
      have h2 : agdaNatEq (agdaCharToNat c₂) 47 = false :=
        not_true_eq_false (and_left (and_right (and_right ok)))
      simp only [hasDotSlashPrefix, h2]
      cases agdaNatEq (agdaCharToNat c₁) 46 <;> rfl

private theorem flat_props (p : String) (ok : ValidFlatFile p = true) :
    normalizeRelPath p = p ∧ eqStr p "." = false ∧ validRelPath p = true ∧ parentPaths p = [] := by
  have hseg : validSegChars (agdaToList p) = true := and_left ok
  have hns  : noSlashOrNull (agdaToList p) = true := and_right ok
  have hnorm : normalizeRelPath p = p := by
    simp only [normalizeRelPath, noSlash_noDotSlash (agdaToList p) hns, agdaIte]
  have hdot : eqStr p "." = false := by
    have hd : agdaNot (eqChars (agdaToList p) ['.']) = true := and_left (and_right hseg)
    have hdotList : agdaToList "." = ['.'] := rfl
    simpa [eqStr, hdotList] using not_true_eq_false hd
  have hrel : validRelPath p = true := by
    simp only [validRelPath, noSlash_split [] (agdaToList p) hns, agdaReverse, agdaFoldl, agdaAppend,
               FsSandbox.all, hseg, noSlash_noNull (agdaToList p) hns, agdaAnd]
  have hpar : parentPaths p = [] := by
    simp only [parentPaths, segments, noSlash_split [] (agdaToList p) hns, agdaMap, parentsFrom]
  exact ⟨hnorm, hdot, hrel, hpar⟩

def readAfterWriteSame (p : String) (bs : Bytes) (v : VirtualFs)
    (flatOk : AgdaId (ValidFlatFile p) true)
    (canOk : AgdaId (CanWriteReg p v) true) :
    AgdaId (readVirtualFile p (writeVirtualFile p bs v).proj₂) (.inj₂ bs) :=
  agdaEqToId (by
    obtain ⟨hnorm, hdot, hrel, hpar⟩ := flat_props p (agdaIdToEq flatOk)
    have hcan := agdaIdToEq canOk
    simp only [CanWriteReg] at hcan
    simp only [writeVirtualFile, writeVirtualFileFuel, hnorm, hdot, hrel, hpar, agdaNot, agdaIte, ensureParents]
    cases hl : lookupEntry p v.fsEntries with
    | nothing =>
        simp only [readVirtualFile, readVirtualFileFuel, hnorm, hdot, hrel, agdaNot, agdaIte,
                   putEntry, lookup_insert_same_eq (FsEntryObs.fsEntry p .regularNode 420 bs) v.fsEntries, eqKind]
    | just e =>
        rw [hl] at hcan
        simp only [isWritableEntry] at hcan
        cases hk : e.entryKind with
        | regularNode =>
            simp only [hk, eqKind, agdaIte, readVirtualFile, readVirtualFileFuel, hnorm, hdot, hrel, agdaNot,
                       putEntry, lookup_insert_same_eq (FsEntryObs.fsEntry p .regularNode e.entryMode bs) v.fsEntries]
        | dirNode     => rw [hk] at hcan; nomatch hcan
        | symlinkNode => rw [hk] at hcan; nomatch hcan)

def readAfterWriteOther (p q : String) (bs : Bytes) (v : VirtualFs)
    (flatP : AgdaId (ValidFlatFile p) true)
    (flatQ : AgdaId (ValidFlatFile q) true)
    (qNeqP : AgdaId q p → AgdaBot)
    (canP : AgdaId (CanWriteReg p v) true)
    (noSymQ : AgdaId (NotSymlink q v) true) :
    AgdaId (readVirtualFile q (writeVirtualFile p bs v).proj₂) (readVirtualFile q v) :=
  agdaEqToId (by
    obtain ⟨hnormP, hdotP, hrelP, hparP⟩ := flat_props p (agdaIdToEq flatP)
    obtain ⟨hnormQ, hdotQ, hrelQ, _⟩     := flat_props q (agdaIdToEq flatQ)
    have hneq : q ≠ p := fun h => nomatch qNeqP (agdaEqToId h)
    have hcan := agdaIdToEq canP
    have hns  := agdaIdToEq noSymQ
    simp only [CanWriteReg] at hcan
    simp only [NotSymlink] at hns
    simp only [writeVirtualFile, writeVirtualFileFuel, hnormP, hdotP, hrelP, hparP, agdaNot, agdaIte, ensureParents]
    cases hlp : lookupEntry p v.fsEntries with
    | nothing =>
        simp only [readVirtualFile, readVirtualFileFuel, hnormQ, hdotQ, hrelQ, agdaNot, agdaIte,
                   putEntry, lookup_insert_other_eq q (FsEntryObs.fsEntry p .regularNode 420 bs) hneq v.fsEntries]
        cases hlq : lookupEntry q v.fsEntries with
        | nothing => rfl
        | just eqE =>
            rw [hlq] at hns
            simp only [isNotSymlinkEntry] at hns
            cases hkq : eqE.entryKind with
            | regularNode => simp only [hkq]; rfl
            | dirNode     => simp only [hkq]; rfl
            | symlinkNode => rw [hkq] at hns; nomatch hns
    | just ep =>
        rw [hlp] at hcan
        simp only [isWritableEntry] at hcan
        cases hkp : ep.entryKind with
        | regularNode =>
            simp only [hkp, eqKind, agdaIte, readVirtualFile, readVirtualFileFuel, hnormQ, hdotQ, hrelQ, agdaNot,
                       putEntry, lookup_insert_other_eq q (FsEntryObs.fsEntry p .regularNode ep.entryMode bs) hneq v.fsEntries]
            cases hlq : lookupEntry q v.fsEntries with
            | nothing => rfl
            | just eqE =>
                rw [hlq] at hns
                simp only [isNotSymlinkEntry] at hns
                cases hkq : eqE.entryKind with
                | regularNode => simp only [hkq]
                | dirNode     => simp only [hkq]
                | symlinkNode => rw [hkq] at hns; nomatch hns
        | dirNode     => rw [hkp] at hcan; nomatch hcan
        | symlinkNode => rw [hkp] at hcan; nomatch hcan)

end FsLaws

/-! ## §10 `Context.Tools.GitLaws` -/
namespace GitLaws

open GitSandbox

def lookupNamePutNameSame {A : Type} (p : String) (v : A) (m : List (AgdaPair String A)) :
    AgdaId (lookupName p (putName p v m)) (.just v) :=
  agdaEqToId (by
    induction m with
    | nil => simp only [putName, lookupName, FsLaws.eqStr_refl_eq, agdaIte]
    | cons qy xs ih =>
        simp only [putName]
        cases hpq : FsSandbox.eqStr p qy.proj₁ with
        | true  => simp only [agdaIte, lookupName, FsLaws.eqStr_refl_eq]
        | false => simp only [agdaIte, lookupName, hpq, ih])

def lookupNamePutNameOther {A : Type} (p q : String) (v : A) (m : List (AgdaPair String A))
    (pNeqQ : AgdaId p q → AgdaBot) :
    AgdaId (lookupName p (putName q v m)) (lookupName p m) :=
  agdaEqToId (by
    have hneq : p ≠ q := fun h => nomatch pNeqQ (agdaEqToId h)
    have hpqF : FsSandbox.eqStr p q = false := by
      cases h : FsSandbox.eqStr p q with
      | false => rfl
      | true  => exact absurd (FsLaws.eqStr_to_eq p q h) hneq
    induction m with
    | nil => simp only [putName, lookupName, hpqF, agdaIte]
    | cons ky xs ih =>
        simp only [putName]
        cases hqk : FsSandbox.eqStr q ky.proj₁ with
        | true =>
            have qk := FsLaws.eqStr_to_eq q ky.proj₁ hqk
            simp only [agdaIte, lookupName, hpqF, ← qk]
        | false =>
            simp only [agdaIte, lookupName]
            cases FsSandbox.eqStr p ky.proj₁ with
            | true  => rfl
            | false => exact ih)

def stepPureGitStatusId (r : PureGitRepo) :
    AgdaId (stepPureGit .gitStatus r) (AgdaPair.mk r (.just (projectSummary r))) := .refl

def stepPureGitStageAllIndex (r : PureGitRepo) :
    AgdaId (stepPureGit .gitStageAll r).proj₁.index r.worktree := .refl

def stepPureGitStageAllHead (r : PureGitRepo) :
    AgdaId (stepPureGit .gitStageAll r).proj₁.headBranch r.headBranch := .refl

def eqMaybeBytesRefl : (mb : AgdaMaybe Bytes) → AgdaId (eqMaybeBytes mb mb) true
  | .nothing  => .refl
  | .just bs  => FsLaws.eqBytesRefl bs

def choosePathsAllFalse (f : String → Bool) :
    (ps : List String) → ((p : String) → AgdaId (f p) false) → AgdaId (choosePaths f ps) []
  | [], _      => .refl
  | p :: ps, h =>
      agdaEqToId (by
        have hp := agdaIdToEq (h p)
        have ih := agdaIdToEq (choosePathsAllFalse f ps h)
        simp only [choosePaths, hp, agdaIte, ih])

def stepPureGitStageAllModifiedEmpty (r : PureGitRepo) :
    AgdaId (projectSummary (stepPureGit .gitStageAll r).proj₁).modifiedPaths [] :=
  choosePathsAllFalse
    (fun p => agdaNot (eqMaybeBytes (lookupName p r.worktree) (lookupName p r.worktree)))
    (sortPaths (agdaMap AgdaPair.proj₁ r.worktree))
    (fun p => idCong agdaNot (eqMaybeBytesRefl (lookupName p r.worktree)))

def runPureGitNil (r : PureGitRepo) : AgdaId (runPureGit [] r) r := .refl

def runPureGitAppend : (xs ys : List GitStep) → (r : PureGitRepo) →
    AgdaId (runPureGit (agdaAppend xs ys) r) (runPureGit ys (runPureGit xs r))
  | [], _, _      => .refl
  | x :: xs, ys, r => runPureGitAppend xs ys (stepPureGit x r).proj₁

end GitLaws

/-! ## §11 `Context.Tools.NetLaws` -/
namespace NetLaws

open NetSandbox

def prefixBytesRefl : (bs : Bytes) → AgdaId (prefixBytes bs bs) true
  | []      => .refl
  | b :: bs =>
      agdaEqToId (by
        have ih : FsSandbox.prefixBytes bs bs = true := agdaIdToEq (prefixBytesRefl bs)
        simp only [prefixBytes, FsSandbox.prefixBytes, FsLaws.natEqB_refl, agdaAnd, ih])

def prefixBytesAppend : (xs ys : Bytes) → AgdaId (prefixBytes xs (agdaAppend xs ys)) true
  | [], _       => .refl
  | x :: xs, ys =>
      agdaEqToId (by
        have ih : FsSandbox.prefixBytes xs (agdaAppend xs ys) = true := agdaIdToEq (prefixBytesAppend xs ys)
        simp only [agdaAppend, prefixBytes, FsSandbox.prefixBytes, FsLaws.natEqB_refl, agdaAnd, ih])

def dropLengthAppend : (xs ys : Bytes) → AgdaId (agdaDrop (agdaLength xs) (agdaAppend xs ys)) ys
  | [], _       => .refl
  | _ :: xs, ys => dropLengthAppend xs ys

def NoCR : Bytes → Bool :=
  FsSandbox.all (fun b => agdaNot (agdaNatEq 13 (agdaFinToNat b)))

def NoCRLF : Bytes → Bool :=
  FsSandbox.all (fun b => agdaAnd (agdaNot (agdaNatEq 13 (agdaFinToNat b))) (agdaNot (agdaNatEq 10 (agdaFinToNat b))))

def TokenByte (b : Byte) : Bool :=
  agdaAnd (agdaNot (isAsciiSpaceByte b))
    (agdaAnd (agdaNot (agdaNatEq 13 (agdaFinToNat b))) (agdaNot (agdaNatEq 10 (agdaFinToNat b))))

def NonEmptyBytes : Bytes → Bool
  | []     => false
  | _ :: _ => true

def ValidTokenBytes (bs : Bytes) : Bool :=
  agdaAnd (NonEmptyBytes bs) (FsSandbox.all TokenByte bs)

def ValidHttpToken (s : String) : Bool :=
  ValidTokenBytes (bytes s)

private theorem allToken_noCR : ∀ (bs : Bytes), FsSandbox.all TokenByte bs = true → NoCR bs = true
  | [], _ => rfl
  | b :: bs, ok => by
      have htb : TokenByte b = true := FsLaws.and_left ok
      have hbs : FsSandbox.all TokenByte bs = true := FsLaws.and_right ok
      have h13 : agdaNot (agdaNatEq 13 (agdaFinToNat b)) = true := FsLaws.and_left (FsLaws.and_right htb)
      simp only [NoCR, FsSandbox.all, h13, agdaAnd]
      exact allToken_noCR bs hbs

private theorem noCR_append : ∀ (xs ys : Bytes), NoCR xs = true → NoCR ys = true → NoCR (agdaAppend xs ys) = true
  | [], _, _, okY => okY
  | x :: xs, ys, okX, okY => by
      have hx  : agdaNot (agdaNatEq 13 (agdaFinToNat x)) = true := FsLaws.and_left okX
      have hxs : NoCR xs = true := FsLaws.and_right okX
      simp only [NoCR, agdaAppend, FsSandbox.all, hx, agdaAnd]
      exact noCR_append xs ys hxs okY

private theorem digitChar_token : ∀ (n : Nat), TokenByte (byte (agdaCharToNat (digitChar n))) = true
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

private theorem decCharsFuel_allToken : ∀ (fuel n : Nat) (acc : List Char),
    FsSandbox.all TokenByte (agdaMap (fun c => byte (agdaCharToNat c)) acc) = true →
    FsSandbox.all TokenByte (agdaMap (fun c => byte (agdaCharToNat c)) (decCharsFuel fuel n acc)) = true
  | 0, _, _, okAcc => okAcc
  | Nat.succ f, n, acc, okAcc => by
      simp only [decCharsFuel]
      cases agdaNatLt n 10 with
      | true  => simp only [agdaIte, agdaMap, FsSandbox.all, digitChar_token, agdaAnd, okAcc]
      | false =>
          simp only [agdaIte]
          apply decCharsFuel_allToken f (agdaDiv n 10) (digitChar (agdaModNat n 10) :: acc)
          simp only [agdaMap, FsSandbox.all, digitChar_token, agdaAnd, okAcc]

private theorem decCharsFuel_nonEmpty_acc : ∀ (fuel n : Nat) (c : Char) (cs : List Char),
    NonEmptyBytes (agdaMap (fun ch => byte (agdaCharToNat ch)) (decCharsFuel fuel n (c :: cs))) = true
  | 0, _, _, _ => rfl
  | Nat.succ f, n, c, cs => by
      simp only [decCharsFuel]
      cases agdaNatLt n 10 with
      | true  => rfl
      | false => exact decCharsFuel_nonEmpty_acc f (agdaDiv n 10) (digitChar (agdaModNat n 10)) (c :: cs)

private theorem decBytes_validToken (n : Nat) : ValidTokenBytes (decBytes n) = true := by
  have hne : NonEmptyBytes (decBytes n) = true := by
    simp only [decBytes, decCharsFuel]
    cases agdaNatLt n 10 with
    | true  => rfl
    | false => exact decCharsFuel_nonEmpty_acc n (agdaDiv n 10) (digitChar (agdaModNat n 10)) []
  have hat : FsSandbox.all TokenByte (decBytes n) = true :=
    decCharsFuel_allToken (Nat.succ n) n [] rfl
  simp only [ValidTokenBytes, hne, hat, agdaAnd]

private theorem decBytes_noCR (n : Nat) : NoCR (decBytes n) = true :=
  allToken_noCR (decBytes n) (decCharsFuel_allToken (Nat.succ n) n [] rfl)

private theorem split_crlf_go : ∀ (acc pre rest : Bytes),
    NoCR pre = true →
    splitMarkGo (bytes "\r\n") acc (agdaAppend pre (agdaAppend (bytes "\r\n") rest)) =
    .just (AgdaPair.mk (agdaAppend (agdaReverse acc) pre) rest)
  | acc, [], rest, _ => by
      simp only [agdaAppend]
      rw [show bytes "\r\n" = [byte 13, byte 10] from rfl]
      simp only [agdaAppend, splitMarkGo, prefixBytes, FsSandbox.prefixBytes,
                 agdaFinToNat, byte, agdaFinFromNatMod, agdaFinOfBounded, agdaNatEq, agdaAnd, agdaIte,
                 agdaLength, agdaDrop, TermLaws.agdaAppend_nil_r]
  | acc, b :: bs, rest, ok => by
      have h13 : agdaNatEq 13 (agdaFinToNat b) = false := FsLaws.not_true_eq_false (FsLaws.and_left ok)
      have hbs : NoCR bs = true := FsLaws.and_right ok
      have hpfx : prefixBytes (bytes "\r\n") (b :: agdaAppend bs (agdaAppend (bytes "\r\n") rest)) = false := by
        rw [show bytes "\r\n" = [byte 13, byte 10] from rfl]
        have h13' : agdaNatEq (agdaFinToNat (byte 13)) (agdaFinToNat b) = false := h13
        simp only [prefixBytes, FsSandbox.prefixBytes, h13', agdaAnd]
      simp only [agdaAppend, splitMarkGo, hpfx, agdaIte]
      rw [split_crlf_go (b :: acc) bs rest hbs, FsLaws.agdaReverse_cons b acc,
          TermLaws.agdaAppend_assoc (agdaReverse acc) [b] bs]
      rfl

private theorem skip_crlf2_simple : ∀ (acc pre tailB : Bytes),
    NoCR pre = true →
    splitMarkGo (bytes "\r\n\r\n") acc (agdaAppend pre tailB) =
    splitMarkGo (bytes "\r\n\r\n") (agdaFoldl (fun a x => x :: a) acc pre) tailB
  | _, [], _, _ => rfl
  | acc, b :: bs, tailB, ok => by
      have h13 : agdaNatEq 13 (agdaFinToNat b) = false := FsLaws.not_true_eq_false (FsLaws.and_left ok)
      have hbs : NoCR bs = true := FsLaws.and_right ok
      have hpfx : prefixBytes (bytes "\r\n\r\n") (b :: agdaAppend bs tailB) = false := by
        rw [show bytes "\r\n\r\n" = [byte 13, byte 10, byte 13, byte 10] from rfl]
        have h13' : agdaNatEq (agdaFinToNat (byte 13)) (agdaFinToNat b) = false := h13
        simp only [prefixBytes, FsSandbox.prefixBytes, h13', agdaAnd]
      simp only [agdaAppend, splitMarkGo, hpfx, agdaIte, agdaFoldl]
      exact skip_crlf2_simple (b :: acc) bs tailB hbs

private theorem words_token_step : ∀ (acc tok rest : Bytes),
    FsSandbox.all TokenByte tok = true →
    wordsBytesGo acc (agdaAppend tok (byte 32 :: rest)) =
    wordsBytesGo (agdaFoldl (fun a x => x :: a) acc tok) (byte 32 :: rest)
  | _, [], _, _ => rfl
  | acc, b :: bs, rest, ok => by
      have hsp : isAsciiSpaceByte b = false := FsLaws.not_true_eq_false (FsLaws.and_left (FsLaws.and_left ok))
      have hbs : FsSandbox.all TokenByte bs = true := FsLaws.and_right ok
      simp only [agdaAppend, wordsBytesGo, hsp, agdaIte, agdaFoldl]
      exact words_token_step (b :: acc) bs rest hbs

private theorem agdaReverse_involutive {A : Type} (xs : List A) : agdaReverse (agdaReverse xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [FsLaws.agdaReverse_cons x xs]
      have hApp : ∀ (as bs : List A), agdaReverse (agdaAppend as bs) = agdaAppend (agdaReverse bs) (agdaReverse as) := by
        intro as
        induction as with
        | nil => intro bs; simp only [agdaAppend, agdaReverse, agdaFoldl, TermLaws.agdaAppend_nil_r]
        | cons a as iha =>
            intro bs
            simp only [agdaAppend]
            rw [FsLaws.agdaReverse_cons a (agdaAppend as bs), iha bs,
                FsLaws.agdaReverse_cons a as, TermLaws.agdaAppend_assoc]
      rw [hApp (agdaReverse xs) [x], ih]
      rfl

private theorem nonEmptyFold : ∀ (x : Byte) (a xs : Bytes),
    agdaFoldl (fun acc y => y :: acc) (x :: a) xs ≠ []
  | _, _, [], h      => nomatch h
  | _, a, y :: ys, h => nonEmptyFold y (_ :: a) ys h

private theorem words_nonempty_token (tok rest : Bytes) (ok : ValidTokenBytes tok = true) :
    wordsBytesGo [] (agdaAppend tok (byte 32 :: rest)) = tok :: wordsBytesGo [] rest := by
  cases tok with
  | nil => simp [ValidTokenBytes, NonEmptyBytes, agdaAnd] at ok
  | cons b bs =>
      have hall : FsSandbox.all TokenByte (b :: bs) = true := FsLaws.and_right ok
      have hsp  : isAsciiSpaceByte b = false := FsLaws.not_true_eq_false (FsLaws.and_left (FsLaws.and_left hall))
      have hbs  : FsSandbox.all TokenByte bs = true := FsLaws.and_right hall
      simp only [agdaAppend, wordsBytesGo, hsp, agdaIte]
      rw [words_token_step [b] bs rest hbs]
      generalize hzs : agdaFoldl (fun a x => x :: a) [b] bs = zs
      cases zs with
      | nil => exact absurd hzs (nonEmptyFold b [] bs)
      | cons h t =>
          have hsp32 : isAsciiSpaceByte (byte 32) = true := rfl
          simp only [wordsBytesGo, hsp32, agdaIte, flushWordAcc, agdaAppend]
          congr 1
          rw [← hzs]
          exact agdaReverse_involutive (b :: bs)

def parseHttpReqEncodeRoundtrip (method path : String) (body : Bytes)
    (okM : AgdaId (ValidHttpToken method) true)
    (okP : AgdaId (ValidHttpToken path) true) :
    AgdaId (parseHttpReq (encodeHttpReq method path [] body))
           (.just (HttpReqView.httpReqView (wireText (bytes method)) (wireText (bytes path)) body)) :=
  agdaEqToId (by
    have hm := agdaIdToEq okM
    have hp := agdaIdToEq okP
    have hmTok : FsSandbox.all TokenByte (bytes method) = true := FsLaws.and_right hm
    have hpTok : FsSandbox.all TokenByte (bytes path) = true := FsLaws.and_right hp
    let line := agdaAppend (bytes method) (agdaAppend (bytes " ") (agdaAppend (bytes path) (bytes " HTTP/1.1")))
    let hdrTail := agdaAppend (bytes "\r\nHost: 127.0.0.1\r\nConnection: close\r\nContent-Length: ")
                     (agdaAppend (decBytes (agdaLength body)) (agdaAppend (bytes "\r\n\r\n") body))
    have noCrLine : NoCR line = true :=
      noCR_append (bytes method) _ (allToken_noCR _ hmTok)
        (noCR_append (bytes " ") _ rfl
          (noCR_append (bytes path) (bytes " HTTP/1.1") (allToken_noCR _ hpTok) rfl))
    have reassoc : encodeHttpReq method path [] body = agdaAppend line hdrTail := by
      simp only [encodeHttpReq, autoHeaderBytes, hasHeader, agdaIte, headerBytes, line, hdrTail]
      simp only [TermLaws.agdaAppend_assoc]
      rfl
    have s1 : splitMark (bytes "\r\n") (encodeHttpReq method path [] body) =
        .just (AgdaPair.mk line (agdaAppend (bytes "Host: 127.0.0.1\r\nConnection: close\r\nContent-Length: ")
                                  (agdaAppend (decBytes (agdaLength body)) (agdaAppend (bytes "\r\n\r\n") body)))) := by
      rw [reassoc]
      exact split_crlf_go [] line _ noCrLine
    have s2 : ∃ hdr, splitMark (bytes "\r\n\r\n") (encodeHttpReq method path [] body) =
        .just (AgdaPair.mk hdr body) := by
      rw [reassoc]
      simp only [splitMark]
      rw [skip_crlf2_simple [] line hdrTail noCrLine]
      have stepLit : ∀ (a : Bytes),
          splitMarkGo (bytes "\r\n\r\n") a hdrTail =
          splitMarkGo (bytes "\r\n\r\n")
            (agdaFoldl (fun acc' x => x :: acc') a (bytes "\r\nHost: 127.0.0.1\r\nConnection: close\r\nContent-Length: "))
            (agdaAppend (decBytes (agdaLength body)) (agdaAppend (bytes "\r\n\r\n") body)) := fun _ => rfl
      rw [stepLit, skip_crlf2_simple _ (decBytes (agdaLength body)) (agdaAppend (bytes "\r\n\r\n") body) (decBytes_noCR _)]
      exact ⟨_, rfl⟩
    obtain ⟨hdr, hs2⟩ := s2
    have wLine : wordsBytes line = [bytes method, bytes path, bytes "HTTP/1.1"] := by
      simp only [wordsBytes, line]
      have hsp1 : agdaAppend (bytes " ") (agdaAppend (bytes path) (bytes " HTTP/1.1")) =
          byte 32 :: agdaAppend (bytes path) (bytes " HTTP/1.1") := rfl
      have hspH : bytes " HTTP/1.1" = byte 32 :: bytes "HTTP/1.1" := rfl
      rw [hsp1, words_nonempty_token (bytes method) (agdaAppend (bytes path) (bytes " HTTP/1.1")) hm]
      rw [hspH, words_nonempty_token (bytes path) (bytes "HTTP/1.1") hp]
      rfl
    have hv : httpVersionBytes (bytes "HTTP/1.1") = true := rfl
    simp only [parseHttpReq, s1, hs2, wLine, requestLineBytes, hv, agdaIte])

def parseHttpReqBodyRoundtrip (method path : String) (body : Bytes)
    (okM : AgdaId (ValidHttpToken method) true)
    (okP : AgdaId (ValidHttpToken path) true) :
    AgdaId (maybeMap HttpReqView.reqBody (parseHttpReq (encodeHttpReq method path [] body))) (.just body) :=
  idCong (fun m => maybeMap HttpReqView.reqBody m) (parseHttpReqEncodeRoundtrip method path body okM okP)

def parseHttpRespEncodeRoundtrip (status : Nat) (reason : String) (body : Bytes)
    (okStatus : AgdaId (statusValue (decBytes status)) (.just status))
    (okReason : AgdaId (NoCR (bytes reason)) true) :
    AgdaId (parseHttpResp (encodeHttpResp status reason [] body))
           (.just (HttpRespView.httpRespView status body)) :=
  agdaEqToId (by
    have hs := agdaIdToEq okStatus
    have hr := agdaIdToEq okReason
    let line := agdaAppend (bytes "HTTP/1.1 ") (agdaAppend (decBytes status) (agdaAppend (bytes " ") (bytes reason)))
    let hdrTail := agdaAppend (bytes "\r\nContent-Length: ")
                     (agdaAppend (decBytes (agdaLength body)) (agdaAppend (bytes "\r\nConnection: close\r\n\r\n") body))
    have noCrLine : NoCR line = true :=
      noCR_append (bytes "HTTP/1.1 ") _ rfl
        (noCR_append (decBytes status) _ (decBytes_noCR status)
          (noCR_append (bytes " ") (bytes reason) rfl hr))
    have reassoc : encodeHttpResp status reason [] body = agdaAppend line hdrTail := by
      simp only [encodeHttpResp, autoHeaderBytes, hasHeader, agdaIte, headerBytes, line, hdrTail]
      simp only [TermLaws.agdaAppend_assoc]
      rfl
    have s1 : splitMark (bytes "\r\n") (encodeHttpResp status reason [] body) =
        .just (AgdaPair.mk line (agdaAppend (bytes "Content-Length: ")
                                  (agdaAppend (decBytes (agdaLength body)) (agdaAppend (bytes "\r\nConnection: close\r\n\r\n") body)))) := by
      rw [reassoc]
      exact split_crlf_go [] line _ noCrLine
    have s2 : ∃ hdr, splitMark (bytes "\r\n\r\n") (encodeHttpResp status reason [] body) =
        .just (AgdaPair.mk hdr body) := by
      rw [reassoc]
      simp only [splitMark]
      rw [skip_crlf2_simple [] line hdrTail noCrLine]
      have stepPre : ∀ (a : Bytes),
          splitMarkGo (bytes "\r\n\r\n") a hdrTail =
          splitMarkGo (bytes "\r\n\r\n")
            (agdaFoldl (fun acc' x => x :: acc') a (bytes "\r\nContent-Length: "))
            (agdaAppend (decBytes (agdaLength body)) (agdaAppend (bytes "\r\nConnection: close\r\n\r\n") body)) := fun _ => rfl
      have stepSuf : ∀ (a : Bytes),
          splitMarkGo (bytes "\r\n\r\n") a (agdaAppend (bytes "\r\nConnection: close\r\n\r\n") body) =
          .just (AgdaPair.mk (agdaReverse (agdaFoldl (fun acc' x => x :: acc') a (bytes "\r\nConnection: close"))) body) := fun _ => rfl
      rw [stepPre, skip_crlf2_simple _ (decBytes (agdaLength body)) _ (decBytes_noCR _), stepSuf]
      exact ⟨_, rfl⟩
    obtain ⟨hdr, hs2⟩ := s2
    have wLine : wordsBytes line = bytes "HTTP/1.1" :: decBytes status :: wordsBytes (bytes reason) := by
      simp only [wordsBytes, line]
      have hpfx : ∀ (rest : Bytes),
          wordsBytesGo [] (agdaAppend (bytes "HTTP/1.1 ") rest) = bytes "HTTP/1.1" :: wordsBytesGo [] rest := fun _ => rfl
      rw [hpfx]
      have hsp : agdaAppend (bytes " ") (bytes reason) = byte 32 :: bytes reason := rfl
      rw [hsp, words_nonempty_token (decBytes status) (bytes reason) (decBytes_validToken status)]
    have hv : httpVersionBytes (bytes "HTTP/1.1") = true := rfl
    simp only [parseHttpResp, s1, hs2, wLine, responseLineBytes, hv, agdaIte, hs, statusView])

def evalStubExchangeReqs (mode : NetTopology) (reqs : List Bytes) :
    AgdaId (evalStubExchange mode reqs).proj₁ reqs := .refl

def evalStubExchangeAppend (mode : NetTopology) : (xs ys : List Bytes) →
    AgdaId (evalStubExchange mode (agdaAppend xs ys)).proj₂
           (agdaAppend (evalStubExchange mode xs).proj₂ (evalStubExchange mode ys).proj₂)
  | [], _       => .refl
  | x :: xs, ys => idCong (stubReply mode x :: ·) (evalStubExchangeAppend mode xs ys)

end NetLaws

/-! ## §12 `Context.WorldLaws` -/
namespace WorldLaws

open World

def bindPureLeft {Δ : List Cap} {A B : Type} (a : A) (k : A → WorldProg Δ B) :
    AgdaId (worldBind (.pure a) k) (k a) := .refl

def bindPureLeftRun {Δ : List Cap} {A B : Type} (a : A) (k : A → WorldProg Δ B) (w : SimWorld) :
    AgdaId (runWorldPure (worldBind (.pure a) k) w) (runWorldPure (k a) w) := .refl

def bindPureRightRun {Δ : List Cap} {A : Type} : (m : WorldProg Δ A) → (w : SimWorld) →
    AgdaId (runWorldPure (worldBind m .pure) w) (runWorldPure m w)
  | .pure _,      _ => .refl
  | .step _ op k, w =>
      let rw := stepWorldPure op w
      bindPureRightRun (k rw.proj₁) rw.proj₂

def runWorldPureBind {Δ : List Cap} {A B : Type} :
    (m : WorldProg Δ A) → (k : A → WorldProg Δ B) → (w : SimWorld) →
    AgdaId (runWorldPure (worldBind m k) w)
           (let r := runWorldPure m w; runWorldPure (k r.proj₁) r.proj₂)
  | .pure _,      _, _ => .refl
  | .step _ op f, k, w =>
      let rw := stepWorldPure op w
      runWorldPureBind (f rw.proj₁) k rw.proj₂

def bindAssocRun {Δ : List Cap} {A B C : Type} :
    (m : WorldProg Δ A) → (f : A → WorldProg Δ B) → (g : B → WorldProg Δ C) → (w : SimWorld) →
    AgdaId (runWorldPure (worldBind (worldBind m f) g) w)
           (runWorldPure (worldBind m (fun x => worldBind (f x) g)) w)
  | .pure _,      _, _, _ => .refl
  | .step _ op k, f, g, w =>
      let rw := stepWorldPure op w
      bindAssocRun (k rw.proj₁) f g rw.proj₂

def mapWorldPure {Δ : List Cap} {A B : Type} (f : A → B) (a : A) :
    AgdaId (mapWorld (Δ := Δ) f (.pure a)) (.pure (f a)) := .refl

def mapWorldRun {Δ : List Cap} {A B : Type} (f : A → B) :
    (m : WorldProg Δ A) → (w : SimWorld) →
    AgdaId (runWorldPure (mapWorld f m) w)
           (AgdaPair.mk (f (runWorldPure m w).proj₁) (runWorldPure m w).proj₂)
  | .pure _,      _ => .refl
  | .step _ op k, w =>
      let rw := stepWorldPure op w
      mapWorldRun f (k rw.proj₁) rw.proj₂

def liftWorldPure {Δ₁ Δ₂ : List Cap} {A : Type} (sub : CapSub Δ₁ Δ₂) (a : A) :
    AgdaId (liftWorld sub (.pure a)) (.pure a) := .refl

def liftWorldPreservesRun {Δ₁ Δ₂ : List Cap} {A : Type} (sub : CapSub Δ₁ Δ₂) :
    (m : WorldProg Δ₁ A) → (w : SimWorld) →
    AgdaId (runWorldPure (liftWorld sub m) w) (runWorldPure m w)
  | .pure _,      _ => .refl
  | .step _ op k, w =>
      let rw := stepWorldPure op w
      liftWorldPreservesRun sub (k rw.proj₁) rw.proj₂

def liftWorldBindRun {Δ₁ Δ₂ : List Cap} {A B : Type} (sub : CapSub Δ₁ Δ₂)
    (m : WorldProg Δ₁ A) (k : A → WorldProg Δ₁ B) (w : SimWorld) :
    AgdaId (runWorldPure (liftWorld sub (worldBind m k)) w)
           (runWorldPure (worldBind (liftWorld sub m) (fun a => liftWorld sub (k a))) w) :=
  idTrans (liftWorldPreservesRun sub (worldBind m k) w)
    (idTrans (runWorldPureBind m k w)
      (idSym (idTrans (runWorldPureBind (liftWorld sub m) (fun a => liftWorld sub (k a)) w)
        (idTrans (idCong (fun r => runWorldPure (liftWorld sub (k r.proj₁)) r.proj₂) (liftWorldPreservesRun sub m w))
                 (liftWorldPreservesRun sub (k (runWorldPure m w).proj₁) (runWorldPure m w).proj₂)))))

def stepPreservesClock {c : Cap} (neq : AgdaId c .clockCap → AgdaBot) :
    (op : Op c) → (w : SimWorld) → AgdaId (stepWorldPure op w).proj₂.clock w.clock
  | .opNowMono, _                  => botElim (neq .refl)
  | .opNowWall, _                  => botElim (neq .refl)
  | .opSleepMs _, _                => botElim (neq .refl)
  | .opGetProgName, _              => .refl
  | .opGetArgs, _                  => .refl
  | .opLookupEnv _, _              => .refl
  | .opReadStdinAll, _             => .refl
  | .opReadStdinLine, _            => .refl
  | .opIsTTYStdin, _               => .refl
  | .opIsTTYStdout, _              => .refl
  | .opIsTTYStderr, _              => .refl
  | .opTermSize, _                 => .refl
  | .opWriteStdout _, _            => .refl
  | .opWriteStderr _, _            => .refl
  | .opReadTTYByte, _              => .refl
  | .opReadFile _, _               => .refl
  | .opWriteFile _ _, _            => .refl
  | .opMkdir _ _, _                => .refl
  | .opSymlink _ _, _              => .refl
  | .opUnlink _, _                 => .refl
  | .opStat _, _                   => .refl
  | .opTcpExchange _ _ _ _ _, _    => .refl
  | .opTlsExchange _ _ _ _ _ _ _, _ => .refl
  | .opGitStep _, _                => .refl
  | .opGitSummary, _               => .refl
  | .opWebViewport, _              => .refl
  | .opWebSetTitle _, _            => .refl
  | .opWebDrawScene _, _           => .refl
  | .opWebHitTest _ _, _           => .refl
  | .opWebPollInput, _             => .refl

def stepPreservesFs {c : Cap} (neq : AgdaId c .fsCap → AgdaBot) :
    (op : Op c) → (w : SimWorld) → AgdaId (stepWorldPure op w).proj₂.fs w.fs
  | .opNowMono, _                  => .refl
  | .opNowWall, _                  => .refl
  | .opSleepMs _, _                => .refl
  | .opGetProgName, _              => .refl
  | .opGetArgs, _                  => .refl
  | .opLookupEnv _, _              => .refl
  | .opReadStdinAll, _             => .refl
  | .opReadStdinLine, _            => .refl
  | .opIsTTYStdin, _               => .refl
  | .opIsTTYStdout, _              => .refl
  | .opIsTTYStderr, _              => .refl
  | .opTermSize, _                 => .refl
  | .opWriteStdout _, _            => .refl
  | .opWriteStderr _, _            => .refl
  | .opReadTTYByte, _              => .refl
  | .opReadFile _, _               => botElim (neq .refl)
  | .opWriteFile _ _, _            => botElim (neq .refl)
  | .opMkdir _ _, _                => botElim (neq .refl)
  | .opSymlink _ _, _              => botElim (neq .refl)
  | .opUnlink _, _                 => botElim (neq .refl)
  | .opStat _, _                   => botElim (neq .refl)
  | .opTcpExchange _ _ _ _ _, _    => .refl
  | .opTlsExchange _ _ _ _ _ _ _, _ => .refl
  | .opGitStep _, _                => .refl
  | .opGitSummary, _               => .refl
  | .opWebViewport, _              => .refl
  | .opWebSetTitle _, _            => .refl
  | .opWebDrawScene _, _           => .refl
  | .opWebHitTest _ _, _           => .refl
  | .opWebPollInput, _             => .refl

def stepPreservesNet {c : Cap} (neq : AgdaId c .netCap → AgdaBot) :
    (op : Op c) → (w : SimWorld) → AgdaId (stepWorldPure op w).proj₂.net w.net
  | .opNowMono, _                  => .refl
  | .opNowWall, _                  => .refl
  | .opSleepMs _, _                => .refl
  | .opGetProgName, _              => .refl
  | .opGetArgs, _                  => .refl
  | .opLookupEnv _, _              => .refl
  | .opReadStdinAll, _             => .refl
  | .opReadStdinLine, _            => .refl
  | .opIsTTYStdin, _               => .refl
  | .opIsTTYStdout, _              => .refl
  | .opIsTTYStderr, _              => .refl
  | .opTermSize, _                 => .refl
  | .opWriteStdout _, _            => .refl
  | .opWriteStderr _, _            => .refl
  | .opReadTTYByte, _              => .refl
  | .opReadFile _, _               => .refl
  | .opWriteFile _ _, _            => .refl
  | .opMkdir _ _, _                => .refl
  | .opSymlink _ _, _              => .refl
  | .opUnlink _, _                 => .refl
  | .opStat _, _                   => .refl
  | .opTcpExchange _ _ _ _ _, _    => botElim (neq .refl)
  | .opTlsExchange _ _ _ _ _ _ _, _ => botElim (neq .refl)
  | .opGitStep _, _                => .refl
  | .opGitSummary, _               => .refl
  | .opWebViewport, _              => .refl
  | .opWebSetTitle _, _            => .refl
  | .opWebDrawScene _, _           => .refl
  | .opWebHitTest _ _, _           => .refl
  | .opWebPollInput, _             => .refl

def stepPreservesTty {c : Cap} (neq : AgdaId c .ttyCap → AgdaBot) :
    (op : Op c) → (w : SimWorld) → AgdaId (stepWorldPure op w).proj₂.tty w.tty
  | .opNowMono, _                  => .refl
  | .opNowWall, _                  => .refl
  | .opSleepMs _, _                => .refl
  | .opGetProgName, _              => .refl
  | .opGetArgs, _                  => .refl
  | .opLookupEnv _, _              => .refl
  | .opReadStdinAll, _             => .refl
  | .opReadStdinLine, _            => .refl
  | .opIsTTYStdin, _               => botElim (neq .refl)
  | .opIsTTYStdout, _              => botElim (neq .refl)
  | .opIsTTYStderr, _              => botElim (neq .refl)
  | .opTermSize, _                 => botElim (neq .refl)
  | .opWriteStdout _, _            => botElim (neq .refl)
  | .opWriteStderr _, _            => botElim (neq .refl)
  | .opReadTTYByte, _              => botElim (neq .refl)
  | .opReadFile _, _               => .refl
  | .opWriteFile _ _, _            => .refl
  | .opMkdir _ _, _                => .refl
  | .opSymlink _ _, _              => .refl
  | .opUnlink _, _                 => .refl
  | .opStat _, _                   => .refl
  | .opTcpExchange _ _ _ _ _, _    => .refl
  | .opTlsExchange _ _ _ _ _ _ _, _ => .refl
  | .opGitStep _, _                => .refl
  | .opGitSummary, _               => .refl
  | .opWebViewport, _              => .refl
  | .opWebSetTitle _, _            => .refl
  | .opWebDrawScene _, _           => .refl
  | .opWebHitTest _ _, _           => .refl
  | .opWebPollInput, _             => .refl

private def substMem {x y : Cap} {cs : List Cap} : AgdaId x y → CapMem x cs → CapMem y cs
  | .refl, m => m

def eqCapRefl : (c : Cap) → AgdaId (eqCap c c) true
  | .clockCap => .refl
  | .envCap   => .refl
  | .ttyCap   => .refl
  | .fsCap    => .refl
  | .netCap   => .refl
  | .gitCap   => .refl
  | .webCap   => .refl

private def orFalseLeft : (a b : Bool) → AgdaId (agdaOr a b) false → AgdaId a false
  | false, _, _ => .refl
  | true,  _, h => nomatch h

private def orFalseRight : (a b : Bool) → AgdaId (agdaOr a b) false → AgdaId b false
  | false, _, h => h
  | true,  _, h => nomatch h

def notHasCapNotIn : {c : Cap} → {Δ : List Cap} → AgdaId (hasCap c Δ) false → CapMem c Δ → AgdaBot
  | c, _ :: ds, eq, .here =>
      nomatch (idTrans (idSym (eqCapRefl c)) (orFalseLeft (eqCap c c) (hasCap c ds) eq))
  | c, d :: ds, eq, .there m =>
      notHasCapNotIn (orFalseRight (eqCap c d) (hasCap c ds) eq) m

def progPreservesClock {Δ : List Cap} {A : Type} (absent : CapMem .clockCap Δ → AgdaBot) :
    (m : WorldProg Δ A) → (w : SimWorld) → AgdaId (runWorldPure m w).proj₂.clock w.clock
  | .pure _,      _ => .refl
  | .step h op k, w =>
      let rw := stepWorldPure op w
      idTrans (progPreservesClock absent (k rw.proj₁) rw.proj₂)
              (stepPreservesClock (fun eq => absent (substMem eq h)) op w)

def progPreservesFs {Δ : List Cap} {A : Type} (absent : CapMem .fsCap Δ → AgdaBot) :
    (m : WorldProg Δ A) → (w : SimWorld) → AgdaId (runWorldPure m w).proj₂.fs w.fs
  | .pure _,      _ => .refl
  | .step h op k, w =>
      let rw := stepWorldPure op w
      idTrans (progPreservesFs absent (k rw.proj₁) rw.proj₂)
              (stepPreservesFs (fun eq => absent (substMem eq h)) op w)

def progPreservesNet {Δ : List Cap} {A : Type} (absent : CapMem .netCap Δ → AgdaBot) :
    (m : WorldProg Δ A) → (w : SimWorld) → AgdaId (runWorldPure m w).proj₂.net w.net
  | .pure _,      _ => .refl
  | .step h op k, w =>
      let rw := stepWorldPure op w
      idTrans (progPreservesNet absent (k rw.proj₁) rw.proj₂)
              (stepPreservesNet (fun eq => absent (substMem eq h)) op w)

def progPreservesTty {Δ : List Cap} {A : Type} (absent : CapMem .ttyCap Δ → AgdaBot) :
    (m : WorldProg Δ A) → (w : SimWorld) → AgdaId (runWorldPure m w).proj₂.tty w.tty
  | .pure _,      _ => .refl
  | .step h op k, w =>
      let rw := stepWorldPure op w
      idTrans (progPreservesTty absent (k rw.proj₁) rw.proj₂)
              (stepPreservesTty (fun eq => absent (substMem eq h)) op w)

def continueReactiveAfter {Δ : List Cap} {S : Type}
    (a : ReactiveApp Δ S) (es : List (Event Δ)) :
    AgdaSum S ExitCode → SimWorld → AgdaPair (AgdaSum S ExitCode) SimWorld
  | .inj₁ s',   w' => runReactiveSteps a s' es w'
  | .inj₂ code, w' => AgdaPair.mk (.inj₂ code) w'

def runReactiveStepsAppend {Δ : List Cap} {S : Type} (app : ReactiveApp Δ S) :
    (s : S) → (evs₁ evs₂ : List (Event Δ)) → (w : SimWorld) →
    AgdaId (runReactiveSteps app s (agdaAppend evs₁ evs₂) w)
           (let r₁ := runReactiveSteps app s evs₁ w
            continueReactiveAfter app evs₂ r₁.proj₁ r₁.proj₂)
  | _, [],      _,    _ => .refl
  | s, e :: es, evs₂, w =>
      agdaEqToId (by
        simp only [agdaAppend, runReactiveSteps]
        cases h : (runWorldPure (app.onStep e s) w).proj₁ with
        | inj₁ s' =>
            exact agdaIdToEq (runReactiveStepsAppend app s' es evs₂ (runWorldPure (app.onStep e s) w).proj₂)
        | inj₂ code => rfl)

end WorldLaws

/-!
## §13 Single Thin IO Interpreter (`OwnershipIO.WorldRunner`)
-/

namespace WorldRunner

open AgdaMirror
open AgdaMirror.Context
open AgdaMirror.Clock
open AgdaMirror.FsSandbox
open AgdaMirror.GitSandbox
open AgdaMirror.WebOperad
open AgdaMirror.World

@[extern "ct_lean_now_mono_ms"]
private opaque ctLeanNowMonoMs : IO Nat

@[extern "ct_lean_now_wall_ms"]
private opaque ctLeanNowWallMs : IO Nat

@[extern "ct_lean_sleep_ms"]
private opaque ctLeanSleepMs (ms : UInt32) : IO Unit

@[extern "ct_lean_lookup_env"]
private opaque ctLeanLookupEnvRaw (key : @& String) : IO (Option String)

@[extern "ct_lean_read_stdin_all"]
private opaque ctLeanReadStdinAll : IO ByteArray

@[extern "ct_lean_read_stdin_line"]
private opaque ctLeanReadStdinLine : IO (Option ByteArray)

@[extern "ct_lean_term_size"]
private opaque ctLeanTermSize : IO (Nat × Nat)

@[extern "ct_lean_write_fd"]
private opaque ctLeanWriteFd (fd : UInt32) (ba : @& ByteArray) : IO Unit

@[extern "ct_lean_read_tty_byte"]
private opaque ctLeanReadTTYByte : IO (Option Nat)

@[extern "ct_lean_poll_reactive_event"]
private opaque ctLeanPollReactiveEvent (waitMs : UInt32) : IO (Nat × (Nat × Nat))

@[extern "ct_lean_fs_read_file"]
private opaque ctLeanFsReadFile (path : @& String) : IO (Except Nat ByteArray)

@[extern "ct_lean_fs_write_file"]
private opaque ctLeanFsWriteFile (path : @& String) (ba : @& ByteArray) : IO (Except Nat Unit)

@[extern "ct_lean_fs_mkdir"]
private opaque ctLeanFsMkdir (path : @& String) (mode : UInt32) : IO (Except Nat Unit)

@[extern "ct_lean_fs_symlink"]
private opaque ctLeanFsSymlink (path : @& String) (dest : @& String) : IO (Except Nat Unit)

@[extern "ct_lean_fs_unlink"]
private opaque ctLeanFsUnlink (path : @& String) : IO (Except Nat Unit)

@[extern "ct_lean_fs_stat"]
private opaque ctLeanFsStat (path : @& String) : IO (Except Nat Nat)

@[extern "ct_lean_tcp_exchange_code"]
private opaque ctLeanTcpExchangeCode (host : @& String) (port : UInt32) (req : @& ByteArray)
    (halfClose : UInt8) (timeoutMs : UInt32) : IO (Except Nat ByteArray)

@[extern "ct_lean_tls_exchange_code"]
private opaque ctLeanTlsExchangeCode (host : @& String) (port : UInt32) (sni : @& String)
    (insecure : UInt8) (tunnelReq : @& ByteArray) (req : @& ByteArray)
    (timeoutMs : UInt32) : IO (Except Nat ByteArray)

@[extern "ct_lean_exit_code"]
private opaque ctLeanExitCode (code : UInt32) : IO Unit

private def wrToByteArray (bs : Bytes) : ByteArray :=
  ByteArray.mk ((bs.map (fun b => UInt8.ofNat (agdaFinToNat b))).toArray)

private def wrFromByteArray (ba : ByteArray) : Bytes :=
  ba.data.toList.map (fun b => byte b.toNat)

private def wrDecodeFsError : Nat → FsError
  | 1 => .fsNotFound
  | 2 => .fsIsDirectory
  | 3 => .fsNotDirectory
  | 4 => .fsAlreadyExists
  | 5 => .fsPermissionDenied
  | 6 => .fsSymlinkLoop
  | 7 => .fsInvalidPath
  | _ => .fsIoError

private def wrDecodeNodeKind : Nat → FsNodeKind
  | 0 => .regularNode
  | 1 => .dirNode
  | _ => .symlinkNode

private def wrDecodeNetError : Nat → NetError
  | 1 => .netConnRefused
  | 2 => .netTimedOut
  | 3 => .netInvalidEndpoint
  | 4 => .netTlsError
  | _ => .netIoError

private def wrDecodeSignal : Nat → TermSignal
  | 1 => .sigINT
  | 2 => .sigTERM
  | 3 => .sigHUP
  | _ => .sigQUIT

private def execOpIO : {c : Cap} → (op : Op c) → PureGitRepo → CanvasDOM → IO (Ret op × PureGitRepo × CanvasDOM)
  | .clockCap, .opNowMono, g, w => do
      let t ← ctLeanNowMonoMs
      pure (t, g, w)
  | .clockCap, .opNowWall, g, w => do
      let t ← ctLeanNowWallMs
      pure (t, g, w)
  | .clockCap, .opSleepMs ms, g, w => do
      let clamped := if ms > 3600000 then 3600000 else ms
      ctLeanSleepMs (UInt32.ofNat clamped)
      pure (.tt, g, w)
  | .envCap, .opGetProgName, g, w => do
      let p ← agdaGetProgName
      pure (p, g, w)
  | .envCap, .opGetArgs, g, w => do
      let as ← agdaGetArgs
      pure (as, g, w)
  | .envCap, .opLookupEnv k, g, w => do
      match (← ctLeanLookupEnvRaw k) with
      | some v => pure (.just v, g, w)
      | none   => pure (.nothing, g, w)
  | .envCap, .opReadStdinAll, g, w => do
      let ba ← ctLeanReadStdinAll
      pure (wrFromByteArray ba, g, w)
  | .envCap, .opReadStdinLine, g, w => do
      match (← ctLeanReadStdinLine) with
      | some ba => pure (.just (wrFromByteArray ba), g, w)
      | none    => pure (.nothing, g, w)
  | .ttyCap, .opIsTTYStdin, g, w => do
      let b ← agdaIsTTYStdin
      pure (b, g, w)
  | .ttyCap, .opIsTTYStdout, g, w => do
      let b ← agdaIsTTYStdout
      pure (b, g, w)
  | .ttyCap, .opIsTTYStderr, g, w => do
      let b ← agdaIsTTYStderr
      pure (b, g, w)
  | .ttyCap, .opTermSize, g, w => do
      let (r, c) ← ctLeanTermSize
      pure (AgdaPair.mk r c, g, w)
  | .ttyCap, .opWriteStdout bs, g, w => do
      ctLeanWriteFd 1 (wrToByteArray bs)
      pure (.tt, g, w)
  | .ttyCap, .opWriteStderr bs, g, w => do
      ctLeanWriteFd 2 (wrToByteArray bs)
      pure (.tt, g, w)
  | .ttyCap, .opReadTTYByte, g, w => do
      match (← ctLeanReadTTYByte) with
      | some b => pure (.just (byte b), g, w)
      | none   => pure (.nothing, g, w)
  | .fsCap, .opReadFile p, g, w => do
      match (← ctLeanFsReadFile p) with
      | .error ec => pure (.inj₁ (wrDecodeFsError ec), g, w)
      | .ok ba    => pure (.inj₂ (wrFromByteArray ba), g, w)
  | .fsCap, .opWriteFile p bs, g, w => do
      match (← ctLeanFsWriteFile p (wrToByteArray bs)) with
      | .error ec => pure (.inj₁ (wrDecodeFsError ec), g, w)
      | .ok _     => pure (.inj₂ .tt, g, w)
  | .fsCap, .opMkdir p mode, g, w => do
      match (← ctLeanFsMkdir p (UInt32.ofNat (mode % 512))) with
      | .error ec => pure (.inj₁ (wrDecodeFsError ec), g, w)
      | .ok _     => pure (.inj₂ .tt, g, w)
  | .fsCap, .opSymlink p dst, g, w => do
      match (← ctLeanFsSymlink p dst) with
      | .error ec => pure (.inj₁ (wrDecodeFsError ec), g, w)
      | .ok _     => pure (.inj₂ .tt, g, w)
  | .fsCap, .opUnlink p, g, w => do
      match (← ctLeanFsUnlink p) with
      | .error ec => pure (.inj₁ (wrDecodeFsError ec), g, w)
      | .ok _     => pure (.inj₂ .tt, g, w)
  | .fsCap, .opStat p, g, w => do
      match (← ctLeanFsStat p) with
      | .error ec => pure (.inj₁ (wrDecodeFsError ec), g, w)
      | .ok kd    => pure (.inj₂ (wrDecodeNodeKind kd), g, w)
  | .netCap, .opTcpExchange host port req hc tms, g, w => do
      let clampedT := if tms > 3600000 then 3600000 else tms
      let portU := if port > 65535 then 65536 else port
      match (← ctLeanTcpExchangeCode host (UInt32.ofNat portU) (wrToByteArray req) (if hc then 1 else 0) (UInt32.ofNat clampedT)) with
      | .error ec => pure (.inj₁ (wrDecodeNetError ec), g, w)
      | .ok ba    => pure (.inj₂ (wrFromByteArray ba), g, w)
  | .netCap, .opTlsExchange host port sni ins tun req tms, g, w => do
      let clampedT := if tms > 3600000 then 3600000 else tms
      let portU := if port > 65535 then 65536 else port
      match (← ctLeanTlsExchangeCode host (UInt32.ofNat portU) sni (if ins then 1 else 0) (wrToByteArray tun) (wrToByteArray req) (UInt32.ofNat clampedT)) with
      | .error ec => pure (.inj₁ (wrDecodeNetError ec), g, w)
      | .ok ba    => pure (.inj₂ (wrFromByteArray ba), g, w)
  | .gitCap, .opGitStep gs, g, w =>
      let r := stepPureGit gs g
      pure (r.proj₂, r.proj₁, w)
  | .gitCap, .opGitSummary, g, w =>
      pure (projectSummary g, g, w)
  | .webCap, .opWebViewport, g, w =>
      pure (w.domViewport, g, w)
  | .webCap, .opWebSetTitle title, g, w =>
      pure (.tt, g, { w with domTitle := title })
  | .webCap, .opWebDrawScene sc, g, w =>
      pure (.tt, g, { w with domCommands := compileDraw sc })
  | .webCap, .opWebHitTest sc q, g, w =>
      pure (hitTest sc q, g, w)
  | .webCap, .opWebPollInput, g, w =>
      let r := popWebEvent w.domEvents
      pure (r.proj₁, g, { w with domEvents := r.proj₂ })

private def runWorldState {Δ : List Cap} {A : Type} :
    PureGitRepo → CanvasDOM → WorldProg Δ A → IO (A × PureGitRepo × CanvasDOM)
  | g, w, .pure a      => pure (a, g, w)
  | g, w, .step _ op k => do
      let (ret, g', w') ← execOpIO op g w
      runWorldState g' w' (k ret)

private def hasLiveEventSource (Δ : List Cap) : Bool :=
  match findCapIn .clockCap Δ, findCapIn .envCap Δ, findCapIn .ttyCap Δ with
  | .just _,  _,        _        => true
  | .nothing, .just _,  _        => true
  | .nothing, .nothing, .just _  => true
  | .nothing, .nothing, .nothing => false

private def decodePolledEvent (Δ : List Cap) (kind a b : Nat) : Option (Event Δ) :=
  if kind == 2 then
    match findCapIn .envCap Δ with
    | .just hEnv => some (Event.mkEvent hEnv (.evSignal (wrDecodeSignal a)))
    | .nothing   => none
  else if kind == 3 then
    match findCapIn .ttyCap Δ with
    | .just hTty => some (Event.mkEvent hTty (.evResize a b))
    | .nothing   => none
  else if kind == 4 then
    match findCapIn .ttyCap Δ with
    | .just hTty => some (Event.mkEvent hTty (.evTTYBytes [byte a]))
    | .nothing   => none
  else
    match findCapIn .clockCap Δ with
    | .just hClk => some (Event.mkEvent hClk (.evTickMs a))
    | .nothing   => none

private partial def reactiveLoop {Δ : List Cap} {S : Type}
    (app : ReactiveApp Δ S) (g : PureGitRepo) (w : CanvasDOM) (s : S) : AgdaIO AgdaTop := do
  if !(hasLiveEventSource Δ) then
    ctLeanExitCode 0
    pure .tt
  else
    let (kind, (a, b)) ← ctLeanPollReactiveEvent 25
    match decodePolledEvent Δ kind a b with
    | none    => reactiveLoop app g w s
    | some ev =>
        let (res, g', w') ← runWorldState g w (app.onStep ev s)
        match res with
        | .inj₁ s'   => reactiveLoop app g' w' s'
        | .inj₂ code =>
            ctLeanExitCode (UInt32.ofNat (code % 256))
            pure .tt

def runWorldIO {Δ : List Cap} {A : Type} (prog : WorldProg Δ A) : AgdaIO A := do
  let (a, _, _) ← runWorldState defaultGitRepo emptyCanvasDOM prog
  pure a

def runCliIO {Δ : List Cap} (app : CliApp Δ) : AgdaIO AgdaTop := do
  let code ← runWorldIO app
  ctLeanExitCode (UInt32.ofNat (code % 256))
  pure .tt

def runReactiveIO {Δ : List Cap} {S : Type} (app : ReactiveApp Δ S) : AgdaIO AgdaTop := do
  let (s₀, g₀, w₀) ← runWorldState defaultGitRepo emptyCanvasDOM app.init
  reactiveLoop app g₀ w₀ s₀

end WorldRunner

end AgdaMirror
