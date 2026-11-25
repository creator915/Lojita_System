import LojitaCtx.Terminal

namespace LojitaCtx.WebOperad

open LojitaCtx.Terminal

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
  (r.rx + (Int.ofNat r.rw))

def bottomEdge (r : Rect) : Int :=
  (r.ry + (Int.ofNat r.rh))

def inIntervalB (lo hi x : Int) (k : Nat) : Bool :=
  let scale := Int.ofNat (Nat.succ k)
  lo * scale ≤ x && Bool.not (hi * scale ≤ x)

def inRectQ (q : QPoint) (r : Rect) : Bool :=
  inIntervalB r.rx (rightEdge r) q.qx q.qdenMinus1 &&
    inIntervalB r.ry (bottomEdge r) q.qy q.qdenMinus1

def inRect (p : Point) (r : Rect) : Bool :=
  inRectQ (fromPixel p) r

def degenerateB (r : Rect) : Bool :=
  r.rw == 0 || r.rh == 0

def edgesB (a b : Rect) : Bool :=
  b.rx ≤ a.rx && (rightEdge a ≤ rightEdge b && (b.ry ≤ a.ry && bottomEdge a ≤ bottomEdge b))

def subRect (a b : Rect) : Bool :=
  degenerateB a || edgesB a b

def disjointRect (a b : Rect) : Bool :=
  degenerateB a ||
    (degenerateB b ||
      (rightEdge a ≤ b.rx || (rightEdge b ≤ a.rx || (bottomEdge a ≤ b.ry || bottomEdge b ≤ a.ry))))

structure Affine2D : Type where
  matrix ::
  num_1 : Nat
  den_1 : Nat
  tx    : Int
  ty    : Int

private def mulPos (a b : Nat) : Nat :=
  b + a * Nat.succ b

def affine (n d : Nat) (x y : Int) : Affine2D :=
  Affine2D.matrix n d (x * Int.ofNat (Nat.succ d)) (y * Int.ofNat (Nat.succ d))

def idAffine : Affine2D :=
  Affine2D.matrix 0 0 (Int.ofNat 0) (Int.ofNat 0)

def compAffine : Affine2D → Affine2D → Affine2D
  | .matrix a b x y, .matrix c d u v =>
    Affine2D.matrix (mulPos a c) (mulPos b d)
      (Int.ofNat (Nat.succ a) * u + x * Int.ofNat (Nat.succ d))
      (Int.ofNat (Nat.succ a) * v + y * Int.ofNat (Nat.succ d))

def invAffine : Affine2D → Affine2D
  | .matrix n d x y => Affine2D.matrix d n (Int.neg x) (Int.neg y)

def applyFwd : Affine2D → QPoint → QPoint
  | .matrix n d x y, q =>
    QPoint.qpt (Int.ofNat (Nat.succ n) * q.qx + x * den q)
      (Int.ofNat (Nat.succ n) * q.qy + y * den q) (mulPos d q.qdenMinus1)

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

def paint {A V : Type} (ink : Option A → Colour → Option V) :
    Scene A → QPoint → (Unit → Option V) → Option V
  | .empty,           _, base => base ()
  | .decorRect _ _,   _, base => base ()
  | .decorLine _ _ _, _, base => base ()
  | .occludeRect c r, q, base => (if (inRectQ q r) then (ink .none c) else base ())
  | .hitRect a c r,   q, base => (if (inRectQ q r) then (ink (.some a) c) else base ())
  | .transform t s,   q, base => paint ink s (applyInv t q) base
  | .clip r s,        q, base =>
      match inRectQ q r with
      | true  => paint ink s q base
      | false => base ()
  | .over f b,        q, base => paint ink f q (fun _ => paint ink b q base)
termination_by structural s _ _ => s

def ownerInk {A : Type} (a : Option A) (_ : Colour) : Option A := a
def colourInk {A : Type} (_ : Option A) (c : Colour) : Option Colour := .some c

def paintOwner {A : Type} (s : Scene A) (q : QPoint) : Option A :=
  paint ownerInk s q (fun _ => none)

def paintSurfaceColour {A : Type} (s : Scene A) (q : QPoint) : Option Colour :=
  paint (colourInk (A := A)) s q (fun _ => none)

inductive HitResult (A : Type) : Type where
  | miss    : HitResult A
  | blocked : HitResult A
  | hit     : A → HitResult A

private def firstHit {A : Type} : HitResult A → (Unit → HitResult A) → HitResult A
  | .miss,    below => below ()
  | .blocked, _     => .blocked
  | .hit a,   _     => .hit a

def route {A : Type} : Scene A → QPoint → HitResult A
  | .empty,           _ => .miss
  | .decorRect _ _,   _ => .miss
  | .decorLine _ _ _, _ => .miss
  | .occludeRect _ r, q => (if (inRectQ q r) then .blocked else .miss)
  | .hitRect a _ r,   q => (if (inRectQ q r) then (.hit a) else .miss)
  | .transform t s,   q => route s (applyInv t q)
  | .clip r s,        q =>
      match inRectQ q r with
      | true  => route s q
      | false => .miss
  | .over front back, q => firstHit (route front q) (fun _ => route back q)
termination_by structural s _ => s

def resolve {A : Type} : HitResult A → (Unit → Option A) → Option A
  | .miss,    base => base ()
  | .blocked, _    => .none
  | .hit a,   _    => .some a

def hitTest {A : Type} (s : Scene A) (q : QPoint) : Option A :=
  resolve (route s q) (fun _ => none)

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

abbrev FrameState : Type := Option QPoint

def mask (r : Rect) : FrameState → FrameState
  | .none => .none
  | .some q  => (if (inRectQ q r) then (.some q) else .none)

def putColour (r : Rect) (c : Colour) : FrameState → Option Colour → Option Colour
  | .none, old => old
  | .some q,  old => (if (inRectQ q r) then (.some c) else old)

def run : List DrawCmd → FrameState → List FrameState → Option Colour → Option Colour
  | [],                   _,     _,             pixel => pixel
  | .cmdSave :: cs,       frame, stack,         pixel => run cs frame (frame :: stack) pixel
  | .cmdRestore :: _,     _,     [],            pixel => pixel
  | .cmdRestore :: cs,    _,     saved :: stack, pixel => run cs saved stack pixel
  | .cmdTransform t :: cs, frame, stack,        pixel => run cs (Option.map (applyInv t) frame) stack pixel
  | .cmdClip r :: cs,     frame, stack,         pixel => run cs (mask r frame) stack pixel
  | .cmdFillRect c r :: cs, frame, stack,       pixel => run cs frame stack (putColour r c frame pixel)
  | .cmdStrokeRect _ _ :: cs, frame, stack, pixel => run cs frame stack pixel
  | .cmdText _ _ _ :: cs, frame, stack, pixel => run cs frame stack pixel
  | .cmdLine _ _ _ :: cs, frame, stack, pixel => run cs frame stack pixel
termination_by structural cs _ _ _ => cs

def runDrawStack (cs : List DrawCmd) (q : QPoint) : Option Colour :=
  run cs (.some q) [] .none

inductive HostInput : Type where
  | hostClick   : Int → Int → HostInput
  | hostPanZoom : Int → Int → Nat → Nat → HostInput
  | hostKey     : Key → HostInput
  | hostResize  : Nat → Nat → HostInput
  | hostTickMs  : Nat → HostInput

private theorem dualRoutePaint {A : Type} :
    ∀ (s : Scene A) (q : QPoint) (base : Unit → Option A),
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
      have hf := dualRoutePaint f q (fun _ => paint ownerInk b q base)
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
termination_by structural x _ _ => x

theorem visualHitConsistent {A : Type} (s : Scene A) (q : QPoint) : hitTest s q = paintOwner s q :=
  id (dualRoutePaint s q (fun _ => none))

private def atFrame {A : Type} (s : Scene A) : FrameState → Option Colour → Option Colour
  | .none, old => old
  | .some q,  old => paint (colourInk (A := A)) s q (fun _ => old)

private theorem machinePrefix {A : Type} :
    ∀ (s : Scene A) (k : List DrawCmd) (f : FrameState) (st : List FrameState) (old : Option Colour),
      run (emit .surfaces s k) f st old = run k f st (atFrame s f old)
  | .empty, _, .none, _, _           => rfl
  | .empty, _, .some _, _, _            => rfl
  | .decorRect _ _, _, .none, _, _   => rfl
  | .decorRect _ _, _, .some _, _, _    => rfl
  | .decorLine _ _ _, _, .none, _, _ => rfl
  | .decorLine _ _ _, _, .some _, _, _  => rfl
  | .occludeRect c r, _, .none, _, _ => rfl
  | .occludeRect c r, k, .some q, st, old => by
      simp only [emit, run, putColour, atFrame, paint, colourInk] <;> try rfl
  | .hitRect a c r, _, .none, _, _   => rfl
  | .hitRect a c r, k, .some q, st, old => by
      simp only [emit, run, putColour, atFrame, paint, colourInk] <;> try rfl
  | .transform t s, k, .none, st, old =>
      machinePrefix s (.cmdRestore :: k) .none (.none :: st) old
  | .transform t s, k, .some q, st, old =>
      machinePrefix s (.cmdRestore :: k) (.some (applyInv t q)) (.some q :: st) old
  | .clip r s, k, .none, st, old =>
      machinePrefix s (.cmdRestore :: k) .none (.none :: st) old
  | .clip r s, k, .some q, st, old => by
      simp only [emit, run, mask, atFrame, paint] <;> try rfl
      cases inRectQ q r with
      | false => exact machinePrefix s (.cmdRestore :: k) .none (.some q :: st) old
      | true  => exact machinePrefix s (.cmdRestore :: k) (.some q) (.some q :: st) old
  | .over f b, k, fr, st, old => by
      simp only [emit] <;> try rfl
      rw [machinePrefix b (emit .surfaces f k) fr st old,
          machinePrefix f k fr st (atFrame b fr old)]
      cases fr <;> rfl
termination_by structural x _ _ _ _ => x

theorem drawMachineSound {A : Type} (s : Scene A) (q : QPoint) :
    runDrawStack (compileSurfaceDraw s) q = paintSurfaceColour s q :=
  id (machinePrefix s [] (.some q) [] .none)

end LojitaCtx.WebOperad
