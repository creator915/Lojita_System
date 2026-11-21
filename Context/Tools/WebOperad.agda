{-# OPTIONS --safe #-}
module Context.Tools.WebOperad where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base as Z using (ℤ; +_)
import Data.Integer.Properties as ZP
open import Data.List.Base as L using (List; []; _∷_; _++_; concat; map)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat as N using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
import Data.Nat.Properties as NP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Algebra.Solver.Ring.Simple as Ring
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; does; ¬_)
open import Relation.Nullary.Decidable using (dec-true; dec-false)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
import Context.Terminal as Term
open Term public using (Colour; defaultColour; indexed; rgb; Key; TimedMachine)

record Point : Set where
  constructor pt
  field px py : ℤ
open Point public

record Size : Set where
  constructor size
  field w h : ℕ
open Size public

record Rect : Set where
  constructor rect
  field rx ry : ℤ
        rw rh : ℕ
open Rect public

-- Both homogeneous coordinates share a positive denominator.
record QPoint : Set where
  constructor qpt
  field qx qy : ℤ
        qdenMinus1 : ℕ
open QPoint public

den : QPoint → ℤ
den q = + suc (qdenMinus1 q)

fromPixel : Point → QPoint
fromPixel p = qpt (px p) (py p) 0

rightEdge bottomEdge : Rect → ℤ
rightEdge r = rx r Z.+ (+ rw r)
bottomEdge r = ry r Z.+ (+ rh r)

private
  witness : ∀ {P : Set} (d : Dec P) → does d ≡ true → P
  witness (yes p) _ = p
  witness (no _) ()

  sameDecision : ∀ {P R : Set} (p : Dec P) (r : Dec R) →
                 (P → R) → (R → P) → does p ≡ does r
  sameDecision (yes p) r f g = sym (dec-true r (f p))
  sameDecision (no np) r f g = sym (dec-false r (λ x → np (g x)))

Interval : ℤ → ℤ → ℤ → ℕ → Set
Interval lo hi x k = lo Z.* (+ suc k) Z.≤ x × ¬ (hi Z.* (+ suc k) Z.≤ x)

interval? : ∀ lo hi x k → Dec (Interval lo hi x k)
interval? lo hi x k = (lo Z.* (+ suc k) ZP.≤? x) ×-dec ¬? (hi Z.* (+ suc k) ZP.≤? x)

Inside : QPoint → Rect → Set
Inside q r = Interval (rx r) (rightEdge r) (qx q) (qdenMinus1 q) ×
             Interval (ry r) (bottomEdge r) (qy q) (qdenMinus1 q)

inside? : ∀ q r → Dec (Inside q r)
inside? q r = interval? (rx r) (rightEdge r) (qx q) (qdenMinus1 q) ×-dec
              interval? (ry r) (bottomEdge r) (qy q) (qdenMinus1 q)

inRectQ : QPoint → Rect → Bool
inRectQ q r = does (inside? q r)

inRect : Point → Rect → Bool
inRect p = inRectQ (fromPixel p)

Edges : Rect → Rect → Set
Edges a b = rx b Z.≤ rx a × rightEdge a Z.≤ rightEdge b ×
            ry b Z.≤ ry a × bottomEdge a Z.≤ bottomEdge b

Degenerate : Rect → Set
Degenerate r = rw r ≡ 0 ⊎ rh r ≡ 0

degenerate? : ∀ r → Dec (Degenerate r)
degenerate? r = (rw r N.≟ 0) ⊎-dec (rh r N.≟ 0)

edges? : ∀ a b → Dec (Edges a b)
edges? a b = (rx b ZP.≤? rx a) ×-dec (rightEdge a ZP.≤? rightEdge b)
          ×-dec (ry b ZP.≤? ry a) ×-dec (bottomEdge a ZP.≤? bottomEdge b)

sub? : ∀ a b → Dec (Degenerate a ⊎ Edges a b)
sub? a b = degenerate? a ⊎-dec edges? a b

subRect : Rect → Rect → Bool
subRect a b = does (sub? a b)

Separate : Rect → Rect → Set
Separate a b = Degenerate a ⊎ Degenerate b ⊎ rightEdge a Z.≤ rx b ⊎ rightEdge b Z.≤ rx a
               ⊎ bottomEdge a Z.≤ ry b ⊎ bottomEdge b Z.≤ ry a

separate? : ∀ a b → Dec (Separate a b)
separate? a b = degenerate? a ⊎-dec degenerate? b ⊎-dec (rightEdge a ZP.≤? rx b)
  ⊎-dec (rightEdge b ZP.≤? rx a) ⊎-dec (bottomEdge a ZP.≤? ry b) ⊎-dec (bottomEdge b ZP.≤? ry a)

disjointRect : Rect → Rect → Bool
disjointRect a b = does (separate? a b)

private
  widen : ∀ {a b c d x k} → c Z.≤ a → b Z.≤ d → Interval a b x k → Interval c d x k
  widen {k = k} ca bd (lo , hi) = ZP.≤-trans (ZP.*-monoʳ-≤-pos k ca) lo ,
                            (λ dx → hi (ZP.≤-trans (ZP.*-monoʳ-≤-pos k bd) dx))

  vacuous : ∀ {q r} → Degenerate r → ¬ Inside q r
  vacuous {r = rect x y _ h} (inj₁ refl) ((lo , hi) , _) rewrite ZP.+-identityʳ x = hi lo
  vacuous {r = rect x y w _} (inj₂ refl) (_ , (lo , hi)) rewrite ZP.+-identityʳ y = hi lo

  exclude : ∀ k {b c x} → b Z.≤ c → ¬ (b Z.* (+ suc k) Z.≤ x) → c Z.* (+ suc k) Z.≤ x → ⊥
  exclude k bc hi lo = hi (ZP.≤-trans (ZP.*-monoʳ-≤-pos k bc) lo)

  apart : ∀ {a b q} → Separate a b → Inside q a → ¬ Inside q b
  apart {a} {b} {q} (inj₁ ea) p v = vacuous {q} {a} ea p
  apart {a} {b} {q} (inj₂ (inj₁ eb)) p v = vacuous {q} {b} eb v
  apart {q = q} (inj₂ (inj₂ (inj₁ x))) p v = exclude (qdenMinus1 q) x (proj₂ (proj₁ p)) (proj₁ (proj₁ v))
  apart {q = q} (inj₂ (inj₂ (inj₂ (inj₁ x)))) p v = exclude (qdenMinus1 q) x (proj₂ (proj₁ v)) (proj₁ (proj₁ p))
  apart {q = q} (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) p v = exclude (qdenMinus1 q) y (proj₂ (proj₂ p)) (proj₁ (proj₂ v))
  apart {q = q} (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y))))) p v = exclude (qdenMinus1 q) y (proj₂ (proj₂ v)) (proj₁ (proj₂ p))

subRect-sound : ∀ {a b} → subRect a b ≡ true → ∀ q → inRectQ q a ≡ true → inRectQ q b ≡ true
subRect-sound {a} {b} sub q mem with witness (sub? a b) sub | witness (inside? q a) mem
... | inj₁ ea | p = ⊥-elim (vacuous {q} {a} ea p)
... | inj₂ (l , r , t , d) | x , y = dec-true (inside? q b) (widen l r x , widen t d y)

disjointRect-sound : ∀ {a b} → disjointRect a b ≡ true → ∀ q → inRectQ q a ≡ true → inRectQ q b ≡ false
disjointRect-sound {a} {b} sep q mem =
  dec-false (inside? q b) (apart {a} {b} {q} (witness (separate? a b) sep) (witness (inside? q a) mem))

-- x ↦ (n·x + tx)/d. The integer translation numerators are closed under
-- composition and inversion, even for fractional pan and zoom.
record Affine2D : Set where
  constructor matrix
  field num-1 den-1 : ℕ
        tx ty : ℤ
open Affine2D public

private
  mulPos : ℕ → ℕ → ℕ
  mulPos a b = b + a N.* suc b

affine : ℕ → ℕ → ℤ → ℤ → Affine2D
affine n d x y = matrix n d (x Z.* (+ suc d)) (y Z.* (+ suc d))

idAffine : Affine2D
idAffine = matrix 0 0 (+ 0) (+ 0)

compAffine : Affine2D → Affine2D → Affine2D
compAffine (matrix a b x y) (matrix c d u v) =
  matrix (mulPos a c) (mulPos b d)
    ((+ suc a) Z.* u Z.+ x Z.* (+ suc d)) ((+ suc a) Z.* v Z.+ y Z.* (+ suc d))

invAffine : Affine2D → Affine2D
invAffine (matrix n d x y) = matrix d n (Z.- x) (Z.- y)

applyFwd : Affine2D → QPoint → QPoint
applyFwd (matrix n d x y) q = qpt
  ((+ suc n) Z.* qx q Z.+ x Z.* den q) ((+ suc n) Z.* qy q Z.+ y Z.* den q)
  (mulPos d (qdenMinus1 q))

applyInv : Affine2D → QPoint → QPoint
applyInv t = applyFwd (invAffine t)

private
  module IntegerRing = Ring (ACR.fromCommutativeRing ZP.+-*-commutativeRing) ZP._≟_
  open IntegerRing

  cancel-axis : ∀ a b t x k → b Z.* (a Z.* x Z.+ t Z.* k) Z.+ (Z.- t) Z.* (b Z.* k)
                              ≡ x Z.* (a Z.* b)
  cancel-axis = solve 5 (λ a b t x k → b :* (a :* x :+ t :* k) :+ (:- t) :* (b :* k)
                                       := x :* (a :* b)) refl

  regroup : ∀ lo a b k → lo Z.* (a Z.* (b Z.* k)) ≡ (lo Z.* k) Z.* (a Z.* b)
  regroup = solve 4 (λ l a b k → l :* (a :* (b :* k)) := (l :* k) :* (a :* b)) refl

  round-bound : ∀ a b t x k lo →
    does ((lo Z.* (+ suc (mulPos a (mulPos b k)))) ZP.≤?
      ((+ suc b) Z.* ((+ suc a) Z.* x Z.+ t Z.* (+ suc k)) Z.+
        (Z.- t) Z.* (+ suc (mulPos b k)))) ≡ does ((lo Z.* (+ suc k)) ZP.≤? x)
  round-bound a b t x k lo
    rewrite sym (ZP.pos-distrib-* (suc a) (suc (mulPos b k)))
          | sym (ZP.pos-distrib-* (suc b) (suc k))
          | cancel-axis (+ suc a) (+ suc b) t x (+ suc k)
          | regroup lo (+ suc a) (+ suc b) (+ suc k)
          | ZP.pos-distrib-* (suc a) (suc b)
    = sameDecision (((lo Z.* (+ suc k)) Z.* (+ suc (mulPos a b))) ZP.≤? (x Z.* (+ suc (mulPos a b))))
                   ((lo Z.* (+ suc k)) ZP.≤? x) (ZP.*-cancelʳ-≤-pos (lo Z.* (+ suc k)) x (mulPos a b)) (ZP.*-monoʳ-≤-pos (mulPos a b))

inRectQ-inv-fwd : ∀ t q r → inRectQ (applyInv t (applyFwd t q)) r ≡ inRectQ q r
inRectQ-inv-fwd (matrix a b x y) (qpt u v k) r
  rewrite round-bound a b x u k (rx r) | round-bound a b x u k (rightEdge r)
        | round-bound a b y v k (ry r) | round-bound a b y v k (bottomEdge r) = refl

inRectQ-fwd-inv : ∀ t q r → inRectQ (applyFwd t (applyInv t q)) r ≡ inRectQ q r
inRectQ-fwd-inv (matrix a b x y) q r with inRectQ-inv-fwd (matrix b a (Z.- x) (Z.- y)) q r
... | eq rewrite ZP.neg-involutive x | ZP.neg-involutive y = eq

data VisualStyle : Set where
  fill stroke : Colour → VisualStyle
  label : String → Colour → VisualStyle

data Scene (A : Set) : Set where
  empty : Scene A
  decorRect : VisualStyle → Rect → Scene A
  occludeRect : Colour → Rect → Scene A
  hitRect : A → Colour → Rect → Scene A
  decorLine : Point → Point → Colour → Scene A
  transform : Affine2D → Scene A → Scene A
  clip : Rect → Scene A → Scene A
  over : Scene A → Scene A → Scene A

mapScene : ∀ {A B} → (A → B) → Scene A → Scene B
mapScene f empty = empty
mapScene f (decorRect v r) = decorRect v r
mapScene f (occludeRect c r) = occludeRect c r
mapScene f (hitRect a c r) = hitRect (f a) c r
mapScene f (decorLine p q c) = decorLine p q c
mapScene f (transform t s) = transform t (mapScene f s)
mapScene f (clip r s) = clip r (mapScene f s)
mapScene f (over front back) = over (mapScene f front) (mapScene f back)

-- The painter threads an existing canvas value through back, then front.
-- A surface is an interactive or occluding fill. Decoration has no owner.
paint : ∀ {A V : Set} → (Maybe A → Colour → Maybe V) → Scene A → QPoint → Maybe V → Maybe V
paint ink empty q base = base
paint ink (decorRect _ _) q base = base
paint ink (decorLine _ _ _) q base = base
paint ink (occludeRect c r) q base = if inRectQ q r then ink nothing c else base
paint ink (hitRect a c r) q base = if inRectQ q r then ink (just a) c else base
paint ink (transform t s) q base = paint ink s (applyInv t q) base
paint ink (clip r s) q base with inRectQ q r
... | true = paint ink s q base
... | false = base
paint ink (over f b) q base = paint ink f q (paint ink b q base)

ownerInk : ∀ {A : Set} → Maybe A → Colour → Maybe A
ownerInk a _ = a

colourInk : ∀ {A : Set} → Maybe A → Colour → Maybe Colour
colourInk _ c = just c

paintOwner : ∀ {A} → Scene A → QPoint → Maybe A
paintOwner s q = paint ownerInk s q nothing

paintSurfaceColour : ∀ {A} → Scene A → QPoint → Maybe Colour
paintSurfaceColour s q = paint colourInk s q nothing

data HitResult (A : Set) : Set where
  miss blocked : HitResult A
  hit : A → HitResult A

private
  firstHit : ∀ {A} → HitResult A → (⊤ → HitResult A) → HitResult A
  firstHit miss below = below tt
  firstHit blocked _ = blocked
  firstHit (hit a) _ = hit a

route : ∀ {A} → Scene A → QPoint → HitResult A
route empty q = miss
route (decorRect _ _) q = miss
route (decorLine _ _ _) q = miss
route (occludeRect _ r) q = if inRectQ q r then blocked else miss
route (hitRect a _ r) q = if inRectQ q r then hit a else miss
route (transform t s) q = route s (applyInv t q)
route (clip r s) q with inRectQ q r
... | true = route s q
... | false = miss
route (over front back) q = firstHit (route front q) (λ _ → route back q)

resolve : ∀ {A} → HitResult A → Maybe A → Maybe A
resolve miss base = base
resolve blocked _ = nothing
resolve (hit a) _ = just a

hitTest : ∀ {A} → Scene A → QPoint → Maybe A
hitTest s q = resolve (route s q) nothing

private
  dual : ∀ {A} (s : Scene A) q base → resolve (route s q) base ≡ paint ownerInk s q base
  dual empty q base = refl
  dual (decorRect _ _) q base = refl
  dual (decorLine _ _ _) q base = refl
  dual (occludeRect c r) q base with inRectQ q r
  ... | true = refl
  ... | false = refl
  dual (hitRect a c r) q base with inRectQ q r
  ... | true = refl
  ... | false = refl
  dual (transform t s) q base = dual s (applyInv t q) base
  dual (clip r s) q base with inRectQ q r
  ... | true = dual s q base
  ... | false = refl
  dual (over f b) q base with route f q | dual f q (paint ownerInk b q base)
  ... | miss | eq = trans (dual b q base) eq
  ... | blocked | eq = eq
  ... | hit _ | eq = eq

visual-hit-consistent : ∀ {A} (s : Scene A) q → hitTest s q ≡ paintOwner s q
visual-hit-consistent s q = dual s q nothing

data DrawCmd : Set where
  cmdSave cmdRestore : DrawCmd
  cmdTransform : Affine2D → DrawCmd
  cmdClip : Rect → DrawCmd
  cmdFillRect cmdStrokeRect : Colour → Rect → DrawCmd
  cmdText : String → Colour → Rect → DrawCmd
  cmdLine : Point → Point → Colour → DrawCmd

styleCmd : VisualStyle → Rect → DrawCmd
styleCmd (fill c) = cmdFillRect c
styleCmd (stroke c) = cmdStrokeRect c
styleCmd (label t c) = cmdText t c

data DrawPass : Set where
  full surfaces : DrawPass

-- Continuation form makes concatenation linear, including skewed stacks.
emit : ∀ {A} → DrawPass → Scene A → List DrawCmd → List DrawCmd
emit pass empty k = k
emit full (decorRect style r) k = styleCmd style r ∷ k
emit full (decorLine p q c) k = cmdLine p q c ∷ k
emit surfaces (decorRect _ _) k = k
emit surfaces (decorLine _ _ _) k = k
emit pass (occludeRect c r) k = cmdFillRect c r ∷ k
emit pass (hitRect _ c r) k = cmdFillRect c r ∷ k
emit pass (transform t s) k = cmdSave ∷ cmdTransform t ∷ emit pass s (cmdRestore ∷ k)
emit pass (clip r s) k = cmdSave ∷ cmdClip r ∷ emit pass s (cmdRestore ∷ k)
emit pass (over f b) k = emit pass b (emit pass f k)

compileDraw compileSurfaceDraw : ∀ {A} → Scene A → List DrawCmd
compileDraw s = emit full s []
compileSurfaceDraw s = emit surfaces s []

private
  module Depth {X : Set} (push pop : X → X) (round : ∀ x → pop (push x) ≡ x) where
    scan : X → List DrawCmd → X
    scan x [] = x
    scan x (cmdSave ∷ k) = scan (push x) k
    scan x (cmdRestore ∷ k) = scan (pop x) k
    scan x (_ ∷ k) = scan x k

    prefix : ∀ {A} (s : Scene A) x k → scan x (emit full s k) ≡ scan x k
    prefix empty x k = refl
    prefix (decorRect (fill _) _) x k = refl
    prefix (decorRect (stroke _) _) x k = refl
    prefix (decorRect (label _ _) _) x k = refl
    prefix (decorLine _ _ _) x k = refl
    prefix (occludeRect _ _) x k = refl
    prefix (hitRect _ _ _) x k = refl
    prefix (transform t s) x k rewrite prefix s (push x) (cmdRestore ∷ k) | round x = refl
    prefix (clip r s) x k rewrite prefix s (push x) (cmdRestore ∷ k) | round x = refl
    prefix (over f b) x k = trans (prefix b x (emit full f k)) (prefix f x k)

  module Delta = Depth Z.suc Z.pred ZP.pred-suc

  popNat : Maybe ℕ → Maybe ℕ
  popNat (just (suc n)) = just n
  popNat _ = nothing

  pop-push : ∀ x → popNat (Maybe.map suc x) ≡ x
  pop-push nothing = refl
  pop-push (just n) = refl

  module SafeDepth = Depth (Maybe.map suc) popNat pop-push

stackDelta : List DrawCmd → ℤ
stackDelta = Delta.scan (+ 0)

stackSafe : ℕ → List DrawCmd → Set
stackSafe n cs = SafeDepth.scan (just n) cs ≡ just n

compileDraw-balanced : ∀ {A} (s : Scene A) → stackDelta (compileDraw s) ≡ + 0
compileDraw-balanced s = Delta.prefix s (+ 0) []

compileDraw-stackSafe : ∀ {A} (s : Scene A) n → stackSafe n (compileDraw s)
compileDraw-stackSafe s n = SafeDepth.prefix s (just n) []

-- A frame stores the inverse-transformed sample. An absent sample represents
-- a clipped-out pixel and stays clipped until RESTORE pops a saved frame.
FrameState : Set
FrameState = Maybe QPoint

mask : Rect → FrameState → FrameState
mask r nothing = nothing
mask r (just q) = if inRectQ q r then just q else nothing

putColour : Rect → Colour → FrameState → Maybe Colour → Maybe Colour
putColour r c nothing old = old
putColour r c (just q) old = if inRectQ q r then just c else old

run : List DrawCmd → FrameState → List FrameState → Maybe Colour → Maybe Colour
run [] frame stack pixel = pixel
run (cmdSave ∷ cs) frame stack pixel = run cs frame (frame ∷ stack) pixel
run (cmdRestore ∷ cs) frame [] pixel = pixel
run (cmdRestore ∷ cs) frame (saved ∷ stack) pixel = run cs saved stack pixel
run (cmdTransform t ∷ cs) frame stack pixel = run cs (Maybe.map (applyInv t) frame) stack pixel
run (cmdClip r ∷ cs) frame stack pixel = run cs (mask r frame) stack pixel
run (cmdFillRect c r ∷ cs) frame stack pixel = run cs frame stack (putColour r c frame pixel)
run (_ ∷ cs) frame stack pixel = run cs frame stack pixel

runDrawStack : List DrawCmd → QPoint → Maybe Colour
runDrawStack cs q = run cs (just q) [] nothing

private
  atFrame : ∀ {A} → Scene A → FrameState → Maybe Colour → Maybe Colour
  atFrame s nothing old = old
  atFrame s (just q) old = paint colourInk s q old

  machine-prefix : ∀ {A} (s : Scene A) k f st old →
    run (emit surfaces s k) f st old ≡ run k f st (atFrame s f old)
  machine-prefix empty k nothing st old = refl
  machine-prefix empty k (just _) st old = refl
  machine-prefix (decorRect _ _) k nothing st old = refl
  machine-prefix (decorRect _ _) k (just _) st old = refl
  machine-prefix (decorLine _ _ _) k nothing st old = refl
  machine-prefix (decorLine _ _ _) k (just _) st old = refl
  machine-prefix (occludeRect c r) k nothing st old = refl
  machine-prefix (occludeRect c r) k (just _) st old = refl
  machine-prefix (hitRect a c r) k nothing st old = refl
  machine-prefix (hitRect a c r) k (just _) st old = refl
  machine-prefix (transform t s) k nothing st old = machine-prefix s (cmdRestore ∷ k) nothing (nothing ∷ st) old
  machine-prefix (transform t s) k (just q) st old =
    machine-prefix s (cmdRestore ∷ k) (just (applyInv t q)) (just q ∷ st) old
  machine-prefix (clip r s) k nothing st old = machine-prefix s (cmdRestore ∷ k) nothing (nothing ∷ st) old
  machine-prefix (clip r s) k (just q) st old with inRectQ q r
  ... | false = machine-prefix s (cmdRestore ∷ k) nothing (just q ∷ st) old
  ... | true = machine-prefix s (cmdRestore ∷ k) (just q) (just q ∷ st) old
  machine-prefix (over f b) k fr st old
    rewrite machine-prefix b (emit surfaces f k) fr st old
          | machine-prefix f k fr st (atFrame b fr old) with fr
  ... | nothing = refl
  ... | just q = refl

draw-machine-sound : ∀ {A} (s : Scene A) q → runDrawStack (compileSurfaceDraw s) q ≡ paintSurfaceColour s q
draw-machine-sound s q = machine-prefix s [] (just q) [] nothing

record SlotColor : Set₁ where
  constructor slotColor
  field minSize : Size
        Msg : Set
open SlotColor public

fits? : ∀ sz r → Dec (w sz ≤ rw r × h sz ≤ rh r)
fits? sz r = (w sz N.≤? rw r) ×-dec (h sz N.≤? rh r)

Fits : Size → Rect → Bool
Fits sz r = does (fits? sz r)

record Placed (parent : Rect) (c : SlotColor) : Set where
  constructor placed
  field box : Rect
        fits : Fits (minSize c) box ≡ true
        edgeCertificate : does (edges? box parent) ≡ true
  edges : Edges box parent
  edges = witness (edges? box parent) edgeCertificate
  contained : subRect box parent ≡ true
  contained = dec-true (sub? box parent) (inj₂ edges)
open Placed public

Scenes : List SlotColor → Set₁
Scenes = All (λ c → Scene (Msg c))

record LayoutOp (inputs : List SlotColor) (out : SlotColor) : Set₁ where
  constructor layout
  field
    placeSlots : (r : Rect) → Fits (minSize out) r ≡ true → All (Placed r) inputs
    assemble : (r : Rect) → Fits (minSize out) r ≡ true → Scenes inputs → Scene (Msg out)
open LayoutOp public

private
  sameEdges : ∀ r → does (edges? r r) ≡ true
  sameEdges r = dec-true (edges? r r) (ZP.≤-refl , ZP.≤-refl , ZP.≤-refl , ZP.≤-refl)

  edge-trans : ∀ {r p z} → Edges p z → Edges r p → Edges r z
  edge-trans (pl , pr , pt′ , pb) (cl , cr , ct , cb) =
    ZP.≤-trans pl cl , ZP.≤-trans cr pr , ZP.≤-trans pt′ ct , ZP.≤-trans cb pb

  enclose : ∀ {c p z} → (parent : Placed z p) → Placed (box parent) c → Placed z c
  enclose {z = z} parent child = placed (box child) (fits child) (dec-true (edges? (box child) z)
    (edge-trans {box child} {box parent} {z} (edges parent) (edges child)))

  appendAll : ∀ {P : SlotColor → Set} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
  appendAll [] ys = ys
  appendAll (x ∷ xs) ys = x ∷ appendAll xs ys

  splitAll : ∀ {P : SlotColor → Set} (xs : List SlotColor) {ys} →
             All P (xs ++ ys) → All P xs × All P ys
  splitAll [] zs = [] , zs
  splitAll (c ∷ cs) (v ∷ vs) with splitAll cs vs
  ... | xs , ys = (v ∷ xs) , ys

idOp : ∀ {c} → LayoutOp (c ∷ []) c
idOp = layout (λ r ok → placed r ok (sameEdges r) ∷ []) (λ { _ _ (s ∷ []) → s })

infixr 5 _∷ᶠ_
data OpForest : List (List SlotColor) → List SlotColor → Set₁ where
  nil : OpForest [] []
  _∷ᶠ_ : ∀ {xs x xss bs} → LayoutOp xs x → OpForest xss bs → OpForest (xs ∷ xss) (x ∷ bs)

private
  forestSlots : ∀ {groups bs r} → OpForest groups bs → All (Placed r) bs → All (Placed r) (concat groups)
  forestSlots nil [] = []
  forestSlots (g ∷ᶠ gs) (p ∷ ps) =
    appendAll (All.map (enclose p) (placeSlots g (box p) (fits p))) (forestSlots gs ps)

  forestScenes : ∀ {groups bs r} → OpForest groups bs → All (Placed r) bs → Scenes (concat groups) → Scenes bs
  forestScenes nil [] [] = []
  forestScenes (_∷ᶠ_ {xs} g gs) (p ∷ ps) ss with splitAll xs ss
  ... | first , rest = assemble g (box p) (fits p) first ∷ forestScenes gs ps rest

compOp : ∀ {bs c groups} → LayoutOp bs c → OpForest groups bs → LayoutOp (concat groups) c
compOp f gs = layout (λ r ok → forestSlots gs (placeSlots f r ok))
                     (λ r ok ss → assemble f r ok (forestScenes gs (placeSlots f r ok) ss))

-- Positions distinguish repeated colours in the same input list.
data Slot (c : SlotColor) : List SlotColor → Set₁ where
  here : ∀ {cs} → Slot c (c ∷ cs)
  there : ∀ {x cs} → Slot c cs → Slot c (x ∷ cs)

singletons : List SlotColor → List (List SlotColor)
singletons = map (λ c → c ∷ [])

idForest : ∀ bs → OpForest (singletons bs) bs
idForest [] = nil
idForest (c ∷ cs) = idOp ∷ᶠ idForest cs

graftGroups : ∀ {c bs} → Slot c bs → List SlotColor → List (List SlotColor)
graftGroups (here {cs}) ds = ds ∷ singletons cs
graftGroups (there {x} i) ds = (x ∷ []) ∷ graftGroups i ds

plugForest : ∀ {c bs ds} (i : Slot c bs) → LayoutOp ds c → OpForest (graftGroups i ds) bs
plugForest (here {cs}) g = g ∷ᶠ idForest cs
plugForest (there i) g = idOp ∷ᶠ plugForest i g

plugOp : ∀ {bs out c ds} (i : Slot c bs) → LayoutOp bs out → LayoutOp ds c →
         LayoutOp (concat (graftGroups i ds)) out
plugOp i f g = compOp f (plugForest i g)

private
  split-append : ∀ {xs ys} (ss : Scenes xs) (ts : Scenes ys) →
                 splitAll xs (appendAll ss ts) ≡ (ss , ts)
  split-append [] ts = refl
  split-append (s ∷ ss) ts rewrite split-append ss ts = refl

-- The input lists are canonically reassociated by flattening. These comparison
-- maps transport actual supplied scenes, without function or proof extensionality.
singletonScenes : ∀ {bs} → Scenes bs → Scenes (concat (singletons bs))
singletonScenes [] = []
singletonScenes (s ∷ ss) = s ∷ singletonScenes ss

compOp-left-id : ∀ {bs c} (g : LayoutOp bs c) r ok (ss : Scenes bs) →
  assemble (compOp idOp (g ∷ᶠ nil)) r ok (appendAll ss []) ≡ assemble g r ok ss
compOp-left-id g r ok ss rewrite split-append ss [] = refl

private
  identity-scenes : ∀ {bs r} (ps : All (Placed r) bs) (ss : Scenes bs) →
    forestScenes (idForest bs) ps (singletonScenes ss) ≡ ss
  identity-scenes [] [] = refl
  identity-scenes (p ∷ ps) (s ∷ ss) = cong (s ∷_) (identity-scenes ps ss)

compOp-right-id : ∀ {bs c} (f : LayoutOp bs c) r ok (ss : Scenes bs) →
  assemble (compOp f (idForest bs)) r ok (singletonScenes ss) ≡ assemble f r ok ss
compOp-right-id f r ok ss = cong (assemble f r ok) (identity-scenes (placeSlots f r ok) ss)

private
  allInside : ∀ {bs r} (ps : All (Placed r) bs) →
    All (λ child → subRect child r ≡ true) (All.reduce box ps)
  allInside [] = []
  allInside (p ∷ ps) = contained p ∷ allInside ps

tree-contained : ∀ {bs c} (f : LayoutOp bs c) r ok →
  All (λ child → subRect child r ≡ true) (All.reduce box (placeSlots f r ok))
tree-contained f r ok = allInside (placeSlots f r ok)

leafOp : ∀ {sz M} → (Rect → Scene M) → LayoutOp [] (slotColor sz M)
leafOp render = layout (λ _ _ → []) (λ r _ _ → render r)

emptyOp : (sz : Size) → LayoutOp [] (slotColor sz ⊥)
emptyOp sz = leafOp (λ _ → empty)

panelOp : (sz : Size) → VisualStyle → LayoutOp [] (slotColor sz ⊥)
panelOp sz style = leafOp (decorRect style)

buttonOp : ∀ {M} (sz : Size) → String → Colour → M → LayoutOp [] (slotColor sz M)
buttonOp sz text colour msg = leafOp (λ r → over (decorRect (label text (rgb 245 247 250)) r) (hitRect msg colour r))

mapMsgOp : ∀ {sz A B} → (A → B) → LayoutOp (slotColor sz A ∷ []) (slotColor sz B)
mapMsgOp f = layout (λ r ok → placed r ok (sameEdges r) ∷ []) (λ { _ _ (s ∷ []) → mapScene f s })

-- The viewport origin is fixed under zoom. Children use their allocated
-- coordinates. The clip lives in device coordinates, outside the transform.
around : Rect → Affine2D → Affine2D
around r t = compAffine (affine 0 0 (rx r) (ry r))
  (compAffine t (affine 0 0 (Z.- rx r) (Z.- ry r)))
viewportOp : ∀ {sz M} → Affine2D → Colour → LayoutOp (slotColor sz M ∷ []) (slotColor sz M)
viewportOp t bg = layout (λ r ok → placed r ok (sameEdges r) ∷ [])
  (λ { r _ (s ∷ []) → clip r (over (transform (around r t) s) (occludeRect bg r)) })

private
  Le : ℕ → ℕ → Set
  Le m n = does (m N.≤? n) ≡ true

  cert : ∀ {m n} → m ≤ n → Le m n
  cert {m} {n} = dec-true (m N.≤? n)

  record Slice (minimum extent : ℕ) : Set where
    constructor slice
    field offset span : ℕ
          enough : Le minimum span
          within : Le (offset + span) extent
  open Slice

  whole : ∀ {m e} → Le m e → Slice m e
  whole {e = e} le = slice 0 e le (cert {e} NP.≤-refl)

  endpoint : ∀ origin i n e → i + n ≤ e →
    (origin Z.+ (+ i)) Z.+ (+ n) Z.≤ origin Z.+ (+ e)
  endpoint origin i n e le rewrite ZP.+-assoc origin (+ i) (+ n) | sym (ZP.pos-+-commute i n)
    = ZP.+-monoʳ-≤ origin (Z.+≤+ le)

  place : ∀ {c} (r : Rect) → Slice (w (minSize c)) (rw r) → Slice (h (minSize c)) (rh r) → Placed r c
  place {c} r u v = placed child (dec-true (fits? (minSize c) child) (witness (_ N.≤? _) (enough u) , witness (_ N.≤? _) (enough v)))
    (dec-true (edges? child r) (ZP.m≤m+n (offset u) , endpoint (rx r) (offset u) (span u) (rw r) (witness (_ N.≤? _) (within u)) ,
     ZP.m≤m+n (offset v) , endpoint (ry r) (offset v) (span v) (rh r) (witness (_ N.≤? _) (within v))))
    where child = rect (rx r Z.+ (+ offset u)) (ry r Z.+ (+ offset v)) (span u) (span v)

  remainder : ∀ k m e → k + m ≤ e → m ≤ e ∸ k
  remainder k m e le = subst (_≤ e ∸ k) (NP.m+n∸m≡n k m) (NP.∸-monoˡ-≤ k le)

  leading : ∀ a gap b e → Le ((a + gap) + b) e → Slice a e
  leading a gap b e ok = slice 0 a (cert {a} NP.≤-refl) (cert (NP.≤-trans (NP.m≤m+n a gap)
    (NP.≤-trans (NP.m≤m+n _ b) (witness (_ N.≤? e) ok))))

  trailing : ∀ k b e → Le (k + b) e → Slice b e
  trailing k b e ok = slice k (e ∸ k) (cert (remainder k b e le))
    (cert (NP.≤-reflexive (NP.m+[n∸m]≡n (NP.≤-trans (NP.m≤m+n k b) le))))
    where le = witness ((k + b) N.≤? e) ok

  inset : ∀ p m e → Le ((p + p) + m) e → Slice m e
  inset p m e ok = slice p (e ∸ (p + p)) (cert (remainder (p + p) m e le))
    (cert (NP.≤-trans (NP.+-monoˡ-≤ _ (NP.m≤m+n p p))
      (NP.≤-reflexive (NP.m+[n∸m]≡n (NP.≤-trans (NP.m≤m+n (p + p) m) le)))))
    where le = witness (((p + p) + m) N.≤? e) ok

addPad : ℕ → Size → Size
addPad p s = size ((p + p) + w s) ((p + p) + h s)

padOp : ∀ {sz M} (pad : ℕ) → LayoutOp (slotColor sz M ∷ []) (slotColor (addPad pad sz) M)
padOp {sz} {M} p = layout (λ r ok → child r ok ∷ []) (λ { r ok (s ∷ []) → clip (box (child r ok)) s })
  where
    child : ∀ r → Fits (addPad p sz) r ≡ true → Placed r (slotColor sz M)
    child r ok = let u , v = witness (fits? (addPad p sz) r) ok in
      place r (inset p (w sz) (rw r) (cert u)) (inset p (h sz) (rh r) (cert v))

hjoinColor vjoinColor : ℕ → SlotColor → SlotColor → SlotColor
hjoinColor gap (slotColor a A) (slotColor b B) =
  slotColor (size ((w a + gap) + w b) (h a ⊔ h b)) (A ⊎ B)
vjoinColor gap (slotColor a A) (slotColor b B) =
  slotColor (size (w a ⊔ w b) ((h a + gap) + h b)) (A ⊎ B)

zjoinColor : SlotColor → SlotColor → SlotColor
zjoinColor (slotColor a A) (slotColor b B) = slotColor (size (w a ⊔ w b) (h a ⊔ h b)) (A ⊎ B)

private
  binary : ∀ {a b sz} → ((r : Rect) → Fits sz r ≡ true → Placed r a × Placed r b) →
           LayoutOp (a ∷ b ∷ []) (slotColor sz (Msg a ⊎ Msg b))
  binary boxes = layout (λ r ok → let p , q = boxes r ok in p ∷ q ∷ [])
    (λ { r ok (f ∷ b ∷ []) → let p , q = boxes r ok in
      over (clip (box p) (mapScene inj₁ f)) (clip (box q) (mapScene inj₂ b)) })

hsplitOp : ∀ {a b} (gap : ℕ) → LayoutOp (a ∷ b ∷ []) (hjoinColor gap a b)
hsplitOp {slotColor a A} {slotColor b B} gap = binary λ r ok →
  let width , height = witness (fits? (size ((w a + gap) + w b) (h a ⊔ h b)) r) ok in
  place r (leading (w a) gap (w b) (rw r) (cert width)) (whole (cert (NP.≤-trans (NP.m≤m⊔n (h a) (h b)) height))) ,
  place r (trailing (w a + gap) (w b) (rw r) (cert width)) (whole (cert (NP.≤-trans (NP.m≤n⊔m (h a) (h b)) height)))

vsplitOp : ∀ {a b} (gap : ℕ) → LayoutOp (a ∷ b ∷ []) (vjoinColor gap a b)
vsplitOp {slotColor a A} {slotColor b B} gap = binary λ r ok →
  let width , height = witness (fits? (size (w a ⊔ w b) ((h a + gap) + h b)) r) ok in
  place r (whole (cert (NP.≤-trans (NP.m≤m⊔n (w a) (w b)) width))) (leading (h a) gap (h b) (rh r) (cert height)) ,
  place r (whole (cert (NP.≤-trans (NP.m≤n⊔m (w a) (w b)) width))) (trailing (h a + gap) (h b) (rh r) (cert height))

zstackOp : ∀ {a b} → LayoutOp (a ∷ b ∷ []) (zjoinColor a b)
zstackOp {slotColor a A} {slotColor b B} = binary λ r ok →
  let width , height = witness (fits? (size (w a ⊔ w b) (h a ⊔ h b)) r) ok in
  placed r (dec-true (fits? a r) (NP.≤-trans (NP.m≤m⊔n (w a) (w b)) width ,
                                  NP.≤-trans (NP.m≤m⊔n (h a) (h b)) height)) (sameEdges r) ,
  placed r (dec-true (fits? b r) (NP.≤-trans (NP.m≤n⊔m (w a) (w b)) width ,
                                  NP.≤-trans (NP.m≤n⊔m (h a) (h b)) height)) (sameEdges r)

private
  gap-separated : ∀ x n gap → (x Z.+ (+ 0)) Z.+ (+ n) Z.≤ x Z.+ (+ (n + gap))
  gap-separated x n gap rewrite ZP.+-identityʳ x = ZP.+-monoʳ-≤ x (Z.+≤+ (NP.m≤m+n n gap))

siblingsApart : ∀ {a b r} → All (Placed r) (a ∷ b ∷ []) → Set
siblingsApart (p ∷ q ∷ []) = disjointRect (box p) (box q) ≡ true

hsplitOp-disjoint : ∀ {a b} gap r ok → siblingsApart (placeSlots (hsplitOp {a} {b} gap) r ok)
hsplitOp-disjoint {a} {b} gap r ok = let ps = placeSlots (hsplitOp {a} {b} gap) r ok in
  dec-true (separate? (box (All.head ps)) (box (All.head (All.tail ps))))
  (inj₂ (inj₂ (inj₁ (gap-separated (rx r) (w (minSize a)) gap))))

vsplitOp-disjoint : ∀ {a b} gap r ok → siblingsApart (placeSlots (vsplitOp {a} {b} gap) r ok)
vsplitOp-disjoint {a} {b} gap r ok = let ps = placeSlots (vsplitOp {a} {b} gap) r ok in
  dec-true (separate? (box (All.head ps)) (box (All.head (All.tail ps))))
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (gap-separated (ry r) (h (minSize a)) gap))))))

record Widget (M : Set) : Set₁ where
  constructor widget
  field minimum : Size
        rootOp : LayoutOp [] (slotColor minimum M)
open Widget public

private
  renderAt : ∀ {M} → Widget M → Rect → Scene M
  renderAt (widget sz f) r with fits? sz r
  ... | yes ok = assemble f r (dec-true (fits? sz r) ok) []
  ... | no _ = assemble f large (dec-true (fits? sz large)
               (NP.m≤m⊔n (w sz) (rw r) , NP.m≤m⊔n (h sz) (rh r))) []
    where large = rect (rx r) (ry r) (w sz ⊔ rw r) (h sz ⊔ rh r)

renderWidget : ∀ {M} → Widget M → Rect → Scene M
renderWidget u r = clip r (renderAt u r)

root-outside : ∀ {M} (u : Widget M) r q → inRectQ q r ≡ false → hitTest (renderWidget u r) q ≡ nothing
root-outside u r q outside rewrite outside = refl

data WebEvent (E M : Set) : Set where
  uiMsg : M → WebEvent E M
  keyInput : Key → WebEvent E M
  panZoom : ℤ → ℤ → ℕ → ℕ → WebEvent E M
  resized : Size → WebEvent E M
  timerFired : E → WebEvent E M

record WebUpdate (S E : Set) : Set where
  constructor webUpdate
  field next : S
        timerEdits : List (Term.TimerEdit E)
open WebUpdate public

record WebProgram (S E M : Set) : Set₁ where
  constructor webProgram
  field view : S → Widget M
        update : WebEvent E M → S → WebUpdate S E
open WebProgram public

data HostInput : Set where
  hostClick : ℤ → ℤ → HostInput
  hostPanZoom : ℤ → ℤ → ℕ → ℕ → HostInput
  hostKey : Key → HostInput
  hostResize : ℕ → ℕ → HostInput
  hostTickMs : ℕ → HostInput

record WebHost (S E : Set) : Set where
  constructor host
  field viewport : Rect
        machine : TimedMachine S E
open WebHost public

clockDue : ∀ {S E} → ℕ → TimedMachine S E → Bool
clockDue zero m = false
clockDue (suc n) m with Term.timers m
... | [] = false
... | t ∷ ts = Term.deadline t N.≤ᵇ (Term.now m + suc n)

private
  effectOf : ∀ {S E} → WebUpdate S E → Term.Effect S E
  effectOf u = Term.effect (next u) Term.emptyObs (timerEdits u)

  clockHandler : ∀ {S E M} → WebProgram S E M → Term.Handler S E
  clockHandler p (Term.timeout e) s = effectOf (update p (timerFired e) s)
  clockHandler p (Term.input _) s = Term.effect s Term.emptyObs []

  -- Inputs do not consume time. Skip idle stretches, then delegate the
  -- deadline tick (including ties and timer edits) to the terminal machine.
  -- Each visited deadline consumes at least one of the supplied milliseconds.
  advanceTo : ∀ {S E} → Term.Handler S E → ℕ → ℕ → TimedMachine S E → TimedMachine S E
  advanceTo handler zero end m = record m { now = end }
  advanceTo handler (suc fuel) end m with Term.timers m
  ... | [] = record m { now = end }
  ... | t ∷ ts with (suc (Term.now m) ⊔ Term.deadline t) N.≤ᵇ end
  ...   | false = record m { now = end }
  ...   | true = advanceTo handler fuel end (Term.advance 1 handler (record m
                   { now = (suc (Term.now m) ⊔ Term.deadline t) ∸ 1 }))

  sendEvent : ∀ {S E M} → WebProgram S E M → WebEvent E M → WebHost S E → WebHost S E
  sendEvent p e (host vp m) = host vp (Term.applyEffect (effectOf (update p e (Term.state m))) m)

hostScene : ∀ {S E M} → WebProgram S E M → WebHost S E → Scene M
hostScene p (host vp m) = renderWidget (view p (Term.state m)) vp

stepWebHost : ∀ {S E M} → WebProgram S E M → HostInput → WebHost S E → WebHost S E
stepWebHost p (hostClick x y) m with hitTest (hostScene p m) (fromPixel (pt x y))
... | nothing = m
... | just a = sendEvent p (uiMsg a) m
stepWebHost p (hostKey k) m = sendEvent p (keyInput k) m
stepWebHost p (hostPanZoom x y n d) m = sendEvent p (panZoom x y n d) m
stepWebHost p (hostResize w h) (host vp m) =
  sendEvent p (resized (size w h)) (host (rect (rx vp) (ry vp) w h) m)
stepWebHost p (hostTickMs n) (host vp m) with clockDue n m
... | false = host vp (record m { now = Term.now m + n })
... | true = host vp (advanceTo (clockHandler p) n (Term.now m + n) m)

hostDraw : ∀ {S E M} → WebProgram S E M → WebHost S E → List DrawCmd
hostDraw p m = compileDraw (hostScene p m)

idle-draw : ∀ {S E M} (p : WebProgram S E M) n live → clockDue n (machine live) ≡ false →
  hostDraw p (stepWebHost p (hostTickMs n) live) ≡ hostDraw p live
idle-draw p n (host vp m) quiet rewrite quiet = refl

click-miss : ∀ {S E M} (p : WebProgram S E M) m x y →
  hitTest (hostScene p m) (fromPixel (pt x y)) ≡ nothing → stepWebHost p (hostClick x y) m ≡ m
click-miss p m x y eq rewrite eq = refl

click-outside : ∀ {S E M} (p : WebProgram S E M) m x y →
  inRect (pt x y) (viewport m) ≡ false → stepWebHost p (hostClick x y) m ≡ m
click-outside p (host vp m) x y eq = click-miss p (host vp m) x y (root-outside (view p (Term.state m)) vp (fromPixel (pt x y)) eq)

click-blocked : ∀ {S E M} (p : WebProgram S E M) m x y →
  route (hostScene p m) (fromPixel (pt x y)) ≡ blocked → stepWebHost p (hostClick x y) m ≡ m
click-blocked p m x y eq = click-miss p m x y (cong (λ v → resolve v nothing) eq)
