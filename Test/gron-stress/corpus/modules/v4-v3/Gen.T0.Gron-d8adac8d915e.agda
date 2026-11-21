module Gen.T0.Gron where

  open import Data.Bool using (Bool)
  open import Data.List using (List; []; _∷_; _++_; replicate)
  open import Data.Nat using (ℕ; suc)
  open import Data.Product using (_×_; _,_)
  open import Data.String using (String)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  data Atom : Set where
    null : Atom
    boolean : Bool → Atom
    number : String → Atom
    text : String → Atom
  data Value : Set where
    scalar : Atom → Value
    array : List Value → Value
    object : List (String × Value) → Value
  data Segment : Set where
    property : String → Segment
    index : ℕ → Segment
  data Payload : Set where
    atom : Atom → Payload
    arrayMark : Payload
    objectMark : Payload
  record Statement : Set where
    constructor assignment
    field
      path : List Segment
      rhs : Payload
  data Failure : Set where
    noStatements : Failure
    arrayConflict : Failure
    objectConflict : Failure
  contents : Payload → Value
  contents (Payload.atom a) = Value.scalar a
  contents Payload.arrayMark = Value.array []
  contents Payload.objectMark = Value.object []
  postulate
    flatten : List Segment → Value → List Statement
  postulate
    flattenFrom : List Segment → ℕ → List Value → List Statement
  postulate
    flattenKeys : List Segment → List (String × Value) → List Statement
  postulate
    flattenScalar : (p : _) → (a : _) → flatten p (Value.scalar a) ≡ (assignment p (Payload.atom a) ∷ [])
  postulate
    flattenArray : (p : _) → (xs : _) → flatten p (Value.array xs) ≡ (assignment p Payload.arrayMark ∷ flattenFrom p 0 xs)
  postulate
    flattenObject : (p : _) → (xs : _) → flatten p (Value.object xs) ≡ (assignment p Payload.objectMark ∷ flattenKeys p xs)
  postulate
    flattenFromEmpty : (p : _) → (i : _) → flattenFrom p i [] ≡ []
  postulate
    flattenFromNext : (p : _) → (i : _) → (v : _) → (vs : _) → flattenFrom p i (v ∷ vs) ≡ (flatten (p ++ (Segment.index i ∷ [])) v ++ flattenFrom p (suc i) vs)
  postulate
    flattenKeysEmpty : (p : _) → flattenKeys p [] ≡ []
  postulate
    flattenKeysNext : (p : _) → (k : _) → (v : _) → (vs : _) → flattenKeys p ((k , v) ∷ vs) ≡ (flatten (p ++ (Segment.property k ∷ [])) v ++ flattenKeys p vs)
  postulate
    graft : List Segment → Value → Value
  postulate
    graftRoot : (v : _) → graft [] v ≡ v
  postulate
    graftProperty : (k : _) → (p : _) → (v : _) → graft (Segment.property k ∷ p) v ≡ Value.object ((k , graft p v) ∷ [])
  postulate
    graftIndex : (i : _) → (p : _) → (v : _) → graft (Segment.index i ∷ p) v ≡ Value.array (replicate i (Value.scalar Atom.null) ++ (graft p v ∷ []))
  postulate
    overlay : Value → Value → Failure ⊎ Value
  postulate
    overlayCell : Value → Value → Failure ⊎ Value
  postulate
    overlayCells : List Value → List Value → Failure ⊎ List Value
  postulate
    overlayMembers : List (String × Value) → List (String × Value) → Failure ⊎ List (String × Value)
  postulate
    replaceScalar : (a : _) → (v : _) → overlay (Value.scalar a) v ≡ inj₂ v
  postulate
    arrayWithScalar : (xs : _) → (a : _) → overlay (Value.array xs) (Value.scalar a) ≡ inj₁ Failure.arrayConflict
  postulate
    arrayWithObject : (xs : _) → (ys : _) → overlay (Value.array xs) (Value.object ys) ≡ inj₁ Failure.arrayConflict
  postulate
    objectWithScalar : (xs : _) → (a : _) → overlay (Value.object xs) (Value.scalar a) ≡ inj₁ Failure.objectConflict
  postulate
    objectWithArray : (xs : _) → (ys : _) → overlay (Value.object xs) (Value.array ys) ≡ inj₁ Failure.objectConflict
  postulate
    overlayArrays : (xs : _) → (ys : _) → (zs : _) → (overlayCells xs ys ≡ inj₂ zs) → overlay (Value.array xs) (Value.array ys) ≡ inj₂ (Value.array zs)
  postulate
    overlayArraysConflict : (xs : _) → (ys : _) → (e : _) → (overlayCells xs ys ≡ inj₁ e) → overlay (Value.array xs) (Value.array ys) ≡ inj₁ e
  postulate
    overlayObjects : (xs : _) → (ys : _) → (zs : _) → (overlayMembers xs ys ≡ inj₂ zs) → overlay (Value.object xs) (Value.object ys) ≡ inj₂ (Value.object zs)
  postulate
    overlayObjectsConflict : (xs : _) → (ys : _) → (e : _) → (overlayMembers xs ys ≡ inj₁ e) → overlay (Value.object xs) (Value.object ys) ≡ inj₁ e
  postulate
    nullCell : (v : _) → overlayCell v (Value.scalar Atom.null) ≡ inj₂ v
  postulate
    assignedCell : (x : _) → (y : _) → (y ≢ Value.scalar Atom.null) → overlayCell x y ≡ overlay x y
  postulate
    cellsLeftEmpty : (ys : _) → overlayCells [] ys ≡ inj₂ ys
  postulate
    cellsRightEmpty : (xs : _) → overlayCells xs [] ≡ inj₂ xs
  postulate
    cellsNext : (x : _) → (xs : _) → (y : _) → (ys : _) → (v : _) → (vs : _) → (overlayCell x y ≡ inj₂ v) → (overlayCells xs ys ≡ inj₂ vs) → overlayCells (x ∷ xs) (y ∷ ys) ≡ inj₂ (v ∷ vs)
  postulate
    cellsHeadConflict : (x : _) → (xs : _) → (y : _) → (ys : _) → (e : _) → (overlayCell x y ≡ inj₁ e) → overlayCells (x ∷ xs) (y ∷ ys) ≡ inj₁ e
  postulate
    cellsTailConflict : (x : _) → (xs : _) → (y : _) → (ys : _) → (v : _) → (e : _) → (overlayCell x y ≡ inj₂ v) → (overlayCells xs ys ≡ inj₁ e) → overlayCells (x ∷ xs) (y ∷ ys) ≡ inj₁ e
  postulate
    membersRightEmpty : (xs : _) → overlayMembers xs [] ≡ inj₂ xs
  postulate
    memberNew : (k : _) → (v : _) → overlayMembers [] ((k , v) ∷ []) ≡ inj₂ ((k , v) ∷ [])
  postulate
    memberSame : (k : _) → (x : _) → (y : _) → (xs : _) → (v : _) → (overlay x y ≡ inj₂ v) → overlayMembers ((k , x) ∷ xs) ((k , y) ∷ []) ≡ inj₂ ((k , v) ∷ xs)
  postulate
    memberSameConflict : (k : _) → (x : _) → (y : _) → (xs : _) → (e : _) → (overlay x y ≡ inj₁ e) → overlayMembers ((k , x) ∷ xs) ((k , y) ∷ []) ≡ inj₁ e
  postulate
    memberOther : (j : _) → (k : _) → (x : _) → (y : _) → (xs : _) → (zs : _) → (j ≢ k) → (overlayMembers xs ((k , y) ∷ []) ≡ inj₂ zs) → overlayMembers ((j , x) ∷ xs) ((k , y) ∷ []) ≡ inj₂ ((j , x) ∷ zs)
  postulate
    memberOtherConflict : (j : _) → (k : _) → (x : _) → (y : _) → (xs : _) → (e : _) → (j ≢ k) → (overlayMembers xs ((k , y) ∷ []) ≡ inj₁ e) → overlayMembers ((j , x) ∷ xs) ((k , y) ∷ []) ≡ inj₁ e
  postulate
    membersNext : (xs : _) → (k : _) → (v : _) → (ys : _) → (zs : _) → (overlayMembers xs ((k , v) ∷ []) ≡ inj₂ zs) → overlayMembers xs ((k , v) ∷ ys) ≡ overlayMembers zs ys
  postulate
    membersConflict : (xs : _) → (k : _) → (v : _) → (ys : _) → (e : _) → (overlayMembers xs ((k , v) ∷ []) ≡ inj₁ e) → overlayMembers xs ((k , v) ∷ ys) ≡ inj₁ e
  postulate
    resume : Value → List Statement → Failure ⊎ Value
  postulate
    reconstruct : List Statement → Failure ⊎ Value
  postulate
    resumeEmpty : (v : _) → resume v [] ≡ inj₂ v
  postulate
    resumeNext : (v : _) → (p : _) → (r : _) → (ss : _) → (w : _) → (overlay v (graft p (contents r)) ≡ inj₂ w) → resume v (assignment p r ∷ ss) ≡ resume w ss
  postulate
    resumeConflict : (v : _) → (p : _) → (r : _) → (ss : _) → (e : _) → (overlay v (graft p (contents r)) ≡ inj₁ e) → resume v (assignment p r ∷ ss) ≡ inj₁ e
  postulate
    reconstructEmpty : reconstruct [] ≡ inj₁ Failure.noStatements
  postulate
    reconstructFirst : (p : _) → (r : _) → (ss : _) → reconstruct (assignment p r ∷ ss) ≡ resume (graft p (contents r)) ss
  postulate
    observedNumber : flatten [] (Value.scalar (Atom.number "-94.00e+2")) ≡ (assignment [] (Payload.atom (Atom.number "-94.00e+2")) ∷ [])
  postulate
    observedArray : flatten [] (Value.array (Value.scalar (Atom.number "1") ∷ (Value.object (("a" , Value.scalar (Atom.number "2")) ∷ []) ∷ (Value.scalar (Atom.number "3") ∷ [])))) ≡ (assignment [] Payload.arrayMark ∷ (assignment (Segment.index 0 ∷ []) (Payload.atom (Atom.number "1")) ∷ (assignment (Segment.index 1 ∷ []) Payload.objectMark ∷ (assignment (Segment.index 1 ∷ (Segment.property "a" ∷ [])) (Payload.atom (Atom.number "2")) ∷ (assignment (Segment.index 2 ∷ []) (Payload.atom (Atom.number "3")) ∷ [])))))
  postulate
    observedRootNull : reconstruct (assignment [] (Payload.atom Atom.null) ∷ []) ≡ inj₂ (Value.scalar Atom.null)
  postulate
    observedSparseReplacement : reconstruct (assignment (Segment.index 1 ∷ []) (Payload.atom (Atom.number "7")) ∷ (assignment (Segment.index 1 ∷ []) (Payload.atom (Atom.number "9")) ∷ (assignment (Segment.index 3 ∷ []) (Payload.atom (Atom.number "11")) ∷ []))) ≡ inj₂ (Value.array (Value.scalar Atom.null ∷ (Value.scalar (Atom.number "9") ∷ (Value.scalar Atom.null ∷ (Value.scalar (Atom.number "11") ∷ [])))))
  postulate
    observedArrayNull : reconstruct (assignment (Segment.index 1 ∷ []) (Payload.atom (Atom.number "3")) ∷ (assignment (Segment.index 1 ∷ []) (Payload.atom Atom.null) ∷ [])) ≡ inj₂ (Value.array (Value.scalar Atom.null ∷ (Value.scalar (Atom.number "3") ∷ [])))
  postulate
    observedObjectNull : reconstruct (assignment (Segment.property "a" ∷ []) (Payload.atom (Atom.number "7")) ∷ (assignment (Segment.property "a" ∷ []) (Payload.atom Atom.null) ∷ [])) ≡ inj₂ (Value.object (("a" , Value.scalar Atom.null) ∷ []))
  postulate
    observedArrayConflict : reconstruct (assignment (Segment.property "a" ∷ []) Payload.arrayMark ∷ (assignment (Segment.property "a" ∷ (Segment.property "k" ∷ [])) (Payload.atom (Atom.number "9")) ∷ [])) ≡ inj₁ Failure.arrayConflict
  postulate
    observedObjectConflict : reconstruct (assignment (Segment.property "a" ∷ (Segment.property "k" ∷ [])) (Payload.atom (Atom.number "9")) ∷ (assignment (Segment.property "a" ∷ []) Payload.arrayMark ∷ [])) ≡ inj₁ Failure.objectConflict
