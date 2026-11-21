module Gen.T0.Gron where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

data Atom : Set where
  null    : Atom
  boolean : Bool → Atom
  number  : String → Atom
  text    : String → Atom

data Value : Set where
  scalar : Atom → Value
  array  : List Value → Value
  object : List (String × Value) → Value

data Segment : Set where
  property : String → Segment
  index    : ℕ → Segment

data Payload : Set where
  atom                   : Atom → Payload
  arrayMark objectMark   : Payload

record Statement : Set where
  constructor assignment
  field
    path : List Segment
    rhs  : Payload

data Failure : Set where
  noStatements arrayConflict objectConflict : Failure

contents : Payload → Value
contents (atom a) = scalar a
contents arrayMark = array []
contents objectMark = object []

postulate
  flatten     : List Segment → Value → List Statement
  flattenFrom : List Segment → ℕ → List Value → List Statement
  flattenKeys : List Segment → List (String × Value) → List Statement

  flattenScalar : ∀ p a →
    flatten p (scalar a) ≡ assignment p (atom a) ∷ []

  flattenArray : ∀ p xs →
    flatten p (array xs) ≡ assignment p arrayMark ∷ flattenFrom p 0 xs

  flattenObject : ∀ p xs →
    flatten p (object xs) ≡ assignment p objectMark ∷ flattenKeys p xs

  flattenFromEmpty : ∀ p i → flattenFrom p i [] ≡ []

  flattenFromNext : ∀ p i v vs →
    flattenFrom p i (v ∷ vs) ≡
      flatten (p ++ (index i ∷ [])) v ++ flattenFrom p (suc i) vs

  flattenKeysEmpty : ∀ p → flattenKeys p [] ≡ []

  flattenKeysNext : ∀ p k v vs →
    flattenKeys p ((k , v) ∷ vs) ≡
      flatten (p ++ (property k ∷ [])) v ++ flattenKeys p vs

postulate
  graft : List Segment → Value → Value

  graftRoot : ∀ v → graft [] v ≡ v

  graftProperty : ∀ k p v →
    graft (property k ∷ p) v ≡ object ((k , graft p v) ∷ [])

  graftIndex : ∀ i p v →
    graft (index i ∷ p) v ≡ array (replicate i (scalar null) ++ (graft p v ∷ []))

postulate
  overlay        : Value → Value → Failure ⊎ Value
  overlayCell    : Value → Value → Failure ⊎ Value
  overlayCells   : List Value → List Value → Failure ⊎ List Value
  overlayMembers : List (String × Value) → List (String × Value) → Failure ⊎ List (String × Value)

  replaceScalar : ∀ a v → overlay (scalar a) v ≡ inj₂ v

  arrayWithScalar : ∀ xs a → overlay (array xs) (scalar a) ≡ inj₁ arrayConflict
  arrayWithObject : ∀ xs ys → overlay (array xs) (object ys) ≡ inj₁ arrayConflict
  objectWithScalar : ∀ xs a → overlay (object xs) (scalar a) ≡ inj₁ objectConflict
  objectWithArray : ∀ xs ys → overlay (object xs) (array ys) ≡ inj₁ objectConflict

  overlayArrays : ∀ xs ys zs →
    overlayCells xs ys ≡ inj₂ zs →
    overlay (array xs) (array ys) ≡ inj₂ (array zs)

  overlayArraysConflict : ∀ xs ys e →
    overlayCells xs ys ≡ inj₁ e →
    overlay (array xs) (array ys) ≡ inj₁ e

  overlayObjects : ∀ xs ys zs →
    overlayMembers xs ys ≡ inj₂ zs →
    overlay (object xs) (object ys) ≡ inj₂ (object zs)

  overlayObjectsConflict : ∀ xs ys e →
    overlayMembers xs ys ≡ inj₁ e →
    overlay (object xs) (object ys) ≡ inj₁ e

  nullCell : ∀ v → overlayCell v (scalar null) ≡ inj₂ v

  assignedCell : ∀ x y → y ≢ scalar null → overlayCell x y ≡ overlay x y

  cellsLeftEmpty : ∀ ys → overlayCells [] ys ≡ inj₂ ys
  cellsRightEmpty : ∀ xs → overlayCells xs [] ≡ inj₂ xs

  cellsNext : ∀ x xs y ys v vs →
    overlayCell x y ≡ inj₂ v →
    overlayCells xs ys ≡ inj₂ vs →
    overlayCells (x ∷ xs) (y ∷ ys) ≡ inj₂ (v ∷ vs)

  cellsHeadConflict : ∀ x xs y ys e →
    overlayCell x y ≡ inj₁ e →
    overlayCells (x ∷ xs) (y ∷ ys) ≡ inj₁ e

  cellsTailConflict : ∀ x xs y ys v e →
    overlayCell x y ≡ inj₂ v →
    overlayCells xs ys ≡ inj₁ e →
    overlayCells (x ∷ xs) (y ∷ ys) ≡ inj₁ e

  membersRightEmpty : ∀ xs → overlayMembers xs [] ≡ inj₂ xs

  memberNew : ∀ k v →
    overlayMembers [] ((k , v) ∷ []) ≡ inj₂ ((k , v) ∷ [])

  memberSame : ∀ k x y xs v →
    overlay x y ≡ inj₂ v →
    overlayMembers ((k , x) ∷ xs) ((k , y) ∷ []) ≡ inj₂ ((k , v) ∷ xs)

  memberSameConflict : ∀ k x y xs e →
    overlay x y ≡ inj₁ e →
    overlayMembers ((k , x) ∷ xs) ((k , y) ∷ []) ≡ inj₁ e

  memberOther : ∀ j k x y xs zs →
    j ≢ k →
    overlayMembers xs ((k , y) ∷ []) ≡ inj₂ zs →
    overlayMembers ((j , x) ∷ xs) ((k , y) ∷ []) ≡ inj₂ ((j , x) ∷ zs)

  memberOtherConflict : ∀ j k x y xs e →
    j ≢ k →
    overlayMembers xs ((k , y) ∷ []) ≡ inj₁ e →
    overlayMembers ((j , x) ∷ xs) ((k , y) ∷ []) ≡ inj₁ e

  membersNext : ∀ xs k v ys zs →
    overlayMembers xs ((k , v) ∷ []) ≡ inj₂ zs →
    overlayMembers xs ((k , v) ∷ ys) ≡ overlayMembers zs ys

  membersConflict : ∀ xs k v ys e →
    overlayMembers xs ((k , v) ∷ []) ≡ inj₁ e →
    overlayMembers xs ((k , v) ∷ ys) ≡ inj₁ e

postulate
  resume      : Value → List Statement → Failure ⊎ Value
  reconstruct : List Statement → Failure ⊎ Value

  resumeEmpty : ∀ v → resume v [] ≡ inj₂ v

  resumeNext : ∀ v p r ss w →
    overlay v (graft p (contents r)) ≡ inj₂ w →
    resume v (assignment p r ∷ ss) ≡ resume w ss

  resumeConflict : ∀ v p r ss e →
    overlay v (graft p (contents r)) ≡ inj₁ e →
    resume v (assignment p r ∷ ss) ≡ inj₁ e

  reconstructEmpty : reconstruct [] ≡ inj₁ noStatements

  reconstructFirst : ∀ p r ss →
    reconstruct (assignment p r ∷ ss) ≡ resume (graft p (contents r)) ss

postulate
  observedNumber : flatten [] (scalar (number "-94.00e+2")) ≡
    assignment [] (atom (number "-94.00e+2")) ∷ []

  observedArray : flatten [] (array
    (scalar (number "1") ∷ object (("a" , scalar (number "2")) ∷ []) ∷ scalar (number "3") ∷ [])) ≡
    assignment [] arrayMark ∷
    assignment (index 0 ∷ []) (atom (number "1")) ∷
    assignment (index 1 ∷ []) objectMark ∷
    assignment (index 1 ∷ property "a" ∷ []) (atom (number "2")) ∷
    assignment (index 2 ∷ []) (atom (number "3")) ∷ []

  observedRootNull : reconstruct (assignment [] (atom null) ∷ []) ≡ inj₂ (scalar null)

  observedSparseReplacement : reconstruct
    (assignment (index 1 ∷ []) (atom (number "7")) ∷
     assignment (index 1 ∷ []) (atom (number "9")) ∷
     assignment (index 3 ∷ []) (atom (number "11")) ∷ []) ≡
    inj₂ (array (scalar null ∷ scalar (number "9") ∷ scalar null ∷ scalar (number "11") ∷ []))

  observedArrayNull : reconstruct
    (assignment (index 1 ∷ []) (atom (number "3")) ∷
     assignment (index 1 ∷ []) (atom null) ∷ []) ≡
    inj₂ (array (scalar null ∷ scalar (number "3") ∷ []))

  observedObjectNull : reconstruct
    (assignment (property "a" ∷ []) (atom (number "7")) ∷
     assignment (property "a" ∷ []) (atom null) ∷ []) ≡
    inj₂ (object (("a" , scalar null) ∷ []))

  observedArrayConflict : reconstruct
    (assignment (property "a" ∷ []) arrayMark ∷
     assignment (property "a" ∷ property "k" ∷ []) (atom (number "9")) ∷ []) ≡
    inj₁ arrayConflict

  observedObjectConflict : reconstruct
    (assignment (property "a" ∷ property "k" ∷ []) (atom (number "9")) ∷
     assignment (property "a" ∷ []) arrayMark ∷ []) ≡
    inj₁ objectConflict
