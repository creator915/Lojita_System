module Gen.T0.Gron where

  open import Data.Empty using (⊥-elim)
  open import Relation.Nullary using (yes; no)
  open import Data.Bool using (Bool)
  open import Data.List using (List; []; _∷_; _++_; replicate)
  open import Data.Nat using (ℕ; suc)
  open import Data.Product using (_×_; _,_)
  open import Data.String using (String; _≟_)
  open import Data.Sum using (_⊎_; inj₁; inj₂; map; [_,_]′)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)
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
  contents (atom a) = scalar a
  contents arrayMark = array []
  contents objectMark = object []
  flattenKeys : List Segment → List (String × Value) → List Statement
  flatten : List Segment → Value → List Statement
  flattenFrom : List Segment → ℕ → List Value → List Statement
  flattenKeys p [] = []
  flattenKeys p ((k , v) ∷ vs) = flatten (p ++ (property k ∷ [])) v ++ flattenKeys p vs
  flatten p (scalar a) = assignment p (atom a) ∷ []
  flatten p (array xs) = assignment p arrayMark ∷ flattenFrom p 0 xs
  flatten p (object xs) = assignment p objectMark ∷ flattenKeys p xs
  flattenFrom p i [] = []
  flattenFrom p i (v ∷ vs) = flatten (p ++ (index i ∷ [])) v ++ flattenFrom p (suc i) vs
  flattenScalar : (p : _) → (a : _) → flatten p (scalar a) ≡ (assignment p (atom a) ∷ [])
  flattenScalar p a = refl
  flattenArray : (p : _) → (xs : _) → flatten p (array xs) ≡ (assignment p arrayMark ∷ flattenFrom p 0 xs)
  flattenArray p xs = refl
  flattenObject : (p : _) → (xs : _) → flatten p (object xs) ≡ (assignment p objectMark ∷ flattenKeys p xs)
  flattenObject p xs = refl
  flattenFromEmpty : (p : _) → (i : _) → flattenFrom p i [] ≡ []
  flattenFromEmpty p i = refl
  flattenFromNext : (p : _) → (i : _) → (v : _) → (vs : _) → flattenFrom p i (v ∷ vs) ≡ (flatten (p ++ (index i ∷ [])) v ++ flattenFrom p (suc i) vs)
  flattenFromNext p i v vs = refl
  flattenKeysEmpty : (p : _) → flattenKeys p [] ≡ []
  flattenKeysEmpty p = refl
  flattenKeysNext : (p : _) → (k : _) → (v : _) → (vs : _) → flattenKeys p ((k , v) ∷ vs) ≡ (flatten (p ++ (property k ∷ [])) v ++ flattenKeys p vs)
  flattenKeysNext p k v vs = refl
  graft : List Segment → Value → Value
  graft [] v = v
  graft ((property k) ∷ p) v = object ((k , graft p v) ∷ [])
  graft ((index i) ∷ p) v = array (replicate i (scalar null) ++ (graft p v ∷ []))
  graftRoot : (v : _) → graft [] v ≡ v
  graftRoot v = refl
  graftProperty : (k : _) → (p : _) → (v : _) → graft (property k ∷ p) v ≡ object ((k , graft p v) ∷ [])
  graftProperty k p v = refl
  graftIndex : (i : _) → (p : _) → (v : _) → graft (index i ∷ p) v ≡ array (replicate i (scalar null) ++ (graft p v ∷ []))
  graftIndex i p v = refl
  private
    mapResult : {A B : Set} → (A → B) → (Failure ⊎ A) → Failure ⊎ B
    mapResult f = map (λ e → e) f
  private
    insertMember : String → Value → (Value → Failure ⊎ Value) → List (String × Value) → Failure ⊎ List (String × Value)
    insertMember k y merge [] = inj₂ ((k , y) ∷ [])
    insertMember k y merge ((j , x) ∷ xs) with (j ≟ k)
    insertMember k y merge ((j , x) ∷ xs) | (yes _) = mapResult (λ v → (k , v) ∷ xs) (merge x)
    insertMember k y merge ((j , x) ∷ xs) | (no _) = mapResult (λ zs → (j , x) ∷ zs) (insertMember k y merge xs)
  overlayCells : List Value → List Value → Failure ⊎ List Value
  overlayMembers : List (String × Value) → List (String × Value) → Failure ⊎ List (String × Value)
  overlay : Value → Value → Failure ⊎ Value
  overlayCell : Value → Value → Failure ⊎ Value
  overlayCells [] ys = inj₂ ys
  overlayCells (x ∷ xs) [] = inj₂ (x ∷ xs)
  overlayCells (x ∷ xs) (y ∷ ys) = [_,_]′ inj₁ (λ v → mapResult (λ vs → v ∷ vs) (overlayCells xs ys)) (overlayCell x y)
  overlayMembers xs [] = inj₂ xs
  overlayMembers xs ((k , y) ∷ []) = insertMember k y (λ x → overlay x y) xs
  overlayMembers xs ((k , y) ∷ (z ∷ zs)) = [_,_]′ inj₁ (λ ws → overlayMembers ws (z ∷ zs)) (insertMember k y (λ x → overlay x y) xs)
  overlay (scalar a) v = inj₂ v
  overlay (array xs) (scalar a) = inj₁ arrayConflict
  overlay (array xs) (array ys) = mapResult array (overlayCells xs ys)
  overlay (array xs) (object ys) = inj₁ arrayConflict
  overlay (object xs) (scalar a) = inj₁ objectConflict
  overlay (object xs) (array ys) = inj₁ objectConflict
  overlay (object xs) (object ys) = mapResult object (overlayMembers xs ys)
  overlayCell x (scalar null) = inj₂ x
  overlayCell x y = overlay x y
  replaceScalar : (a : _) → (v : _) → overlay (scalar a) v ≡ inj₂ v
  replaceScalar a v = refl
  arrayWithScalar : (xs : _) → (a : _) → overlay (array xs) (scalar a) ≡ inj₁ arrayConflict
  arrayWithScalar xs a = refl
  arrayWithObject : (xs : _) → (ys : _) → overlay (array xs) (object ys) ≡ inj₁ arrayConflict
  arrayWithObject xs ys = refl
  objectWithScalar : (xs : _) → (a : _) → overlay (object xs) (scalar a) ≡ inj₁ objectConflict
  objectWithScalar xs a = refl
  objectWithArray : (xs : _) → (ys : _) → overlay (object xs) (array ys) ≡ inj₁ objectConflict
  objectWithArray xs ys = refl
  overlayArrays : (xs : _) → (ys : _) → (zs : _) → (overlayCells xs ys ≡ inj₂ zs) → overlay (array xs) (array ys) ≡ inj₂ (array zs)
  overlayArrays xs ys zs merged = cong (mapResult array) merged
  overlayArraysConflict : (xs : _) → (ys : _) → (e : _) → (overlayCells xs ys ≡ inj₁ e) → overlay (array xs) (array ys) ≡ inj₁ e
  overlayArraysConflict xs ys e merged = cong (mapResult array) merged
  overlayObjects : (xs : _) → (ys : _) → (zs : _) → (overlayMembers xs ys ≡ inj₂ zs) → overlay (object xs) (object ys) ≡ inj₂ (object zs)
  overlayObjects xs ys zs merged = cong (mapResult object) merged
  overlayObjectsConflict : (xs : _) → (ys : _) → (e : _) → (overlayMembers xs ys ≡ inj₁ e) → overlay (object xs) (object ys) ≡ inj₁ e
  overlayObjectsConflict xs ys e merged = cong (mapResult object) merged
  nullCell : (v : _) → overlayCell v (scalar null) ≡ inj₂ v
  nullCell v = refl
  assignedCell : (x : _) → (y : _) → (y ≢ scalar null) → overlayCell x y ≡ overlay x y
  assignedCell x (scalar null) different = ⊥-elim (different refl)
  assignedCell x (scalar (boolean b)) different = refl
  assignedCell x (scalar (number n)) different = refl
  assignedCell x (scalar (text s)) different = refl
  assignedCell x (array ys) different = refl
  assignedCell x (object ys) different = refl
  cellsLeftEmpty : (ys : _) → overlayCells [] ys ≡ inj₂ ys
  cellsLeftEmpty ys = refl
  cellsRightEmpty : (xs : _) → overlayCells xs [] ≡ inj₂ xs
  cellsRightEmpty [] = refl
  cellsRightEmpty (x ∷ xs) = refl
  cellsNext : (x : _) → (xs : _) → (y : _) → (ys : _) → (v : _) → (vs : _) → (overlayCell x y ≡ inj₂ v) → (overlayCells xs ys ≡ inj₂ vs) → overlayCells (x ∷ xs) (y ∷ ys) ≡ inj₂ (v ∷ vs)
  cellsNext x xs y ys v vs headResult tailResult = trans (cong ([ inj₁ , (λ w → mapResult (λ ws → w ∷ ws) (overlayCells xs ys)) ]′) headResult) (cong (mapResult (λ ws → v ∷ ws)) tailResult)
  cellsHeadConflict : (x : _) → (xs : _) → (y : _) → (ys : _) → (e : _) → (overlayCell x y ≡ inj₁ e) → overlayCells (x ∷ xs) (y ∷ ys) ≡ inj₁ e
  cellsHeadConflict x xs y ys e headResult = cong ([ inj₁ , (λ w → mapResult (λ ws → w ∷ ws) (overlayCells xs ys)) ]′) headResult
  cellsTailConflict : (x : _) → (xs : _) → (y : _) → (ys : _) → (v : _) → (e : _) → (overlayCell x y ≡ inj₂ v) → (overlayCells xs ys ≡ inj₁ e) → overlayCells (x ∷ xs) (y ∷ ys) ≡ inj₁ e
  cellsTailConflict x xs y ys v e headResult tailResult = trans (cong ([ inj₁ , (λ w → mapResult (λ ws → w ∷ ws) (overlayCells xs ys)) ]′) headResult) (cong (mapResult (λ ws → v ∷ ws)) tailResult)
  membersRightEmpty : (xs : _) → overlayMembers xs [] ≡ inj₂ xs
  membersRightEmpty xs = refl
  memberNew : (k : _) → (v : _) → overlayMembers [] ((k , v) ∷ []) ≡ inj₂ ((k , v) ∷ [])
  memberNew k v = refl
  memberSame : (k : _) → (x : _) → (y : _) → (xs : _) → (v : _) → (overlay x y ≡ inj₂ v) → overlayMembers ((k , x) ∷ xs) ((k , y) ∷ []) ≡ inj₂ ((k , v) ∷ xs)
  memberSame k x y xs v merged with (k ≟ k)
  memberSame k x y xs v merged | (yes _) = cong (mapResult (λ w → (k , w) ∷ xs)) merged
  memberSame k x y xs v merged | (no different) = ⊥-elim (different refl)
  memberSameConflict : (k : _) → (x : _) → (y : _) → (xs : _) → (e : _) → (overlay x y ≡ inj₁ e) → overlayMembers ((k , x) ∷ xs) ((k , y) ∷ []) ≡ inj₁ e
  memberSameConflict k x y xs e merged with (k ≟ k)
  memberSameConflict k x y xs e merged | (yes _) = cong (mapResult (λ w → (k , w) ∷ xs)) merged
  memberSameConflict k x y xs e merged | (no different) = ⊥-elim (different refl)
  memberOther : (j : _) → (k : _) → (x : _) → (y : _) → (xs : _) → (zs : _) → (j ≢ k) → (overlayMembers xs ((k , y) ∷ []) ≡ inj₂ zs) → overlayMembers ((j , x) ∷ xs) ((k , y) ∷ []) ≡ inj₂ ((j , x) ∷ zs)
  memberOther j k x y xs zs different merged with (j ≟ k)
  memberOther j k x y xs zs different merged | (yes same) = ⊥-elim (different same)
  memberOther j k x y xs zs different merged | (no _) = cong (mapResult (λ ws → (j , x) ∷ ws)) merged
  memberOtherConflict : (j : _) → (k : _) → (x : _) → (y : _) → (xs : _) → (e : _) → (j ≢ k) → (overlayMembers xs ((k , y) ∷ []) ≡ inj₁ e) → overlayMembers ((j , x) ∷ xs) ((k , y) ∷ []) ≡ inj₁ e
  memberOtherConflict j k x y xs e different merged with (j ≟ k)
  memberOtherConflict j k x y xs e different merged | (yes same) = ⊥-elim (different same)
  memberOtherConflict j k x y xs e different merged | (no _) = cong (mapResult (λ ws → (j , x) ∷ ws)) merged
  membersNext : (xs : _) → (k : _) → (v : _) → (ys : _) → (zs : _) → (overlayMembers xs ((k , v) ∷ []) ≡ inj₂ zs) → overlayMembers xs ((k , v) ∷ ys) ≡ overlayMembers zs ys
  membersNext xs k v [] zs merged = merged
  membersNext xs k v (y ∷ ys) zs merged = cong ([ inj₁ , (λ ws → overlayMembers ws (y ∷ ys)) ]′) merged
  membersConflict : (xs : _) → (k : _) → (v : _) → (ys : _) → (e : _) → (overlayMembers xs ((k , v) ∷ []) ≡ inj₁ e) → overlayMembers xs ((k , v) ∷ ys) ≡ inj₁ e
  membersConflict xs k v [] e merged = merged
  membersConflict xs k v (y ∷ ys) e merged = cong ([ inj₁ , (λ ws → overlayMembers ws (y ∷ ys)) ]′) merged
  resume : Value → List Statement → Failure ⊎ Value
  resume v [] = inj₂ v
  resume v ((assignment p r) ∷ ss) = [_,_]′ inj₁ (λ w → resume w ss) (overlay v (graft p (contents r)))
  reconstruct : List Statement → Failure ⊎ Value
  reconstruct [] = inj₁ noStatements
  reconstruct ((assignment p r) ∷ ss) = resume (graft p (contents r)) ss
  resumeEmpty : (v : _) → resume v [] ≡ inj₂ v
  resumeEmpty v = refl
  resumeNext : (v : _) → (p : _) → (r : _) → (ss : _) → (w : _) → (overlay v (graft p (contents r)) ≡ inj₂ w) → resume v (assignment p r ∷ ss) ≡ resume w ss
  resumeNext v p r ss w merged = cong ([ inj₁ , (λ value → resume value ss) ]′) merged
  resumeConflict : (v : _) → (p : _) → (r : _) → (ss : _) → (e : _) → (overlay v (graft p (contents r)) ≡ inj₁ e) → resume v (assignment p r ∷ ss) ≡ inj₁ e
  resumeConflict v p r ss e merged = cong ([ inj₁ , (λ value → resume value ss) ]′) merged
  reconstructEmpty : reconstruct [] ≡ inj₁ noStatements
  reconstructEmpty = refl
  reconstructFirst : (p : _) → (r : _) → (ss : _) → reconstruct (assignment p r ∷ ss) ≡ resume (graft p (contents r)) ss
  reconstructFirst p r ss = refl
  observedNumber : flatten [] (scalar (number "-94.00e+2")) ≡ (assignment [] (atom (number "-94.00e+2")) ∷ [])
  observedNumber = refl
  observedArray : flatten [] (array (scalar (number "1") ∷ (object (("a" , scalar (number "2")) ∷ []) ∷ (scalar (number "3") ∷ [])))) ≡ (assignment [] arrayMark ∷ (assignment (index 0 ∷ []) (atom (number "1")) ∷ (assignment (index 1 ∷ []) objectMark ∷ (assignment (index 1 ∷ (property "a" ∷ [])) (atom (number "2")) ∷ (assignment (index 2 ∷ []) (atom (number "3")) ∷ [])))))
  observedArray = refl
  observedRootNull : reconstruct (assignment [] (atom null) ∷ []) ≡ inj₂ (scalar null)
  observedRootNull = refl
  observedSparseReplacement : reconstruct (assignment (index 1 ∷ []) (atom (number "7")) ∷ (assignment (index 1 ∷ []) (atom (number "9")) ∷ (assignment (index 3 ∷ []) (atom (number "11")) ∷ []))) ≡ inj₂ (array (scalar null ∷ (scalar (number "9") ∷ (scalar null ∷ (scalar (number "11") ∷ [])))))
  observedSparseReplacement = refl
  observedArrayNull : reconstruct (assignment (index 1 ∷ []) (atom (number "3")) ∷ (assignment (index 1 ∷ []) (atom null) ∷ [])) ≡ inj₂ (array (scalar null ∷ (scalar (number "3") ∷ [])))
  observedArrayNull = refl
  observedObjectNull : reconstruct (assignment (property "a" ∷ []) (atom (number "7")) ∷ (assignment (property "a" ∷ []) (atom null) ∷ [])) ≡ inj₂ (object (("a" , scalar null) ∷ []))
  observedObjectNull = refl
  observedArrayConflict : reconstruct (assignment (property "a" ∷ []) arrayMark ∷ (assignment (property "a" ∷ (property "k" ∷ [])) (atom (number "9")) ∷ [])) ≡ inj₁ arrayConflict
  observedArrayConflict = refl
  observedObjectConflict : reconstruct (assignment (property "a" ∷ (property "k" ∷ [])) (atom (number "9")) ∷ (assignment (property "a" ∷ []) arrayMark ∷ [])) ≡ inj₁ objectConflict
  observedObjectConflict = refl
