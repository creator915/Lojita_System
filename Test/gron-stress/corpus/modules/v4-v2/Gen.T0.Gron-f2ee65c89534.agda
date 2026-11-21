module Gen.T0.Gron where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)
open import Relation.Nullary using (Dec; yes; no)

data Atom : Set where
  null : Atom
  truth : Bool → Atom
  numeral : String → Atom
  text : String → Atom

data Value : Set where
  scalar : Atom → Value
  object : List (String × Value) → Value
  array : List Value → Value

data Segment : Set where
  key : String → Segment
  index : ℕ → Segment

data Cell : Set where
  leaf : Atom → Cell
  objectCell : Cell
  arrayCell : Cell

data Row : Set where
  row : List Segment → Cell → Row

data Mode : Set where
  forward : Mode
  reverse : Mode
  values : Mode

data MergeFault : Set where
  objectConflict : MergeFault
  arrayConflict : MergeFault

chooseMode : (ungron valueOnly : Bool) → Mode
chooseMode true _ = reverse
chooseMode false true = values
chooseMode false false = forward

reverse-selected : (v : _) → chooseMode true v ≡ reverse
reverse-selected v = refl

values-selected : chooseMode false true ≡ values
values-selected = refl

forward-selected : chooseMode false false ≡ forward
forward-selected = refl

useColor : (stdoutTTY forceColor monochrome : Bool) → Bool
useColor tty true _ = true
useColor tty false true = false
useColor tty false false = tty

force-color : (tty : _) → (mono : _) → useColor tty true mono ≡ true
force-color tty mono = refl

force-monochrome : (tty : _) → useColor tty false true ≡ false
force-monochrome tty = refl

auto-color : (tty : _) → useColor tty false false ≡ tty
auto-color tty = refl

mutual
  rowsAt : List Segment → Value → List Row
  rowsAt p (scalar a) = row p (leaf a) ∷ []
  rowsAt p (object fs) = row p objectCell ∷ fieldRowsAt p fs
  rowsAt p (array xs) = row p arrayCell ∷ itemRowsAt p zero xs

  fieldRowsAt : List Segment → List (String × Value) → List Row
  fieldRowsAt p [] = []
  fieldRowsAt p ((k , v) ∷ fs) =
    rowsAt (p ++ (key k ∷ [])) v ++ fieldRowsAt p fs

  itemRowsAt : List Segment → ℕ → List Value → List Row
  itemRowsAt p i [] = []
  itemRowsAt p i (v ∷ xs) =
    rowsAt (p ++ (index i ∷ [])) v ++ itemRowsAt p (suc i) xs

rows-scalar : (p : _) → (a : _) → rowsAt p (scalar a) ≡ (row p (leaf a) ∷ [])
rows-scalar p a = refl

rows-object : (p : _) → (fs : _) → rowsAt p (object fs) ≡ (row p objectCell ∷ fieldRowsAt p fs)
rows-object p fs = refl

rows-array : (p : _) → (xs : _) → rowsAt p (array xs) ≡ (row p arrayCell ∷ itemRowsAt p zero xs)
rows-array p xs = refl

rows-no-fields : (p : _) → fieldRowsAt p [] ≡ []
rows-no-fields p = refl

rows-field : (p : _) → (k : _) → (v : _) → (fs : _) → fieldRowsAt p ((k , v) ∷ fs) ≡ (rowsAt (p ++ (key k ∷ [])) v ++ fieldRowsAt p fs)
rows-field p k v fs = refl

rows-no-items : (p : _) → (i : _) → itemRowsAt p i [] ≡ []
rows-no-items p i = refl

rows-item : (p : _) → (i : _) → (v : _) → (xs : _) → itemRowsAt p i (v ∷ xs) ≡ (rowsAt (p ++ (index i ∷ [])) v ++ itemRowsAt p (suc i) xs)
rows-item p i v xs = refl

valuesOf : List (Maybe Row) → List Atom
valuesOf [] = []
valuesOf (nothing ∷ rs) = valuesOf rs
valuesOf (just (row p objectCell) ∷ rs) = valuesOf rs
valuesOf (just (row p arrayCell) ∷ rs) = valuesOf rs
valuesOf (just (row p (leaf a)) ∷ rs) = a ∷ valuesOf rs

values-empty : valuesOf [] ≡ []
values-empty = refl

values-skip-invalid : (rs : _) → valuesOf (nothing ∷ rs) ≡ valuesOf rs
values-skip-invalid rs = refl

values-skip-object : (p : _) → (rs : _) → valuesOf (just (row p objectCell) ∷ rs) ≡ valuesOf rs
values-skip-object p rs = refl

values-skip-array : (p : _) → (rs : _) → valuesOf (just (row p arrayCell) ∷ rs) ≡ valuesOf rs
values-skip-array p rs = refl

values-keep-leaf : (p : _) → (a : _) → (rs : _) → valuesOf (just (row p (leaf a)) ∷ rs) ≡ (a ∷ valuesOf rs)
values-keep-leaf p a rs = refl

sparseItems : ℕ → Value → List Value
sparseItems zero v = v ∷ []
sparseItems (suc i) v = scalar null ∷ sparseItems i v

singletonAt : List Segment → Cell → Value
singletonAt [] (leaf a) = scalar a
singletonAt [] objectCell = object []
singletonAt [] arrayCell = array []
singletonAt (key k ∷ p) c = object ((k , singletonAt p c) ∷ [])
singletonAt (index i ∷ p) c = array (sparseItems i (singletonAt p c))

sparse-zero : (v : _) → sparseItems zero v ≡ (v ∷ [])
sparse-zero v = refl

sparse-next : (i : _) → (v : _) → sparseItems (suc i) v ≡ (scalar null ∷ sparseItems i v)
sparse-next i v = refl

singleton-scalar : (a : _) → singletonAt [] (leaf a) ≡ scalar a
singleton-scalar a = refl

singleton-object : singletonAt [] objectCell ≡ object []
singleton-object = refl

singleton-array : singletonAt [] arrayCell ≡ array []
singleton-array = refl

singleton-key : (k : _) → (p : _) → (c : _) → singletonAt (key k ∷ p) c ≡ object ((k , singletonAt p c) ∷ [])
singleton-key k p c = refl

singleton-index : (i : _) → (p : _) → (c : _) → singletonAt (index i ∷ p) c ≡ array (sparseItems i (singletonAt p c))
singleton-index i p c = refl

private
  select : {A P : Set} → Dec P → A → A → A
  select (yes p) hit miss = hit
  select (no n) hit miss = miss

  select-hit : {A P : Set} → (d : Dec P) → P → {h m result : A} →
    h ≡ result → select d h m ≡ result
  select-hit (yes p) witness eq = eq
  select-hit (no n) witness eq = ⊥-elim (n witness)

  select-miss : {A P : Set} → (d : Dec P) → (P → ⊥) → {h m result : A} →
    m ≡ result → select d h m ≡ result
  select-miss (yes p) witness eq = ⊥-elim (witness p)
  select-miss (no n) witness eq = eq

  putFields : String → Value → (Value → MergeFault ⊎ Value) → List (String × Value) → MergeFault ⊎ List (String × Value)
  putFields k new update [] = inj₂ ((k , new) ∷ [])
  putFields k new update ((l , v) ∷ fs) =
    select (k ≟ l)
      ([_,_] inj₁ (λ w → inj₂ ((l , w) ∷ fs)) (update v))
      ([_,_] inj₁ (λ gs → inj₂ ((l , v) ∷ gs)) (putFields k new update fs))

  putItems : ℕ → Value → (Value → MergeFault ⊎ Value) → List Value → MergeFault ⊎ List Value
  putItems i new update [] = inj₂ (sparseItems i new)
  putItems zero new update (v ∷ xs) = [_,_] inj₁ (λ w → inj₂ (w ∷ xs)) (update v)
  putItems (suc i) new update (v ∷ xs) =
    [_,_] inj₁ (λ ys → inj₂ (v ∷ ys)) (putItems i new update xs)

  updateItem : Row → (Value → MergeFault ⊎ Value) → Value → MergeFault ⊎ Value
  updateItem (row [] (leaf null)) update v = inj₂ v
  updateItem _ update v = update v

  update-item-other : (r : Row) → (update : Value → MergeFault ⊎ Value) → (v : Value) →
    r ≢ row [] (leaf null) → updateItem r update v ≡ update v
  update-item-other (row [] (leaf null)) update v neq = ⊥-elim (neq refl)
  update-item-other (row [] (leaf (truth b))) update v neq = refl
  update-item-other (row [] (leaf (numeral n))) update v neq = refl
  update-item-other (row [] (leaf (text s))) update v neq = refl
  update-item-other (row [] objectCell) update v neq = refl
  update-item-other (row [] arrayCell) update v neq = refl
  update-item-other (row (s ∷ p) c) update v neq = refl

insertAt : List Segment → Cell → Value → MergeFault ⊎ Value
insertAt p c (scalar a) = inj₂ (singletonAt p c)
insertAt [] (leaf a) (object fs) = inj₁ objectConflict
insertAt [] objectCell (object fs) = inj₂ (object fs)
insertAt [] arrayCell (object fs) = inj₁ objectConflict
insertAt [] (leaf a) (array xs) = inj₁ arrayConflict
insertAt [] objectCell (array xs) = inj₁ arrayConflict
insertAt [] arrayCell (array xs) = inj₂ (array xs)
insertAt (key k ∷ p) c (object fs) =
  [_,_] inj₁ (λ gs → inj₂ (object gs)) (putFields k (singletonAt p c) (λ w → insertAt p c w) fs)
insertAt (key k ∷ p) c (array xs) = inj₁ arrayConflict
insertAt (index i ∷ p) c (object fs) = inj₁ objectConflict
insertAt (index i ∷ p) c (array xs) =
  [_,_] inj₁ (λ ys → inj₂ (array ys))
    (putItems i (singletonAt p c) (updateItem (row p c) (λ w → insertAt p c w)) xs)

insertField : String → List Segment → Cell → List (String × Value) → MergeFault ⊎ List (String × Value)
insertField k p c fs = putFields k (singletonAt p c) (λ w → insertAt p c w) fs

insertItem : ℕ → List Segment → Cell → List Value → MergeFault ⊎ List Value
insertItem i p c xs =
  putItems i (singletonAt p c) (updateItem (row p c) (λ w → insertAt p c w)) xs

insert-over-scalar : (p : _) → (c : _) → (a : _) → insertAt p c (scalar a) ≡ inj₂ (singletonAt p c)
insert-over-scalar [] (leaf b) a = refl
insert-over-scalar [] objectCell a = refl
insert-over-scalar [] arrayCell a = refl
insert-over-scalar (key k ∷ p) c a = refl
insert-over-scalar (index i ∷ p) c a = refl

insert-keep-object : (fs : _) → insertAt [] objectCell (object fs) ≡ inj₂ (object fs)
insert-keep-object fs = refl

insert-keep-array : (xs : _) → insertAt [] arrayCell (array xs) ≡ inj₂ (array xs)
insert-keep-array xs = refl

insert-object-into-array : (xs : _) → insertAt [] objectCell (array xs) ≡ inj₁ arrayConflict
insert-object-into-array xs = refl

insert-array-into-object : (fs : _) → insertAt [] arrayCell (object fs) ≡ inj₁ objectConflict
insert-array-into-object fs = refl

insert-leaf-into-object : (a : _) → (fs : _) → insertAt [] (leaf a) (object fs) ≡ inj₁ objectConflict
insert-leaf-into-object a fs = refl

insert-leaf-into-array : (a : _) → (xs : _) → insertAt [] (leaf a) (array xs) ≡ inj₁ arrayConflict
insert-leaf-into-array a xs = refl

insert-index-into-object : (i : _) → (p : _) → (c : _) → (fs : _) → insertAt (index i ∷ p) c (object fs) ≡ inj₁ objectConflict
insert-index-into-object i p c fs = refl

insert-key-into-array : (k : _) → (p : _) → (c : _) → (xs : _) → insertAt (key k ∷ p) c (array xs) ≡ inj₁ arrayConflict
insert-key-into-array k p c xs = refl

insert-key-ok : (k : _) → (p : _) → (c : _) → (fs : _) → (gs : _) → (insertField k p c fs ≡ inj₂ gs) → insertAt (key k ∷ p) c (object fs) ≡ inj₂ (object gs)
insert-key-ok k p c fs gs eq = cong ([_,_] inj₁ (λ ts → inj₂ (object ts))) {y = inj₂ gs} eq

insert-key-fault : (k : _) → (p : _) → (c : _) → (fs : _) → (e : _) → (insertField k p c fs ≡ inj₁ e) → insertAt (key k ∷ p) c (object fs) ≡ inj₁ e
insert-key-fault k p c fs e eq = cong ([_,_] inj₁ (λ ts → inj₂ (object ts))) {y = inj₁ e} eq

insert-index-ok : (i : _) → (p : _) → (c : _) → (xs : _) → (ys : _) → (insertItem i p c xs ≡ inj₂ ys) → insertAt (index i ∷ p) c (array xs) ≡ inj₂ (array ys)
insert-index-ok i p c xs ys eq = cong ([_,_] inj₁ (λ ts → inj₂ (array ts))) {y = inj₂ ys} eq

insert-index-fault : (i : _) → (p : _) → (c : _) → (xs : _) → (e : _) → (insertItem i p c xs ≡ inj₁ e) → insertAt (index i ∷ p) c (array xs) ≡ inj₁ e
insert-index-fault i p c xs e eq = cong ([_,_] inj₁ (λ ts → inj₂ (array ts))) {y = inj₁ e} eq

field-new : (k : _) → (p : _) → (c : _) → insertField k p c [] ≡ inj₂ ((k , singletonAt p c) ∷ [])
field-new k p c = refl

field-hit-ok : (k : _) → (p : _) → (c : _) → (v : _) → (fs : _) → (w : _) → (insertAt p c v ≡ inj₂ w) → insertField k p c ((k , v) ∷ fs) ≡ inj₂ ((k , w) ∷ fs)
field-hit-ok k p c v fs w eq =
  select-hit (k ≟ k) refl (cong ([_,_] inj₁ (λ t → inj₂ ((k , t) ∷ fs))) {y = inj₂ w} eq)

field-hit-fault : (k : _) → (p : _) → (c : _) → (v : _) → (fs : _) → (e : _) → (insertAt p c v ≡ inj₁ e) → insertField k p c ((k , v) ∷ fs) ≡ inj₁ e
field-hit-fault k p c v fs e eq =
  select-hit (k ≟ k) refl (cong ([_,_] inj₁ (λ t → inj₂ ((k , t) ∷ fs))) {y = inj₁ e} eq)

field-miss-ok : (k : _) → (l : _) → (p : _) → (c : _) → (v : _) → (fs : _) → (gs : _) → (k ≢ l) → (insertField k p c fs ≡ inj₂ gs) → insertField k p c ((l , v) ∷ fs) ≡ inj₂ ((l , v) ∷ gs)
field-miss-ok k l p c v fs gs neq eq =
  select-miss (k ≟ l) neq (cong ([_,_] inj₁ (λ ts → inj₂ ((l , v) ∷ ts))) {y = inj₂ gs} eq)

field-miss-fault : (k : _) → (l : _) → (p : _) → (c : _) → (v : _) → (fs : _) → (e : _) → (k ≢ l) → (insertField k p c fs ≡ inj₁ e) → insertField k p c ((l , v) ∷ fs) ≡ inj₁ e
field-miss-fault k l p c v fs e neq eq =
  select-miss (k ≟ l) neq (cong ([_,_] inj₁ (λ ts → inj₂ ((l , v) ∷ ts))) {y = inj₁ e} eq)

item-new : (i : _) → (p : _) → (c : _) → insertItem i p c [] ≡ inj₂ (sparseItems i (singletonAt p c))
item-new zero p c = refl
item-new (suc i) p c = refl

item-null : (v : _) → (xs : _) → insertItem zero [] (leaf null) (v ∷ xs) ≡ inj₂ (v ∷ xs)
item-null v xs = refl

item-hit-ok : (p : _) → (c : _) → (v : _) → (xs : _) → (w : _) → (row p c ≢ row [] (leaf null)) → (insertAt p c v ≡ inj₂ w) → insertItem zero p c (v ∷ xs) ≡ inj₂ (w ∷ xs)
item-hit-ok p c v xs w neq eq =
  cong ([_,_] inj₁ (λ t → inj₂ (t ∷ xs))) {y = inj₂ w}
    (trans (update-item-other (row p c) (λ t → insertAt p c t) v neq) eq)

item-hit-fault : (p : _) → (c : _) → (v : _) → (xs : _) → (e : _) → (row p c ≢ row [] (leaf null)) → (insertAt p c v ≡ inj₁ e) → insertItem zero p c (v ∷ xs) ≡ inj₁ e
item-hit-fault p c v xs e neq eq =
  cong ([_,_] inj₁ (λ t → inj₂ (t ∷ xs))) {y = inj₁ e}
    (trans (update-item-other (row p c) (λ t → insertAt p c t) v neq) eq)

item-next-ok : (i : _) → (p : _) → (c : _) → (v : _) → (xs : _) → (ys : _) → (insertItem i p c xs ≡ inj₂ ys) → insertItem (suc i) p c (v ∷ xs) ≡ inj₂ (v ∷ ys)
item-next-ok i p c v xs ys eq = cong ([_,_] inj₁ (λ ts → inj₂ (v ∷ ts))) {y = inj₂ ys} eq

item-next-fault : (i : _) → (p : _) → (c : _) → (v : _) → (xs : _) → (e : _) → (insertItem i p c xs ≡ inj₁ e) → insertItem (suc i) p c (v ∷ xs) ≡ inj₁ e
item-next-fault i p c v xs e eq = cong ([_,_] inj₁ (λ ts → inj₂ (v ∷ ts))) {y = inj₁ e} eq

rebuildMore : Value → List Row → MergeFault ⊎ Value
rebuildMore v [] = inj₂ v
rebuildMore v (row p c ∷ rs) = [_,_] inj₁ (λ w → rebuildMore w rs) (insertAt p c v)

rebuild : List Row → Maybe (MergeFault ⊎ Value)
rebuild [] = nothing
rebuild (row p c ∷ rs) = just (rebuildMore (singletonAt p c) rs)

rebuild-empty : rebuild [] ≡ nothing
rebuild-empty = refl

rebuild-first : (p : _) → (c : _) → (rs : _) → rebuild (row p c ∷ rs) ≡ just (rebuildMore (singletonAt p c) rs)
rebuild-first p c rs = refl

rebuild-done : (v : _) → rebuildMore v [] ≡ inj₂ v
rebuild-done v = refl

rebuild-next : (p : _) → (c : _) → (rs : _) → (v : _) → (w : _) → (insertAt p c v ≡ inj₂ w) → rebuildMore v (row p c ∷ rs) ≡ rebuildMore w rs
rebuild-next p c rs v w eq = cong (λ r → [_,_] inj₁ (λ t → rebuildMore t rs) r) {y = inj₂ w} eq

rebuild-conflict : (p : _) → (c : _) → (rs : _) → (v : _) → (e : _) → (insertAt p c v ≡ inj₁ e) → rebuildMore v (row p c ∷ rs) ≡ inj₁ e
rebuild-conflict p c rs v e eq = cong (λ r → [_,_] inj₁ (λ t → rebuildMore t rs) r) {y = inj₁ e} eq

observed-wide-number : rowsAt [] (scalar (numeral "1e309")) ≡ (row [] (leaf (numeral "1e309")) ∷ [])
observed-wide-number = refl

observed-index-order : itemRowsAt (key "a" ∷ []) 9 (scalar (numeral "9") ∷ (scalar (numeral "10") ∷ (scalar (numeral "11") ∷ []))) ≡ (row (key "a" ∷ (index 9 ∷ [])) (leaf (numeral "9")) ∷ (row (key "a" ∷ (index 10 ∷ [])) (leaf (numeral "10")) ∷ (row (key "a" ∷ (index 11 ∷ [])) (leaf (numeral "11")) ∷ [])))
observed-index-order = refl

observed-sparse-nesting : rebuild (row (index 2 ∷ (key "x" ∷ [])) (leaf (truth true)) ∷ []) ≡ just (inj₂ (array (scalar null ∷ (scalar null ∷ (object (("x" , scalar (truth true)) ∷ []) ∷ [])))))
observed-sparse-nesting = refl

observed-duplicate-property : rebuild (row (key "a" ∷ []) (leaf (numeral "1")) ∷ (row (key "a" ∷ []) (leaf (numeral "2")) ∷ [])) ≡ just (inj₂ (object (("a" , scalar (numeral "2")) ∷ [])))
observed-duplicate-property = refl

observed-null-index : rebuild (row (index 1 ∷ []) (leaf (numeral "1")) ∷ (row (index 1 ∷ []) (leaf null) ∷ [])) ≡ just (inj₂ (array (scalar null ∷ (scalar (numeral "1") ∷ []))))
observed-null-index = refl

observed-array-conflict : rebuild (row (key "a" ∷ (index 1 ∷ [])) (leaf (numeral "2")) ∷ (row (key "a" ∷ (key "b" ∷ [])) (leaf (numeral "3")) ∷ [])) ≡ just (inj₁ arrayConflict)
observed-array-conflict = refl

observed-values : valuesOf (just (row (key "a" ∷ []) (leaf (text "a\nb"))) ∷ (just (row (key "b" ∷ []) (leaf null)) ∷ (just (row (key "c" ∷ []) objectCell) ∷ (just (row (key "d" ∷ []) arrayCell) ∷ (just (row (key "e" ∷ []) (leaf (numeral "1.2500"))) ∷ []))))) ≡ (text "a\nb" ∷ (null ∷ (numeral "1.2500" ∷ [])))
observed-values = refl

observed-reverse-precedence : chooseMode true true ≡ reverse
observed-reverse-precedence = refl

observed-tty-color : useColor true false false ≡ true
observed-tty-color = refl

observed-pipe-color : useColor false false false ≡ false
observed-pipe-color = refl

observed-force-precedence : useColor false true true ≡ true
observed-force-precedence = refl
