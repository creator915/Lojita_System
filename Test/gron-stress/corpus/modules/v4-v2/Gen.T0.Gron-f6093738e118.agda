module Gen.T0.Gron where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

data Atom : Set where
  null : Atom
  truth : Bool → Atom
  numeral text : String → Atom

data Value : Set where
  scalar : Atom → Value
  object : List (String × Value) → Value
  array : List Value → Value

data Segment : Set where
  key : String → Segment
  index : ℕ → Segment

data Cell : Set where
  leaf : Atom → Cell
  objectCell arrayCell : Cell

data Row : Set where
  row : List Segment → Cell → Row

data Mode : Set where
  forward reverse values : Mode

data MergeFault : Set where
  objectConflict arrayConflict : MergeFault

postulate
  chooseMode : (ungron valueOnly : Bool) → Mode
  reverse-selected : ∀ v → chooseMode true v ≡ reverse
  values-selected : chooseMode false true ≡ values
  forward-selected : chooseMode false false ≡ forward

  useColor : (stdoutTTY forceColor monochrome : Bool) → Bool
  force-color : ∀ tty mono → useColor tty true mono ≡ true
  force-monochrome : ∀ tty → useColor tty false true ≡ false
  auto-color : ∀ tty → useColor tty false false ≡ tty

-- The field list supplies the order for emitting sibling properties.
postulate
  rowsAt : List Segment → Value → List Row
  fieldRowsAt : List Segment → List (String × Value) → List Row
  itemRowsAt : List Segment → ℕ → List Value → List Row

  rows-scalar : ∀ p a → rowsAt p (scalar a) ≡ (row p (leaf a) ∷ [])
  rows-object : ∀ p fs → rowsAt p (object fs) ≡ (row p objectCell ∷ fieldRowsAt p fs)
  rows-array : ∀ p xs → rowsAt p (array xs) ≡ (row p arrayCell ∷ itemRowsAt p zero xs)

  rows-no-fields : ∀ p → fieldRowsAt p [] ≡ []
  rows-field : ∀ p k v fs → fieldRowsAt p ((k , v) ∷ fs) ≡
    (rowsAt (p ++ (key k ∷ [])) v ++ fieldRowsAt p fs)
  rows-no-items : ∀ p i → itemRowsAt p i [] ≡ []
  rows-item : ∀ p i v xs → itemRowsAt p i (v ∷ xs) ≡
    (rowsAt (p ++ (index i ∷ [])) v ++ itemRowsAt p (suc i) xs)

postulate
  valuesOf : List (Maybe Row) → List Atom
  values-empty : valuesOf [] ≡ []
  values-skip-invalid : ∀ rs → valuesOf (nothing ∷ rs) ≡ valuesOf rs
  values-skip-object : ∀ p rs → valuesOf (just (row p objectCell) ∷ rs) ≡ valuesOf rs
  values-skip-array : ∀ p rs → valuesOf (just (row p arrayCell) ∷ rs) ≡ valuesOf rs
  values-keep-leaf : ∀ p a rs → valuesOf (just (row p (leaf a)) ∷ rs) ≡ (a ∷ valuesOf rs)

postulate
  singletonAt : List Segment → Cell → Value
  sparseItems : ℕ → Value → List Value

  sparse-zero : ∀ v → sparseItems zero v ≡ (v ∷ [])
  sparse-next : ∀ i v → sparseItems (suc i) v ≡ (scalar null ∷ sparseItems i v)
  singleton-scalar : ∀ a → singletonAt [] (leaf a) ≡ scalar a
  singleton-object : singletonAt [] objectCell ≡ object []
  singleton-array : singletonAt [] arrayCell ≡ array []
  singleton-key : ∀ k p c → singletonAt (key k ∷ p) c ≡ object ((k , singletonAt p c) ∷ [])
  singleton-index : ∀ i p c → singletonAt (index i ∷ p) c ≡ array (sparseItems i (singletonAt p c))

postulate
  insertAt : List Segment → Cell → Value → MergeFault ⊎ Value
  insertField : String → List Segment → Cell → List (String × Value) → MergeFault ⊎ List (String × Value)
  insertItem : ℕ → List Segment → Cell → List Value → MergeFault ⊎ List Value

  insert-over-scalar : ∀ p c a → insertAt p c (scalar a) ≡ inj₂ (singletonAt p c)
  insert-keep-object : ∀ fs → insertAt [] objectCell (object fs) ≡ inj₂ (object fs)
  insert-keep-array : ∀ xs → insertAt [] arrayCell (array xs) ≡ inj₂ (array xs)
  insert-object-into-array : ∀ xs → insertAt [] objectCell (array xs) ≡ inj₁ arrayConflict
  insert-array-into-object : ∀ fs → insertAt [] arrayCell (object fs) ≡ inj₁ objectConflict
  insert-leaf-into-object : ∀ a fs → insertAt [] (leaf a) (object fs) ≡ inj₁ objectConflict
  insert-leaf-into-array : ∀ a xs → insertAt [] (leaf a) (array xs) ≡ inj₁ arrayConflict
  insert-index-into-object : ∀ i p c fs → insertAt (index i ∷ p) c (object fs) ≡ inj₁ objectConflict
  insert-key-into-array : ∀ k p c xs → insertAt (key k ∷ p) c (array xs) ≡ inj₁ arrayConflict

  insert-key-ok : ∀ k p c fs gs → insertField k p c fs ≡ inj₂ gs →
    insertAt (key k ∷ p) c (object fs) ≡ inj₂ (object gs)
  insert-key-fault : ∀ k p c fs e → insertField k p c fs ≡ inj₁ e →
    insertAt (key k ∷ p) c (object fs) ≡ inj₁ e
  insert-index-ok : ∀ i p c xs ys → insertItem i p c xs ≡ inj₂ ys →
    insertAt (index i ∷ p) c (array xs) ≡ inj₂ (array ys)
  insert-index-fault : ∀ i p c xs e → insertItem i p c xs ≡ inj₁ e →
    insertAt (index i ∷ p) c (array xs) ≡ inj₁ e

  field-new : ∀ k p c → insertField k p c [] ≡ inj₂ ((k , singletonAt p c) ∷ [])
  field-hit-ok : ∀ k p c v fs w → insertAt p c v ≡ inj₂ w →
    insertField k p c ((k , v) ∷ fs) ≡ inj₂ ((k , w) ∷ fs)
  field-hit-fault : ∀ k p c v fs e → insertAt p c v ≡ inj₁ e →
    insertField k p c ((k , v) ∷ fs) ≡ inj₁ e
  field-miss-ok : ∀ k l p c v fs gs → k ≢ l → insertField k p c fs ≡ inj₂ gs →
    insertField k p c ((l , v) ∷ fs) ≡ inj₂ ((l , v) ∷ gs)
  field-miss-fault : ∀ k l p c v fs e → k ≢ l → insertField k p c fs ≡ inj₁ e →
    insertField k p c ((l , v) ∷ fs) ≡ inj₁ e

  item-new : ∀ i p c → insertItem i p c [] ≡ inj₂ (sparseItems i (singletonAt p c))
  item-null : ∀ v xs → insertItem zero [] (leaf null) (v ∷ xs) ≡ inj₂ (v ∷ xs)
  item-hit-ok : ∀ p c v xs w → row p c ≢ row [] (leaf null) → insertAt p c v ≡ inj₂ w →
    insertItem zero p c (v ∷ xs) ≡ inj₂ (w ∷ xs)
  item-hit-fault : ∀ p c v xs e → row p c ≢ row [] (leaf null) → insertAt p c v ≡ inj₁ e →
    insertItem zero p c (v ∷ xs) ≡ inj₁ e
  item-next-ok : ∀ i p c v xs ys → insertItem i p c xs ≡ inj₂ ys →
    insertItem (suc i) p c (v ∷ xs) ≡ inj₂ (v ∷ ys)
  item-next-fault : ∀ i p c v xs e → insertItem i p c xs ≡ inj₁ e →
    insertItem (suc i) p c (v ∷ xs) ≡ inj₁ e

postulate
  rebuild : List Row → Maybe (MergeFault ⊎ Value)
  rebuildMore : Value → List Row → MergeFault ⊎ Value
  rebuild-empty : rebuild [] ≡ nothing
  rebuild-first : ∀ p c rs → rebuild (row p c ∷ rs) ≡ just (rebuildMore (singletonAt p c) rs)
  rebuild-done : ∀ v → rebuildMore v [] ≡ inj₂ v
  rebuild-next : ∀ p c rs v w → insertAt p c v ≡ inj₂ w →
    rebuildMore v (row p c ∷ rs) ≡ rebuildMore w rs
  rebuild-conflict : ∀ p c rs v e → insertAt p c v ≡ inj₁ e →
    rebuildMore v (row p c ∷ rs) ≡ inj₁ e

postulate
  observed-wide-number : rowsAt [] (scalar (numeral "1e309")) ≡ (row [] (leaf (numeral "1e309")) ∷ [])
  observed-index-order : itemRowsAt (key "a" ∷ []) 9
    (scalar (numeral "9") ∷ scalar (numeral "10") ∷ scalar (numeral "11") ∷ []) ≡
    (row (key "a" ∷ index 9 ∷ []) (leaf (numeral "9")) ∷
     row (key "a" ∷ index 10 ∷ []) (leaf (numeral "10")) ∷
     row (key "a" ∷ index 11 ∷ []) (leaf (numeral "11")) ∷ [])

  observed-sparse-nesting : rebuild (row (index 2 ∷ key "x" ∷ []) (leaf (truth true)) ∷ []) ≡
    just (inj₂ (array (scalar null ∷ scalar null ∷ object (("x" , scalar (truth true)) ∷ []) ∷ [])))
  observed-duplicate-property :
    rebuild (row (key "a" ∷ []) (leaf (numeral "1")) ∷ row (key "a" ∷ []) (leaf (numeral "2")) ∷ []) ≡
    just (inj₂ (object (("a" , scalar (numeral "2")) ∷ [])))
  observed-null-index :
    rebuild (row (index 1 ∷ []) (leaf (numeral "1")) ∷ row (index 1 ∷ []) (leaf null) ∷ []) ≡
    just (inj₂ (array (scalar null ∷ scalar (numeral "1") ∷ [])))
  observed-array-conflict :
    rebuild (row (key "a" ∷ index 1 ∷ []) (leaf (numeral "2")) ∷
             row (key "a" ∷ key "b" ∷ []) (leaf (numeral "3")) ∷ []) ≡
    just (inj₁ arrayConflict)

  observed-values : valuesOf
    (just (row (key "a" ∷ []) (leaf (text "a\nb"))) ∷
     just (row (key "b" ∷ []) (leaf null)) ∷
     just (row (key "c" ∷ []) objectCell) ∷
     just (row (key "d" ∷ []) arrayCell) ∷
     just (row (key "e" ∷ []) (leaf (numeral "1.2500"))) ∷ []) ≡
    (text "a\nb" ∷ null ∷ numeral "1.2500" ∷ [])

  observed-reverse-precedence : chooseMode true true ≡ reverse
  observed-tty-color : useColor true false false ≡ true
  observed-pipe-color : useColor false false false ≡ false
  observed-force-precedence : useColor false true true ≡ true
