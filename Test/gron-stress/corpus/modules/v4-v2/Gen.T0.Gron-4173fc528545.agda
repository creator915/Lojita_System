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
  postulate
    chooseMode : (ungron valueOnly : Bool) → Mode
  postulate
    reverse-selected : (v : _) → chooseMode true v ≡ Mode.reverse
  postulate
    values-selected : chooseMode false true ≡ Mode.values
  postulate
    forward-selected : chooseMode false false ≡ Mode.forward
  postulate
    useColor : (stdoutTTY forceColor monochrome : Bool) → Bool
  postulate
    force-color : (tty : _) → (mono : _) → useColor tty true mono ≡ true
  postulate
    force-monochrome : (tty : _) → useColor tty false true ≡ false
  postulate
    auto-color : (tty : _) → useColor tty false false ≡ tty
  postulate
    rowsAt : List Segment → Value → List Row
  postulate
    fieldRowsAt : List Segment → List (String × Value) → List Row
  postulate
    itemRowsAt : List Segment → ℕ → List Value → List Row
  postulate
    rows-scalar : (p : _) → (a : _) → rowsAt p (Value.scalar a) ≡ (Row.row p (Cell.leaf a) ∷ [])
  postulate
    rows-object : (p : _) → (fs : _) → rowsAt p (Value.object fs) ≡ (Row.row p Cell.objectCell ∷ fieldRowsAt p fs)
  postulate
    rows-array : (p : _) → (xs : _) → rowsAt p (Value.array xs) ≡ (Row.row p Cell.arrayCell ∷ itemRowsAt p zero xs)
  postulate
    rows-no-fields : (p : _) → fieldRowsAt p [] ≡ []
  postulate
    rows-field : (p : _) → (k : _) → (v : _) → (fs : _) → fieldRowsAt p ((k , v) ∷ fs) ≡ (rowsAt (p ++ (Segment.key k ∷ [])) v ++ fieldRowsAt p fs)
  postulate
    rows-no-items : (p : _) → (i : _) → itemRowsAt p i [] ≡ []
  postulate
    rows-item : (p : _) → (i : _) → (v : _) → (xs : _) → itemRowsAt p i (v ∷ xs) ≡ (rowsAt (p ++ (Segment.index i ∷ [])) v ++ itemRowsAt p (suc i) xs)
  postulate
    valuesOf : List (Maybe Row) → List Atom
  postulate
    values-empty : valuesOf [] ≡ []
  postulate
    values-skip-invalid : (rs : _) → valuesOf (nothing ∷ rs) ≡ valuesOf rs
  postulate
    values-skip-object : (p : _) → (rs : _) → valuesOf (just (Row.row p Cell.objectCell) ∷ rs) ≡ valuesOf rs
  postulate
    values-skip-array : (p : _) → (rs : _) → valuesOf (just (Row.row p Cell.arrayCell) ∷ rs) ≡ valuesOf rs
  postulate
    values-keep-leaf : (p : _) → (a : _) → (rs : _) → valuesOf (just (Row.row p (Cell.leaf a)) ∷ rs) ≡ (a ∷ valuesOf rs)
  postulate
    singletonAt : List Segment → Cell → Value
  postulate
    sparseItems : ℕ → Value → List Value
  postulate
    sparse-zero : (v : _) → sparseItems zero v ≡ (v ∷ [])
  postulate
    sparse-next : (i : _) → (v : _) → sparseItems (suc i) v ≡ (Value.scalar Atom.null ∷ sparseItems i v)
  postulate
    singleton-scalar : (a : _) → singletonAt [] (Cell.leaf a) ≡ Value.scalar a
  postulate
    singleton-object : singletonAt [] Cell.objectCell ≡ Value.object []
  postulate
    singleton-array : singletonAt [] Cell.arrayCell ≡ Value.array []
  postulate
    singleton-key : (k : _) → (p : _) → (c : _) → singletonAt (Segment.key k ∷ p) c ≡ Value.object ((k , singletonAt p c) ∷ [])
  postulate
    singleton-index : (i : _) → (p : _) → (c : _) → singletonAt (Segment.index i ∷ p) c ≡ Value.array (sparseItems i (singletonAt p c))
  postulate
    insertAt : List Segment → Cell → Value → MergeFault ⊎ Value
  postulate
    insertField : String → List Segment → Cell → List (String × Value) → MergeFault ⊎ List (String × Value)
  postulate
    insertItem : ℕ → List Segment → Cell → List Value → MergeFault ⊎ List Value
  postulate
    insert-over-scalar : (p : _) → (c : _) → (a : _) → insertAt p c (Value.scalar a) ≡ inj₂ (singletonAt p c)
  postulate
    insert-keep-object : (fs : _) → insertAt [] Cell.objectCell (Value.object fs) ≡ inj₂ (Value.object fs)
  postulate
    insert-keep-array : (xs : _) → insertAt [] Cell.arrayCell (Value.array xs) ≡ inj₂ (Value.array xs)
  postulate
    insert-object-into-array : (xs : _) → insertAt [] Cell.objectCell (Value.array xs) ≡ inj₁ MergeFault.arrayConflict
  postulate
    insert-array-into-object : (fs : _) → insertAt [] Cell.arrayCell (Value.object fs) ≡ inj₁ MergeFault.objectConflict
  postulate
    insert-leaf-into-object : (a : _) → (fs : _) → insertAt [] (Cell.leaf a) (Value.object fs) ≡ inj₁ MergeFault.objectConflict
  postulate
    insert-leaf-into-array : (a : _) → (xs : _) → insertAt [] (Cell.leaf a) (Value.array xs) ≡ inj₁ MergeFault.arrayConflict
  postulate
    insert-index-into-object : (i : _) → (p : _) → (c : _) → (fs : _) → insertAt (Segment.index i ∷ p) c (Value.object fs) ≡ inj₁ MergeFault.objectConflict
  postulate
    insert-key-into-array : (k : _) → (p : _) → (c : _) → (xs : _) → insertAt (Segment.key k ∷ p) c (Value.array xs) ≡ inj₁ MergeFault.arrayConflict
  postulate
    insert-key-ok : (k : _) → (p : _) → (c : _) → (fs : _) → (gs : _) → (insertField k p c fs ≡ inj₂ gs) → insertAt (Segment.key k ∷ p) c (Value.object fs) ≡ inj₂ (Value.object gs)
  postulate
    insert-key-fault : (k : _) → (p : _) → (c : _) → (fs : _) → (e : _) → (insertField k p c fs ≡ inj₁ e) → insertAt (Segment.key k ∷ p) c (Value.object fs) ≡ inj₁ e
  postulate
    insert-index-ok : (i : _) → (p : _) → (c : _) → (xs : _) → (ys : _) → (insertItem i p c xs ≡ inj₂ ys) → insertAt (Segment.index i ∷ p) c (Value.array xs) ≡ inj₂ (Value.array ys)
  postulate
    insert-index-fault : (i : _) → (p : _) → (c : _) → (xs : _) → (e : _) → (insertItem i p c xs ≡ inj₁ e) → insertAt (Segment.index i ∷ p) c (Value.array xs) ≡ inj₁ e
  postulate
    field-new : (k : _) → (p : _) → (c : _) → insertField k p c [] ≡ inj₂ ((k , singletonAt p c) ∷ [])
  postulate
    field-hit-ok : (k : _) → (p : _) → (c : _) → (v : _) → (fs : _) → (w : _) → (insertAt p c v ≡ inj₂ w) → insertField k p c ((k , v) ∷ fs) ≡ inj₂ ((k , w) ∷ fs)
  postulate
    field-hit-fault : (k : _) → (p : _) → (c : _) → (v : _) → (fs : _) → (e : _) → (insertAt p c v ≡ inj₁ e) → insertField k p c ((k , v) ∷ fs) ≡ inj₁ e
  postulate
    field-miss-ok : (k : _) → (l : _) → (p : _) → (c : _) → (v : _) → (fs : _) → (gs : _) → (k ≢ l) → (insertField k p c fs ≡ inj₂ gs) → insertField k p c ((l , v) ∷ fs) ≡ inj₂ ((l , v) ∷ gs)
  postulate
    field-miss-fault : (k : _) → (l : _) → (p : _) → (c : _) → (v : _) → (fs : _) → (e : _) → (k ≢ l) → (insertField k p c fs ≡ inj₁ e) → insertField k p c ((l , v) ∷ fs) ≡ inj₁ e
  postulate
    item-new : (i : _) → (p : _) → (c : _) → insertItem i p c [] ≡ inj₂ (sparseItems i (singletonAt p c))
  postulate
    item-null : (v : _) → (xs : _) → insertItem zero [] (Cell.leaf Atom.null) (v ∷ xs) ≡ inj₂ (v ∷ xs)
  postulate
    item-hit-ok : (p : _) → (c : _) → (v : _) → (xs : _) → (w : _) → (Row.row p c ≢ Row.row [] (Cell.leaf Atom.null)) → (insertAt p c v ≡ inj₂ w) → insertItem zero p c (v ∷ xs) ≡ inj₂ (w ∷ xs)
  postulate
    item-hit-fault : (p : _) → (c : _) → (v : _) → (xs : _) → (e : _) → (Row.row p c ≢ Row.row [] (Cell.leaf Atom.null)) → (insertAt p c v ≡ inj₁ e) → insertItem zero p c (v ∷ xs) ≡ inj₁ e
  postulate
    item-next-ok : (i : _) → (p : _) → (c : _) → (v : _) → (xs : _) → (ys : _) → (insertItem i p c xs ≡ inj₂ ys) → insertItem (suc i) p c (v ∷ xs) ≡ inj₂ (v ∷ ys)
  postulate
    item-next-fault : (i : _) → (p : _) → (c : _) → (v : _) → (xs : _) → (e : _) → (insertItem i p c xs ≡ inj₁ e) → insertItem (suc i) p c (v ∷ xs) ≡ inj₁ e
  postulate
    rebuild : List Row → Maybe (MergeFault ⊎ Value)
  postulate
    rebuildMore : Value → List Row → MergeFault ⊎ Value
  postulate
    rebuild-empty : rebuild [] ≡ nothing
  postulate
    rebuild-first : (p : _) → (c : _) → (rs : _) → rebuild (Row.row p c ∷ rs) ≡ just (rebuildMore (singletonAt p c) rs)
  postulate
    rebuild-done : (v : _) → rebuildMore v [] ≡ inj₂ v
  postulate
    rebuild-next : (p : _) → (c : _) → (rs : _) → (v : _) → (w : _) → (insertAt p c v ≡ inj₂ w) → rebuildMore v (Row.row p c ∷ rs) ≡ rebuildMore w rs
  postulate
    rebuild-conflict : (p : _) → (c : _) → (rs : _) → (v : _) → (e : _) → (insertAt p c v ≡ inj₁ e) → rebuildMore v (Row.row p c ∷ rs) ≡ inj₁ e
  postulate
    observed-wide-number : rowsAt [] (Value.scalar (Atom.numeral "1e309")) ≡ (Row.row [] (Cell.leaf (Atom.numeral "1e309")) ∷ [])
  postulate
    observed-index-order : itemRowsAt (Segment.key "a" ∷ []) 9 (Value.scalar (Atom.numeral "9") ∷ (Value.scalar (Atom.numeral "10") ∷ (Value.scalar (Atom.numeral "11") ∷ []))) ≡ (Row.row (Segment.key "a" ∷ (Segment.index 9 ∷ [])) (Cell.leaf (Atom.numeral "9")) ∷ (Row.row (Segment.key "a" ∷ (Segment.index 10 ∷ [])) (Cell.leaf (Atom.numeral "10")) ∷ (Row.row (Segment.key "a" ∷ (Segment.index 11 ∷ [])) (Cell.leaf (Atom.numeral "11")) ∷ [])))
  postulate
    observed-sparse-nesting : rebuild (Row.row (Segment.index 2 ∷ (Segment.key "x" ∷ [])) (Cell.leaf (Atom.truth true)) ∷ []) ≡ just (inj₂ (Value.array (Value.scalar Atom.null ∷ (Value.scalar Atom.null ∷ (Value.object (("x" , Value.scalar (Atom.truth true)) ∷ []) ∷ [])))))
  postulate
    observed-duplicate-property : rebuild (Row.row (Segment.key "a" ∷ []) (Cell.leaf (Atom.numeral "1")) ∷ (Row.row (Segment.key "a" ∷ []) (Cell.leaf (Atom.numeral "2")) ∷ [])) ≡ just (inj₂ (Value.object (("a" , Value.scalar (Atom.numeral "2")) ∷ [])))
  postulate
    observed-null-index : rebuild (Row.row (Segment.index 1 ∷ []) (Cell.leaf (Atom.numeral "1")) ∷ (Row.row (Segment.index 1 ∷ []) (Cell.leaf Atom.null) ∷ [])) ≡ just (inj₂ (Value.array (Value.scalar Atom.null ∷ (Value.scalar (Atom.numeral "1") ∷ []))))
  postulate
    observed-array-conflict : rebuild (Row.row (Segment.key "a" ∷ (Segment.index 1 ∷ [])) (Cell.leaf (Atom.numeral "2")) ∷ (Row.row (Segment.key "a" ∷ (Segment.key "b" ∷ [])) (Cell.leaf (Atom.numeral "3")) ∷ [])) ≡ just (inj₁ MergeFault.arrayConflict)
  postulate
    observed-values : valuesOf (just (Row.row (Segment.key "a" ∷ []) (Cell.leaf (Atom.text "a\nb"))) ∷ (just (Row.row (Segment.key "b" ∷ []) (Cell.leaf Atom.null)) ∷ (just (Row.row (Segment.key "c" ∷ []) Cell.objectCell) ∷ (just (Row.row (Segment.key "d" ∷ []) Cell.arrayCell) ∷ (just (Row.row (Segment.key "e" ∷ []) (Cell.leaf (Atom.numeral "1.2500"))) ∷ []))))) ≡ (Atom.text "a\nb" ∷ (Atom.null ∷ (Atom.numeral "1.2500" ∷ [])))
  postulate
    observed-reverse-precedence : chooseMode true true ≡ Mode.reverse
  postulate
    observed-tty-color : useColor true false false ≡ true
  postulate
    observed-pipe-color : useColor false false false ≡ false
  postulate
    observed-force-precedence : useColor false true true ≡ true
