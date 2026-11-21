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
    reverse-selected : (v : _) → chooseMode true v ≡ reverse
  postulate
    values-selected : chooseMode false true ≡ values
  postulate
    forward-selected : chooseMode false false ≡ forward
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
    rows-scalar : (p : _) → (a : _) → rowsAt p (scalar a) ≡ (row p (leaf a) ∷ [])
  postulate
    rows-object : (p : _) → (fs : _) → rowsAt p (object fs) ≡ (row p objectCell ∷ fieldRowsAt p fs)
  postulate
    rows-array : (p : _) → (xs : _) → rowsAt p (array xs) ≡ (row p arrayCell ∷ itemRowsAt p zero xs)
  postulate
    rows-no-fields : (p : _) → fieldRowsAt p [] ≡ []
  postulate
    rows-field : (p : _) → (k : _) → (v : _) → (fs : _) → fieldRowsAt p ((k , v) ∷ fs) ≡ (rowsAt (p ++ (key k ∷ [])) v ++ fieldRowsAt p fs)
  postulate
    rows-no-items : (p : _) → (i : _) → itemRowsAt p i [] ≡ []
  postulate
    rows-item : (p : _) → (i : _) → (v : _) → (xs : _) → itemRowsAt p i (v ∷ xs) ≡ (rowsAt (p ++ (index i ∷ [])) v ++ itemRowsAt p (suc i) xs)
  postulate
    valuesOf : List (Maybe Row) → List Atom
  postulate
    values-empty : valuesOf [] ≡ []
  postulate
    values-skip-invalid : (rs : _) → valuesOf (nothing ∷ rs) ≡ valuesOf rs
  postulate
    values-skip-object : (p : _) → (rs : _) → valuesOf (just (row p objectCell) ∷ rs) ≡ valuesOf rs
  postulate
    values-skip-array : (p : _) → (rs : _) → valuesOf (just (row p arrayCell) ∷ rs) ≡ valuesOf rs
  postulate
    values-keep-leaf : (p : _) → (a : _) → (rs : _) → valuesOf (just (row p (leaf a)) ∷ rs) ≡ (a ∷ valuesOf rs)
  postulate
    singletonAt : List Segment → Cell → Value
  postulate
    sparseItems : ℕ → Value → List Value
  postulate
    sparse-zero : (v : _) → sparseItems zero v ≡ (v ∷ [])
  postulate
    sparse-next : (i : _) → (v : _) → sparseItems (suc i) v ≡ (scalar null ∷ sparseItems i v)
  postulate
    singleton-scalar : (a : _) → singletonAt [] (leaf a) ≡ scalar a
  postulate
    singleton-object : singletonAt [] objectCell ≡ object []
  postulate
    singleton-array : singletonAt [] arrayCell ≡ array []
  postulate
    singleton-key : (k : _) → (p : _) → (c : _) → singletonAt (key k ∷ p) c ≡ object ((k , singletonAt p c) ∷ [])
  postulate
    singleton-index : (i : _) → (p : _) → (c : _) → singletonAt (index i ∷ p) c ≡ array (sparseItems i (singletonAt p c))
  postulate
    insertAt : List Segment → Cell → Value → MergeFault ⊎ Value
  postulate
    insertField : String → List Segment → Cell → List (String × Value) → MergeFault ⊎ List (String × Value)
  postulate
    insertItem : ℕ → List Segment → Cell → List Value → MergeFault ⊎ List Value
  postulate
    insert-over-scalar : (p : _) → (c : _) → (a : _) → insertAt p c (scalar a) ≡ inj₂ (singletonAt p c)
  postulate
    insert-keep-object : (fs : _) → insertAt [] objectCell (object fs) ≡ inj₂ (object fs)
  postulate
    insert-keep-array : (xs : _) → insertAt [] arrayCell (array xs) ≡ inj₂ (array xs)
  postulate
    insert-object-into-array : (xs : _) → insertAt [] objectCell (array xs) ≡ inj₁ arrayConflict
  postulate
    insert-array-into-object : (fs : _) → insertAt [] arrayCell (object fs) ≡ inj₁ objectConflict
  postulate
    insert-leaf-into-object : (a : _) → (fs : _) → insertAt [] (leaf a) (object fs) ≡ inj₁ objectConflict
  postulate
    insert-leaf-into-array : (a : _) → (xs : _) → insertAt [] (leaf a) (array xs) ≡ inj₁ arrayConflict
  postulate
    insert-index-into-object : (i : _) → (p : _) → (c : _) → (fs : _) → insertAt (index i ∷ p) c (object fs) ≡ inj₁ objectConflict
  postulate
    insert-key-into-array : (k : _) → (p : _) → (c : _) → (xs : _) → insertAt (key k ∷ p) c (array xs) ≡ inj₁ arrayConflict
  postulate
    insert-key-ok : (k : _) → (p : _) → (c : _) → (fs : _) → (gs : _) → (insertField k p c fs ≡ inj₂ gs) → insertAt (key k ∷ p) c (object fs) ≡ inj₂ (object gs)
  postulate
    insert-key-fault : (k : _) → (p : _) → (c : _) → (fs : _) → (e : _) → (insertField k p c fs ≡ inj₁ e) → insertAt (key k ∷ p) c (object fs) ≡ inj₁ e
  postulate
    insert-index-ok : (i : _) → (p : _) → (c : _) → (xs : _) → (ys : _) → (insertItem i p c xs ≡ inj₂ ys) → insertAt (index i ∷ p) c (array xs) ≡ inj₂ (array ys)
  postulate
    insert-index-fault : (i : _) → (p : _) → (c : _) → (xs : _) → (e : _) → (insertItem i p c xs ≡ inj₁ e) → insertAt (index i ∷ p) c (array xs) ≡ inj₁ e
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
    item-null : (v : _) → (xs : _) → insertItem zero [] (leaf null) (v ∷ xs) ≡ inj₂ (v ∷ xs)
  postulate
    item-hit-ok : (p : _) → (c : _) → (v : _) → (xs : _) → (w : _) → (row p c ≢ row [] (leaf null)) → (insertAt p c v ≡ inj₂ w) → insertItem zero p c (v ∷ xs) ≡ inj₂ (w ∷ xs)
  postulate
    item-hit-fault : (p : _) → (c : _) → (v : _) → (xs : _) → (e : _) → (row p c ≢ row [] (leaf null)) → (insertAt p c v ≡ inj₁ e) → insertItem zero p c (v ∷ xs) ≡ inj₁ e
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
    rebuild-first : (p : _) → (c : _) → (rs : _) → rebuild (row p c ∷ rs) ≡ just (rebuildMore (singletonAt p c) rs)
  postulate
    rebuild-done : (v : _) → rebuildMore v [] ≡ inj₂ v
  postulate
    rebuild-next : (p : _) → (c : _) → (rs : _) → (v : _) → (w : _) → (insertAt p c v ≡ inj₂ w) → rebuildMore v (row p c ∷ rs) ≡ rebuildMore w rs
  postulate
    rebuild-conflict : (p : _) → (c : _) → (rs : _) → (v : _) → (e : _) → (insertAt p c v ≡ inj₁ e) → rebuildMore v (row p c ∷ rs) ≡ inj₁ e
  postulate
    observed-wide-number : rowsAt [] (scalar (numeral "1e309")) ≡ (row [] (leaf (numeral "1e309")) ∷ [])
  postulate
    observed-index-order : itemRowsAt (key "a" ∷ []) 9 (scalar (numeral "9") ∷ (scalar (numeral "10") ∷ (scalar (numeral "11") ∷ []))) ≡ (row (key "a" ∷ (index 9 ∷ [])) (leaf (numeral "9")) ∷ (row (key "a" ∷ (index 10 ∷ [])) (leaf (numeral "10")) ∷ (row (key "a" ∷ (index 11 ∷ [])) (leaf (numeral "11")) ∷ [])))
  postulate
    observed-sparse-nesting : rebuild (row (index 2 ∷ (key "x" ∷ [])) (leaf (truth true)) ∷ []) ≡ just (inj₂ (array (scalar null ∷ (scalar null ∷ (object (("x" , scalar (truth true)) ∷ []) ∷ [])))))
  postulate
    observed-duplicate-property : rebuild (row (key "a" ∷ []) (leaf (numeral "1")) ∷ (row (key "a" ∷ []) (leaf (numeral "2")) ∷ [])) ≡ just (inj₂ (object (("a" , scalar (numeral "2")) ∷ [])))
  postulate
    observed-null-index : rebuild (row (index 1 ∷ []) (leaf (numeral "1")) ∷ (row (index 1 ∷ []) (leaf null) ∷ [])) ≡ just (inj₂ (array (scalar null ∷ (scalar (numeral "1") ∷ []))))
  postulate
    observed-array-conflict : rebuild (row (key "a" ∷ (index 1 ∷ [])) (leaf (numeral "2")) ∷ (row (key "a" ∷ (key "b" ∷ [])) (leaf (numeral "3")) ∷ [])) ≡ just (inj₁ arrayConflict)
  postulate
    observed-values : valuesOf (just (row (key "a" ∷ []) (leaf (text "a\nb"))) ∷ (just (row (key "b" ∷ []) (leaf null)) ∷ (just (row (key "c" ∷ []) objectCell) ∷ (just (row (key "d" ∷ []) arrayCell) ∷ (just (row (key "e" ∷ []) (leaf (numeral "1.2500"))) ∷ []))))) ≡ (text "a\nb" ∷ (null ∷ (numeral "1.2500" ∷ [])))
  postulate
    observed-reverse-precedence : chooseMode true true ≡ reverse
  postulate
    observed-tty-color : useColor true false false ≡ true
  postulate
    observed-pipe-color : useColor false false false ≡ false
  postulate
    observed-force-precedence : useColor false true true ≡ true
