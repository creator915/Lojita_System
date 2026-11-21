module Gen.T0.Gron where

  open import Agda.Builtin.Char using (Char; primCharToNat)
  open import Agda.Builtin.Nat using () renaming (_<_ to _<ᵇ_)
  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.List using (List; []; _∷_; _++_)
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product using (_×_; _,_)
  open import Data.String using (String; toList)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  data Operation : Set where
    forward : Operation
    valuesOnly : Operation
    reverse : Operation

  operation : (ungron values : Bool) → Operation
  operation true _ = reverse
  operation false true = valuesOnly
  operation false false = forward

  reverseWins : (values : _) → operation true values ≡ reverse
  reverseWins values = refl

  valuesSelected : operation false true ≡ valuesOnly
  valuesSelected = refl

  forwardSelected : operation false false ≡ forward
  forwardSelected = refl

  colorOn : (forceColor monochrome stdoutTTY : Bool) → Bool
  colorOn true _ _ = true
  colorOn false true _ = false
  colorOn false false tty = tty

  forceWins : (monochrome : _) → (tty : _) → colorOn true monochrome tty ≡ true
  forceWins monochrome tty = refl

  monochromeWins : (tty : _) → colorOn false true tty ≡ false
  monochromeWins tty = refl

  terminalDefault : (tty : _) → colorOn false false tty ≡ tty
  terminalDefault tty = refl

  data Failure : Set where
    openInput : Failure
    readInput : Failure
    formStatements : Failure
    fetchURL : Failure
    parseStatements : Failure
    encodeJSON : Failure

  exitCode : Failure → ℕ
  exitCode openInput = 1
  exitCode readInput = 2
  exitCode formStatements = 3
  exitCode fetchURL = 4
  exitCode parseStatements = 5
  exitCode encodeJSON = 6

  data Key : Set where
    dotted : (raw : String) → Key
    quoted : (raw spelling : String) → Key

  keyText : Key → String
  keyText (dotted raw) = raw
  keyText (quoted raw _) = raw

  data Step : Set where
    property : Key → Step
    index : ℕ → Step

  Path : Set
  Path = List Step

  extend : Path → Step → Path
  extend p s = p ++ (s ∷ [])

  data Tree (A : Set) : Set where
    leaf : A → Tree A
    object : List (Key × Tree A) → Tree A
    array : List (Tree A) → Tree A

  data Payload (A : Set) : Set where
    scalar : A → Payload A
    objectStart : Payload A
    arrayStart : Payload A

  record Statement (A : Set) : Set where
    constructor statement
    field
      path : Path
      payload : Payload A

  data Order : Set where
    earlier : Order
    equal : Order
    later : Order

  onEqual : Order → Order → Order
  onEqual earlier _ = earlier
  onEqual equal next = next
  onEqual later _ = later

  natOrder : ℕ → ℕ → Order
  natOrder m n = if (m <ᵇ n) then earlier else (if (n <ᵇ m) then later else equal)

  lexical : List Char → List Char → Order
  lexical [] [] = equal
  lexical [] (_ ∷ _) = earlier
  lexical (_ ∷ _) [] = later
  lexical (x ∷ xs) (y ∷ ys) = onEqual (natOrder (primCharToNat x) (primCharToNat y)) (lexical xs ys)

  keyOrder : Key → Key → Order
  keyOrder (dotted x) (dotted y) = lexical (toList x) (toList y)
  keyOrder (dotted _) (quoted _ _) = earlier
  keyOrder (quoted _ _) (dotted _) = later
  keyOrder (quoted _ x) (quoted _ y) = lexical (toList x) (toList y)

  data SiblingOrder : Set where
    canonical : SiblingOrder
    enumerated : SiblingOrder

  insertMember : {A : Set} → (Key × A) → List (Key × A) → List (Key × A)
  insertMember item [] = item ∷ []
  insertMember (k , x) ((l , y) ∷ rest) with keyOrder k l
  insertMember (k , x) ((l , y) ∷ rest) | later = (l , y) ∷ insertMember (k , x) rest
  insertMember (k , x) ((l , y) ∷ rest) | _ = (k , x) ∷ ((l , y) ∷ rest)

  sortMembers : {A : Set} → List (Key × A) → List (Key × A)
  sortMembers [] = []
  sortMembers (item ∷ rest) = insertMember item (sortMembers rest)

  arrange : {A : Set} → SiblingOrder → List (Key × A) → List (Key × A)
  arrange canonical = sortMembers
  arrange enumerated = λ members → members

  joinBranches : {A : Set} → List (Key × List (Statement A)) → List (Statement A)
  joinBranches [] = []
  joinBranches ((_ , branch) ∷ rest) = branch ++ joinBranches rest

  mutual
    emitAt : {A : Set} → SiblingOrder → Path → Tree A → List (Statement A)
    emitAt order p (leaf value) = statement p (scalar value) ∷ []
    emitAt order p (object members) =
      statement p objectStart ∷ joinBranches (arrange order (fieldBranches order p members))
    emitAt order p (array children) =
      statement p arrayStart ∷ arrayItems order p zero children

    fieldBranches : {A : Set} → SiblingOrder → Path → List (Key × Tree A) → List (Key × List (Statement A))
    fieldBranches order p [] = []
    fieldBranches order p ((k , child) ∷ rest) =
      (k , emitAt order (extend p (property k)) child) ∷ fieldBranches order p rest

    arrayItems : {A : Set} → SiblingOrder → Path → ℕ → List (Tree A) → List (Statement A)
    arrayItems order p n [] = []
    arrayItems order p n (child ∷ rest) =
      emitAt order (extend p (index n)) child ++ arrayItems order p (suc n) rest

  emitLeaf : {A : Set} → (order : _) → (p : _) → (value : A) →
    emitAt order p (leaf value) ≡ (statement p (scalar value) ∷ [])
  emitLeaf order p value = refl

  emitObject : {A : Set} → (order : _) → (p : _) → (members : List (Key × Tree A)) →
    emitAt order p (object members) ≡
      (statement p objectStart ∷ joinBranches (arrange order (fieldBranches order p members)))
  emitObject order p members = refl

  emitArray : {A : Set} → (order : _) → (p : _) → (children : List (Tree A)) →
    emitAt order p (array children) ≡
      (statement p arrayStart ∷ arrayItems order p zero children)
  emitArray order p children = refl

  emptyFields : {A : Set} → (order : _) → (p : _) → fieldBranches {A} order p [] ≡ []
  emptyFields order p = refl

  nextField : {A : Set} → (order : _) → (p : _) → (k : _) → (child : Tree A) → (rest : _) →
    fieldBranches order p ((k , child) ∷ rest) ≡
      ((k , emitAt order (extend p (property k)) child) ∷ fieldBranches order p rest)
  nextField order p k child rest = refl

  emptyItems : {A : Set} → (order : _) → (p : _) → (n : _) → arrayItems {A} order p n [] ≡ []
  emptyItems order p n = refl

  nextItem : {A : Set} → (order : _) → (p : _) → (n : _) → (child : Tree A) → (rest : _) →
    arrayItems order p n (child ∷ rest) ≡
      (emitAt order (extend p (index n)) child ++ arrayItems order p (suc n) rest)
  nextItem order p n child rest = refl

  nestedExample : Tree ℕ
  nestedExample =
    object
      ((quoted "a.b" "\"a.b\"" , leaf 5) ∷
       (dotted "a0" , leaf 4) ∷
       (dotted "a" ,
        object
          ((quoted "1" "\"1\"" , leaf 1) ∷
           (dotted "b" , array (leaf 2 ∷ [])) ∷
           [])) ∷
       [])

  nestedStatements : List (Statement ℕ)
  nestedStatements =
    statement [] objectStart ∷
    statement (property (dotted "a") ∷ []) objectStart ∷
    statement (property (dotted "a") ∷ property (dotted "b") ∷ []) arrayStart ∷
    statement (property (dotted "a") ∷ property (dotted "b") ∷ index 0 ∷ []) (scalar 2) ∷
    statement (property (dotted "a") ∷ property (quoted "1" "\"1\"") ∷ []) (scalar 1) ∷
    statement (property (dotted "a0") ∷ []) (scalar 4) ∷
    statement (property (quoted "a.b" "\"a.b\"") ∷ []) (scalar 5) ∷
    []

  nestedOrder : emitAt canonical [] nestedExample ≡ nestedStatements
  nestedOrder = refl

  lexicalDigits : keyOrder (dotted "z10") (dotted "z2") ≡ earlier
  lexicalDigits = refl

  escapedOrder : keyOrder (quoted "!" "\"!\"") (quoted "\n" "\"\\n\"") ≡ earlier
  escapedOrder = refl
