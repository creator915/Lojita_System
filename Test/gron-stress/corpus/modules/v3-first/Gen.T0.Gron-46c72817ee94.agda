module Gen.T0.Gron where

  open import Agda.Builtin.Char using (Char; primCharToNat)
  open import Agda.Builtin.Nat using () renaming (_<_ to _<ᵇ_)
  open import Data.Bool using (Bool; true; false; if_then_else_)
  open import Data.List using (List; []; _∷_; _++_)
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product using (_×_; _,_)
  open import Data.String using (String; toList)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  data Operation : Set where
    forward : Operation
    valuesOnly : Operation
    reverse : Operation
  postulate
    operation : (ungron values : Bool) → Operation
  postulate
    reverseWins : (values : _) → operation true values ≡ reverse
  postulate
    valuesSelected : operation false true ≡ valuesOnly
  postulate
    forwardSelected : operation false false ≡ forward
  postulate
    colorOn : (forceColor monochrome stdoutTTY : Bool) → Bool
  postulate
    forceWins : (monochrome : _) → (tty : _) → colorOn true monochrome tty ≡ true
  postulate
    monochromeWins : (tty : _) → colorOn false true tty ≡ false
  postulate
    terminalDefault : (tty : _) → colorOn false false tty ≡ tty
  data Failure : Set where
    openInput : Failure
    readInput : Failure
    formStatements : Failure
    fetchURL : Failure
    parseStatements : Failure
    encodeJSON : Failure
  postulate
    exitCode : Failure → ℕ
  data Key : Set where
    dotted : (raw : String) → Key
    quoted : (raw spelling : String) → Key
  postulate
    keyText : Key → String
  data Step : Set where
    property : Key → Step
    index : ℕ → Step
  postulate
    Path : Set
  postulate
    extend : Path → Step → Path
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
  postulate
    onEqual : Order → Order → Order
  postulate
    natOrder : ℕ → ℕ → Order
  postulate
    lexical : List Char → List Char → Order
  postulate
    keyOrder : Key → Key → Order
  data SiblingOrder : Set where
    canonical : SiblingOrder
    enumerated : SiblingOrder
  postulate
    insertMember : {A : Set} → (Key × A) → List (Key × A) → List (Key × A)
  postulate
    sortMembers : {A : Set} → List (Key × A) → List (Key × A)
  postulate
    arrange : {A : Set} → SiblingOrder → List (Key × A) → List (Key × A)
  postulate
    joinBranches : {A : Set} → List (Key × List (Statement A)) → List (Statement A)
  postulate
    emitAt : {A : Set} → SiblingOrder → Path → Tree A → List (Statement A)
  postulate
    fieldBranches : {A : Set} → SiblingOrder → Path → List (Key × Tree A) → List (Key × List (Statement A))
  postulate
    arrayItems : {A : Set} → SiblingOrder → Path → ℕ → List (Tree A) → List (Statement A)
  postulate
    emitLeaf : {A : Set} → (order : _) → (p : _) → (value : A) → emitAt order p (leaf value) ≡ (statement p (scalar value) ∷ [])
  postulate
    emitObject : {A : Set} → (order : _) → (p : _) → (members : List (Key × Tree A)) → emitAt order p (object members) ≡ (statement p objectStart ∷ joinBranches (arrange order (fieldBranches order p members)))
  postulate
    emitArray : {A : Set} → (order : _) → (p : _) → (children : List (Tree A)) → emitAt order p (array children) ≡ (statement p arrayStart ∷ arrayItems order p zero children)
  postulate
    emptyFields : {A : Set} → (order : _) → (p : _) → fieldBranches {A} order p [] ≡ []
  postulate
    nextField : {A : Set} → (order : _) → (p : _) → (k : _) → (child : Tree A) → (rest : _) → fieldBranches order p ((k , child) ∷ rest) ≡ ((k , emitAt order (extend p (property k)) child) ∷ fieldBranches order p rest)
  postulate
    emptyItems : {A : Set} → (order : _) → (p : _) → (n : _) → arrayItems {A} order p n [] ≡ []
  postulate
    nextItem : {A : Set} → (order : _) → (p : _) → (n : _) → (child : Tree A) → (rest : _) → arrayItems order p n (child ∷ rest) ≡ (emitAt order (extend p (index n)) child ++ arrayItems order p (suc n) rest)
  postulate
    nestedExample : Tree ℕ
  postulate
    nestedStatements : List (Statement ℕ)
  postulate
    nestedOrder : emitAt canonical [] nestedExample ≡ nestedStatements
  postulate
    lexicalDigits : keyOrder (dotted "z10") (dotted "z2") ≡ earlier
  postulate
    escapedOrder : keyOrder (quoted "!" "\"!\"") (quoted "\n" "\"\\n\"") ≡ earlier
