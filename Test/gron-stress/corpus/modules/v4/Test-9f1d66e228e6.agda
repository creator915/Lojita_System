module Test where

open import Agda.Builtin.Char using (primCharEquality; primNatToChar)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool using (Bool; false; true; _∧_; _∨_)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; [_]; _++_; any; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; fromList; toList) renaming (_++_ to _++ˢ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

data Expectation : Set where
  valueStart : Expectation
  inWord : String → Char → Expectation
  objectKey : Expectation
  afterKey : Expectation
  afterMember : Expectation
  afterElement : Expectation
  integerDigit : Expectation
  fractionalDigit : Expectation
  exponentDigit : Expectation
  insideString : Expectation
  afterEscape : Expectation
  unicodeDigit : Expectation
  afterDocument : Expectation
  exceededDepth : Expectation

data Fault : Set where
  missingDocument : Fault
  incompleteDocument : Fault
  unexpected : Char → Expectation → Fault

data Prefix (A : Set) : Set where
  consumed : A → List Char → Prefix A
  failed : Fault → Prefix A

record Comparison : Set where
  constructor comparison
  field
    charRefl : (c : Char) → primCharEquality c c ≡ true
    charReflects : (c d : Char) → (primCharEquality c d ≡ true) → c ≡ d
    stringRefl : (s : String) → primStringEquality s s ≡ true
    stringReflects : (s t : String) → (primStringEquality s t ≡ true) → s ≡ t

record Layout : Set where
  constructor layoutRules
  field
    isSpace : Char → Bool
    spaceClass : (c : Char) → isSpace c ≡ (primCharEquality c ' ' ∨ (primCharEquality c '	' ∨ (primCharEquality c '\r' ∨ primCharEquality c '\n')))
    trimSpace : List Char → List Char
    trimEmpty : trimSpace [] ≡ []
    trimHead : (c : Char) → (xs : List Char) → (isSpace c ≡ true) → trimSpace (c ∷ xs) ≡ trimSpace xs
    keepHead : (c : Char) → (xs : List Char) → (isSpace c ≡ false) → trimSpace (c ∷ xs) ≡ (c ∷ xs)

record Constructors (A : Set) : Set where
  constructor constructors
  field
    nullValue : A
    booleanValue : Bool → A
    numericValue : String → A
    textValue : String → A
    objectValue : List (String × A) → A
    arrayValue : List A → A

choose : {A : Set} → Bool → A → A → A
choose true yes no = yes
choose false yes no = no

chooseYes : {A : Set} → (b : Bool) → (yes no : A) → b ≡ true → choose b yes no ≡ yes
chooseYes b yes no p = cong (λ bit → choose bit yes no) p

chooseNo : {A : Set} → (b : Bool) → (yes no : A) → b ≡ false → choose b yes no ≡ no
chooseNo b yes no p = cong (λ bit → choose bit yes no) p

splitBool : {A : Set} → (b : Bool) → (b ≡ true → A) → (b ≡ false → A) → A
splitBool true yes no = yes refl
splitBool false yes no = no refl

boolHolds : Bool → Set
boolHolds true = ⊤
boolHolds false = ⊥

falseNotTrue : false ≡ true → ⊥
falseNotTrue p = subst boolHolds (sym p) tt

trueNotFalse : true ≡ false → ⊥
trueNotFalse p = subst boolHolds p tt

denyTrue : (b : Bool) → b ≢ true → b ≡ false
denyTrue true no = ⊥-elim (no refl)
denyTrue false no = refl

andLeft : {b c : Bool} → (b ∧ c) ≡ true → b ≡ true
andLeft {true} p = refl
andLeft {false} p = ⊥-elim (falseNotTrue p)

andRight : {b c : Bool} → (b ∧ c) ≡ true → c ≡ true
andRight {true} p = p
andRight {false} p = ⊥-elim (falseNotTrue p)

andRightFalse : (b c : Bool) → c ≡ false → (b ∧ c) ≡ false
andRightFalse true c p = p
andRightFalse false c p = refl

orLeftFalse : {b c : Bool} → (b ∨ c) ≡ false → b ≡ false
orLeftFalse {true} p = p
orLeftFalse {false} p = refl

orRightFalse : {b c : Bool} → (b ∨ c) ≡ false → c ≡ false
orRightFalse {true} p = ⊥-elim (trueNotFalse p)
orRightFalse {false} p = p

orFalse : {b c : Bool} → b ≡ false → c ≡ false → (b ∨ c) ≡ false
orFalse {b} {c} p q = trans (cong (λ bit → bit ∨ c) p) q

notBelowZero : (n : ℕ) → (n <ᵇ zero) ≡ true → ⊥
notBelowZero zero p = falseNotTrue p
notBelowZero (suc n) p = falseNotTrue p

aboveExcludesBelow : (lo hi n : ℕ) → (lo <ᵇ suc hi) ≡ true → (hi <ᵇ n) ≡ true → (n <ᵇ lo) ≡ false
aboveExcludesBelow zero hi zero p q = refl
aboveExcludesBelow zero hi (suc n) p q = refl
aboveExcludesBelow (suc lo) zero n p q = ⊥-elim (notBelowZero lo p)
aboveExcludesBelow (suc lo) (suc hi) zero p q = ⊥-elim (falseNotTrue q)
aboveExcludesBelow (suc lo) (suc hi) (suc n) p q = aboveExcludesBelow lo hi n p q

charNo : (eqs : Comparison) → (c d : Char) → c ≢ d → primCharEquality c d ≡ false
charNo eqs c d apart = denyTrue (primCharEquality c d) (λ p → apart (Comparison.charReflects eqs c d p))

headNo : (eqs : Comparison) → (c d : Char) → (xs : List Char) → take 1 (c ∷ xs) ≢ ([ d ]) → primCharEquality c d ≡ false
headNo eqs c d xs apart = charNo eqs c d (λ p → apart (cong (λ t → [ t ]) p))

data Suffix : List Char → List Char → Set where
  here : {xs : List Char} → Suffix xs xs
  skip : {c : Char} → {xs ys : List Char} → Suffix xs ys → Suffix (c ∷ xs) ys

joinSuffix : {xs ys zs : List Char} → Suffix xs ys → Suffix ys zs → Suffix xs zs
joinSuffix here t = t
joinSuffix (skip s) t = skip (joinSuffix s t)

data Read (A : Set) (xs : List Char) : Set where
  readOK : A → (ys : List Char) → Suffix xs ys → Read A xs
  readError : Fault → Read A xs

erase : {A : Set} → {xs : List Char} → Read A xs → Prefix A
erase (readOK a ys p) = consumed a ys
erase (readError e) = failed e

mapRead : {A B : Set} → {xs : List Char} → (A → B) → Read A xs → Read B xs
mapRead f (readOK a ys p) = readOK (f a) ys p
mapRead f (readError e) = readError e

pushRead : {A : Set} → {xs ys : List Char} → Suffix xs ys → Read A ys → Read A xs
pushRead s (readOK a zs t) = readOK a zs (joinSuffix s t)
pushRead s (readError e) = readError e

bindRead : {A B : Set} → {xs : List Char} → Read A xs → ((a : A) → (ys : List Char) → Suffix xs ys → Read B ys) → Read B xs
bindRead (readOK a ys p) k = pushRead p (k a ys p)
bindRead (readError e) k = readError e

pushErases : {A : Set} → {xs ys : List Char} → (s : Suffix xs ys) → (r : Read A ys) → erase (pushRead s r) ≡ erase r
pushErases s (readOK a ys t) = refl
pushErases s (readError e) = refl

mapPrefix : {A B : Set} → (A → B) → Prefix A → Prefix B
mapPrefix f (consumed a ys) = consumed (f a) ys
mapPrefix f (failed e) = failed e

mapErases : {A B : Set} → {xs : List Char} → (f : A → B) → (r : Read A xs) → erase (mapRead f r) ≡ mapPrefix f (erase r)
mapErases f (readOK a ys s) = refl
mapErases f (readError e) = refl

mapOK : {A B : Set} → {xs : List Char} → (f : A → B) → (r : Read A xs) → {a : A} → {ys : List Char} → erase r ≡ consumed a ys → erase (mapRead f r) ≡ consumed (f a) ys
mapOK f r p = trans (mapErases f r) (cong (mapPrefix f) p)

mapError : {A B : Set} → {xs : List Char} → (f : A → B) → (r : Read A xs) → {e : Fault} → erase r ≡ failed e → erase (mapRead f r) ≡ failed e
mapError f r p = trans (mapErases f r) (cong (mapPrefix f) p)
