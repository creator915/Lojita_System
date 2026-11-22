{-# OPTIONS --safe #-}
module Countermodel where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (Char; primCharToNat; primNatToChar)
open import Agda.Builtin.Char.Properties using (primCharToNatInjective)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _==_)
open import Data.Bool.Base using (_∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (_++_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)

atFalse : Bool → Set
atFalse false = ⊤
atFalse true = ⊥

false≢true : false ≡ true → ⊥
false≢true p = subst atFalse p tt

natEq-refl : (n : Nat) → (n == n) ≡ true
natEq-refl zero = refl
natEq-refl (suc n) = natEq-refl n

natEq⇒≡ : (m n : Nat) → (m == n) ≡ true → m ≡ n
natEq⇒≡ zero zero _ = refl
natEq⇒≡ zero (suc _) p = ⊥-elim (false≢true p)
natEq⇒≡ (suc _) zero p = ⊥-elim (false≢true p)
natEq⇒≡ (suc m) (suc n) p = cong suc (natEq⇒≡ m n p)

eqChar : Char → Char → Bool
eqChar a b = primCharToNat a == primCharToNat b

eqChars : List Char → List Char → Bool
eqChars [] [] = true
eqChars (x ∷ xs) (y ∷ ys) = eqChar x y ∧ eqChars xs ys
eqChars _ _ = false

withinList : {A : Set} → List A → Nat → Bool
withinList [] _ = true
withinList (_ ∷ _) zero = false
withinList (_ ∷ xs) (suc k) = withinList xs k

within : {A : Set} → Nat → List A → Bool
within k xs = withinList xs k

withinNat : Nat → Nat → Bool
withinNat zero _ = true
withinNat (suc _) zero = false
withinNat (suc x) (suc k) = withinNat x k

record StringAlg : Set₁ where
  constructor stringAlg
  field
    Str : Set
    toList : Str → List Char
    fromList : List Char → Str
    append : Str → Str → Str
    strEq : Str → Str → Bool
    toListInjective : (a b : Str) → toList a ≡ toList b → a ≡ b
    fromListInjective : (xs ys : List Char) → fromList xs ≡ fromList ys → xs ≡ ys

record SoundStringModel : Set₁ where
  constructor soundStringModel
  field
    atStage : Nat → StringAlg
    toFromWithin : (k : Nat) (xs : List Char) →
                   within k xs ≡ true →
                   StringAlg.toList (atStage k) (StringAlg.fromList (atStage k) xs) ≡ xs
    appendWithin : (k : Nat) (xs ys : List Char) →
                   within k xs ≡ true → within k ys ≡ true → within k (xs ++ ys) ≡ true →
                   StringAlg.append (atStage k) (StringAlg.fromList (atStage k) xs) (StringAlg.fromList (atStage k) ys)
                   ≡ StringAlg.fromList (atStage k) (xs ++ ys)
    strEqWithin : (k : Nat) (xs ys : List Char) →
                  within k xs ≡ true → within k ys ≡ true →
                  StringAlg.strEq (atStage k) (StringAlg.fromList (atStage k) xs) (StringAlg.fromList (atStage k) ys)
                  ≡ eqChars xs ys

record CharAlg : Set₁ where
  constructor charAlg
  field
    Chr : Set
    charToNat : Chr → Nat
    natToChar : Nat → Chr
    charEq : Chr → Chr → Bool
    charToNatInjective : (x y : Chr) → charToNat x ≡ charToNat y → x ≡ y

record SoundCharModel : Set₁ where
  constructor soundCharModel
  field
    atCharStage : Nat → CharAlg
    embedChar : (k : Nat) → Char → CharAlg.Chr (atCharStage k)
    charToNatWithin : (k : Nat) (c : Char) →
                      withinNat (primCharToNat c) k ≡ true →
                      CharAlg.charToNat (atCharStage k) (embedChar k c) ≡ primCharToNat c
    natToCharLaw : (k n : Nat) →
                   CharAlg.natToChar (atCharStage k) n ≡ embedChar k (primNatToChar n)
    charEqLaw : (k : Nat) (c d : Char) →
                CharAlg.charEq (atCharStage k) (embedChar k c) (embedChar k d) ≡ eqChar c d

data CountermodelBundle : Set₁ where
  stringCountermodel :
    (Claim : StringAlg → Set) →
    (M : SoundStringModel) →
    ((k : Nat) → Claim (SoundStringModel.atStage M k) → ⊥) →
    CountermodelBundle
  charCountermodel :
    (Claim : CharAlg → Set) →
    (M : SoundCharModel) →
    ((k : Nat) → Claim (SoundCharModel.atCharStage M k) → ⊥) →
    CountermodelBundle

------------------------------------------------------------------------
-- Standard reusable SoundStringModel & SoundCharModel morphisms
------------------------------------------------------------------------

private
  onBool : {A : Set} (v : Bool) → (v ≡ true → A) → (v ≡ false → A) → A
  onBool true t _ = t refl
  onBool false _ f = f refl

  andTrue : {a b : Bool} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
  andTrue {a} {b} pa pb = trans (cong (λ u → u ∧ b) pa) pb

  cong₂ : {A B C : Set} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
  cong₂ f {x₁} {x₂} {y₁} {y₂} px py = trans (cong (λ u → f u y₁) px) (cong (f x₂) py)

  sameChar : (a b : Char) → eqChar a b ≡ true → a ≡ b
  sameChar a b p = primCharToNatInjective a b (natEq⇒≡ (primCharToNat a) (primCharToNat b) p)

  ifTrue : {A : Set} {v : Bool} (x y : A) → v ≡ true → (if v then x else y) ≡ x
  ifTrue x y p = cong (λ v → if v then x else y) p

  ifFalse : {A : Set} {v : Bool} (x y : A) → v ≡ false → (if v then x else y) ≡ y
  ifFalse x y p = cong (λ v → if v then x else y) p

strEqBroken : Nat → List Char → List Char → Bool
strEqBroken k xs ys = if within k xs ∧ within k ys then eqChars xs ys else false

breakStrEqAlg : Nat → StringAlg
breakStrEqAlg k = stringAlg (List Char) (λ s → s) (λ cs → cs) _++_ (strEqBroken k) (λ _ _ p → p) (λ _ _ p → p)

breakStrEqModel : SoundStringModel
breakStrEqModel = soundStringModel
  breakStrEqAlg
  (λ _ _ _ → refl)
  (λ _ _ _ _ _ _ → refl)
  (λ _ xs ys px py → ifTrue (eqChars xs ys) false (andTrue px py))

swapChar : Char → Char → Char → Char
swapChar a b c = if eqChar c a then b else (if eqChar c b then a else c)

modelHead : Char → Char → Bool → Char → Char
modelHead _ _ true c = c
modelHead a b false c = swapChar a b c

fromListSwapped : Char → Char → Nat → List Char → List Char
fromListSwapped _ _ _ [] = []
fromListSwapped a b k (c ∷ cs) = modelHead a b (within k (c ∷ cs)) c ∷ cs

private
  swapFirst : (a b c : Char) → eqChar c a ≡ true → swapChar a b c ≡ b
  swapFirst a b c = ifTrue b (if eqChar c b then a else c)

  swapSecond : (a b c : Char) → eqChar c a ≡ false → swapChar a b c ≡ (if eqChar c b then a else c)
  swapSecond a b c = ifFalse b (if eqChar c b then a else c)

  swapRight : (a b : Char) → swapChar a b b ≡ a
  swapRight a b = onBool (eqChar b a)
    (λ p → trans (swapFirst a b b p) (sameChar b a p))
    (λ p → trans (swapSecond a b b p) (ifTrue a b (natEq-refl (primCharToNat b))))

  swapInvolution : (a b c : Char) → swapChar a b (swapChar a b c) ≡ c
  swapInvolution a b c = onBool (eqChar c a)
    (λ p → trans (cong (swapChar a b) (swapFirst a b c p)) (trans (swapRight a b) (sym (sameChar c a p))))
    (λ p → onBool (eqChar c b)
      (λ q → trans (cong (swapChar a b) (trans (swapSecond a b c p) (ifTrue a c q)))
                   (trans (swapFirst a b a (natEq-refl (primCharToNat a))) (sym (sameChar c b q))))
      (λ q → let fixed = trans (swapSecond a b c p) (ifFalse a c q)
              in trans (cong (swapChar a b) fixed) fixed))

  headInvolution : (a b : Char) (inside : Bool) (c : Char) →
                   modelHead a b inside (modelHead a b inside c) ≡ c
  headInvolution _ _ true c = refl
  headInvolution a b false c = swapInvolution a b c

  fromListSwappedInv : (a b : Char) (k : Nat) (cs : List Char) →
                       fromListSwapped a b k (fromListSwapped a b k cs) ≡ cs
  fromListSwappedInv _ _ _ [] = refl
  fromListSwappedInv a b zero (c ∷ cs) =
    cong (λ d → d ∷ cs) (swapInvolution a b c)
  fromListSwappedInv a b (suc k) (c ∷ cs) =
    cong (λ d → d ∷ cs) (headInvolution a b (within k cs) c)

  fromListSwappedInj : (a b : Char) (k : Nat) (xs ys : List Char) →
                       fromListSwapped a b k xs ≡ fromListSwapped a b k ys → xs ≡ ys
  fromListSwappedInj a b k xs ys p =
    trans (sym (fromListSwappedInv a b k xs))
          (trans (cong (fromListSwapped a b k) p) (fromListSwappedInv a b k ys))

  toFromSwapped : (a b : Char) (k : Nat) (xs : List Char) →
                  within k xs ≡ true → fromListSwapped a b k xs ≡ xs
  toFromSwapped _ _ _ [] _ = refl
  toFromSwapped a b _ (c ∷ cs) px = cong (λ d → d ∷ cs) (cong (λ v → modelHead a b v c) px)

swapStringAlg : Char → Char → Nat → StringAlg
swapStringAlg a b k = stringAlg
  (List Char)
  (λ s → s)
  (fromListSwapped a b k)
  _++_
  eqChars
  (λ _ _ p → p)
  (fromListSwappedInj a b k)

swapStringModel : Char → Char → SoundStringModel
swapStringModel a b = soundStringModel
  (swapStringAlg a b)
  (toFromSwapped a b)
  (λ k xs ys px py pxy →
    trans (cong₂ _++_ (toFromSwapped a b k xs px) (toFromSwapped a b k ys py))
          (sym (toFromSwapped a b k (xs ++ ys) pxy)))
  (λ k xs ys px py → cong₂ eqChars (toFromSwapped a b k xs px) (toFromSwapped a b k ys py))

PhantomChar : Set
PhantomChar = Char ⊎ ⊤

skipCode : Nat → Nat → Nat
skipCode zero _ = zero
skipCode (suc x) zero = suc (suc x)
skipCode (suc x) (suc k) = suc (skipCode x k)

phantomCharToNat : Nat → PhantomChar → Nat
phantomCharToNat k (inj₁ c) = skipCode (primCharToNat c) k
phantomCharToNat k (inj₂ _) = suc k

phantomNatToChar : Nat → PhantomChar
phantomNatToChar n = inj₁ (primNatToChar n)

phantomCharEq : PhantomChar → PhantomChar → Bool
phantomCharEq (inj₁ c) (inj₁ d) = eqChar c d
phantomCharEq _ _ = false

private
  skipWithin : (x k : Nat) → withinNat x k ≡ true → skipCode x k ≡ x
  skipWithin zero _ _ = refl
  skipWithin (suc _) zero p = ⊥-elim (false≢true p)
  skipWithin (suc x) (suc k) p = cong suc (skipWithin x k p)

  unskip : Nat → Nat → Nat
  unskip zero _ = zero
  unskip (suc x) zero = x
  unskip (suc x) (suc k) = suc (unskip x k)

  unskip-skip : (x k : Nat) → unskip (skipCode x k) k ≡ x
  unskip-skip zero _ = refl
  unskip-skip (suc _) zero = refl
  unskip-skip (suc x) (suc k) = cong suc (unskip-skip x k)

  isOne : Nat → Bool
  isOne zero = false
  isOne (suc zero) = true
  isOne (suc (suc _)) = false

  atGap : Nat → Nat → Bool
  atGap zero x = isOne x
  atGap (suc k) zero = false
  atGap (suc k) (suc x) = atGap k x

  gap-phantom : (k : Nat) → atGap k (suc k) ≡ true
  gap-phantom zero = refl
  gap-phantom (suc k) = gap-phantom k

  gap-skip : (x k : Nat) → atGap k (skipCode x k) ≡ false
  gap-skip zero zero = refl
  gap-skip zero (suc _) = refl
  gap-skip (suc _) zero = refl
  gap-skip (suc x) (suc k) = gap-skip x k

  skip≢gap : (x k : Nat) → skipCode x k ≡ suc k → ⊥
  skip≢gap x k p = false≢true
    (trans (sym (gap-skip x k)) (trans (cong (atGap k) p) (gap-phantom k)))

  phantomCharToNatInj : (k : Nat) (x y : PhantomChar) →
                        phantomCharToNat k x ≡ phantomCharToNat k y → x ≡ y
  phantomCharToNatInj k (inj₁ a) (inj₁ b) p = cong inj₁
    (primCharToNatInjective a b (trans (sym (unskip-skip (primCharToNat a) k))
      (trans (cong (λ u → unskip u k) p) (unskip-skip (primCharToNat b) k))))
  phantomCharToNatInj k (inj₁ a) (inj₂ _) p = ⊥-elim (skip≢gap (primCharToNat a) k p)
  phantomCharToNatInj k (inj₂ _) (inj₁ b) p = ⊥-elim (skip≢gap (primCharToNat b) k (sym p))
  phantomCharToNatInj _ (inj₂ tt) (inj₂ tt) _ = refl

phantomCharAlg : Nat → CharAlg
phantomCharAlg k = charAlg PhantomChar (phantomCharToNat k) phantomNatToChar phantomCharEq (phantomCharToNatInj k)

phantomCharModel : SoundCharModel
phantomCharModel = soundCharModel
  phantomCharAlg
  (λ _ c → inj₁ c)
  (λ k c p → skipWithin (primCharToNat c) k p)
  (λ _ _ → refl)
  (λ _ _ _ → refl)
