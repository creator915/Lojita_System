{-# OPTIONS --safe #-}
module Context.Tools.FuzzGen where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using () renaming (toℕ to octet)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Product using (_×_; _,_; proj₁)
open import Context.Terminal using (Byte; Bytes; byte; bytes)

-- A full-period 32-bit LCG. Agda's builtin natural arithmetic and
-- division primitives make closed-seed normalization inexpensive.
record Seed : Set where
  constructor seed
  field state : ℕ
open Seed public

mkSeed : ℕ → Seed
mkSeed n = seed (n % 4294967296)

nextNat : Seed → ℕ × Seed
nextNat s = n , seed n
  where n = (1664525 * state s + 1013904223) % 4294967296

Gen : Set → Set
Gen A = Seed → A × Seed

runGen : ∀ {A : Set} → Gen A → Seed → A × Seed
runGen g s = g s

genPure : ∀ {A : Set} → A → Gen A
genPure a s = a , s

genMap : ∀ {A B : Set} → (A → B) → Gen A → Gen B
genMap f g s with g s
... | a , t = f a , t

genBind : ∀ {A B : Set} → Gen A → (A → Gen B) → Gen B
genBind g f s with g s
... | a , t = f a t

genPair : ∀ {A B : Set} → Gen A → Gen B → Gen (A × B)
genPair a b = genBind a (λ x → genMap (λ y → x , y) b)

genBounded : ℕ → Gen ℕ
genBounded n = genMap (λ k → k % suc n) nextNat

genBool : Gen Bool
genBool = genMap (λ n → n ≡ᵇ 1) (genBounded 1)

genByte : Gen Byte
genByte = genMap byte (genBounded 255)

-- genList has a fixed length; genBytes samples a length in 0..bound.
genList : ∀ {A : Set} → ℕ → Gen A → Gen (List A)
genList zero g = genPure []
genList (suc n) g = genBind g (λ x → genMap (λ xs → x ∷ xs) (genList n g))

genBytes : ℕ → Gen Bytes
genBytes n = genBind (genBounded n) (λ k → genList k genByte)

chooseAt : ∀ {A : Set} → A → ℕ → List A → A
chooseAt d n [] = d
chooseAt d zero (x ∷ xs) = x
chooseAt d (suc n) (x ∷ xs) = chooseAt d n xs

genChoose : ∀ {A : Set} → A → List A → Gen A
genChoose d xs = genMap (λ n → chooseAt d n (d ∷ xs)) (genBounded (length xs))

sampleMany : ∀ {A : Set} → ℕ → Gen A → Seed → List A
sampleMany zero g s = []
sampleMany (suc n) g s with g s
... | x , t = x ∷ sampleMany n g t

Shrinker : Set → Set
Shrinker A = A → List A

-- Candidates are strictly smaller and duplicates are omitted.
shrinkNat : ℕ → List ℕ
shrinkNat zero = []
shrinkNat (suc n) = 0 ∷ (if h ≡ᵇ 0 then [] else h ∷ []) ++
  (if (n ≡ᵇ 0) then [] else if n ≡ᵇ h then [] else n ∷ [])
  where h = suc n / 2

shrinkByte : Byte → List Byte
shrinkByte b = map byte (shrinkNat (octet b))

-- Every position can be deleted or shrunk; recursive tails retain their prefix.
shrinkList : ∀ {A : Set} → Shrinker A → Shrinker (List A)
shrinkList shrink [] = []
shrinkList shrink (x ∷ xs) = xs ∷
  (map (λ y → y ∷ xs) (shrink x) ++ map (λ ys → x ∷ ys) (shrinkList shrink xs))

shrinkBytes : Shrinker Bytes
shrinkBytes = shrinkList shrinkByte

firstFailure : ∀ {A : Set} → (A → Bool) → List A → Maybe A
firstFailure ok [] = nothing
firstFailure ok (x ∷ xs) = if ok x then firstFailure ok xs else just x

minimize : ∀ {A : Set} → ℕ → Shrinker A → (A → Bool) → A → A
minimize zero shrink ok x = x
minimize (suc fuel) shrink ok x with firstFailure ok (shrink x)
... | nothing = x
... | just y = minimize fuel shrink ok y

fuzzCheck : ∀ {A : Set} → ℕ → ℕ → Gen A → Shrinker A → (A → Bool) → Seed → Maybe A
fuzzCheck zero fuel g shrink ok s = nothing
fuzzCheck (suc count) fuel g shrink ok s with g s
... | x , t = if ok x then fuzzCheck count fuel g shrink ok t
  else just (minimize fuel shrink ok x)
