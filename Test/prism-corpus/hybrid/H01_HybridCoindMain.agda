{-# OPTIONS --guardedness #-}
module H01_HybridCoindMain where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Show using (show)
open import Data.List using (List; []; _∷_)
open import Data.String using () renaming (_++_ to _++ˢ_)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import IO using (Main; run; putStrLn)

-- §1 Fast Focus F₁ (verified 100% by Lean 4; abstracted as module params in SlowSlice.agda)
tri : ℕ → ℕ
tri zero    = zero
tri (suc n) = suc n + tri n

_ : tri 6 ≡ 21
_ = refl

fastStep : ℕ → ℕ
fastStep n = n + tri 2

fastWeight : ℕ → ℕ
fastWeight n = n * 2 + 1

sumList : List ℕ → ℕ
sumList []       = zero
sumList (x ∷ xs) = x + sumList xs

_ : sumList (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
_ = refl

-- §2 Minimal Exotic Residual S (checked by Agda --guardedness; lowered to Thunk + partial def)
record Stream : Set where
  coinductive
  field
    hd : ℕ
    tl : Stream
open Stream public

orbitFrom : ℕ → Stream
hd (orbitFrom n) = fastWeight n
tl (orbitFrom n) = orbitFrom (fastStep n)

-- §3 Fast Downstream Callers F₂ (verified 100% by Lean 4 against opaque ∂_S; omitted from SlowSlice)
takeStream : ℕ → Stream → List ℕ
takeStream zero    _ = []
takeStream (suc k) s = hd s ∷ takeStream k (tl s)

prefixScore : ℕ → Stream → ℕ
prefixScore k s = sumList (takeStream k s)

main : Main
main = run (putStrLn ("score=" ++ˢ show (prefixScore 5 (orbitFrom 1))))
