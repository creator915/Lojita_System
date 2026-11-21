{-# OPTIONS --guardedness #-}
module H03_HybridLexAndWithMain where

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import IO using (Main; run; putStrLn)

-- F₁: Fast helper
scale : ℕ → ℕ
scale n = n * 3

_ : scale 4 ≡ 12
_ = refl

-- S₁: Multi-argument lexicographic Foetus recursion
ack : ℕ → ℕ → ℕ
ack zero    n       = suc n
ack (suc m) zero    = ack m 1
ack (suc m) (suc n) = ack m (ack (suc m) n)

_ : ack 2 2 ≡ 7
_ = refl

-- S₂: Multi-function mutual recursion + with-abstraction clause
mutual
  isEven : ℕ → Bool
  isEven zero    = true
  isEven (suc n) = isOdd n

  isOdd : ℕ → Bool
  isOdd zero    = false
  isOdd (suc n) = isEven n

parityLabel : ℕ → String
parityLabel n with isEven n
... | true  = "even"
... | false = "odd"

-- F₂: Fast downstream formatting & Main
formatReport : ℕ → String
formatReport k = "ack=" ++ˢ show k ++ˢ ",parity=" ++ˢ parityLabel k

main : Main
main = run (putStrLn (formatReport (ack 2 3)))
