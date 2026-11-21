{-# OPTIONS --safe #-}
module P04_LetAndMixfix where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infixl 6 _⊕_

_⊕_ : ℕ → ℕ → ℕ
m ⊕ n = m + n + 1

compute : ℕ → ℕ
compute n =
  let p : ℕ × ℕ
      p = (n ⊕ 2 , n * 3)
      (a , b) = p
  in if true ∧ not false then a + b else 0

_ : compute 4 ≡ 19
_ = refl
