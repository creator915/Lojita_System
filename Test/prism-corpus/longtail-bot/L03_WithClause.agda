{-# OPTIONS --safe #-}
module L03_WithClause where

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false)

eqZero : ℕ → Bool
eqZero n with n ≡ᵇ 0
... | true  = true
... | false = false
