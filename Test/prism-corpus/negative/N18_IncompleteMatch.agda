{-# OPTIONS --safe #-}
module N18_IncompleteMatch where
open import Data.Nat using (ℕ; zero)
bad : ℕ → ℕ
bad zero = zero
