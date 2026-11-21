{-# OPTIONS --safe #-}
module N15_RightZeroRefl where
open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- Lean 4 `Nat.add` reduces `n + 0` by `rfl`, whereas Agda `_+_` gets stuck on open `n`!
bad : (n : ℕ) → n + 0 ≡ n
bad n = refl
