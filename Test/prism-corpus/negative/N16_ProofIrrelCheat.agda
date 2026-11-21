{-# OPTIONS --safe #-}
module N16_ProofIrrelCheat where
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- Lean 4 `Prop` `Eq` equates open `p q` by `rfl`, whereas Agda `_≡_` in `Set` rejects it!
cheat : (x y : ℕ) → (p q : x ≡ y) → p ≡ q
cheat x y p q = refl
