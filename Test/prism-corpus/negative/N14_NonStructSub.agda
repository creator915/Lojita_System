{-# OPTIONS --safe #-}
module N14_NonStructSub where
open import Data.Nat using (ℕ; zero; suc; _∸_)
-- Default Lean 4 `WellFounded + omega` accepts `suc n ∸ 1`, whereas Agda Foetus rejects it!
bad : ℕ → ℕ
bad zero    = zero
bad (suc n) = bad (suc n ∸ 1)
