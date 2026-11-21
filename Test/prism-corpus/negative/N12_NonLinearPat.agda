module N12_NonLinearPat where
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
same : ℕ → ℕ → Bool
same x x = true
same _ _ = false
