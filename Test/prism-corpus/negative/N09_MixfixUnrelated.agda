module N09_MixfixUnrelated where
open import Data.Nat using (ℕ; _+_)
-- Unannotated operators default to non-associative `infix 20` in Agda:
-- mixing two unannotated operators `1 ⊕ 2 ⊗ 3` without parens is a parse ambiguity error!
_⊕_ : ℕ → ℕ → ℕ
a ⊕ b = a + b
_⊗_ : ℕ → ℕ → ℕ
a ⊗ b = a + b
bad : ℕ
bad = 1 ⊕ 2 ⊗ 3
