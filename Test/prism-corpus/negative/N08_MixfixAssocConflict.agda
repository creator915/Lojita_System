module N08_MixfixAssocConflict where
open import Data.Nat using (ℕ; _+_)
infixl 6 _⊕_
infixr 6 _⊗_
_⊕_ : ℕ → ℕ → ℕ
a ⊕ b = a + b
_⊗_ : ℕ → ℕ → ℕ
a ⊗ b = a + b
bad : ℕ
bad = 1 ⊕ 2 ⊗ 3
