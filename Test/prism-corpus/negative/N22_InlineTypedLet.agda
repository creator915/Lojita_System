module N22_InlineTypedLet where
open import Data.Nat using (ℕ)
-- Valid in Lean/Haskell (`let x : T = 1 in x`), but a PARSE ERROR in Agda!
bad : ℕ
bad = let x : ℕ = 1 in x
