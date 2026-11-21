module N11_ForwardRefNoMutual where
open import Data.Nat using (ℕ; suc)
f : ℕ → ℕ
f n = g n

g : ℕ → ℕ
g n = suc n
