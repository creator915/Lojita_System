module M0 where

open import Data.Nat using (ℕ; _<_; _<ᵇ_)
open import Data.Nat.Properties using (<ᵇ⇒<)
open import Data.Bool using (T)

data A : Set where
  one two : A

surrogateBound : (n : ℕ) → T (56319 <ᵇ n) → 56319 < n
surrogateBound n = <ᵇ⇒< 56319 n
