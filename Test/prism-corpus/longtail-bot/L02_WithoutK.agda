{-# OPTIONS --without-K --safe #-}
module L02_WithoutK where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

idNat : ℕ → ℕ
idNat n = n

_ : idNat 3 ≡ 3
_ = refl
