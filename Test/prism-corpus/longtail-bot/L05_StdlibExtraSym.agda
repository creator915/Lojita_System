{-# OPTIONS --safe #-}
module L05_StdlibExtraSym where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

singletonVec : ℕ → Vec ℕ (suc zero)
singletonVec x = x ∷ []

_ : singletonVec 4 ≡ 4 ∷ []
_ = refl
