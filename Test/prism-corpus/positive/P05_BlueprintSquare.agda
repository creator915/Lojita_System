module P05_BlueprintSquare where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Context.Blueprint using (PortLift; portLift; Commutes₁)

parity : ℕ → ℕ
parity n = n

stepUpper : ℕ → ℕ
stepUpper n = suc n

liftId : PortLift ℕ ℕ
liftId = portLift parity

squareOK : Commutes₁ liftId liftId (λ _ → ⊤) _≡_ stepUpper stepUpper
squareOK u _ = refl
