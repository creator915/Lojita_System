module Context.Blueprint where

open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

record PortLift (Base Upper : Set) : Set₁ where
  constructor portLift
  field
    project : Upper → Base
open PortLift public

keepPort : (A : Set) → PortLift A A
keepPort A = portLift (λ a → a)

fromEl : {Base : Set} (El : Base → Set) → PortLift Base (Σ Base El)
fromEl El = portLift proj₁

FiberOf : {B U : Set} → PortLift B U → B → Set
FiberOf {U = U} p b = Σ U (λ u → project p u ≡ b)

composeLift : {A B C : Set} → PortLift A B → PortLift B C → PortLift A C
composeLift p q = portLift (λ c → project p (project q c))

Commutes₁ : {A B U V : Set} → PortLift A U → PortLift B V
          → (U → Set) → (B → B → Set) → (A → B) → (U → V) → Set
Commutes₁ p q Dom _≈_ f g = ∀ u → Dom u → project q (g u) ≈ f (project p u)

Commutes₂ : {A B C U V W : Set} → PortLift A U → PortLift B V → PortLift C W
          → (U → V → Set) → (C → C → Set) → (A → B → C) → (U → V → W) → Set
Commutes₂ p q r Dom _≈_ f g = ∀ u v → Dom u v → project r (g u v) ≈ f (project p u) (project q v)

Commutes₃ : {A B C D U V W X : Set} → PortLift A U → PortLift B V → PortLift C W → PortLift D X
          → (U → V → W → Set) → (D → D → Set) → (A → B → C → D) → (U → V → W → X) → Set
Commutes₃ p q r s Dom _≈_ f g = ∀ u v w → Dom u v w → project s (g u v w) ≈ f (project p u) (project q v) (project r w)
