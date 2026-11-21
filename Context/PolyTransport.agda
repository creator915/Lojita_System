{-# OPTIONS --safe #-}
module Context.PolyTransport where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; map₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

record PortRel (A B : Set) : Set₁ where
  constructor portRel
  field
    rel : A → B → Set
open PortRel public

idPort : (A : Set) → PortRel A A
idPort A = portRel _≡_

equivPort : {A : Set} → (A → A → Set) → PortRel A A
equivPort = portRel

graphPort : {A B : Set} → (A → B) → PortRel A B
graphPort f = portRel (λ a b → f a ≡ b)

cographPort : {A B : Set} → (B → A) → PortRel A B
cographPort g = portRel (λ a b → a ≡ g b)

tensorPort : {A₁ B₁ A₂ B₂ : Set} → PortRel A₁ B₁ → PortRel A₂ B₂
           → PortRel (A₁ × A₂) (B₁ × B₂)
tensorPort P Q = portRel (λ x y → rel P (proj₁ x) (proj₁ y) × rel Q (proj₂ x) (proj₂ y))

splitPort : {A B₁ B₂ : Set} → (A → B₁ × B₂) → PortRel A (B₁ × B₂)
splitPort = graphPort

mergePort : {A₁ A₂ B : Set} → (A₁ × A₂ → B) → PortRel (A₁ × A₂) B
mergePort = graphPort

introPort : (B : Set) → PortRel ⊤ B
introPort B = portRel (λ _ _ → ⊤)

elimPort : (A : Set) → PortRel A ⊤
elimPort A = portRel (λ _ _ → ⊤)

compPort : {A B C : Set} → PortRel A B → PortRel B C → PortRel A C
compPort {B = B} P Q = portRel (λ a c → Σ B (λ b → rel P a b × rel Q b c))

cut₁ : {A B C D : Set} → (A → B × C) → (B → D) → A → D × C
cut₁ f g a = map₁ g (f a)

cutRel : {A B C D : Set} → (A → B → C → Set) → (B → D → Set) → A → D → C → Set
cutRel {B = B} R S a d c = Σ B (λ b → R a b c × S b d)

TransportsPoly : {Aᵢ Aₒ Bᵢ Bₒ : Set} → PortRel Aᵢ Bᵢ → PortRel Aₒ Bₒ
               → (Aᵢ → Set) → (Aᵢ → Aₒ) → (Bᵢ → Bₒ) → Set
TransportsPoly Rin Rout Dom f g = ∀ x y → Dom x → rel Rin x y → rel Rout (f x) (g y)

Transports₁ : {A B C D : Set} → PortRel A B → PortRel C D
            → (A → Set) → (A → C) → (B → D) → Set
Transports₁ = TransportsPoly

Transports₂ : {A₁ B₁ A₂ B₂ C D : Set} → PortRel A₁ B₁ → PortRel A₂ B₂ → PortRel C D
            → (A₁ → A₂ → Set) → (A₁ → A₂ → C) → (B₁ → B₂ → D) → Set
Transports₂ R₁ R₂ Rout Dom f g = ∀ x₁ x₂ y₁ y₂ → Dom x₁ x₂ → rel R₁ x₁ y₁ → rel R₂ x₂ y₂
                                → rel Rout (f x₁ x₂) (g y₁ y₂)

composeTransportsCut :
  {A A′ B B′ C C′ D D′ : Set}
  {Rin : PortRel A A′} {Rmid : PortRel B B′} {Rc : PortRel C C′} {Rd : PortRel D D′}
  {f : A → B × C} {f′ : A′ → B′ × C′} {g : B → D} {g′ : B′ → D′}
  → TransportsPoly Rin (tensorPort Rmid Rc) (λ _ → ⊤) f f′
  → TransportsPoly Rmid Rd (λ _ → ⊤) g g′
  → TransportsPoly Rin (tensorPort Rd Rc) (λ _ → ⊤) (cut₁ f g) (cut₁ f′ g′)
composeTransportsCut {f = f} {f′} first second x y dom related with first x y dom related
... | mid , side = second (proj₁ (f x)) (proj₁ (f′ y)) tt mid , side

-- At p = project inputLift and q = project outputLift, the last two
-- types reduce to Context.Blueprint.Commutes₁ for the respective bases.
transportLiftCube :
  {A B U V : Set} (p : U → A) (q : V → B)
  {Dom : U → Set} {b₀ b₀′ : A → B} {u : U → V}
  → TransportsPoly (idPort A) (idPort B) (λ _ → ⊤) b₀ b₀′
  → (∀ x → Dom x → q (u x) ≡ b₀ (p x))
  → (∀ x → Dom x → q (u x) ≡ b₀′ (p x))
transportLiftCube p q base upper x dom = trans (upper x dom) (base (p x) (p x) tt refl)
