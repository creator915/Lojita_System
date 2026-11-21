{-# OPTIONS --safe #-}
module P06_ClassicalNotNot where

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)

-- Constructive double-negation monad and Friedman A-translation monad:
NotNot : Set → Set
NotNot A = (A → ⊥) → ⊥

nnPure : {A : Set} → A → NotNot A
nnPure a = λ k → k a

nnBind : {A B : Set} → NotNot A → (A → NotNot B) → NotNot B
nnBind m f = λ kb → m (λ a → f a kb)

-- Excluded Middle holds constructively inside NotNot with ZERO classical axioms:
nnLEM : (A : Set) → NotNot (A ⊎ ¬ A)
nnLEM A = λ k → k (inj₂ (λ a → k (inj₁ a)))

-- Friedman continuation monad (extracts witnesses for Π⁰₂ specs):
Cont : Set → Set → Set
Cont R A = (A → R) → R

callCC : {R A B : Set} → ((A → Cont R B) → Cont R A) → Cont R A
callCC f = λ k → f (λ a _ → k a) k
