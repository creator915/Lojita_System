{-# OPTIONS --safe #-}
module P03_RecordEtaSigma where

open import Data.Nat using (ℕ; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record PairBox (A B : Set) : Set where
  constructor mkBox
  field
    fstB : A
    sndB : B
open PairBox public

swapBox : {A B : Set} → PairBox A B → PairBox B A
swapBox b = record { fstB = sndB b ; sndB = fstB b }

bumpBox : PairBox ℕ Bool → PairBox ℕ Bool
bumpBox b = record b { fstB = fstB b + 1 }

-- Tests judgmental η-equality on both `⊤` and `×` (`AgdaSigma`):
unitEta : (u : ⊤) → u ≡ tt
unitEta _ = refl

prodEta : {A B : Set} → (p : A × B) → (proj₁ p , proj₂ p) ≡ p
prodEta _ = refl

_ : fstB (bumpBox (mkBox 41 true)) ≡ 42
_ = refl
