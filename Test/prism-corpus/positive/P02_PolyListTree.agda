{-# OPTIONS --safe #-}
module P02_PolyListTree where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length; reverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

data Tree (A : Set) : Set where
  leaf   : A → Tree A
  branch : Tree A → Tree A → Tree A

mirror : {A : Set} → Tree A → Tree A
mirror (leaf x)     = leaf x
mirror (branch l r) = branch (mirror r) (mirror l)

mirrorInv : {A : Set} → (t : Tree A) → mirror (mirror t) ≡ t
mirrorInv (leaf _)     = refl
mirrorInv (branch l r) = cong₂ branch (mirrorInv l) (mirrorInv r)

flatten : {A : Set} → Tree A → List A
flatten (leaf x)     = x ∷ []
flatten (branch l r) = flatten l ++ flatten r

_ : length (reverse (flatten (branch (leaf 1) (leaf 2)))) ≡ 2
_ = refl
