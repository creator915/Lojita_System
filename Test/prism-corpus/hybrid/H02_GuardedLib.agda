{-# OPTIONS --guardedness #-}
module H02_GuardedLib where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Pure sweet-spot units inside a --guardedness module
data Tree (A : Set) : Set where
  leaf   : A → Tree A
  branch : Tree A → Tree A → Tree A

mirror : {A : Set} → Tree A → Tree A
mirror (leaf x)     = leaf x
mirror (branch l r) = branch (mirror r) (mirror l)

leafSum : Tree ℕ → ℕ
leafSum (leaf n)     = n
leafSum (branch l r) = leafSum l + leafSum r

_ : leafSum (branch (leaf 3) (leaf 4)) ≡ 7
_ = refl

-- Coinductive residual inside the same library module
record Stream : Set where
  coinductive
  field
    hd : ℕ
    tl : Stream
open Stream public

natsFrom : ℕ → Stream
hd (natsFrom n) = n
tl (natsFrom n) = natsFrom (suc n)
