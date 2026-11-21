{-# OPTIONS --guardedness #-}
module SharedPureHelperSig where
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data A : Set where
  one two : A

h : A → Bool
h one = true
h two = false

f : (a : A) → h a ≡ h a
f a = refl

record Stream (b : Bool) : Set where
  coinductive
  field
    head : Bool
    tail : Stream b
open Stream

g : (a : A) → Stream (h a)
head (g a) = h a
tail (g a) = g a
