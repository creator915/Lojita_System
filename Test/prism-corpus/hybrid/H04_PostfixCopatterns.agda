{-# OPTIONS --guardedness #-}
module H04_PostfixCopatterns where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- F₁
toggleVal : Bool → ℕ
toggleVal true  = 10
toggleVal false = 1

_ : toggleVal true + toggleVal false ≡ 11
_ = refl

-- S: Postfix `.hd` / `.tl` copatterns with heterogeneous pattern splits across projections!
record Stream : Set where
  coinductive
  field
    hd : ℕ
    tl : Stream
open Stream public

altStream : Bool → Stream
altStream b     .hd = toggleVal b
altStream true  .tl = altStream false
altStream false .tl = altStream true

-- F₂
takeS : ℕ → Stream → List ℕ
takeS zero    _ = []
takeS (suc n) s = hd s ∷ takeS n (tl s)
