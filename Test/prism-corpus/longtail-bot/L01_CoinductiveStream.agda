{-# OPTIONS --guardedness #-}
module L01_CoinductiveStream where

open import Data.Nat using (ℕ; zero; suc)

record Stream : Set where
  coinductive
  field
    hd : ℕ
    tl : Stream
open Stream public

from : ℕ → Stream
hd (from n) = n
tl (from n) = from (suc n)
