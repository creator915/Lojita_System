{-# OPTIONS --guardedness #-}
module M1 where
import M0

record Stream : Set where
  coinductive
  field
    head : M0.A
    tail : Stream
open Stream

g : M0.A → Stream
head (g a) = a
tail (g a) = g a
