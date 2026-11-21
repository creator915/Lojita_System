{-# OPTIONS --guardedness #-}
module N26_BadCoindRecordLit where

open import Data.Nat using (ℕ; zero; suc)

record Stream : Set where
  coinductive
  field
    hd : ℕ
    tl : Stream
open Stream public

-- INVALID in Agda: unguarded self-loop via `record { ... }` literal instead of copatterns!
badLoop : Stream
badLoop = record { hd = zero ; tl = badLoop }
