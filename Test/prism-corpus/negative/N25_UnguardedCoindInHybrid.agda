{-# OPTIONS --guardedness #-}
module N25_UnguardedCoindInHybrid where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)

fastDouble : ℕ → ℕ
fastDouble zero    = zero
fastDouble (suc n) = suc (suc (fastDouble n))

record Stream : Set where
  coinductive
  field
    hd : ℕ
    tl : Stream
open Stream public

-- INVALID in Agda: `tl badStream` on RHS is NOT guarded by coinductive constructor!
badStream : Stream
hd badStream = fastDouble 3
tl badStream = tl badStream

takeS : ℕ → Stream → List ℕ
takeS zero    _ = []
takeS (suc n) s = hd s ∷ takeS n (tl s)
