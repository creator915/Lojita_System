{-# OPTIONS --safe #-}
module L04_AckermannLex where

open import Data.Nat using (ℕ; zero; suc)

ack : ℕ → ℕ → ℕ
ack zero    n       = suc n
ack (suc m) zero    = ack m 1
ack (suc m) (suc n) = ack m (ack (suc m) n)
