{-# OPTIONS --guardedness #-}
module N27_TypeErrorInF2AfterCoind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true)
open import Data.List using (List; []; _∷_)

record Stream : Set where
  coinductive
  field
    hd : ℕ
    tl : Stream
open Stream public

from : ℕ → Stream
hd (from n) = n
tl (from n) = from (suc n)

takeStream : ℕ → Stream → List ℕ
takeStream zero    _ = []
takeStream (suc n) s = hd s ∷ takeStream n (tl s)

-- INVALID in F₂: passes `true : Bool` where `ℕ` is expected!
-- Caught by Lean 4 FastFocus kernel check in <400ms without even invoking Agda!
badCaller : List ℕ
badCaller = takeStream true (from 0)
