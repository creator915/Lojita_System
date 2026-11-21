{-# OPTIONS --safe #-}
module N19_TypeMismatch where
open import Data.Nat using (ℕ)
open import Data.Bool using (true)
bad : ℕ
bad = true
