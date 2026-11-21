{-# OPTIONS --safe #-}
module N21_UntypedSigmaLet where
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁)
-- Agda rejects unannotated `let p = (n + 1 , n * 2)` with unsolved meta `_B`
-- (`_B (n + 1) =?= ℕ` outside Miller pattern fragment), whereas Lean 4 solves it!
bad : ℕ → ℕ
bad n =
  let p = (n + 1 , n * 2)
  in proj₁ p
