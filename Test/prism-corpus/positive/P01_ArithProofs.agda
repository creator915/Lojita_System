{-# OPTIONS --safe #-}
module P01_ArithProofs where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

sumTo : ℕ → ℕ
sumTo zero    = zero
sumTo (suc n) = suc n + sumTo n

leftZero : (m : ℕ) → 0 + m ≡ m
leftZero m = refl

rightZero : (n : ℕ) → n + 0 ≡ n
rightZero zero    = refl
rightZero (suc n) = cong suc (rightZero n)

_ : double 7 ≡ 14
_ = refl

_ : sumTo 10 ≡ 55
_ = refl
