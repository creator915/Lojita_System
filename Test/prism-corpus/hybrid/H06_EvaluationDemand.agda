{-# OPTIONS --guardedness #-}
module H06_EvaluationDemand where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using (show)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import IO using (Main; run; putStrLn)

-- A terminating, expensive subterm makes eager evaluation observable.
cost : ℕ → ℕ → ℕ
cost zero seed = seed
cost (suc n) seed = cost n (suc seed) + cost n (suc (suc seed))

cold : ℕ
cold = cost 42 0

select : Bool → ℕ → ℕ
select false _       = 7
select true  zero    = 8
select true  (suc n) = n

ordered : Bool → ℕ → ℕ
ordered true zero = 0
ordered true _    = 1
ordered false _   = 2

fallthrough : Bool → ℕ → ℕ
fallthrough false _       = 3
fallthrough _     zero    = 4
fallthrough _     (suc n) = n

data Alternatives : Set where
  both : ℕ → ℕ → Alternatives

second : Alternatives → ℕ
second (both a b) = b

record Choices : Set where
  field unused chosen : ℕ

project : Bool → Choices → ℕ
project true  p = Choices.unused p
project false p = Choices.chosen p

evidence : ℕ → zero ≡ zero
evidence zero = refl
evidence (suc n) = evidence n

use : zero ≡ zero → ℕ
use refl = 1

instance
  trivial : zero ≡ zero
  trivial = refl

one : {{p : zero ≡ zero}} → ℕ
one = 1

first : ℕ → ℕ → ℕ
first x _ = x

apply : (ℕ → ℕ → ℕ) → ℕ
apply f = f 1 (cost 42 7)

main : Main
main = run (putStrLn (show
  (select false cold + select true 3
   + ordered false (cost 42 4) + fallthrough false (cost 42 5)
   + ordered true 1 + fallthrough true 2
   + second (both (cost 42 1) 4)
   + project false (record { unused = cost 42 2 ; chosen = 5 })
   + use (evidence (cost 42 3)) + one + one {{evidence (cost 42 6)}}
   + apply first + apply (λ (x y : ℕ) → x))))
