module N07_MixfixNonAssocChain where
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
bad : Set
bad = 1 ≡ 2 ≡ 3
