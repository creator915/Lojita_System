module Gen.T2.JsonInput.Comparison where

  open import Agda.Builtin.Char using (primCharEquality)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Bool using (true)
  open import Data.Char using (Char)
  open import Data.String using (String)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  postulate
    charReflexive : (c : Char) → primCharEquality c c ≡ true
  postulate
    charSound : (c d : Char) → (primCharEquality c d ≡ true) → c ≡ d
  postulate
    stringReflexive : (s : String) → primStringEquality s s ≡ true
  postulate
    stringSound : (s t : String) → (primStringEquality s t ≡ true) → s ≡ t
