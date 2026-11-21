module Gen.T2.JsonInput.Comparison.Primitive.Reflection where

  open import Agda.Builtin.Char using (primCharEquality)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Bool using (true; false)
  open import Data.Char using (Char)
  open import Data.String using (String)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  postulate
    charEqual : (c d : Char) → (c ≡ d) → primCharEquality c d ≡ true
  postulate
    charDifferent : (c d : Char) → (c ≢ d) → primCharEquality c d ≡ false
  postulate
    stringEqual : (s t : String) → (s ≡ t) → primStringEquality s t ≡ true
  postulate
    stringDifferent : (s t : String) → (s ≢ t) → primStringEquality s t ≡ false
