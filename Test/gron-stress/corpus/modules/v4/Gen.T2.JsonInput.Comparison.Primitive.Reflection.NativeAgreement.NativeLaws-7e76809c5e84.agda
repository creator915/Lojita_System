module Gen.T2.JsonInput.Comparison.Primitive.Reflection.NativeAgreement.NativeLaws where

  open import Agda.Builtin.Char using (primCharEquality)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Bool using (true)
  open import Data.Char using (Char)
  open import Data.String using (String)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  postulate
    char-sound : (c d : Char) → (primCharEquality c d ≡ true) → c ≡ d
  postulate
    char-complete : (c d : Char) → (c ≡ d) → primCharEquality c d ≡ true
  postulate
    string-sound : (s t : String) → (primStringEquality s t ≡ true) → s ≡ t
  postulate
    string-complete : (s t : String) → (s ≡ t) → primStringEquality s t ≡ true
