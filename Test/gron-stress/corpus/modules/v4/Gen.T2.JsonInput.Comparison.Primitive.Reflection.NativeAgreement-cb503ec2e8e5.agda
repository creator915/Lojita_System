module Gen.T2.JsonInput.Comparison.Primitive.Reflection.NativeAgreement where

  open import Agda.Builtin.Char using (primCharEquality)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Char using (Char)
  open import Data.String using (String)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Relation.Nullary using (does)
  import Data.Char as Char using (_≟_)
  import Data.String as String using (_≟_)
  postulate
    char-agrees : (c d : Char) → primCharEquality c d ≡ does (c Char.≟ d)
  postulate
    string-agrees : (s t : String) → primStringEquality s t ≡ does (s String.≟ t)
