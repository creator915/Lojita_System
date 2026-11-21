module Gen.T2.JsonInput.Comparison.Primitive.Reflection.NativeAgreement.NativeLaws.Agreement where

  open import Agda.Builtin.Char using (primCharEquality)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Char using (Char)
  open import Data.String using (String)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Relation.Nullary using (does)
  import Data.Char.Properties as CharProps
  import Data.String.Properties as StringProps
  postulate
    char-agrees : (c d : Char) → primCharEquality c d ≡ does (c CharProps.≟ d)
  postulate
    string-agrees : (s t : String) → primStringEquality s t ≡ does (s StringProps.≟ t)
