module Gen.T2.JsonInput.Comparison.Primitive.Reflection.NativeAgreement.NativeLaws where

  open import Agda.Builtin.Char using (primCharEquality)
  open import Agda.Builtin.String using (primStringEquality)
  open import Agda.Builtin.TrustMe using (primTrustMe)
  open import Data.Bool using (Bool; true; false)
  open import Data.Char using (Char)
  open import Data.Empty using (⊥-elim)
  open import Data.String using (String)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
  open import Relation.Nullary using (Dec; yes; no)
  import Data.Char.Properties as CharProps
  import Data.String.Properties as StringProps
  private
    answer : {P : Set} → Dec P → Bool
    answer (yes _) = true
    answer (no _) = false
  private
    answer-sound : {P : Set} → (decision : Dec P) → (answer decision ≡ true) → P
    answer-sound (yes proof) _ = proof
    answer-sound (no _) ()
  private
    answer-complete : {P : Set} → (decision : Dec P) → P → answer decision ≡ true
    answer-complete (yes _) _ = refl
    answer-complete (no refute) proof = ⊥-elim (refute proof)
  private
    char-native : (c d : Char) → primCharEquality c d ≡ answer (c CharProps.≟ d)
    char-native c d = primTrustMe
  private
    string-native : (s t : String) → primStringEquality s t ≡ answer (s StringProps.≟ t)
    string-native s t = primTrustMe
  char-sound : (c d : Char) → (primCharEquality c d ≡ true) → c ≡ d
  char-sound c d proof = answer-sound (c CharProps.≟ d) (trans (sym (char-native c d)) proof)
  char-complete : (c d : Char) → (c ≡ d) → primCharEquality c d ≡ true
  char-complete c d proof = trans (char-native c d) (answer-complete (c CharProps.≟ d) proof)
  string-sound : (s t : String) → (primStringEquality s t ≡ true) → s ≡ t
  string-sound s t proof = answer-sound (s StringProps.≟ t) (trans (sym (string-native s t)) proof)
  string-complete : (s t : String) → (s ≡ t) → primStringEquality s t ≡ true
  string-complete s t proof = trans (string-native s t) (answer-complete (s StringProps.≟ t) proof)
