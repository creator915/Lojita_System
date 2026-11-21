(submission (kind independent) (why "gron stress") (refute @proof))
```agda proof
module UnprovableRefute where

import Gen.T2.JsonInput as Spec
open import Context.Taboo using (SafeTaboo; taboo-primStrRefl)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

present : List Spec.Json → Bool
present [] = false
present (_ ∷ _) = true

appended : List Spec.Json → Bool
appended xs = present (xs ++ (Spec.jsonNull ∷ []))

impossibleMiss : (k : String) → primStringEquality k k ≡ false → true ≡ false
impossibleMiss k p = trans (sym (cong appended (Spec.noMatchingValues k)))
  (trans (sym (cong present (Spec.nextMatchingValue k Spec.jsonNull [])))
    (trans (cong present (Spec.otherMatchingValue k k Spec.jsonNull [] p))
      (cong present (Spec.noMatchingValues k))))

mustMatch : (b : Bool) → (b ≡ false → true ≡ false) → b ≡ true
mustMatch true h = refl
mustMatch false h = sym (h refl)

witness : SafeTaboo
witness = taboo-primStrRefl (λ k → mustMatch (primStringEquality k k) (impossibleMiss k))
```
