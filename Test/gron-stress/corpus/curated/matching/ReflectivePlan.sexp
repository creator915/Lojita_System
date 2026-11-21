(submission (kind plan) (why "gron stress") (main @proof) (moves))
```agda proof
module Gen.T2.JsonInput where

open import Context.Tools.FsSandbox using (eqStr)
open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Context.Tools.FsLaws using (eqStr-refl)

data Json : Set where
  jsonNull : Json
  jsonBool : Bool → Json
  jsonNumber : String → Json
  jsonText : String → Json
  jsonObject : List (String × Json) → Json
  jsonArray : List Json → Json

matchingValues : String → List (String × Json) → List Json
matchingValues k [] = []
matchingValues k ((l , v) ∷ fields) = if eqStr k l then matchingValues k fields ++ [ v ] else matchingValues k fields

noMatchingValues : ∀ k → matchingValues k [] ≡ []
noMatchingValues k = refl

nextMatchingValue : ∀ k v fields → matchingValues k ((k , v) ∷ fields) ≡ (matchingValues k fields ++ [ v ])
nextMatchingValue k v fields = cong (λ b → if b then matchingValues k fields ++ [ v ] else matchingValues k fields) (eqStr-refl k)

otherMatchingValue : ∀ k l v fields → eqStr k l ≡ false → matchingValues k ((l , v) ∷ fields) ≡ matchingValues k fields
otherMatchingValue k l v fields h = cong (λ b → if b then matchingValues k fields ++ [ v ] else matchingValues k fields) h
```
