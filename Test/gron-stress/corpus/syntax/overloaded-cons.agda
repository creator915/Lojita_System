module OverloadedCons where

open import Data.Bool using (Bool; true)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Unit using (⊤; tt)

flags : List Bool
flags = List._∷_ true List.[]

evidence : All (λ _ → ⊤) flags
evidence = All._∷_ tt All.[]

moreFlags : List Bool
moreFlags = true ∷ flags

moreEvidence : All (λ _ → ⊤) moreFlags
moreEvidence = tt ∷ evidence
