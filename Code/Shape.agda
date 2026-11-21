module Code.Shape where

open import Data.List using (List)
open import Data.Product using (_×_)
open import Code using (Name)

data HomeShape : Set where
  node : List (Name × HomeShape) → HomeShape
