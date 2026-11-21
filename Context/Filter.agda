module Context.Filter where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Char using (Char; toLower)
open import Agda.Builtin.Char using (primCharEquality)
open import Data.List using (List; []; _∷_; map; reverse)
open import Data.String using (String; toList)
open import Context.Blueprint using (PortLift; portLift)

data Mode : Set where
  sensitive insensitive : Mode

data Kind : Set where
  prefix suffix exclude : Kind

record Signal : Set where
  constructor signal
  field
    kind : Kind
    exact folded : Bool
open Signal public

record Input : Set where
  constructor input
  field
    operation : Kind
    needle text : String
open Input public

starts : List Char → List Char → Bool
starts [] _ = true
starts (_ ∷ _) [] = false
starts (p ∷ ps) (c ∷ cs) = primCharEquality p c ∧ starts ps cs

contains : List Char → List Char → Bool
contains [] _ = true
contains (_ ∷ _) [] = false
contains ps (c ∷ cs) = starts ps (c ∷ cs) ∨ contains ps cs

hit : Kind → List Char → List Char → Bool
hit prefix p s = starts p s
hit suffix p s = starts (reverse p) (reverse s)
hit exclude p s = contains p s

classify : Input → Signal
classify (input k p s) = signal k (hit k (toList p) (toList s)) (hit k (map toLower (toList p)) (map toLower (toList s)))

choose : Mode → Signal → Bool
choose sensitive s = exact s
choose insensitive s = folded s

combine : Kind → Bool → Bool
combine prefix b = b
combine suffix b = b
combine exclude b = not b

expected0 : Mode → Signal → Bool
expected0 mode s = combine (kind s) (choose mode s)

expected1 : Mode → Input → Bool
expected1 mode i = expected0 mode (classify i)

inputPort : PortLift Signal Input
inputPort = portLift classify
