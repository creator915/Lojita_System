{-# OPTIONS --safe #-}
module Meta.Boundary where

open import Agda.Builtin.Char using (primCharEquality)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool.Base using (Bool; true; false; not; _∨_; _∧_)
open import Data.Char.Base using (Char; isSpace; toℕ)
open import Data.List.Base using (List; []; _∷_; all)
open import Data.String.Base using (String; toList)
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_; _∉_)
open import Data.Nat.Base using (_<ᵇ_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Nullary using (yes; no)

reservedPrefixes : List String
reservedPrefixes = "Ownership" ∷ "OwnershipIO" ∷ "Code" ∷ "Store" ∷ "Meta" ∷
                   "Backend" ∷ "Test" ∷ "Verification" ∷ "SessionEnv" ∷ "Main" ∷ "UI" ∷ []

ModulePath : Set
ModulePath = List String

firstSegment : ModulePath → String
firstSegment [] = ""
firstSegment (n ∷ _) = n

-- A QName segment must fit in one filename component. In particular a
-- constructed Code cannot use a dotted segment to hide a reserved prefix.
validPart : String → Bool
validPart s = not (primStringEquality s "") ∧ all allowed (toList s)
  where
  allowed : Char → Bool
  allowed c = not (isSpace c ∨ (toℕ c <ᵇ 32) ∨ primCharEquality c '.' ∨
                   primCharEquality c '/' ∨ primCharEquality c '\\')

entryMain : ModulePath → Bool
entryMain (n ∷ []) = primStringEquality n "Main"
entryMain _ = false

objectNamespace : Bool → ModulePath → Bool
objectNamespace allowEntryMain [] = false
objectNamespace allowEntryMain path@(n ∷ rest) with n ∈? reservedPrefixes
... | yes _ = allowEntryMain ∧ entryMain path
... | no _ = all validPart path

entryAllowedImport : ModulePath → Bool
entryAllowedImport ("OwnershipIO" ∷ "WorldRunner" ∷ []) = true
entryAllowedImport ("OwnershipIO" ∷ "FFI" ∷ [])         = true
entryAllowedImport path = objectNamespace false path

checkModulePaths : Bool → ModulePath → List ModulePath → Bool
checkModulePaths false name imports =
  objectNamespace false name ∧ all (objectNamespace false) imports
checkModulePaths true name imports =
  objectNamespace true name ∧ all entryAllowedImport imports

-- Code.agda has no --safe annotation. This projection is instantiated with
-- Code.modName and the AST's import paths in Meta.Sandbox. The theorem is
-- independent of the projection, and specializes to those exact fields.
record ModuleView (Code : Set) : Set where
  constructor moduleView
  field
    modulePath : Code → ModulePath
    importPaths : Code → List ModulePath
open ModuleView {{...}} public

module _ {Code : Set} {{view : ModuleView Code}} where
  checkObjectModuleSafe : Bool → Code → Bool
  checkObjectModuleSafe allow c = checkModulePaths allow (modulePath c) (importPaths c)

  ordinary-prefix-safe : (c : Code) → checkObjectModuleSafe false c ≡ true →
                         firstSegment (modulePath c) ∉ reservedPrefixes
  ordinary-prefix-safe c with modulePath c
  ... | [] = λ ()
  ... | n ∷ ns with n ∈? reservedPrefixes
  ...   | yes _ = λ ()
  ...   | no absent = λ _ → absent
