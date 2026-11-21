{-# OPTIONS --safe #-}
-- Agda 2.6.3 reports cubical transport warnings for indexed matches in the
-- imported stdlib modules. This datatype has no pattern matches.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Context.Taboo where

open import Agda.Builtin.Char using (primCharEquality)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Char.Base using (Char)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (∃)
open import Data.String.Base using (String; toList; fromList)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

data SafeTaboo : Set where
  taboo-⊥             : ⊥ → SafeTaboo
  taboo-primStrRefl   : (∀ (s : String) → primStringEquality s s ≡ true) → SafeTaboo
  taboo-primCharRefl  : (∀ (c : Char) → primCharEquality c c ≡ true) → SafeTaboo
  taboo-strRoundtrip  : (∀ (s : String) → fromList (toList s) ≡ s) → SafeTaboo
  taboo-listRoundtrip : (∀ (cs : List Char) → toList (fromList cs) ≡ cs) → SafeTaboo
  taboo-funExtBool    : (∀ (f g : ℕ → Bool) → (∀ n → f n ≡ g n) → f ≡ g) → SafeTaboo
  taboo-wlpo          : (∀ (f : ℕ → Bool) → (∀ n → f n ≡ false) ⊎ (∃ λ n → f n ≡ true)) → SafeTaboo
  taboo-markov        : (∀ (f : ℕ → Bool) → ((∀ n → f n ≡ false) → ⊥) → ∃ λ n → f n ≡ true) → SafeTaboo
