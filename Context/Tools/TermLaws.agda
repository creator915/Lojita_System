{-# OPTIONS --safe #-}
module Context.Tools.TermLaws where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; foldl)
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Context.Terminal

foldl-++ : ∀ {A B : Set} (f : B → A → B) (acc : B) (xs ys : List A) →
  foldl f acc (xs ++ ys) ≡ foldl f (foldl f acc xs) ys
foldl-++ _ _   []       _  = refl
foldl-++ f acc (x ∷ xs) ys = foldl-++ f (f acc x) xs ys

stepANSI-[] : ∀ (s : Screen) → stepANSI s [] ≡ s
stepANSI-[] _ = refl

stepANSI-∷ : ∀ (s : Screen) (b : Byte) (bs : Bytes) →
  stepANSI s (b ∷ bs) ≡ stepANSI (ansiByte b s) bs
stepANSI-∷ _ _ _ = refl

-- Core ANSI Screen concatenation homomorphism law (`∀ s a b`)
stepANSI-++ : ∀ (s : Screen) (a b : Bytes) →
  stepANSI s (a ++ b) ≡ stepANSI (stepANSI s a) b
stepANSI-++ s a b = foldl-++ (λ t b′ → ansiByte b′ t) s a b

latest-nothing-left : ∀ (x : Maybe ℕ) → latest nothing x ≡ x
latest-nothing-left nothing  = refl
latest-nothing-left (just _) = refl

latest-nothing-right : ∀ (x : Maybe ℕ) → latest x nothing ≡ x
latest-nothing-right _ = refl

latest-assoc : ∀ (a b c : Maybe ℕ) → latest (latest a b) c ≡ latest a (latest b c)
latest-assoc _ _        (just _) = refl
latest-assoc _ nothing  nothing  = refl
latest-assoc _ (just _) nothing  = refl

appendObs-empty-left : ∀ (o : RawTermObs) → appendObs emptyObs o ≡ o
appendObs-empty-left (rawObs t so se ex) rewrite latest-nothing-left ex = refl

appendObs-empty-right : ∀ (o : RawTermObs) → appendObs o emptyObs ≡ o
appendObs-empty-right (rawObs t so se ex)
  rewrite LP.++-identityʳ t | LP.++-identityʳ so | LP.++-identityʳ se = refl

appendObs-assoc : ∀ (a b c : RawTermObs) →
  appendObs (appendObs a b) c ≡ appendObs a (appendObs b c)
appendObs-assoc (rawObs t₁ o₁ e₁ x₁) (rawObs t₂ o₂ e₂ x₂) (rawObs t₃ o₃ e₃ x₃)
  rewrite LP.++-assoc t₁ t₂ t₃
        | LP.++-assoc o₁ o₂ o₃
        | LP.++-assoc e₁ e₂ e₃
        | latest-assoc x₁ x₂ x₃ = refl

advance-zero : ∀ {S E : Set} (h : Handler S E) (m : TimedMachine S E) →
  advance 0 h m ≡ m
advance-zero _ _ = refl

advance-+ : ∀ {S E : Set} (a b : ℕ) (h : Handler S E) (m : TimedMachine S E) →
  advance (a + b) h m ≡ advance b h (advance a h m)
advance-+ zero    _ _ _ = refl
advance-+ (suc a) b h m =
  advance-+ a b h (fireDue (Data.List.length (timers m)) h (record m { now = suc (now m) }))

altScreen-roundtrip : ∀ (s : Screen) → primary s ≡ nothing →
  altScreen false (altScreen true s) ≡ s
altScreen-roundtrip (screen h w act .nothing p) refl = refl
