{-# OPTIONS --guardedness #-}
module H02_DeinfectedCaller where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import H02_GuardedLib using (Tree; leaf; branch; mirror; leafSum; Stream; hd; tl; natsFrom)

-- Forced to carry `--guardedness` by Agda's infective flag rule, yet 100% of units
-- in this module are pure FastFocus (0 Agda invocations required for H02_DeinfectedCaller!)
mirrorInvol : {A : Set} → (t : Tree A) → Tree A
mirrorInvol t = mirror (mirror t)

_ : leafSum (mirror (branch (leaf 10) (leaf 5))) ≡ 15
_ = refl

takeStream : ℕ → Stream → List ℕ
takeStream zero    _ = []
takeStream (suc n) s = hd s ∷ takeStream n (tl s)

samplePrefix : List ℕ
samplePrefix = takeStream 4 (natsFrom 10)
