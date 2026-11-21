{-# OPTIONS --safe #-}
module Test.WorldReactiveTarget where

open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Fin using () renaming (toℕ to octet)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.String using () renaming (_++_ to _++ˢ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Context.Terminal using (Bytes)
open import Context.World

RCaps : List Cap
RCaps = clockCap ∷ ttyCap ∷ []

tty∈RCaps : ttyCap ∈ RCaps
tty∈RCaps = there here

hasQuitByte : Bytes → Bool
hasQuitByte []       = false
hasQuitByte (b ∷ bs) = (octet b ≡ᵇ 113) ∨ hasQuitByte bs

handlePayload : ∀ {c} → EventPayload c → ℕ → WorldProg RCaps (ℕ ⊎ ExitCode)
handlePayload (evTTYBytes bs) cnt =
  if hasQuitByte bs then
    (writeStdoutStrW tty∈RCaps ("DONE:" ++ˢ show cnt ++ˢ "\n") >>w pure (inj₂ 0))
  else
    (let next = cnt + length bs in
     writeStdoutStrW tty∈RCaps ("STEP:" ++ˢ show next ++ˢ "\n") >>w pure (inj₁ next))
handlePayload (evResize r c) cnt =
  writeStdoutStrW tty∈RCaps ("RESIZE:" ++ˢ show r ++ˢ "x" ++ˢ show c ++ˢ "\n") >>w
  pure (inj₁ cnt)
handlePayload _ cnt =
  pure (inj₁ cnt)

reactiveCounter : ReactiveApp RCaps ℕ
reactiveCounter = reactiveApp
  (writeStdoutStrW tty∈RCaps "READY\n" >>w pure 0)
  (λ ev cnt → handlePayload (evPayload ev) cnt)
