{-# OPTIONS --safe #-}
module Context.Tools.ClockLaws where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
import Data.Nat.Properties as NP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Context.Tools.Clock

advanceClock-zero : ∀ (c : SimClock) → advanceClock 0 c ≡ c
advanceClock-zero _ = refl

advanceClock-add : ∀ (a b : ℕ) (c : SimClock) →
  advanceClock (a + b) c ≡ advanceClock a (advanceClock b c)
advanceClock-add a b c =
  cong₂ (λ m w → simClock m w (autoTicks c))
    (NP.+-assoc a b (monoMs c))
    (NP.+-assoc a b (wallEpochMs c))

advanceClock-comm : ∀ (a b : ℕ) (c : SimClock) →
  advanceClock a (advanceClock b c) ≡ advanceClock b (advanceClock a c)
advanceClock-comm a b c =
  trans (sym (advanceClock-add a b c))
    (trans (cong (λ k → advanceClock k c) (NP.+-comm a b))
      (advanceClock-add b a c))

advanceClock-mono≤ : ∀ (d : ℕ) (c : SimClock) →
  monoMs c ≤ monoMs (advanceClock d c)
advanceClock-mono≤ d c = NP.m≤n+m (monoMs c) d

advanceClock-wall≤ : ∀ (d : ℕ) (c : SimClock) →
  wallEpochMs c ≤ wallEpochMs (advanceClock d c)
advanceClock-wall≤ d c = NP.m≤n+m (wallEpochMs c) d

advanceClock-ticks : ∀ (d : ℕ) (c : SimClock) →
  autoTicks (advanceClock d c) ≡ autoTicks c
advanceClock-ticks _ _ = refl

readMono-monotonic : ∀ (c : SimClock) → monoMs c ≤ proj₁ (readMonoMs c)
readMono-monotonic c = NP.m≤n+m (monoMs c) (proj₁ (popTick (autoTicks c)))

readWall-monotonic : ∀ (c : SimClock) → wallEpochMs c ≤ proj₁ (readWallMs c)
readWall-monotonic c = NP.m≤n+m (wallEpochMs c) (proj₁ (popTick (autoTicks c)))

readMono-idle : ∀ (m w : ℕ) → readMonoMs (simClock m w []) ≡ (m , simClock m w [])
readMono-idle _ _ = refl

sleepClock-zero : ∀ (c : SimClock) → sleepClockMs 0 c ≡ c
sleepClock-zero _ = refl

sleepClock-add : ∀ (a b : ℕ) (c : SimClock) →
  sleepClockMs (a + b) c ≡ sleepClockMs a (sleepClockMs b c)
sleepClock-add = advanceClock-add

foldClockSteps : List ClockStep → SimClock → SimClock
foldClockSteps []       st = st
foldClockSteps (s ∷ ss) st = foldClockSteps ss (proj₁ (stepSimClock s st))

traceSimClock-++ : ∀ (xs ys : List ClockStep) (c : SimClock) →
  traceSimClock (xs ++ ys) c ≡ traceSimClock xs c ++ traceSimClock ys (foldClockSteps xs c)
traceSimClock-++ []       _  _ = refl
traceSimClock-++ (s ∷ xs) ys c =
  cong (proj₂ (stepSimClock s c) ∷_) (traceSimClock-++ xs ys (proj₁ (stepSimClock s c)))
