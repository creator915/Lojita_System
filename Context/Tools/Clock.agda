{-# OPTIONS --safe #-}
module Context.Tools.Clock where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- Deterministic logical + wall clock parameterized by initial timestamps and
-- an explicit tick-step schedule (milliseconds advanced per clock query).
-- Note: `d + monoMs c` places the step delta on the left of `_+_` so that
-- `advanceClock 0 c` reduces definitionally (`refl`) to `c` via record η!
record SimClock : Set where
  constructor simClock
  field
    monoMs      : ℕ
    wallEpochMs : ℕ
    autoTicks   : List ℕ
open SimClock public

initClock : ℕ → ℕ → List ℕ → SimClock
initClock mono wall ticks = simClock mono wall ticks

zeroClock : SimClock
zeroClock = simClock 0 0 []

fixedStepClock : ℕ → ℕ → ℕ → ℕ → SimClock
fixedStepClock mono wall count delta = simClock mono wall (replicate count delta)

popTick : List ℕ → ℕ × List ℕ
popTick []       = 0 , []
popTick (d ∷ ds) = d , ds

advanceClock : ℕ → SimClock → SimClock
advanceClock d c = record c
  { monoMs      = d + monoMs c
  ; wallEpochMs = d + wallEpochMs c
  }

tickClock : SimClock → SimClock
tickClock c =
  let dt = popTick (autoTicks c)
      d  = proj₁ dt
  in record c
       { monoMs      = d + monoMs c
       ; wallEpochMs = d + wallEpochMs c
       ; autoTicks   = proj₂ dt
       }

readMonoMs : SimClock → ℕ × SimClock
readMonoMs c =
  let c′ = tickClock c
  in monoMs c′ , c′

readWallMs : SimClock → ℕ × SimClock
readWallMs c =
  let c′ = tickClock c
  in wallEpochMs c′ , c′

sleepClockMs : ℕ → SimClock → SimClock
sleepClockMs = advanceClock

deadlineReached : ℕ → SimClock → Bool
deadlineReached deadline c = deadline ≤ᵇ monoMs c

remainingMs : ℕ → SimClock → ℕ
remainingMs deadline c = deadline ∸ monoMs c

-- Simulate an operation taking `costMs` against `timeoutMs` (0 = 30000ms default).
withTimeoutClock : ∀ {A : Set} → ℕ → ℕ → A → SimClock → Maybe A × SimClock
withTimeoutClock timeoutMs costMs result c =
  let effTimeout = if timeoutMs ≡ᵇ 0 then 30000 else timeoutMs
      timedOut   = effTimeout ≤ᵇ costMs
      spent      = if timedOut then effTimeout else costMs
      val        = if timedOut then nothing else just result
  in val , advanceClock spent c

data ClockStep : Set where
  stepNowMono       : ClockStep
  stepNowWall       : ClockStep
  stepSleepMs       : ℕ → ClockStep
  stepCheckDeadline : ℕ → ClockStep

record RawClockObs : Set where
  constructor rawClockObs
  field
    observedMs : ℕ
    expired    : Bool
open RawClockObs public

stepSimClock : ClockStep → SimClock → SimClock × RawClockObs
stepSimClock stepNowMono c =
  let r = readMonoMs c in proj₂ r , rawClockObs (proj₁ r) false
stepSimClock stepNowWall c =
  let r = readWallMs c in proj₂ r , rawClockObs (proj₁ r) false
stepSimClock (stepSleepMs d) c =
  let c′ = sleepClockMs d c in c′ , rawClockObs (monoMs c′) false
stepSimClock (stepCheckDeadline dl) c =
  c , rawClockObs (monoMs c) (deadlineReached dl c)

traceSimClock : List ClockStep → SimClock → List RawClockObs
traceSimClock []       _ = []
traceSimClock (s ∷ ss) c =
  let r = stepSimClock s c
  in proj₂ r ∷ traceSimClock ss (proj₁ r)
