import LojitaCtx.Terminal

namespace LojitaCtx.Clock

open LojitaCtx.Terminal

structure SimClock : Type where
  simClock ::
  monoMs      : Nat
  wallEpochMs : Nat
  autoTicks   : List Nat

def initClock (mono wall : Nat) (ticks : List Nat) : SimClock :=
  SimClock.simClock mono wall ticks

def zeroClock : SimClock :=
  SimClock.simClock 0 0 []

def fixedStepClock (mono wall count delta : Nat) : SimClock :=
  SimClock.simClock mono wall (List.replicate count delta)

def popTick : List Nat → (Nat × (List Nat))
  | []      => Prod.mk 0 []
  | d :: ds => Prod.mk d ds

def advanceClock (d : Nat) (c : SimClock) : SimClock :=
  { c with
    monoMs      := (d + c.monoMs)
    wallEpochMs := (d + c.wallEpochMs) }

def tickClock (c : SimClock) : SimClock :=
  let dt := popTick c.autoTicks
  let d  := dt.1
  { c with
    monoMs      := (d + c.monoMs)
    wallEpochMs := (d + c.wallEpochMs)
    autoTicks   := dt.2 }

def readMonoMs (c : SimClock) : (Nat × SimClock) :=
  let c' := tickClock c
  Prod.mk c'.monoMs c'

def readWallMs (c : SimClock) : (Nat × SimClock) :=
  let c' := tickClock c
  Prod.mk c'.wallEpochMs c'

def sleepClockMs : Nat → SimClock → SimClock :=
  advanceClock

def deadlineReached (deadline : Nat) (c : SimClock) : Bool :=
  (deadline ≤ c.monoMs)

def remainingMs (deadline : Nat) (c : SimClock) : Nat :=
  (deadline - c.monoMs)

def withTimeoutClock {A : Type} (timeoutMs costMs : Nat) (result : A) (c : SimClock) :
    Option A × SimClock :=
  let effTimeout := if timeoutMs == 0 then 30000 else timeoutMs
  let timedOut := effTimeout ≤ costMs
  let spent := if timedOut then effTimeout else costMs
  let val := if timedOut then .none else .some result
  Prod.mk val (advanceClock spent c)

inductive ClockStep : Type where
  | stepNowMono       : ClockStep
  | stepNowWall       : ClockStep
  | stepSleepMs       : Nat → ClockStep
  | stepCheckDeadline : Nat → ClockStep

structure RawClockObs : Type where
  rawClockObs ::
  observedMs : Nat
  expired    : Bool

def stepSimClock : ClockStep → SimClock → (SimClock × RawClockObs)
  | .stepNowMono, c =>
      let r := readMonoMs c
      Prod.mk r.2 (RawClockObs.rawClockObs r.1 false)
  | .stepNowWall, c =>
      let r := readWallMs c
      Prod.mk r.2 (RawClockObs.rawClockObs r.1 false)
  | .stepSleepMs d, c =>
      let c' := sleepClockMs d c
      Prod.mk c' (RawClockObs.rawClockObs c'.monoMs false)
  | .stepCheckDeadline dl, c =>
      Prod.mk c (RawClockObs.rawClockObs c.monoMs (deadlineReached dl c))

def traceSimClock : List ClockStep → SimClock → List RawClockObs
  | [], _ => []
  | s :: ss, c =>
      let r := stepSimClock s c
      r.2 :: traceSimClock ss r.1
termination_by structural ss _ => ss

def foldClockSteps : List ClockStep → SimClock → SimClock
  | [], st      => st
  | s :: ss, st => foldClockSteps ss (stepSimClock s st).1
termination_by structural ss _ => ss

theorem traceSimClockAppend :
    (xs ys : List ClockStep) →
      (c : SimClock) →
        traceSimClock (xs ++ ys) c = traceSimClock xs c ++ traceSimClock ys (foldClockSteps xs c)
  | [], _, _ => rfl
  | s :: xs, ys, c =>
    congrArg ((stepSimClock s c).2 :: ·) (traceSimClockAppend xs ys (stepSimClock s c).1)
termination_by structural x _ _ => x

end LojitaCtx.Clock
