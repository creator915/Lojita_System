import Lojita

namespace Test.KernelTaboos
open Lojita.Kernel Lean

structure MetricResult (α : Type) where
  value    : α
  elapsedMs : Nat
  rssDeltaKB : Nat

def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError s!"ASSERTION_FAILED: {message}")

def q (s : String) : QName := ⟨s.splitOn "."⟩

def parseMod (s : String) : IO LeanMod :=
  IO.ofExcept (parseLeanMod s)

def mkObject (ns body : String) (imports : List String := []) : IO LeanMod :=
  parseMod (String.intercalate "\n"
    ((imports.map ("import " ++ ·)) ++ ["namespace " ++ ns, body, "end " ++ ns]))

def errorTag (message : String) : String :=
  ((message.splitOn ":").headD "").trimAscii.toString

/-- Execute an action inside a worker thread (`IO.asTask`), measuring wall-clock ms and RSS delta.
    Asserts RSS delta stays strictly below `maxRssDeltaMB` (default `256 MiB`). -/
def runMeasuredOnWorker {α : Type} (label : String) (maxMs : Nat) (act : IO α)
    (maxRssDeltaMB : Nat := 256) (dedicated : Bool := false) :
    IO (MetricResult α) := do
  initKernelLimits
  let rssBefore ← readProcessRssKB
  let t0 ← IO.monoNanosNow
  let task ← if dedicated then IO.asTask (prio := .dedicated) act else IO.asTask act
  let res ← IO.wait task
  let elapsedMs := ((← IO.monoNanosNow) - t0) / 1000000
  let rssAfter ← readProcessRssKB
  let rssDeltaKB := if rssAfter > rssBefore then rssAfter - rssBefore else 0
  let value ← match res with
    | .ok v    => pure v
    | .error e => throw e
  ensure (elapsedMs <= maxMs)
    s!"[{label}] exceeded time limit: {elapsedMs} ms > {maxMs} ms"
  ensure (rssDeltaKB <= maxRssDeltaMB * 1024)
    s!"[{label}] exceeded RSS delta limit: {rssDeltaKB / 1024} MiB > {maxRssDeltaMB} MiB"
  return { value, elapsedMs, rssDeltaKB }

/-- Expect `act` to fail on a worker thread within `maxMs` and `maxRssDeltaMB`,
    returning `(errorMessage, elapsedMs, rssDeltaKB)`. -/
def expectRejectedBounded {α : Type} (label : String) (expectedSubstring : String)
    (maxMs : Nat) (act : IO α) (maxRssDeltaMB : Nat := 256) :
    IO (String × Nat × Nat) := do
  let wrapped : IO (Option String) := do
    try
      discard act
      return none
    catch e =>
      return some (toString e)
  let m ← runMeasuredOnWorker label maxMs wrapped maxRssDeltaMB (dedicated := false)
  let some msg := m.value
    | throw (IO.userError s!"[{label}] UNEXPECTEDLY ACCEPTED input that must fail with `{expectedSubstring}`")
  ensure (msg.contains expectedSubstring)
    s!"[{label}] expected error containing `{expectedSubstring}`, but got:\n{msg.take 600}"
  return (msg, m.elapsedMs, m.rssDeltaKB)

def expectErrorCode {α : Type} (expectedCode : String) (act : IO α) : IO Unit := do
  let err? ← try
      discard act
      pure none
    catch e =>
      pure (some (toString e))
  let some msg := err?
    | throw (IO.userError s!"accepted input requiring `{expectedCode}`")
  ensure (errorTag msg == expectedCode)
    s!"expected code `{expectedCode}`, got `{errorTag msg}`:\n{msg.take 400}"

def expectSyntaxCode (expectedCode src : String) : IO Unit := do
  match readEnvelope src with
  | .ok _    => throw (IO.userError s!"accepted syntax requiring `{expectedCode}`:\n{src.take 200}")
  | .error e =>
    ensure (e.code == expectedCode) s!"expected syntax code `{expectedCode}`, got `{e}`"

end Test.KernelTaboos
