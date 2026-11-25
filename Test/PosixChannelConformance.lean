import Gen.Gate2.Channels
import Gen.FzfSelect
import Gen.GronStreamProbe
import Lojita.Kernel.Driver
import Lojita.Ownership.Tools.Relay
import LojitaCtx.FuzzGen

namespace Test.PosixChannelConformance
open LojitaCtx.Terminal LojitaCtx.PosixChannel LojitaCtx.World LojitaCtx.WorldLaws LojitaCtx.Cli
open Lojita.Kernel Lojita.Ownership.Tools LojitaCtx.FuzzGen

-- Specialize the public frame laws and check the operations reduce definitionally.
example (w : SimWorld) : stepPreservesEnv .opReadStdinByte w = rfl := rfl
example (w : SimWorld) : stepPreservesStdio (by decide) (.opWriteTTY [0]) w = rfl := rfl
example (w : SimWorld) : stepPreservesTty (by decide) (.opWriteStdout [255]) w = rfl := rfl

theorem query_preserves_stdout (s : Gen.FzfSelect.Selection) (w : SimWorld) :
    let ev : Event CliCaps := ⟨ttyInCli, .evTTYBytes (bytes "b")⟩
    let next := (runWorldPure (Gen.FzfSelect.app.onStep ev s) w).2
    next.stdio.stdout = w.stdio.stdout ∧ next.stdio.stderr = w.stdio.stderr :=
  Gen.FzfSelect.nonExit_preserves_stdout _ (.ttyBytes (bytes "b")) s w rfl rfl

-- The candidate also handles a query and Enter arriving in one kernel read.
#guard
  let w := pipeWithTTYSimWorld "cand" [] [] false
  let events : List (Event CliCaps) := [⟨stdioInCli, .evStdinBytes (bytes "alpha\nbeta\ngamma\n")⟩,
    ⟨ttyInCli, .evTTYBytes (bytes "beta\r")⟩]
  let (result, next) := runReactivePure Gen.FzfSelect.app events w
  (result matches .inr 0) && next.stdio.stdout.written.data.toList == bytes "beta\n" &&
    next.stdio.stderr.written.isEmpty

def writeLine : CliApp [.stdioCap] := do
  let some line ← readStdinLineW .here | return 1
  writeStdoutW .here (bytes "json = " ++ line.takeWhile (· != 10) ++ bytes ";\n")
  return 0

def twoLines : CliApp [.stdioCap] := do
  if (← writeLine) != 0 then return 1
  writeLine

theorem twoLines_before_eof :
    let (code, w) := runCliPure twoLines (pipeSimWorld "cand" ["--stream"] (bytes "1\n2\nrest") false)
    (code, w.stdio.stdout.written.data.toList, w.stdio.stdin) =
      (0, bytes "json = 1;\njson = 2;\n", openPipe (bytes "rest")) := rfl

abbrev scan := Gen.GronStreamProbe.scanner
abbrev reply := Gen.GronDocument.reply "json"

theorem object_emits : evalScanner scan (openPipe (bytes "{}")) =
    (.emit (reply (bytes "{}")), emptyOpenPipe) := rfl
theorem nul_emits : evalScanner scan (openPipe [0]) = (.emit (reply [0]), emptyOpenPipe) := rfl
theorem delimited_number_emits : evalScanner scan (openPipe (bytes "123 ")) =
    (.emit (reply (bytes "123 ")), emptyOpenPipe) := rfl
theorem number_waits : evalScanner scan (openPipe (bytes "123")) =
    (.wouldBlock, InChan.inChan [] false true) := rfl
theorem string_waits : evalScanner scan (openPipe (bytes "\"a\"")) =
    (.wouldBlock, InChan.inChan [] false true) := rfl

def chunksAsEvents := List.map (Event.mkEvent stdioInCli ∘ EventPayload.evStdinBytes)

theorem partitioned_emit (chunks : List Bytes) (w : SimWorld) (r : StreamReply) (rest : InChan)
    (emits : evalScanner scan (openPipe chunks.flatten) = (.emit r, rest)) :
    runReactivePure (streamScannerApp stdioInCli scan) (chunksAsEvents chunks) w =
    runReactivePure (streamScannerApp stdioInCli scan) (chunksAsEvents [chunks.flatten]) w := by
  apply (streamScannerApp_early_exit stdioInCli scan chunks r rest w emits).trans
  apply (streamScannerApp_early_exit stdioInCli scan [chunks.flatten] r rest w _).symm
  simpa using emits

example (w : SimWorld) :
    let chunks := [bytes "{", [], bytes "\"a\":", bytes "1}", bytes " rest"]
    runReactivePure Gen.GronStreamProbe.document (chunksAsEvents chunks) w =
      runReactivePure Gen.GronStreamProbe.document (chunksAsEvents [chunks.flatten]) w :=
  partitioned_emit _ w (reply (bytes "{\"a\":1}")) (openPipe (bytes " rest")) rfl

example (w : SimWorld) :
    let chunks := [bytes "1", [], bytes "23"]
    let eof : Event CliCaps := ⟨stdioInCli, .evStdinEOF⟩
    runReactivePure Gen.GronStreamProbe.document (chunksAsEvents chunks ++ [eof]) w =
      runReactivePure Gen.GronStreamProbe.document (chunksAsEvents [chunks.flatten] ++ [eof]) w :=
  streamScannerApp_eof_confluent stdioInCli scan _ (reply (bytes "123")) w rfl

-- The 29 literal prefixes and four seeded documents from probe_167.lean.
def examples : List Bytes :=
  ["{}", "[]", "{\"a\":[1", "{\"a\":[1]}", "{\n\t\"a\" : [\"a\\\"[\",true, {}]}",
   "\"a\"", "\"a\"x", "\"\\uD800\\uDC00\"", "\"\\uD800\\uDC00\"-", "\"\\u00x", "true",
   "true!", "null ", "tru", "trux", "-0", "-1.2e+", "-1.2e+2", "-1.2e+2\n",
   "01", "[01", "[1.", "[1.x", "[ 1 , ]", "{\"a\" [", "{\"a\":1,}", "[}", "x", "\r\n "].map bytes

def blocks (n : Nat) : Bytes :=
  bytes ("{\"nested\":[\"[\\\"]\",{\"decimal\":" ++ toString n ++ ".25e-2},[true,null,false]]}")

def prefixes : List Bytes :=
  examples ++ (sampleMany 4 (genBounded 9999) (mkSeed 2026)).map blocks ++ [[0]]

example : prefixes.length = 34 := rfl

private def stimulus : Bytes := [0, 255, 98, 10]

private def observation (allTTY : Bool) (code : ExitCode) (w : SimWorld) : Lean.Json := Id.run do
  let out := w.stdio.stdout.written.data.toList
  let err := w.stdio.stderr.written.data.toList
  let tty := w.tty.ttyOut.data.toList
  -- Channels.report writes stdout, stderr, then /dev/tty in this order.
  let (tty, out, err) := if allTTY then (out ++ err ++ tty, [], []) else (tty, out, err)
  return Lean.Json.mkObj [("tty", hex tty), ("out", hex out), ("err", hex err), ("code", Lean.toJson code)]

private def topologyModel (name : String) (w : SimWorld) : IO (String × Lean.Json) := do
  let (code, cli) := runCliPure Gen.Gate2.Channels.cli w
  if cli.stdio.stdin.waited then throw (IO.userError s!"{name}: CLI waited for EOF")
  let interactive := name == "tty"
  let event (bs : Bytes) : Event CliCaps := if interactive then ⟨ttyInCli, .evTTYBytes bs⟩
    else ⟨stdioInCli, .evStdinBytes bs⟩
  let (.inr rc, reactive) := runReactivePure Gen.Gate2.Channels.reactive
      [event (stimulus.take 2), event (stimulus.drop 2)] w
    | throw (IO.userError s!"{name}: reactive app did not exit")
  return (name, Lean.Json.mkObj [("cli", observation interactive code cli),
    ("reactive", observation interactive rc reactive)])

private def compile (dir : System.FilePath) (bin name entry : String) (mode : ExeMode)
    (deps : List String := []) : IO Unit := do
  let mods ← (name :: deps).mapM fun n => do
    let path := System.FilePath.mk "Test/Posix" / (n.replace "." "/" ++ ".lean")
    IO.ofExcept (parseLeanMod (← IO.FS.readFile path))
  compileVerifiedExe mods ⟨name.splitOn "." ++ [entry]⟩ mode (dir / bin)

def prepare (dir : System.FilePath) : IO Unit := do
  let tty := interactiveSimWorld "cand" [] 24 80 stimulus
  let models ← [("stdio", pipeSimWorld "cand" [] stimulus false),
    ("pipe", pipeWithTTYSimWorld "cand" [] stimulus false),
    ("tty", {tty with stdio := {tty.stdio with stdin := openPipe stimulus}})].mapM
      fun (name, w) => topologyModel name w
  let prefixCase (bs : Bytes) := Lean.Json.mkObj [("input", hex bs),
    ("early", Lean.toJson (!(evalScanner Gen.GronBoundary.scanner (openPipe bs)).1.isBlocked))]
  let model := Lean.Json.mkObj [("topologies", Lean.Json.mkObj models), ("input", hex stimulus),
    ("prefixes", Lean.toJson (prefixes.map prefixCase)),
    ("numberLookahead", Lean.toJson ([bytes "123", bytes "123 "].map prefixCase))]
  IO.FS.writeFile (dir / "model.json") model.compress
  compile dir "VerifiedCli" "Gen.Gate2.Channels" "cli" .cli
  compile dir "VerifiedReactive" "Gen.Gate2.Channels" "reactive" .reactive
  compile dir "VerifiedInterrupted" "Gen.Gate2.Channels" "interrupted" .reactive
  compile dir "VerifiedInputs" "Gen.Gate2.Channels" "inputs" .reactive
  compile dir "VerifiedHangup" "Gen.Gate2.Channels" "hangup" .reactive
  compile dir "VerifiedFzfTTY" "Gen.FzfTTY" "app" .cli
  compile dir "VerifiedFzfSelect" "Gen.FzfSelect" "app" .reactive
  compile dir "VerifiedGronStreamProbe" "Gen.GronStreamProbe" "app" .reactive
    ["Gen.GronDocument", "Gen.GronBoundary"]
  IO.println "Gate 1 passed. Verified object modules compiled for the Linux and cleanroom gates."

def screens (path : System.FilePath) : IO Unit := do
  let [ref, cand] := (← IO.FS.readFile path).trimAscii.toString.splitOn "\n"
    | throw (IO.userError "expected two live fzf terminal observations")
  for (name, frame) in [("ref", ref), ("cand", cand)] do
    let bs ← unhex frame
    let rows := screenLines (stepANSI (blankScreen 24 80) bs)
    unless !bs.isEmpty && (rows.filter (·.contains "beta")).length ≥ 2 do
      throw (IO.userError (name ++ " missing beta query or result row:\n" ++ String.intercalate "\n" rows))
  IO.println "Gate 3 passed. Both live terminal screens rendered beta before acceptance."

end Test.PosixChannelConformance

def main (args : List String) : IO Unit := do
  match args with
  | ["prepare", dir] => Test.PosixChannelConformance.prepare dir
  | ["screens", path] => Test.PosixChannelConformance.screens path
  | _ => throw (IO.userError "expected prepare DIRECTORY or screens FILE")
