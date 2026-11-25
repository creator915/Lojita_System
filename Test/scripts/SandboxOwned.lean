import Lojita.Sandbox.LinuxIso

open System Lojita.Store.TreeCAS Lojita.Sandbox.LinuxIso

private def check (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw <| IO.userError msg

def main (args : List String) : IO Unit := do
  let [launcher, binary] := args | throw <| IO.userError "expected native launcher and probe"
  IO.FS.withTempDir fun top => do
    let store := top / "store"
    let fixture := top / "fixtures"
    let seed := top / "seed"
    IO.FS.createDir fixture
    IO.FS.createDir seed
    IO.FS.writeFile (fixture / "immutable") "original"
    IO.FS.writeFile (seed / "keep") "unchanged"
    let fixtureHash ← captureDir store fixture
    let input ← captureDir store seed
    let host : Host := {
      store := store, launcher := launcher, executable := binary, fixtures := fixtureHash,
      timeoutMs := 2000, captureBytes := 4 }
    let bytes : ByteArray := ⟨#[0,255,128,10]⟩
    let (result,output) ← run host input {args := #["cas"], stdin := bytes}
    check (result.code == 125 && !result.timedOut) "payload exit status"
    check (result.stdout.data == bytes && !result.stdout.truncated) "binary stdout"
    check (result.stderr.data == "abcd".toUTF8 && result.stderr.truncated) "bounded stderr"
    check (input != output) "work snapshot update"
    verifyTree store fixtureHash
    verifyTree store input
    verifyTree store output
    let restored := top / "restored"
    materialize store output restored
    check ((← IO.FS.readBinFile (restored / "saved")) == bytes) "CAS binary output"
    check ((← IO.FS.readFile (restored / "keep")) == "unchanged") "preserved seed"
    let (timed,after) ← run {host with timeoutMs := 100} output {args := #["wait"]}
    check (timed.timedOut && timed.code == 124 && after == output) "timeout resource recovery"
    let broken := top / "broken"
    IO.FS.writeFile broken "invalid executable"
    let refused ← try
      let _ ← run {host with executable := broken} input {}
      pure false
    catch _ => pure true
    check refused "an infrastructure failure must not be published as a candidate exit"
    check ((← captureDir store fixture) == fixtureHash) "fixture unchanged"
    IO.println "LinuxIso binary I/O, output cap, failure, timeout and TreeCAS return passed."
