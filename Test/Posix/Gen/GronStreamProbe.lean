import Gen.GronDocument

namespace Gen.GronStreamProbe
open LojitaCtx.Terminal LojitaCtx.PosixChannel LojitaCtx.World LojitaCtx.Cli

abbrev Scan := Gen.GronBoundary.Boundary × Bytes

def scanner : ByteScanner Scan StreamReply where
  init := (Gen.GronBoundary.start, [])
  onByte
    | (s, rev), b =>
      let acc := b :: rev
      match Gen.GronBoundary.advance s b with
      | some next => .more (next, acc)
      | none => .done (Gen.GronDocument.reply "json" acc.reverse)
  onEOF s := Gen.GronDocument.reply "json" s.2.reverse

def document := streamScannerApp stdioInCli scanner

inductive Lines where
  | stream (index : Nat)
  | ungron (root : Option Bytes)

inductive Mode where
  | scanning (s : Scan)
  | reading (lines : Lines) (lineRev : Bytes)

def ungronReply (root : Option Bytes) : StreamReply :=
  match root with
  | some value => ⟨value ++ [10], [], 0⟩
  | none => ⟨[], bytes "no statements were parsed\n", 5⟩

-- In inverse mode the reference collects statements through EOF. A blank
-- line contributes no statement, so an empty group fails when stdin closes.
def lineStep (lines : Lines) (line : Bytes) : WorldProg CliCaps (Sum Lines ExitCode) := do
  match lines with
  | .stream i =>
    let r := Gen.GronDocument.reply ("json[" ++ toString i ++ "]") line
    let code ← emitStreamReply stdioInCli r
    return if code == 0 then .inl (.stream (i + 1)) else .inr code
  | .ungron root =>
    let s := (decodeUtf8Lossy line).trimAscii
    if s.startsWith "json = " && s.endsWith ";" then
      return .inl (.ungron (some (bytes ((s.drop 7).dropEnd 1).toString)))
    return .inl (.ungron root)

def feedLines (lines : Lines) (rev : Bytes) : Bytes → WorldProg CliCaps (Sum Mode ExitCode)
  | [] => pure (.inl (.reading lines rev))
  | b :: bs => do
    if b == 10 then
      match ← lineStep lines rev.reverse with
      | .inl next => feedLines next [] bs
      | .inr code => return .inr code
    else feedLines lines (b :: rev) bs
termination_by structural bs => bs

def finishLines (lines : Lines) (rev : Bytes) : WorldProg CliCaps (Sum Mode ExitCode) := do
  let result ← if rev.isEmpty then pure (.inl lines) else lineStep lines rev.reverse
  match result with
  | .inr code => return .inr code
  | .inl (.stream _) => return .inr 0
  | .inl (.ungron root) => return .inr (← emitStreamReply stdioInCli (ungronReply root))

def app : ReactiveApp CliCaps Mode where
  init := do
    match ← getArgsW envInCli with
    | ["--stream"] =>
      writeStdoutStrW stdioInCli (Gen.GronDocument.assignment "json" "[]")
      return .reading (.stream 0) []
    | ["--ungron"] => return .reading (.ungron none) []
    | _ => return .scanning (← document.init)
  onStep ev state := match state with
    | .scanning s => mapWorld (Sum.map Mode.scanning id) (document.onStep ev s)
    | .reading lines rev => match ev with
      | ⟨_, .evStdinBytes bs⟩ => feedLines lines rev bs
      | ⟨_, .evStdinEOF⟩ => finishLines lines rev
      | _ => pure (.inl state)

end Gen.GronStreamProbe
