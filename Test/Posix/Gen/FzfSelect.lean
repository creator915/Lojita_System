import LojitaCtx.Cli

namespace Gen.FzfSelect
open LojitaCtx.Terminal LojitaCtx.World LojitaCtx.Cli

structure Selection where
  lines : Array String := #[]
  lineRev : Bytes := []
  queryRev : Bytes := []

def ingest (s : Selection) (b : Byte) : Selection :=
  if b == 10 then {s with lines := s.lines.push (decodeUtf8Lossy s.lineRev.reverse), lineRev := []}
  else {s with lineRev := b :: s.lineRev}

def matchesQuery (s : Selection) (query : String) : List String := Id.run do
  let mut visible := #[]
  for line in s.lines do
    if query.isEmpty || line.contains query then
      visible := visible.push line
      if visible.size == 20 then break
  return visible.toList

def frame (s : Selection) (accept : Bool) : Selection × Bytes × Option (Bytes × ExitCode) :=
  let query := decodeUtf8Lossy s.queryRev.reverse
  let visible := matchesQuery s query
  let ui := bytes ("\x1b[H\x1b[J> " ++ query ++ "\r\n" ++ String.intercalate "\r\n" visible)
  let selected := if accept then some (match visible with
    | line :: _ => (bytes (line ++ "\n"), 0)
    | [] => ([], 1)) else none
  (s, ui, selected)

def keys (s : Selection) : Bytes → Selection × Bytes × Option (Bytes × ExitCode)
  | [] => frame s false
  | b :: bs =>
    if b == 13 || b == 10 then frame s true
    else if b == 127 || b == 8 then keys {s with queryRev := s.queryRev.drop 1} bs
    else keys {s with queryRev := b :: s.queryRev} bs
termination_by structural bs => bs

def spec : TuiSpec Selection where
  init := {}
  step
    | .stdinChunk bs, s => frame (bs.foldl ingest s) false
    | .stdinEOF, s => frame (if s.lineRev.isEmpty then s else ingest s 10) false
    | .ttyBytes bs, s => keys s bs
    | _, s => (s, [], none)

def app : ReactiveApp CliCaps Selection := tuiReactiveApp stdioInCli ttyInCli true spec

theorem nonExit_preserves_stdout (ev : Event CliCaps) (inp : TuiInput) (s : Selection) (w : SimWorld)
    (classified : classifyEvent ev = some inp) (running : (spec.step inp s).2.2 = none) :
    let w' := (runWorldPure (app.onStep ev s) w).2
    w'.stdio.stdout = w.stdio.stdout ∧ w'.stdio.stderr = w.stdio.stderr :=
  tuiReactiveApp_nonExit_preserves_stdout stdioInCli ttyInCli true spec ev inp s w classified running

end Gen.FzfSelect
