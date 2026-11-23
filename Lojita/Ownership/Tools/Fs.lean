import Lojita.Ownership.Tools.Relay

namespace Lojita.Ownership.Tools.Fs
open LojitaCtx.Terminal LojitaCtx.FsSandbox

def fsSpec := OwnedSpec "fsbox" FsConfig Bytes FsStep RawFsObs FsConfig.ownedFiles

def command : FsStep → String
  | .runCmd exe args input ms => runRequest exe args input ms
  | .writeFileStep p bs => s!"W {hexText p} {hex bs}"
  | .mkdirStep p mode => s!"D {hexText p} {maskMode mode}"
  | .symlinkStep p dst => s!"L {hexText p} {hexText dst}"
  | .chmodStep p mode => s!"M {hexText p} {maskMode mode}"
  | .unlinkStep p => s!"U {hexText p}"
  | .snapshotStep => "S"

def request (p : Pipe) (line : String) : IO RawFsObs := do
  let ["O", out, err, code, timed, count] ← exchange p line | throw (IO.userError "invalid filesystem reply")
  let result ← status code
  requireWire (line.startsWith "R " || result.isNone) "filesystem operation rejected"
  let mut entries := #[]
  for _ in [:← natural count] do
    let ["F", path, kind, mode, data] := (← readLine p).splitOn " " | throw (IO.userError "invalid snapshot entry")
    let k ← match kind with
      | "0" => pure FsNodeKind.regularNode | "1" => pure .dirNode | "2" => pure .symlinkNode
      | _ => throw (IO.userError "invalid snapshot node kind")
    entries := entries.push ⟨← wireText path, k, ← natural mode, ← unhex data⟩
  return ⟨← unhex out, ← unhex err, result, ← flag timed, entries.toList⟩

private def fixturePath : FsFixture → String
  | .fixDir p _ | .fixFile p .. | .fixSymlink p _ => p

private def setup (cfg : FsConfig) (owned : ModelsIO (filesCtx Bytes cfg.ownedFiles)) (p : Pipe) : IO Unit := do
  let send := fun q => discard (request p (command q))
  for (k, v) in cfg.envVars do discard <| request p ("E " ++ hexText (k ++ "=" ++ v))
  let dirs := (cfg.fixtures.filterMap fun | .fixDir path mode => some (path, mode) | _ => none)
    |>.mergeSort (fun a b => a.1.length ≤ b.1.length)
  for (path, _) in dirs do send (.mkdirStep path 493)
  visitFiles (fun name bs => send (.writeFileStep name bs)) cfg.ownedFiles owned
  for fixture in cfg.fixtures do
    match fixture with
    | .fixDir .. => pure ()
    | .fixFile path mode bs => send (.writeFileStep path bs) *> send (.chmodStep path mode)
    | .fixSymlink path dst => send (.symlinkStep path dst)
  for (path, mode) in dirs.reverse do send (.chmodStep path mode)

def fsToolWithMount (bin scratch : System.FilePath) (candidate : Option System.FilePath) : HandlerIO fsSpec := fun cfg owned => do
  checkEnv cfg.envVars
  let paths := cfg.ownedFiles ++ cfg.fixtures.map fixturePath
  let leaves := cfg.ownedFiles ++ cfg.fixtures.filterMap (fun | .fixDir .. => none | f => some (fixturePath f))
  requireWire (paths.all validRelPath && paths.eraseDups.length == paths.length &&
    leaves.all (fun leaf => !paths.any (isParent leaf))) "invalid or overlapping filesystem fixtures"
  openBytes bin scratch cfg.target cfg.ownedFiles owned #[] (setup cfg owned)
    (fun p q => request p (command q)) (fun p => discard (request p "Q")) false candidate

def fsTool (bin scratch : System.FilePath) : HandlerIO fsSpec :=
  fsToolWithMount bin scratch none

end Lojita.Ownership.Tools.Fs
