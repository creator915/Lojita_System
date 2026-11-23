import Lojita.Ownership.Tools.Relay
import LojitaCtx.GitSandbox

namespace Lojita.Ownership.Tools.Git
open LojitaCtx.Terminal LojitaCtx.GitSandbox

def gitSpec := OwnedSpec "gitbox" GitConfig Bytes GitStep RawGitObs GitConfig.ownedFiles

def command : GitStep → String
  | .gitWriteFile path bs => s!"W {hexText path} {hex bs}"
  | .gitRemoveFile path => "U " ++ hexText path
  | .gitStageAll => "A"
  | .gitStagePaths paths => String.intercalate " " (["P", toString paths.length] ++ paths.map hexText)
  | .gitCommit msg offset => s!"C {offset} {hexText msg}"
  | .gitSwitchBranch name create => s!"B {if create then 1 else 0} {hexText name}"
  | .gitCreateTag name => "T " ++ hexText name
  | .gitStatus => "S"
  | .gitRunTarget exe args bs ms => runRequest exe args bs ms

private def names (p : Pipe) (count : String) : IO (List String) := do
  let mut ns := #[]
  for _ in [:← natural count] do
    let ["N", n] := (← readLine p).splitOn " " | throw (IO.userError "invalid Git name")
    ns := ns.push (← wireText n)
  return ns.toList

private def summary (p : Pipe) : IO GitRepoSummary := do
  let ["S", head, commits, branches, tags, staged, modified, untracked] := (← readLine p).splitOn " "
    | throw (IO.userError "invalid Git summary")
  return ⟨← wireText head, ← natural commits, ← names p branches, ← names p tags, ← names p staged,
    ← names p modified, ← names p untracked⟩

def request (p : Pipe) (line : String) : IO RawGitObs := do
  let ["O", out, err, code, timed, oid, present] ← exchange p line | throw (IO.userError "invalid Git reply")
  let hash ← wireText oid
  requireWire (hash.isEmpty || (hash.length == 40 && hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))))
    "invalid Git object identifier"
  let s ← status code
  let obs := RawGitObs.rawGitObs (← unhex out) (← unhex err) hash s (← flag timed)
    (← if ← flag present then some <$> summary p else pure none)
  requireWire (line.startsWith "R " || s.getD 0 == 0) "Git operation rejected"
  return obs

def gitToolWithMount (bin scratch : System.FilePath) (candidate : Option System.FilePath) : HandlerIO gitSpec := fun cfg owned => do
  checkEnv cfg.envVars
  requireWire (cfg.baseEpochSec ≤ 9223372036854775807 && [cfg.authorName, cfg.authorEmail].all (fun s =>
    !s.isEmpty && !s.toList.any (fun c => c.toNat == 0 || "\r\n<>".toList.contains c))) "invalid Git identity or epoch"
  requireWire (cfg.ownedFiles.all validGitPath && validBranch cfg.defaultBranch) "invalid Git configuration"
  let setup := fun p => do
    discard <| request p s!"I {hexText cfg.defaultBranch} {hexText cfg.authorName} {hexText cfg.authorEmail} {cfg.baseEpochSec}"
    for (k, v) in cfg.envVars do discard <| request p ("E " ++ hexText (k ++ "=" ++ v))
    visitFiles (fun path bs => discard (request p (command (.gitWriteFile path bs)))) cfg.ownedFiles owned
  openBytes bin scratch cfg.target cfg.ownedFiles owned #[] setup (fun p q => request p (command q))
    (fun p => discard (request p "Q")) false candidate

def gitTool (bin scratch : System.FilePath) : HandlerIO gitSpec :=
  gitToolWithMount bin scratch none

end Lojita.Ownership.Tools.Git
