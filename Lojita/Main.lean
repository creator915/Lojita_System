import Lojita.MCP.Server

namespace Lojita.CLI
open System Lojita.Session Lojita.Kernel Lojita.Store Lojita.Transport Lojita.Harness

private def readModule (path : String) : IO LeanMod := do
  let src ← IO.FS.readFile path
  if (System.FilePath.mk path).extension == some "sexp" then
    let some m := decodeCanonical src | fail "expected canonical Lean module"
    return m
  IO.ofExcept (parseLeanMod src)

private def deps : List String → IO (List LeanMod)
  | [] => pure []
  | "--dep" :: p :: more => return (← readModule p) :: (← deps more)
  | _ => fail "expected --dep <module.lean>"

private def hostRepo : IO FilePath := do
  let exe ← IO.FS.realPath (← IO.appPath)
  let repo := exe.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
  if let some dir := repo then
    if ← (dir / "Lojita.lean").pathExists then return dir
  IO.currentDir

private def verifySelf : IO Unit := do
  let m ← IO.ofExcept (parseLeanMod "namespace Gen.Self.Root\ndef n := 1\ntheorem checked : n = 1 := rfl\nend Gen.Self.Root")
  discard <| checkClosedModule [] m
  unless (parseLeanMod "import Lojita.Session.SessionEnv\nnamespace Gen.Self.Bad\nend Gen.Self.Bad").isOk == false do
    fail "closed-world import boundary failed"
  IO.println "ok: resident kernel, proof and closed-world import boundary"

def dispatch (args : List String) : IO UInt32 := do
  match args with
  | "mcp" :: rest => Lojita.MCP.serve (← IO.ofExcept (Lojita.MCP.parseConfig rest))
  | ["probe-worker",repo,ws,dir] =>
    let root : FilePath := dir
    let ref ← IO.ofExcept (parseRefSpec (← IO.FS.readFile (root / "ref.sexp")))
    let r ← probeWorker repo ws root ref (← IO.FS.readFile (root / "probe.lean"))
    IO.println (Lean.toJson r).compress
  | _ =>
    let repo ← hostRepo
    preload (repo / ".lake/build/lib/lean")
    match args with
    | ["verify-self"] => verifySelf
    | ["session",dir,goal,refFile] =>
      IO.FS.createDirAll dir
      let ws ← IO.FS.realPath dir
      let path ← IO.FS.realPath refFile
      let backend ← CodexCLIBackend {repo,workspace := ws,refFile := path}
      IO.println (← runSession ⟨repo,ws,← IO.FS.readFile goal,← readReference path,backend,true,none,none⟩)
    | ["session-probe",ws,path,script] =>
      let r ← runScript repo ws (← readReference path) (← IO.FS.readFile script)
      (← IO.getStdout).putStr r.stdout
      (← IO.getStderr).putStr r.stderr
      return r.exitCode.toUInt32
    | ["node",specFile,dir] =>
      let src ← IO.FS.readFile specFile
      let spec ← IO.ofExcept (parseLeanMod src)
      let some epoch := spec.modName.segments[1]? | fail "expected Gen.<epoch>.<path>"
      IO.FS.createDirAll dir
      let ws ← IO.FS.realPath dir
      initWorkspace ws
      let backend ← CodexCLIBackend {repo,workspace := ws,refFile := ws / "reference.sexp"}
      let cfg : SessionConfig := ⟨repo,ws,"",⟨.local "",[],30000⟩,backend,false,none,none⟩
      let outcome ← driveTree cfg epoch "standalone node" src [] none none
      IO.println outcome
      if outcome != "ok" then return 1
    | "check" :: path :: rest =>
      let m ← readModule path
      discard <| checkClosedModule (← deps rest) m
      IO.println s!"ok {m.modName}"
    | ["roundtrip",path] => IO.print (renderLeanMod (← readModule path))
    | ["units",path] =>
      let m ← readModule path
      for u in m.units do IO.println s!"{u.uname} {u.synRefs.map toString}"
    | ["order",path] =>
      let m ← readModule path
      for u in orderUnits m.modName m.units do IO.println u.uname
    | ["apply",path,plan] =>
      let m ← readModule path
      let src ← IO.FS.readFile plan
      let p ← match SExpr.parseSExpr src >>= decodePlan with
        | some p => pure p
        | none => do
          let .plan p _ ← IO.ofExcept (parseSubmission src) | fail "expected a plan"
          pure p
      let out := apply p m
      IO.ofExcept (planError (validate m p out) |>.mapError toString)
      IO.print (renderLeanMod out)
    | _ => fail "usage: lojita verify-self | mcp --mode ... | session WS GOAL REF | session-probe WS REF SCRIPT | node SPEC STATE | check MAIN [--dep DEP ...] | roundtrip|units|order FILE | apply OLD PLAN"
  return 0

end Lojita.CLI

def main (args : List String) : IO UInt32 := do
  try Lojita.CLI.dispatch args
  catch e =>
    (← IO.getStderr).putStrLn (toString e)
    return 1
