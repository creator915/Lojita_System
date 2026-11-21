import Prism.TranscodeExec
import Prism.KernelDriver
import Prism.CatStructure
import Lean.Data.Json

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.Driver`: Unit-SCC Lens Orchestrator, Parameterized `SlowSlice` Verifier & Unified `leanc -O3` Builder
-/

namespace Prism

-- Exit code contract shared with `Backend/PrismFFI.agda` & `Backend/Switch.agda`:
--   0  : Translated & Verified OK (Pure Fast OR Hybrid Fast+Slow Lens!)
--   10 : Agda frontend syntax or scope error
--   11 : Kernel Type / Termination / Productivity / Axiom Error (Lean 4 Fast OR Agda SlowSlice)
--   20 : Module-Level `⊥` (BOT, e.g. `--without-K`, unwhitelisted import) -> Fallback to `LegacyAgda`
def exitOK        : UInt32 := 0
def exitSyntaxErr : UInt32 := 10
def exitTypeErr   : UInt32 := 11
def exitBot       : UInt32 := 20

structure SourceUnit : Type where
  path    : String
  modName : String
  imports : List String
  content : String
  point? : Option CatStructure.PreTCPoint := none
  checkErrors : List String := []
  deriving Inhabited

structure SlicedModule : Type where
  srcUnit : SourceUnit
  codeMod : CodeMod
  expMod  : ExportedModule
  plan    : SlicePlan
  depMods : List (CodeMod × ExportedModule)
  topoIndex : Nat
  split : Thunk CatStructure.PushoutSplitPlan

-- The nominated module can itself be imported by another supplied module.
private def orderedModules (others : List SlicedModule) (main : SlicedModule) : List SlicedModule :=
  let (before, after) := others.splitAt main.topoIndex
  before ++ main :: after

partial def topoSortUnits (units : List SourceUnit) : PrismOutcome (List SourceUnit) :=
  let knownNames := units.map (·.modName)
  let rec visit (visiting visited : List String) (acc : List SourceUnit) (u : SourceUnit) :
      PrismOutcome (List String × List SourceUnit) := do
    if visited.contains u.modName then
      .translated (visited, acc)
    else if visiting.contains u.modName then
      .syntaxErr s!"cyclic module import involving '{u.modName}'"
    else
      let mut vis := visited
      let mut out := acc
      for imp in u.imports do
        if knownNames.contains imp then
          if let some depU := units.find? (fun x => x.modName == imp) then
            let (v', o') ← visit (u.modName :: visiting) vis out depU
            vis := v'
            out := o'
      .translated (u.modName :: vis, u :: out)
  let rec visitAll (rem : List SourceUnit) (vis : List String) (acc : List SourceUnit) :
      PrismOutcome (List SourceUnit) := do
    match rem with
    | [] => .translated acc.reverse
    | u :: rs =>
        let (vis', acc') ← visit [] vis acc u
        visitAll rs vis' acc'
  visitAll units [] []

def stripStdlibWarningsLean (txt : String) : String :=
  let stdlibPfx := "/usr/share/agda-stdlib/"
  let cubicalHdr := "This clause uses pattern-matching features that are not yet"
  let whenDef := "when checking the definition of"
  let whenDefSp := "when checking the definition of "
  let rec
    skipBlk : List String → List String
      | [] => []
      | l :: ls =>
          if l == whenDef then
            match ls with
            | _ :: rest => go rest
            | []        => []
          else if l.startsWith whenDefSp then
            go ls
          else
            skipBlk ls,
    go : List String → List String
      | [] => []
      | l :: (rest@(l2 :: _)) =>
          if l.startsWith stdlibPfx && l2.startsWith cubicalHdr then
            skipBlk rest
          else
            l :: go rest
      | [l] => [l]
  String.intercalate "\n" (go (txt.splitOn "\n"))

def runSubproc (cmd : String) (args : Array String) (leanPath : Option String := none)
    (cwd : Option String := none) (extraEnv : Array (String × Option String) := #[]) :
    IO (UInt32 × String × String) := do
  let lpEnv : Array (String × Option String) :=
    match leanPath with
    | some lp => #[("LEAN_PATH", some lp)]
    | none    => #[]
  let out ← IO.Process.output {
    cmd  := cmd
    args := args
    cwd  := cwd.map System.FilePath.mk
    env  := lpEnv ++ extraEnv
  }
  pure (out.exitCode, out.stdout, out.stderr)

private def relAgdaFilePath (modParts : List String) : String :=
  String.intercalate "/" modParts ++ ".agda"

private def parentRelDir (modParts : List String) : String :=
  match modParts.dropLast with
  | [] => "."
  | ds => String.intercalate "/" ds

private def findRepoRoot (mirrorLibDir : String) : IO (Option String) := do
  -- Node workspaces may contain a read-only Context view of their own.
  -- Resolve the installed frontend before considering the caller's working directory.
  for start in [← IO.appPath, System.FilePath.mk mirrorLibDir] do
    let mut ancestor := some start
    while let some root := ancestor do
      if (← (root / "dump/dump").pathExists) && (← (root / "Context/Blueprint.agda").pathExists) then
        return some (← IO.FS.realPath root).toString
      ancestor := root.parent
  return none

private def autoContextModFiles : List (String × String) :=
  [ ("Context.Tools.Clock",      "Context/Tools/Clock.agda")
  , ("Context.Tools.ClockLaws",  "Context/Tools/ClockLaws.agda")
  , ("Context.Tools.TermLaws",   "Context/Tools/TermLaws.agda")
  , ("Context.Tools.FuzzGen",    "Context/Tools/FuzzGen.agda")
  , ("Context.Tools.FsSandbox",  "Context/Tools/FsSandbox.agda")
  , ("Context.Tools.NetSandbox", "Context/Tools/NetSandbox.agda")
  , ("Context.Tools.GitSandbox", "Context/Tools/GitSandbox.agda")
  , ("Context.Tools.WebOperad",  "Context/Tools/WebOperad.agda")
  , ("Context.World",            "Context/World.agda")
  , ("Context.Tools.FsLaws",     "Context/Tools/FsLaws.agda")
  , ("Context.Tools.GitLaws",    "Context/Tools/GitLaws.agda")
  , ("Context.Tools.NetLaws",    "Context/Tools/NetLaws.agda")
  , ("Context.WorldLaws",        "Context/WorldLaws.agda")
  , ("Context.Protocol",         "Context/Protocol.agda")
  ]

private def contextWhitelist : List (String × String) :=
  autoContextModFiles ++
    [ ("Context.Blueprint", "Context/Blueprint.agda")
    , ("Context.PolyTransport", "Context/PolyTransport.agda")
    , ("Context.Terminal", "Context/Terminal.agda")
    , ("Context.Filter", "Context/Filter.agda")
    , ("Context.Taboo", "Context/Taboo.agda") ]

private def requiresAgdaSlowCheck (mirrorLibDir : String) (sm : SlicedModule) : IO Bool := do
  if sm.split.get.agdaResidual?.isNone then return false
  let some (_, rel) := contextWhitelist.find? (fun (name, _) => name == sm.srcUnit.modName)
    | return true
  let some repo ← findRepoRoot mirrorLibDir | return true
  try
    return sm.srcUnit.content.toUTF8 != (← IO.FS.readBinFile s!"{repo}/{rel}")
  catch _ =>
    return true

-- Keep the immutable include view hermetic. Group links by directory so
-- constructing it does not need a subprocess for every interface file.
private def prepareContext (repo dir : System.FilePath) (staged : List String)
    (entry : Bool) : IO Unit := do
  let permitted := contextWhitelist ++
    (if entry then [("OwnershipIO.WorldRunner", "OwnershipIO/WorldRunner.agda"),
                    ("OwnershipIO.FFI", "OwnershipIO/FFI.agda")] else [])
  let files := permitted.filter (fun (name, _) => !staged.contains name) |>.map Prod.snd
  let folders := files.map (fun rel => (System.FilePath.mk rel).parent.getD ".") |>.eraseDups
  for folder in folders do
    IO.FS.createDirAll (dir / folder)
    let mut links := #[]
    for rel in files do
      if (System.FilePath.mk rel).parent == some folder then
        let source := repo / rel
        links := links.push source.toString
        let iface := source.withExtension "agdai"
        if ← iface.pathExists then links := links.push iface.toString
    let (rc, _, msg) ← runSubproc "ln" (#["-s", "-t", (dir / folder).toString, "--"] ++ links)
    if rc != 0 then throw (IO.userError msg)

private abbrev Worker := IO.Process.Child {stdin := .piped, stdout := .piped, stderr := .inherit}
private initialize dumpWorker : IO.Ref (Option (String × Worker)) ← IO.mkRef none
private initialize checkWorker : IO.Ref (Option Worker) ← IO.mkRef none

private def stopWorker (child : Worker) : IO Unit := do
  if (← child.tryWait).isNone then child.kill
  discard child.wait

def withFrontendSession {α : Type} (action : IO α) : IO α := do
  try action finally
    KernelDriver.close
    if let some (_, c) ← dumpWorker.swap none then stopWorker c
    if let some c ← checkWorker.swap none then stopWorker c

private def getDumpWorker (bin : String) : IO Worker := do
  if let some (binary, child) ← dumpWorker.get then
    if binary == bin && (← child.tryWait).isNone then return child
    stopWorker child
  let child ← IO.Process.spawn {
    cmd := bin, args := #["--daemon"],
    stdin := .piped, stdout := .piped, stderr := .inherit}
  dumpWorker.set (some (bin, child))
  return child

private def frontendRequest (bin : String) (req : Lean.Json) : IO (Except String Lean.Json) := do
  try
    let child ← getDumpWorker bin
    child.stdin.putStrLn req.compress
    child.stdin.flush
    let response ← child.stdout.getLine
    if response.isEmpty then throw (IO.userError "agda-dumpd closed its output")
    return do
      let j ← Lean.Json.parse response
      if !(← j.getObjValAs? Bool "ok") then throw (← j.getObjValAs? String "error")
      return j
  catch e =>
    if let some (_, child) ← dumpWorker.swap none then stopWorker child
    return .error (toString e)

private def scopeRequest (bin : String) (includes deps : List String) (main : String) :
    IO (Except String (List String × String × List String)) := do
  let result ← frontendRequest bin <| Lean.Json.mkObj [("cmd", "dump"), ("includes", Lean.toJson includes),
                                                        ("deps", Lean.toJson deps), ("main", main)]
  return do
    let j ← result
    let errors ← match j.getObjVal? "check_errors" with
      | .ok value => Lean.fromJson? (α := List String) value
      | .error _ => pure []
    return (← j.getObjValAs? (List String) "dep_sexprs", ← j.getObjValAs? String "sexpr", errors)

def inspectSources (mirrorLibDir : String) (dumpBin : Option String) (inputs : List (String × String)) :
    IO (Except String (List SourceUnit)) := do
  let some repo ← findRepoRoot mirrorLibDir | return .error "cannot locate frontend installation"
  let result ← frontendRequest (dumpBin.getD s!"{repo}/dump/dump") <| Lean.Json.mkObj
    [("cmd", "headers"), ("sources", Lean.toJson (inputs.map Prod.snd))]
  return do
    let j ← result
    let headers ← j.getObjValAs? (List Lean.Json) "headers"
    if headers.length != inputs.length then throw "incomplete agda-dumpd header response"
    (inputs.zip headers).mapM fun ((path, content), header) => do
      let name ← header.getObjValAs? String "name"
      let imports ← header.getObjValAs? (List String) "imports"
      let parts := name.splitOn "."
      if parts.any (fun p => p.isEmpty || p.toList.any (fun c => c == '/' || c == '\\' || c.toNat < 32)) then
        throw s!"invalid module path '{name}'"
      return { path, modName := name, imports, content }

abbrev ScopedBundle := List (SourceUnit × CodeMod) × (SourceUnit × CodeMod)

def dumpSurfaceBundle (depFiles : List String) (mainFile mirrorLibDir workDir : String)
    (dumpBin : Option String := none) : IO (Except String ScopedBundle) := do
  let some root ← findRepoRoot mirrorLibDir | return .error "cannot locate frontend installation"
  let repo := System.FilePath.mk root
  let bin := dumpBin.getD (repo / "dump/dump").toString
  let base := if workDir.isEmpty then repo / "tmp" else System.FilePath.mk workDir
  let stage := base / s!"scope_{← IO.monoNanosNow}"
  IO.FS.createDirAll stage
  let stage ← IO.FS.realPath stage
  try
    let inputs ← (depFiles ++ [mainFile]).mapM fun (file : String) => do return (file, ← IO.FS.readFile file)
    let units ← match ← inspectSources mirrorLibDir dumpBin inputs with
      | .ok units => pure units
      | .error e => return .error e
    let names := units.map (·.modName)
    if names.length != names.eraseDups.length then return .error "duplicate module name in bundle"
    let paths ← units.mapM fun u => do
      let path := stage / relAgdaFilePath (u.modName.splitOn ".")
      if let some parent := path.parent then IO.FS.createDirAll parent
      IO.FS.writeFile path u.content
      return path.toString
    let main := units.getLast!
    prepareContext repo stage (units.map (·.modName))
      (main.modName == "Main" || main.modName == "Code.HarnessEngineMain")
    let stdlib := (← IO.getEnv "AGDA_STDLIB").getD "/usr/share/agda-stdlib"
    let result ← scopeRequest bin [stage.toString, stdlib] paths.dropLast paths.getLast!
    return do
      let (ds, m, checkErrors) ← result
      if ds.length != depFiles.length then throw "frontend returned an incomplete dependency bundle"
      let modules ← (units.zip (ds ++ [m])).mapM fun (u, sexp) => do
        let some point := parseSExprText sexp >>= (decodeSurfacePoint · (.authored u.content))
          | throw s!"invalid dump for {u.modName}"
        let cm := point.code
        if fullDot cm.modName != u.modName then throw s!"declared module name differs from {u.modName}"
        let imps := cm.decls.flatMap allImportsInDecl |>.map fullDot
        return ({u with imports := imps.eraseDups, point? := some point}, cm)
      let some last := modules.getLast? | throw "empty dump bundle"
      return (modules.dropLast, {last.1 with checkErrors}, last.2)
  finally IO.FS.removeDirAll stage

private def computeChkSlicePlan (deps : List (CodeMod × ExportedModule)) (cm : CodeMod)
    (em : ExportedModule) : PrismOutcome (SlicePlan × ExportedModule) := do
  let group (ctx : EmitCtx) (units : List ModUnit) : PrismOutcome Unit := do
    if units.length > 1 && !(units.all (fun u => u.kind matches .dataUnit ..) ||
        (structuralArguments ctx.modPrefix units).isSome || (FactorMutual.stage? ctx units).isSome) then
      PrismOutcome.bot "mixed recursive declaration group"
    units.forM (probeFastUnit ctx)
  let (view, variables) ← checkedVariableView cm
  let (plan, exports) ← planUnitSlices group probeBoundaryUnit deps view em
  if let some name := variables then
    if plan.units.any (fun u => plan.slowUnitIds.contains u.uid &&
        u.definedCanons.contains (cm.modName.full ++ [name])) then
      .bot "generalized variable type requires Agda"
  return ({plan with checkedVariable? := variables}, exports)

/-- Execution uses the complete declaration graph after verification. Kernel-only
    residual boundaries have no role in ordering the bodies of an executable. -/
private def execPlan (cm : CodeMod) (em : ExportedModule) : PrismOutcome (SlicePlan × ExportedModule) := do
  let (headers, units) ← extractModUnits cm
  return (⟨headers, units, computeUnitSCCs units, [], units.map (·.uid), [], em.coindRecords, none⟩, em)

def sliceCodeBundle (deps : List (SourceUnit × CodeMod)) (main : SourceUnit × CodeMod)
    (forExe : Bool := false) : PrismOutcome (List SlicedModule × SlicedModule) := do
  if !main.1.checkErrors.isEmpty then PrismOutcome.syntaxErr (String.intercalate "\n" main.1.checkErrors)
  let name := main.1.modName
  let all := deps ++ [main]
  let sorted ← topoSortUnits (all.map Prod.fst)
  let mut done_ : List SlicedModule := []
  for u in sorted do
    if !forExe then
      if let some bad := u.imports.find? (fun n => (n.splitOn ".").any (fun p => p == "TrustMe" || p == "Unsafe")) then
        .syntaxErr s!"Prism verification forbids the unsafe import '{bad}'"
    let some (_, cm) := all.find? (fun (v, _) => v.modName == u.modName)
      | .syntaxErr s!"unknown bundle module {u.modName}"
    let direct := done_.filter (fun sm => u.imports.contains sm.srcUnit.modName)
    let ancestors := direct.flatMap fun sm => sm.srcUnit.modName :: sm.depMods.map (fun d => fullDot d.1.modName)
    let scope := if forExe then done_ else done_.filter (fun sm => ancestors.contains sm.srcUnit.modName)
    let upstream := scope.map (fun sm => (sm.codeMod, sm.expMod))
    let atModule {α : Type} (step : PrismOutcome α) : PrismOutcome α := match step with
      | .bot cause => PrismOutcome.bot s!"{u.modName}: {cause}"
      | other => other
    let raw ← atModule (synthesizeExportedModule (upstream.map Prod.snd) cm forExe)
    let (plan, exports) ← atModule (if forExe then execPlan cm raw else computeChkSlicePlan upstream cm raw)
    let exotic := (plan.units.filter fun v => plan.slowUnitIds.contains v.uid).flatMap fun v =>
      match v.kind with
      | .anonUnit i .. => [cm.modName.full ++ [s!"_#{i}"]]
      | _ => v.definedCanons
    let pushout := Thunk.mk fun _ => CatStructure.computePushoutSplit cm (fun v =>
      if exotic.contains v.name.full then some "Agda residual" else none)
    done_ := done_ ++ [⟨u, cm, exports, plan, upstream, done_.length, pushout⟩]
  let some sm := done_.find? (fun sm => sm.srcUnit.modName == name) | .syntaxErr "missing main"
  return (done_.filter (fun m => m.srcUnit.modName != name), sm)

def parseAndSliceBundle (depFiles : List String) (mainFile : String)
    (mirrorLibDir : String := ".") (workDir : String := "") (dumpBin : Option String := none)
    (forExe : Bool := false) : IO (PrismOutcome (List SlicedModule × SlicedModule)) := do
  match ← dumpSurfaceBundle depFiles mainFile mirrorLibDir workDir dumpBin with
  | .error e => return .syntaxErr e
  | .ok (deps, main) => return sliceCodeBundle deps main forExe

def readCodeBundle (path : String) (forExe : Bool := false) : IO (PrismOutcome (List SlicedModule × SlicedModule)) := do
  let some (.list (.sym "bundle" :: modules)) := parseSExprText (← IO.FS.readFile path)
    | return .syntaxErr "expected (bundle <dependencies ...> <main>)"
  let some codes := modules.mapM decodeCodeMod | return .syntaxErr "invalid Code module in bundle"
  let units := codes.map fun cm =>
    ((⟨"", fullDot cm.modName, (cm.decls.flatMap allImportsInDecl).map fullDot, "", none, []⟩ : SourceUnit), cm)
  let some last := units.getLast? | return .syntaxErr "empty code bundle"
  if codes.any (fun cm => cm.modName.full.isEmpty || cm.modName.full.any
      (fun p => p.isEmpty || p.toList.any (fun c => c == '.' || c == '/' || c == '\\' || c.toNat < 32))) then
    return .syntaxErr "invalid module path in code bundle"
  let names := units.map (fun (u, _) => u.modName)
  if names != names.eraseDups then return .syntaxErr "duplicate module name in code bundle"
  return sliceCodeBundle units.dropLast last forExe

private def readBytes (h : IO.FS.Handle) (n : Nat) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  while bytes.size < n do
    let part ← h.read (n - bytes.size).toUSize
    if part.isEmpty then throw (IO.userError "agda-checkd closed its output")
    bytes := bytes ++ part
  return bytes

private def getCheckWorker : IO Worker := do
  if let some c ← checkWorker.get then
    if (← c.tryWait).isNone then return c
  let c ← IO.Process.spawn {cmd := "agda", args := #["--interaction-json", "--no-libraries"],
                            stdin := .piped, stdout := .piped, stderr := .inherit}
  checkWorker.set (some c)
  unless (← readBytes c.stdout 6) == "JSON> ".toUTF8 do
    throw (IO.userError "invalid Agda interaction prompt")
  return c

-- Send fresh load options on every request. The worker keeps decoded
-- interfaces, and Agda invalidates them according to each file's source hash.
private def checkResidual (root file : System.FilePath) (safe : Bool) : IO (Except String Unit) := do
  let stdlib := (← IO.getEnv "AGDA_STDLIB").getD "/usr/share/agda-stdlib"
  let opts := Lean.toJson ((if safe then ["--safe"] else []) ++ ["--no-libraries", "-i", root.toString, "-i", stdlib])
  let path := (Lean.toJson file.toString).compress
  let c ← getCheckWorker
  c.stdin.putStrLn s!"IOTCM {path} None Direct (Cmd_load {path} {opts.compress})"
  c.stdin.flush
  let mut checked := false
  let mut reason := "Agda did not report a checked residual"
  repeat
    let first ← readBytes c.stdout 1
    if first == "J".toUTF8 then
      unless (← readBytes c.stdout 5) == "SON> ".toUTF8 do
        throw (IO.userError "invalid Agda interaction prompt")
      break
    let line := (String.fromUTF8? first).getD "" ++ (← c.stdout.getLine)
    let .ok j := Lean.Json.parse line | throw (IO.userError s!"invalid agda-checkd response: {line}")
    match j.getObjValAs? String "kind" with
    | .ok "Status" =>
      checked := ((j.getObjVal? "status") >>= (·.getObjValAs? Bool "checked")).toOption.getD false
    | .ok "DisplayInfo" =>
      if let .ok info := j.getObjVal? "info" then
        if let .ok msg := info.getObjVal? "error" >>= (·.getObjValAs? String "message") then reason := msg
    | _ => pure ()
  return if checked then .ok () else .error reason

def renderCode (mirrorLibDir workDir : String) (cm : CodeMod) : IO String := do
  let some repo ← findRepoRoot mirrorLibDir | throw (IO.userError "cannot locate harness-engine")
  let engine := s!"{repo}/runtime/lean-prism/.lake/build/bin/harness-engine"
  let dir := if workDir.isEmpty then s!"{repo}/tmp" else workDir
  IO.FS.createDirAll dir
  let path := s!"{dir}/render_{← IO.monoNanosNow}.sexp"
  IO.FS.writeFile path (renderTopSExpr (encodeCodeMod cm))
  try
    let (rc, out, err) ← runSubproc engine #["roundtrip", path]
    if rc != 0 || out.startsWith "-- parse error" then throw (IO.userError s!"Code renderer: {err}{out}")
    return out
  finally IO.FS.removeFile path

def pushoutFor (sm : SlicedModule) := sm.split.get

def residualFor (sm : SlicedModule) : Option CatStructure.AgdaResidualPoint :=
  sm.split.get.agdaResidual?.map fun r =>
    r.projectImports (sm.depMods.map Prod.fst).toArray (forSafeKernel := true)

def verifyAgdaSlowSlices (lib work : String) (mods : List SlicedModule) : IO (UInt32 × String) := do
  let slowMods ← mods.filterM (requiresAgdaSlowCheck lib)
  if slowMods.isEmpty then return (exitOK, "OK")
  let some repo ← findRepoRoot lib | return (exitBot, "cannot locate context")
  for sm in slowMods do
    let some residual := residualFor sm
      | return (exitBot, s!"cannot construct residual for {sm.srcUnit.modName}")
    let dir := System.FilePath.mk work / s!"agda_slice_{← IO.monoNanosNow}"
    IO.FS.createDirAll dir
    let dir ← IO.FS.realPath dir
    let shells := residual.upstreamShells.toList
    let all := shells ++ [residual.residualCode]
    prepareContext repo dir (all.map (fun c => fullDot c.modName)) (sm.srcUnit.modName == "Main")
    for cm in all do
      let path := dir / relAgdaFilePath cm.modName.full
      if let some parent := path.parent then IO.FS.createDirAll parent
      let src ← renderCode lib work cm
      IO.FS.writeFile path src
      if cm.modName.full == sm.codeMod.modName.full then
        IO.FS.writeFile (System.FilePath.mk work / s!"SlowSlice_{String.intercalate "_" cm.modName.full}.agda") src
    match ← checkResidual dir (dir / relAgdaFilePath sm.codeMod.modName.full)
        (CatStructure.requiresSafeAgda residual.residualCode) with
    | .error e => return (exitTypeErr, s!"AGDA_SLICE_ERROR ({sm.srcUnit.modName}):\n{e}")
    | .ok () => pure ()
  return (exitOK, "OK")

/-- A terminal independence verdict has an additional full Agda judgment.
    First check the exact staged sources. Then discharge the same judgment with
    --safe, quantifying over just the authoritative stub's named postulates.
    No projection, slow-unit substitution, or witness-result cache is involved. -/
private def confirmIndependence (lib work spec : String) (deps : List SlicedModule)
    (main : SlicedModule) : IO (Except String Unit) := do
  let some root ← findRepoRoot lib | return .error "cannot locate Agda context"
  let modules := deps ++ [main]
  let names := modules.map (·.srcUnit.modName)
  if modules.any (·.srcUnit.content.isEmpty) then
    return .error "the authored witness and its specification sources are required"
  let stage (dir : System.FilePath) (sources : List (String × String)) (safe : Bool) := do
    IO.FS.createDirAll dir
    let dir ← IO.FS.realPath dir
    prepareContext root dir names false
    for (name, source) in sources do
      let file := dir / relAgdaFilePath (name.splitOn ".")
      if let some parent := file.parent then IO.FS.createDirAll parent
      IO.FS.writeFile file source
    checkResidual dir (dir / relAgdaFilePath main.codeMod.modName.full) safe
  let exact := modules.map fun m => (m.srcUnit.modName, m.srcUnit.content)
  let dir := System.FilePath.mk work / s!"independent_{← IO.monoNanosNow}"
  try
    match ← stage (dir / "authored") exact false with
    | .error e => return .error e
    | .ok () => pure ()
    let checked := CatStructure.kernelResidual ⟨main.codeMod, deps.toArray.map (·.codeMod), []⟩
      (some (spec.splitOn "."))
    let safeSources ← (checked.upstreamShells.toList ++ [checked.residualCode]).mapM fun cm => do
      return (fullDot cm.modName, ← renderCode lib work cm)
    stage (dir / "safe") safeSources true
  finally
    if ← dir.pathExists then IO.FS.removeDirAll dir

private def witnessType : Expr → Bool
  | .def_ q => [["Context", "Taboo", "SafeTaboo"], ["Data", "Empty", "⊥"],
                ["Agda", "Builtin", "Empty", "⊥"]].contains q.full
  | _ => false

private def independenceAudit (specName : String) (deps : List SlicedModule)
    (main : SlicedModule) : Except String (Array Lean.Name × Array Lean.Name) := do
  let some spec := deps.find? (fun m => fullDot m.codeMod.modName == specName)
    | throw s!"authoritative specification stub '{specName}' is missing"
  let specNS := Lean.Name.mkSimple (leanModNamespace spec.codeMod.modName.full)
  let allowed := spec.plan.units.filterMap fun unit =>
    match unit.kind with
    | .postulateUnit _ name _ => some (specNS.str (leanMangleIdent name))
    | _ => none
  let mainNS := Lean.Name.mkSimple (leanModNamespace main.codeMod.modName.full)
  let mut witnesses := #[]
  for unit in main.plan.units do
    let target := match unit.kind with
      | .funUnit mods name ty _ =>
          if !mods.isPrivate && witnessType ty then some (leanMangleIdent name) else none
      | .anonUnit i ty _ => if witnessType ty then some s!"_ag_anon_test_{i}" else none
      | _ => none
    if let some name := target then
      if !(main.plan.fastUnitIds.contains unit.uid) then
        throw s!"witness '{name}' requires a Lean proof body; rewrite its SlowSlice using FastFocus-supported syntax"
      witnesses := witnesses.push (mainNS.str name)
  if witnesses.isEmpty then throw "no public closed witness of Context.Taboo.SafeTaboo or ⊥ to audit"
  return (witnesses, allowed.toArray)

def checkSlicedBundle (mirrorLibDir cleanWork : String) (slicedDeps : List SlicedModule)
    (mainSm : SlicedModule) (independenceSpec : Option String := none) (oneShot := false)
    (allowAgda := true) : IO (UInt32 × String) := do
  try
    KernelDriver.preload mirrorLibDir
    let mut done_ : List (String × KernelDriver.Snapshot) := []
    let mut fresh := #[]
    for sm in orderedModules slicedDeps mainSm do
      let deps := (sm.srcUnit.imports.eraseDups.filterMap (fun n => done_.lookup n)).toArray
      let terminal := oneShot && sm.srcUnit.modName == mainSm.srcUnit.modName &&
        !slicedDeps.any (fun d => d.srcUnit.imports.contains sm.srcUnit.modName)
      let key : Option KernelDriver.ModuleKey := if terminal then none else
        some ⟨renderSExpr (encodeCodeMod sm.codeMod), deps.map (·.id)⟩
      let saved ← key.mapM KernelDriver.lookup
      let snap ← match saved.join with
        | some snap => pure snap
        | none => do
          let guarded ← key.mapM KernelDriver.lookupGuarded
          let checked ← match guarded.join with
            | some snap => pure snap
            | none => do
              let allowed := (deps.toList.flatMap (fun d => d.allowed.toList)).eraseDups.toArray
              let slice ← match transcodeChk sm.depMods sm.codeMod sm.expMod (pushoutFor sm) allowed sm.plan with
                | .ok slice => pure slice
                | .error e => throw <| IO.userError e
              let snap ← KernelDriver.elaborate slice deps terminal
              if let some k := key then KernelDriver.rememberGuarded k snap
              pure snap
          fresh := fresh.push (sm, key, checked)
          pure checked
      if let some spec := independenceSpec then
        if sm.srcUnit.modName == mainSm.srcUnit.modName then
          let (targets, axioms) ← match independenceAudit spec slicedDeps mainSm with
            | .ok guard => pure guard
            | .error e => return (exitTypeErr, "INDEPENDENCE_AXIOM_ERROR: " ++ e)
          try KernelDriver.audit snap targets axioms
          catch e => return (exitTypeErr, s!"INDEPENDENCE_AXIOM_ERROR: {e}")
      done_ := (sm.srcUnit.modName, snap) :: done_
    -- Establish all fast judgments first. A downstream type error needs no
    -- native residual check. Publication requires both sides of the pushout.
    for (sm, key, snap) in fresh do
      if allowAgda then
        let (rc, diagnostic) ← verifyAgdaSlowSlices mirrorLibDir cleanWork [sm]
        if rc != exitOK then return (rc, diagnostic)
      else if ← requiresAgdaSlowCheck mirrorLibDir sm then
        return (exitBot, s!"{sm.srcUnit.modName} requires independent prism-check before trusted code generation")
      if let some k := key then KernelDriver.publish k snap
    return (exitOK, "OK")
  catch e => return (exitTypeErr, s!"LEAN_TYPE_ERROR:\n{e}")

def runPrismCheck (mirrorLibDir workDir : String) (depFiles : List String) (mainFile : String)
    (dumpBin : Option String := none) (independenceSpec : Option String := none) (sexprBundle : Bool := false) :
    IO (UInt32 × String) := do
  let workAbs ← IO.Process.output { cmd := "realpath", args := #["-m", workDir] }
  let cleanWork := workAbs.stdout.trimAscii.toString
  let parsed ← if sexprBundle then readCodeBundle mainFile else parseAndSliceBundle depFiles mainFile mirrorLibDir cleanWork dumpBin
  match parsed with
  | .syntaxErr e => pure (exitSyntaxErr, s!"SYNTAX_ERROR: {e}")
  | .bot r => pure (exitBot, s!"BOT: {r}")
  | .translated (deps, sm) => do
    let result ← checkSlicedBundle mirrorLibDir cleanWork deps sm (independenceSpec := independenceSpec) (oneShot := true)
    if result.1 == exitOK then
      if let some spec := independenceSpec then
        match ← confirmIndependence mirrorLibDir cleanWork spec deps sm with
        | .error e => return (exitTypeErr, s!"INDEPENDENCE_AGDA_ERROR: {e}")
        | .ok () => return (exitOK, "OK (Lean witness audit + Agda --safe)")
    return result

private def gcc (args : Array String) : IO Unit := do
  let (rc, out, err) ← runSubproc "gcc" args
  if rc != 0 then throw <| IO.userError s!"gcc (exit {rc}): {out}{err}"

/-- Separate translation units allow GCC to optimize unrelated modules in parallel.
    Wait for every worker in a batch before surfacing an error. Link only completed
    objects and publish the ELF by an atomic rename. -/
private def compileNative (sysroot libDir irDir : System.FilePath) (sources : Array System.FilePath)
    (outBin : String) : IO Unit := do
  let flags := #["-O3", "-I", (sysroot / "include").toString, "-fstack-clash-protection",
                 "-ffp-contract=off", "-ffunction-sections", "-fdata-sections"]
  let mut objects := #[]
  for i in [0:sources.size:4] do
    let mut jobs := #[]
    for src in sources.extract i (i + 4) do
      let obj := (src.addExtension "o").toString
      jobs := jobs.push (← IO.asTask (gcc (flags ++ #["-c", src.toString, "-o", obj])) .dedicated)
      objects := objects.push obj
    let results ← jobs.mapM (m := BaseIO) IO.wait
    for result in results do IO.ofExcept result
  for stem in ["Utf8", "CharClass", "Core", "Context", "World", "Protocol"] do
    let obj := irDir / "AgdaMirror" / (stem ++ ".c.o")
    -- Lake 4.36 names the export-enabled native object .c.o.export.
    let exported := obj.addExtension "export"
    objects := objects.push (if ← exported.pathExists then exported else obj).toString
  let host := irDir / ".." / "cbits" / "lean_cli_host.o"
  let hostLib := libDir / ".." / "liblean_cli_host.a"
  objects := objects.push (if ← host.pathExists then host else hostLib).toString
  let staged := s!"{outBin}.{← IO.monoNanosNow}.tmp"
  try
    gcc <| #["-O3", "-static"] ++ objects ++
      #["-L", (sysroot / "lib/lean").toString, "-L", (sysroot / "lib").toString,
        "-Wl,--start-group", "-lStd", "-lInit", "-lleanrt", "-lcadical",
        "-lc++", "-lc++abi", "-lunwind",
        "-lgmp", "-luv", "-lssl", "-lcrypto", "-lpthread", "-ldl", "-lrt", "-lm",
        "-lc", "-Wl,--end-group", "-Wl,--gc-sections", "-o", staged]
    IO.FS.rename staged outBin
  finally
    if ← System.FilePath.pathExists staged then IO.FS.removeFile staged

def runPrismBuildExe (mirrorLibDir mirrorIrDir workDir outBin : String)
    (depFiles : List String) (mainFile : String)
    (dumpBin : Option String := none) (trustedCodegen : Bool := false) (sexprBundle : Bool := false)
    (slices : Option (PrismOutcome (List SlicedModule × SlicedModule)) := none) : IO (UInt32 × String) := do
  let workAbs ← IO.Process.output { cmd := "realpath", args := #["-m", workDir] }
  let cleanWork := workAbs.stdout.trimAscii.toString
  let libAbs ← IO.Process.output { cmd := "realpath", args := #["-m", mirrorLibDir] }
  let cleanLib := libAbs.stdout.trimAscii.toString
  let irAbs ← IO.Process.output { cmd := "realpath", args := #["-m", mirrorIrDir] }
  let cleanIr := irAbs.stdout.trimAscii.toString
  let parsed ← match slices with
    | some result => pure result
    | none => if sexprBundle then readCodeBundle mainFile true else parseAndSliceBundle depFiles mainFile cleanLib cleanWork dumpBin true
  match parsed with
  | .syntaxErr e => pure (exitSyntaxErr, s!"SYNTAX_ERROR: {e}")
  | .bot r       => pure (exitBot, s!"BOT: {r}")
  | .translated (slicedDeps, mainSm) => do
      let allMods := orderedModules slicedDeps mainSm

      -- Check the abstract input before lowering residual definitions for execution.
      if !trustedCodegen then
        let checked := sliceCodeBundle (slicedDeps.map fun sm => (sm.srcUnit, sm.codeMod)) (mainSm.srcUnit, mainSm.codeMod)
        match checked with
        | .syntaxErr e => return (exitSyntaxErr, e)
        | .bot e => return (exitBot, e)
        | .translated (deps, main) =>
          let result ← checkSlicedBundle cleanLib cleanWork deps main (allowAgda := false)
          if result.1 != exitOK then return result

      try
        let cDir := System.FilePath.mk cleanWork / "c_build" / toString (← IO.monoNanosNow)
        IO.FS.createDirAll cDir
        let mut imports ← KernelDriver.startExec cleanLib
        let mut sources := #[]
        let fields := ExecFields.layout (allMods.map (fun sm => (sm.codeMod, sm.plan)))
        for (sm, i) in allMods.zipIdx do
          let origin := sm.srcUnit.modName
          let cmds ← match transcodeExec sm.depMods sm.codeMod sm.expMod sm.plan fields (origin == mainSm.srcUnit.modName) with
            | .ok cmds => pure cmds
            | .error e => return (exitBot, s!"EXEC_LOWERING_ERROR ({origin}): {e}")
          let modName := Lean.Name.mkSimple ("PrismExec" ++ toString i)
          let src := cDir / (modName.toString ++ ".c")
          imports ← KernelDriver.compileExec imports modName origin cmds src (i + 1 == allMods.length)
          sources := sources.push src
        compileNative (← Lean.findSysroot) cleanLib cleanIr sources outBin
        return (exitOK, "OK")
      catch e => return (exitTypeErr, s!"EXEC_BUILD_ERROR: {e}")

end Prism
