import Prism.EmitLean
import Prism.DecodeSExpr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.Driver`: Unit-SCC Lens Orchestrator, Parameterized `SlowSlice` Verifier & Unified `leanc -O3` Builder
-/

namespace Prism

-- Exit code contract shared with `Backend/PrismFFI.agda` & `Backend/Switch.agda`:
--   0  : Translated & Verified OK (Pure Fast OR Hybrid Fast+Slow Lens!)
--   10 : Definitive Agda Syntax / Layout / Mixfix-DAG / Closed-Scope Error (< 2ms)
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

structure SlicedModule : Type where
  srcUnit : SourceUnit
  codeMod : CodeMod
  expMod  : ExportedModule
  plan    : SlicePlan
  depMods : List (CodeMod × ExportedModule)

private def quickScanHeader (path : String) (src : String) : PrismOutcome SourceUnit := do
  let toks ← tokenizeAgda src
  let rec scan (rem : List Token) (mName : Option String) (imps : List String) :
      Option String × List String :=
    match rem with
    | [] => (mName, imps.reverse.eraseDups)
    | { kind := .kwModule, .. } :: { kind := .ident nm, .. } :: rest =>
        scan rest (if mName.isNone then some nm else mName) imps
    | { kind := .kwImport, .. } :: { kind := .ident imp, .. } :: rest =>
        scan rest mName (imp :: imps)
    | _ :: rest => scan rest mName imps
  let (mName, imps) := scan toks none []
  match mName with
  | some nm => .translated { path := path, modName := nm, imports := imps, content := src }
  | none    => .syntaxErr s!"{path}: missing 'module <Name> where' header"

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
  let candRoots := [s!"{mirrorLibDir}/../../../../../..", s!"{mirrorLibDir}/../../../../..", "."]
  for r in candRoots do
    if (← System.FilePath.pathExists s!"{r}/Context/Blueprint.agda") then
      return some r
  pure none

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

private def isImmutableContextMod (modName : String) : Bool :=
  autoContextModFiles.any (fun (m, _) => m == modName) ||
  modName == "Context.Blueprint" || modName == "Context.PolyTransport" ||
  modName == "Context.Terminal" || modName == "Context.Filter"

-- Prepare a hermetic read-only Context whitelist view (`Context/{Blueprint,PolyTransport,Terminal,Filter,World,Tools/*}.agda`)
-- ONLY when a hybrid module actually needs to run `agda` on `SlowSlice` or `dump` fallback!
private def prepareContextWhitelistView (mirrorLibDir workDir : String) (excludeMod : String) :
    IO (Option String) := do
  match (← findRepoRoot mirrorLibDir) with
  | none => pure none
  | some repo => do
      let ctxDir := s!"{workDir}/agda_ctx_view"
      IO.FS.createDirAll s!"{ctxDir}/Context/Tools"
      for (mName, relF) in [
        ("Context.Blueprint",        "Context/Blueprint.agda"),
        ("Context.PolyTransport",    "Context/PolyTransport.agda"),
        ("Context.Terminal",         "Context/Terminal.agda"),
        ("Context.Filter",           "Context/Filter.agda"),
        ("Context.Tools.Clock",      "Context/Tools/Clock.agda"),
        ("Context.Tools.ClockLaws",  "Context/Tools/ClockLaws.agda"),
        ("Context.Tools.TermLaws",   "Context/Tools/TermLaws.agda"),
        ("Context.Tools.FuzzGen",    "Context/Tools/FuzzGen.agda"),
        ("Context.Tools.FsSandbox",  "Context/Tools/FsSandbox.agda"),
        ("Context.Tools.NetSandbox", "Context/Tools/NetSandbox.agda"),
        ("Context.Tools.GitSandbox", "Context/Tools/GitSandbox.agda"),
        ("Context.Tools.WebOperad",  "Context/Tools/WebOperad.agda"),
        ("Context.World",            "Context/World.agda"),
        ("Context.Tools.FsLaws",     "Context/Tools/FsLaws.agda"),
        ("Context.Tools.GitLaws",    "Context/Tools/GitLaws.agda"),
        ("Context.Tools.NetLaws",    "Context/Tools/NetLaws.agda"),
        ("Context.WorldLaws",        "Context/WorldLaws.agda"),
        ("Context.Protocol",         "Context/Protocol.agda")
      ] do
        if mName != excludeMod then
          let srcP := s!"{repo}/{relF}"
          if (← System.FilePath.pathExists srcP) then
            let txt ← IO.FS.readFile srcP
            IO.FS.writeFile s!"{ctxDir}/{relF}" txt
      if excludeMod == "Main" then
        IO.FS.createDirAll s!"{ctxDir}/OwnershipIO"
        for relF in ["OwnershipIO/WorldRunner.agda", "OwnershipIO/FFI.agda"] do
          let srcP := s!"{repo}/{relF}"
          if (← System.FilePath.pathExists srcP) then
            let txt ← IO.FS.readFile srcP
            IO.FS.writeFile s!"{ctxDir}/{relF}" txt
      pure (some ctxDir)

private def parseModuleWithDumpFallback (mirrorLibDir workDir : String)
    (dumpBin : Option String) (allRawUnits : List SourceUnit)
    (curDeps : List ExportedModule) (u : SourceUnit) :
    IO (PrismOutcome (CodeMod × ExportedModule)) := do
  match parseAgdaModule curDeps u.content with
  | .syntaxErr e => pure (.syntaxErr e)
  | .translated res => pure (.translated res)
  | .bot r =>
      match dumpBin with
      | none => pure (.bot r)
      | some db => do
          if !(← System.FilePath.pathExists db) then
            pure (.bot r)
          else
            let dWork := s!"{workDir}/dump_fallback_{u.modName.replace "." "_"}"
            IO.FS.createDirAll dWork
            for ru in allRawUnits do
              let parts := ru.modName.splitOn "."
              IO.FS.createDirAll s!"{dWork}/{parentRelDir parts}"
              IO.FS.writeFile s!"{dWork}/{relAgdaFilePath parts}" ru.content
            let ctxOpt ← prepareContextWhitelistView mirrorLibDir s!"{dWork}/_ctx" u.modName
            let targetRel := relAgdaFilePath (u.modName.splitOn ".")
            let mut dArgs : Array String := #["-i", "."]
            if let some cv := ctxOpt then
              dArgs := dArgs ++ #["-i", cv]
            dArgs := dArgs ++ #["-i", "/usr/share/agda-stdlib", s!"./{targetRel}"]
            let (dCode, dOut, dErr) ← runSubproc db dArgs none (some dWork)
            if dCode != 0 then
              pure (.syntaxErr (stripStdlibWarningsLean (dOut ++ dErr)))
            else
              match parseSExprText dOut >>= decodeCodeMod with
              | none => pure (.bot s!"{r} (and dump S-expr decode returned none)")
              | some cm =>
                  match synthesizeExportedModule curDeps cm with
                  | .syntaxErr e => pure (.syntaxErr e)
                  | .bot r2      => pure (.bot r2)
                  | .translated em => pure (.translated (cm, em))

def parseAndSliceBundle (depFiles : List String) (mainFile : String)
    (mirrorLibDir : String := ".") (workDir : String := "/tmp/prism_parse")
    (dumpBin : Option String := none) :
    IO (PrismOutcome (List SlicedModule × SlicedModule)) := do
  let mut rawDeps : List SourceUnit := []
  for df in depFiles do
    let txt ← IO.FS.readFile df
    match quickScanHeader df txt with
    | .syntaxErr e => return .syntaxErr e
    | .bot r       => return .bot r
    | .translated u => rawDeps := rawDeps ++ [u]
  let mainTxt ← IO.FS.readFile mainFile
  let mainU ← match quickScanHeader mainFile mainTxt with
    | .syntaxErr e => return .syntaxErr e
    | .bot r       => return .bot r
    | .translated u => pure u
  -- Auto-attach immutable `Context.*` Agda modules (`Context.Tools.*`, full `Context.Terminal`)
  -- when imported by `main` or `deps` and not already supplied explicitly.
  if let some repo := (← findRepoRoot mirrorLibDir) then
    let mut changed := true
    while changed do
      changed := false
      let presentMods := mainU.modName :: rawDeps.map (·.modName)
      let allImps := (mainU :: rawDeps).flatMap (·.imports) |>.eraseDups
      for (ctxMod, ctxRel) in autoContextModFiles do
        if !presentMods.contains ctxMod && (lookupStdModule ctxMod).isNone && allImps.contains ctxMod then
          let p := s!"{repo}/{ctxRel}"
          if (← System.FilePath.pathExists p) then
            let txt ← IO.FS.readFile p
            if let .translated cu := quickScanHeader p txt then
              rawDeps := cu :: rawDeps
              changed := true
  match topoSortUnits rawDeps with
  | .syntaxErr e => return .syntaxErr e
  | .bot r       => return .bot r
  | .translated sortedDeps =>
      let allRaw := sortedDeps ++ [mainU]
      let mut slicedDeps : List SlicedModule := []
      for du in sortedDeps do
        let curDeps := slicedDeps.map (fun m => (m.codeMod, m.expMod))
        match (← parseModuleWithDumpFallback mirrorLibDir workDir dumpBin allRaw (curDeps.map Prod.snd) du) with
        | .syntaxErr e => return .syntaxErr e
        | .bot r       => return .bot r
        | .translated (cm, rawEm) =>
            match computeSlicePlan curDeps cm rawEm with
            | .syntaxErr e => return .syntaxErr e
            | .bot r       => return .bot r
            | .translated (plan, em) =>
                slicedDeps := slicedDeps ++ [{ srcUnit := du, codeMod := cm, expMod := em, plan := plan, depMods := curDeps }]
      let mainDeps := slicedDeps.map (fun m => (m.codeMod, m.expMod))
      match (← parseModuleWithDumpFallback mirrorLibDir workDir dumpBin allRaw (mainDeps.map Prod.snd) mainU) with
      | .syntaxErr e => return .syntaxErr e
      | .bot r       => return .bot r
      | .translated (mainCm, mainRawEm) =>
          match computeSlicePlan mainDeps mainCm mainRawEm with
          | .syntaxErr e => return .syntaxErr e
          | .bot r       => return .bot r
          | .translated (mainPlan, mainEm) =>
              let mainSm : SlicedModule :=
                { srcUnit := mainU, codeMod := mainCm, expMod := mainEm, plan := mainPlan, depMods := mainDeps }
              return .translated (slicedDeps, mainSm)

def emitBundleFiles (slicedDeps : List SlicedModule) (mainSm : SlicedModule)
    (mode : EmitMode) (forExe : Bool := false) (withGuard : Bool := false) :
    PrismOutcome (List (String × String)) := do
  let mut files : List (String × String) := []
  for dm in slicedDeps do
    let src ← emitLeanModuleWithPlan dm.depMods dm.codeMod dm.expMod dm.plan mode false withGuard
    files := files ++ [(leanModuleFileName dm.codeMod.modName.full, src)]
  let mainSrc ← emitLeanModuleWithPlan mainSm.depMods mainSm.codeMod mainSm.expMod mainSm.plan mode forExe withGuard
  return files ++ [(leanModuleFileName mainSm.codeMod.modName.full, mainSrc)]

-- Verify ONLY user/task modules with `plan.hasSlowUnits == true` via parameterized `SlowSlice_<Mod>.agda`!
-- Immutable `Context.*` modules are verified under `--safe` at repository build time.
private def verifyAgdaSlowSlices (mirrorLibDir workDir : String) (allMods : List SlicedModule) :
    IO (UInt32 × String) := do
  let slowMods := allMods.filter (fun m => m.plan.hasSlowUnits && !isImmutableContextMod m.srcUnit.modName)
  if slowMods.isEmpty then
    pure (exitOK, "OK")
  else do
    IO.FS.createDirAll workDir
    let agdaCfg := s!"{workDir}/agda_cfg"
    IO.FS.createDirAll agdaCfg
    let mut idx : Nat := 0
    for sm in slowMods do
      let sliceWork := s!"{workDir}/agda_slice_{idx}"
      let ctxViewOpt ← prepareContextWhitelistView mirrorLibDir s!"{workDir}/ctx_{idx}" sm.srcUnit.modName
      idx := idx + 1
      IO.FS.createDirAll sliceWork
      IO.FS.writeFile s!"{sliceWork}/object.agda-lib" "name: prism-slow-slice\ninclude: .\n"
      -- Write preceding bundle dependencies so `SlowSlice` can resolve any imported local module
      for dm in allMods do
        if dm.srcUnit.modName != sm.srcUnit.modName then
          let dDir := s!"{sliceWork}/{parentRelDir dm.codeMod.modName.full}"
          IO.FS.createDirAll dDir
          IO.FS.writeFile s!"{sliceWork}/{relAgdaFilePath dm.codeMod.modName.full}" dm.srcUnit.content
      -- Generate & write parameterized `SlowSlice` (drops `F₂`, abstracts `F₁` as `_SlowResidual` params!)
      let sliceSrc := renderAgdaSlowSlice (sm.depMods.map Prod.snd) sm.codeMod sm.plan
      let sDir := s!"{sliceWork}/{parentRelDir sm.codeMod.modName.full}"
      IO.FS.createDirAll sDir
      let relTarget := relAgdaFilePath sm.codeMod.modName.full
      IO.FS.writeFile s!"{sliceWork}/{relTarget}" sliceSrc
      -- Save inspectable artifact in `workDir` for auditability
      let flatMod := String.intercalate "_" sm.codeMod.modName.full
      IO.FS.writeFile s!"{workDir}/SlowSlice_{flatMod}.agda" sliceSrc

      let mut incArgs : Array String := #["--no-libraries", "-i", "."]
      if let some cv := ctxViewOpt then
        incArgs := incArgs ++ #["-i", cv]
      incArgs := incArgs ++ #["-i", "/usr/share/agda-stdlib", s!"./{relTarget}"]
      let (aCode, aOut, aErr) ← runSubproc "agda" incArgs none (some sliceWork) #[("AGDA_DIR", some agdaCfg)]
      if aCode != 0 then
        return (exitTypeErr, s!"AGDA_SLICE_ERROR ({sm.srcUnit.modName}):\n{stripStdlibWarningsLean (aOut ++ aErr)}")
    pure (exitOK, "OK")

private def runLeanCheckFiles (mirrorLibDir workDir : String) (leanFiles : List (String × String)) :
    IO (UInt32 × String) := do
  IO.FS.createDirAll workDir
  let leanPath := s!"{workDir}:{mirrorLibDir}"
  let total := leanFiles.length
  let mut idx := 0
  for (modStem, leanSrc) in leanFiles do
    idx := idx + 1
    let srcPath := s!"{workDir}/{modStem}.lean"
    let oleanPath := s!"{workDir}/{modStem}.olean"
    IO.FS.writeFile srcPath leanSrc
    let args :=
      if idx < total then #["-R", workDir, srcPath, "-o", oleanPath]
      else #["-R", workDir, srcPath]
    let (code, out, err) ← runSubproc "lean" args (some leanPath)
    if code != 0 then
      return (exitTypeErr, s!"LEAN_TYPE_ERROR:\n{out}{err}")
  pure (exitOK, "OK")

def runPrismCheck (mirrorLibDir workDir : String) (depFiles : List String) (mainFile : String)
    (dumpBin : Option String := none) :
    IO (UInt32 × String) := do
  let workAbs ← IO.Process.output { cmd := "realpath", args := #["-m", workDir] }
  let cleanWork := workAbs.stdout.trimAscii.toString
  let parsed ← parseAndSliceBundle depFiles mainFile mirrorLibDir cleanWork dumpBin
  match parsed with
  | .syntaxErr e => pure (exitSyntaxErr, s!"SYNTAX_ERROR: {e}")
  | .bot r       => pure (exitBot, s!"BOT: {r}")
  | .translated (slicedDeps, mainSm) => do
      let allMods := slicedDeps ++ [mainSm]
      let anySlow := allMods.any (·.plan.hasSlowUnits)
      let anyFast := allMods.any (fun m => !m.plan.fastUnitIds.isEmpty)
      -- 1. Lean 4 Fast-Lane Kernel Check (`F₁ + ∂_S + F₂`)
      if anyFast then
        let mode : EmitMode := if anySlow then .hybridCheck else .pureFast
        match emitBundleFiles slicedDeps mainSm mode false false with
        | .syntaxErr e => return (exitSyntaxErr, s!"SYNTAX_ERROR: {e}")
        | .bot r       => return (exitBot, s!"BOT: {r}")
        | .translated leanFiles => do
            let (lCode, lMsg) ← runLeanCheckFiles mirrorLibDir cleanWork leanFiles
            if lCode != exitOK then
              return (lCode, lMsg)
      -- 2. Agda Slow-Lane Parameterized Slice Check (`∂_{F₁} ⊢ S : ∂_S`), ONLY for modules with `SlowUnits ≠ ∅`!
      verifyAgdaSlowSlices mirrorLibDir cleanWork allMods

def runPrismBuildExe (mirrorLibDir mirrorIrDir workDir outBin : String)
    (depFiles : List String) (mainFile : String)
    (dumpBin : Option String := none) (trustedCodegen : Bool := false) : IO (UInt32 × String) := do
  let workAbs ← IO.Process.output { cmd := "realpath", args := #["-m", workDir] }
  let cleanWork := workAbs.stdout.trimAscii.toString
  let libAbs ← IO.Process.output { cmd := "realpath", args := #["-m", mirrorLibDir] }
  let cleanLib := libAbs.stdout.trimAscii.toString
  let irAbs ← IO.Process.output { cmd := "realpath", args := #["-m", mirrorIrDir] }
  let cleanIr := irAbs.stdout.trimAscii.toString
  let parsed ← parseAndSliceBundle depFiles mainFile cleanLib cleanWork dumpBin
  match parsed with
  | .syntaxErr e => pure (exitSyntaxErr, s!"SYNTAX_ERROR: {e}")
  | .bot r       => pure (exitBot, s!"BOT: {r}")
  | .translated (slicedDeps, mainSm) => do
      let allMods := slicedDeps ++ [mainSm]
      let anySlow := allMods.any (·.plan.hasSlowUnits)

      -- When `anyUserSlow == true` (and `!trustedCodegen`), run full two-lane Cut verification
      -- (`hybridCheck` + `SlowSlice`) FIRST before lowering `S` to erased `Thunk` / `partial def` C code!
      let anyUserSlow := allMods.any (fun m => m.plan.hasSlowUnits && !isImmutableContextMod m.srcUnit.modName)
      if anyUserSlow && !trustedCodegen then
        match emitBundleFiles slicedDeps mainSm .hybridCheck false false with
        | .syntaxErr e => return (exitSyntaxErr, s!"SYNTAX_ERROR: {e}")
        | .bot r       => return (exitBot, s!"BOT: {r}")
        | .translated chkFiles => do
            let (lCode, lMsg) ← runLeanCheckFiles cleanLib s!"{cleanWork}/hybrid_chk" chkFiles
            if lCode != exitOK then
              return (lCode, lMsg)
            let (aCode, aMsg) ← verifyAgdaSlowSlices cleanLib cleanWork allMods
            if aCode != exitOK then
              return (aCode, aMsg)

      let execMode : EmitMode := if anySlow then .erasedExec else .pureFast
      match emitBundleFiles slicedDeps mainSm execMode true false with
      | .syntaxErr e => pure (exitSyntaxErr, s!"SYNTAX_ERROR: {e}")
      | .bot r       => pure (exitBot, s!"BOT: {r}")
      | .translated leanFiles => do
          let cWork := s!"{cleanWork}/c_build"
          IO.FS.createDirAll cWork
          let leanPath := s!"{cWork}:{cleanLib}"
          let coreObj :=
            if (← System.FilePath.pathExists s!"{cleanIr}/AgdaMirror/Core.c.o") then
              s!"{cleanIr}/AgdaMirror/Core.c.o"
            else s!"{cleanIr}/AgdaMirror/Core.c"
          let ctxObj :=
            if (← System.FilePath.pathExists s!"{cleanIr}/AgdaMirror/Context.c.o") then
              s!"{cleanIr}/AgdaMirror/Context.c.o"
            else s!"{cleanIr}/AgdaMirror/Context.c"
          let worldObj :=
            if (← System.FilePath.pathExists s!"{cleanIr}/AgdaMirror/World.c.o") then
              s!"{cleanIr}/AgdaMirror/World.c.o"
            else s!"{cleanIr}/AgdaMirror/World.c"
          let protoObj :=
            if (← System.FilePath.pathExists s!"{cleanIr}/AgdaMirror/Protocol.c.o") then
              s!"{cleanIr}/AgdaMirror/Protocol.c.o"
            else s!"{cleanIr}/AgdaMirror/Protocol.c"
          let cliHostLib := s!"{cleanLib}/../liblean_cli_host.a"
          let cliHostObj := s!"{cleanIr}/../cbits/lean_cli_host.o"
          let mut linkObjs : Array String := #[coreObj, ctxObj, worldObj, protoObj]
          if (← System.FilePath.pathExists cliHostObj) then
            linkObjs := linkObjs.push cliHostObj
          else if (← System.FilePath.pathExists cliHostLib) then
            linkObjs := linkObjs.push cliHostLib
          for (modStem, leanSrc) in leanFiles do
            let srcPath := s!"{cWork}/{modStem}.lean"
            let oleanPath := s!"{cWork}/{modStem}.olean"
            let cPath := s!"{cWork}/{modStem}.c"
            IO.FS.writeFile srcPath leanSrc
            let (code, out, err) ← runSubproc "lean" #["-R", cWork, srcPath, "-o", oleanPath, "-c", cPath] (some leanPath)
            if code != 0 then
              return (exitTypeErr, s!"LEAN_TYPE_ERROR:\n{out}{err}")
            linkObjs := linkObjs.push cPath
          -- Prefer 100% static ELF linking (`gcc -O3 -static`) for hermetic cleanroom container execution!
          let (pfxCode, pfxOut, _) ← runSubproc "lean" #["--print-prefix"] none
          let tcPrefix := pfxOut.trimAscii.toString
          let mut linkedStatic : Bool := false
          if pfxCode == 0 && !tcPrefix.isEmpty then
            let staticArgs : Array String :=
              #[ "-O3", "-static"
               , "-I", s!"{tcPrefix}/include"
               , "-fstack-clash-protection", "-ffp-contract=off"
               , "-fdata-sections", "-ffunction-sections" ] ++
              linkObjs ++
              #[ "-L", s!"{tcPrefix}/lib/lean"
               , "-L", s!"{tcPrefix}/lib"
               , "-Wl,--start-group"
               , "-lleancpp", "-lLean", "-lStd", "-lInit", "-lleanrt"
               , "-lcadical", "-lLake", "-lLeanExport"
               , "-lc++", "-lc++abi", "-lunwind"
               , "-lgmp", "-luv", "-lssl", "-lcrypto"
               , "-lpthread", "-ldl", "-lrt", "-lm", "-lc"
               , "-Wl,--end-group", "-Wl,--gc-sections"
               , "-o", outBin ]
            let (sCode, _, _) ← runSubproc "gcc" staticArgs none
            if sCode == 0 then
              linkedStatic := true
          if !linkedStatic then
            let leancArgs := #["-O3"] ++ linkObjs ++ #["-o", outBin]
            let (lCode, lOut, lErr) ← runSubproc "leanc" leancArgs none
            if lCode != 0 then
              return (exitTypeErr, s!"LEANC_LINK_ERROR:\n{lOut}{lErr}")
          let _ ← runSubproc "chmod" #["0755", outBin] none
          pure (exitOK, "OK")

end Prism