import Prism.CatStructure
import AgdaMirror.Protocol
import AgdaMirror.AxiomGuard
import Lean.Compiler.LCNF.EmitC

/-! Resident command elaboration. Only a successfully guarded kernel environment can be
    published as a dependency. The artifact used at a join is Lean's own module image. -/
namespace Prism.KernelDriver

open Lean Elab

private def options : Options := ({} : Options)
  |>.setBool `Elab.async false
  -- Verification uses structural recursors. Newly generated datatypes need
  -- neither a SizeOf instance and its specifications nor injectivity lemmas.
  |>.setBool `genSizeOf false
  |>.setBool `genSizeOfSpec false
  |>.setBool `genInjectivity false
  -- Sparse eliminators use propositional extensionality even for datatype cases.
  |>.setBool `backward.match.sparseCases false
  |>.setBool `autoImplicit false
  |>.setBool `relaxedAutoImplicit false
  |>.setBool `linter.all false
  |>.set `maxRecDepth (100000 : Nat)
  |>.set `maxHeartbeats (2000000 : Nat)

private def mirrorImports : Array Import :=
  #[`AgdaMirror.Utf8, `AgdaMirror.Core, `AgdaMirror.Context, `AgdaMirror.World,
    `AgdaMirror.Protocol, `AgdaMirror.AxiomGuard].map fun n => { module := n }

structure Snapshot where
  id : Nat
  env : Environment
  allowed : Array Name

/-- Hash table lookup also compares the entire scoped input, including overload alternatives.
    A dependency ID identifies its exact, already verified content and import closure. -/
structure ModuleKey where
  code : String
  dependencies : Array Nat
  deriving BEq, Hashable

private structure Resident where
  lib : System.FilePath
  dir : System.FilePath
  imports : ImportState
  base : Environment
  nextId : Nat := 0
  modules : Std.HashMap ModuleKey Snapshot := {}
  guarded : Std.HashMap ModuleKey Snapshot := {}
  artifacts : NameMap ImportArtifacts := {}
  parents : Std.HashMap (Array Nat) Environment := {}

private initialize resident : IO.Ref (Option Resident) ← IO.mkRef none

def close : IO Unit := do
  if let some k ← resident.swap none then IO.FS.removeDirAll k.dir

def preload (lib : String) : IO Unit := do
  let lib ← IO.FS.realPath lib
  if let some k ← resident.get then
    unless k.lib == lib do throw <| IO.userError "kernel session mirror path changed"
    return
  initSearchPath (← findSysroot) [lib]
  -- Retain the import state as well as the environment: subsequent joins can extend it
  -- with verified module images without rereading any of the installed mirrors.
  let (imports, base) ← withImporting do
    unsafe enableInitializersExecution
    let (_, imports) ← (importModulesCore mirrorImports).run
    -- The CLI and MCP server retain this immutable base for their entire process.
    -- Marking it persistent avoids atomic reference counting on each command.
    let base ← finalizeImport imports mirrorImports options (trustLevel := 0)
      (leakEnv := true) (loadExts := true)
    pure (imports, base)
  let dir ← IO.FS.createTempDir
  resident.set (some {lib, dir, imports, base})

private def getResident : IO Resident := do
  let some k ← resident.get | throw <| IO.userError "kernel session was not initialized"
  return k

def lookup (key : ModuleKey) : IO (Option Snapshot) := do
  return (← getResident).modules[key]?

/-- A guarded fast slice can be used to check another fast slice. The module
    judgment is published only once its residual and every dependency pass. -/
def lookupGuarded (key : ModuleKey) : IO (Option Snapshot) := do
  return (← getResident).guarded[key]?

def rememberGuarded (key : ModuleKey) (snap : Snapshot) : IO Unit := do
  let k ← getResident
  resident.set (some {k with guarded := k.guarded.insert key snap})

private def parentEnvironment (deps : Array Snapshot) : IO Environment := do
  let k ← getResident
  if deps.isEmpty then return k.base
  let ids := deps.map (·.id)
  if let some env := k.parents[ids]? then return env
  let mut artifacts := k.artifacts
  for dep in deps do
    unless artifacts.contains dep.env.mainModule do
      let path := k.dir / s!"{dep.id}.olean"
      writeModule dep.env path (writeIR := false)
      artifacts := artifacts.insert dep.env.mainModule (.ofArrays #[#[path]])
  let direct := mirrorImports ++ deps.map (fun d => {module := d.env.mainModule})
  let env ← withImporting do
    unsafe enableInitializersExecution
    let (_, imports) ← (importModulesCore direct (arts := artifacts)).run k.imports
    finalizeImport imports direct options (trustLevel := 0) (leakEnv := false) (loadExts := true)
  resident.set (some {k with artifacts, parents := k.parents.insert ids env})
  return env

private def runIn {α : Type} (env : Environment) (action : Command.CommandElabM α)
    (opts : Options := options) :
    IO (α × Environment) := do
  let ctx : Command.Context := { fileName := env.mainModule.toString, fileMap := default,
                                 snap? := none, cancelTk? := none }
  let state := {Command.mkState env {} opts with infoState := {enabled := false}}
  match ← EIO.toIO' ((action ctx).run state) with
  | .error e => throw <| IO.userError (← e.toMessageData.toString)
  | .ok (v, st) => return (v, st.env)

/-- The checking and execution functors use the same command elaborator and diagnostics. -/
private def elabCommand (origin : String) (cmd : TSyntax `command) : Command.CommandElabM Unit := do
  Command.elabCommandTopLevel cmd.raw
  let messages := (← get).messages
  if messages.hasErrors || messages.toList.any (·.kind == `hasSorry) then
    let text ← messages.toList.mapM fun m => m.toString
    throwError "{origin}: {String.intercalate "\n" text}"

/-- Diagnostic view used by the translate command. -/
def renderCommands (lib : String) (cmds : Array (TSyntax `command)) : IO String := do
  initSearchPath (← findSysroot) [← IO.FS.realPath lib]
  unsafe enableInitializersExecution
  let env ← importModules #[{module := `Prism.TranscodeExec}] options (loadExts := true)
  let lines ← (cmds.mapM fun cmd => do return (← PrettyPrinter.ppCommand cmd).pretty)
    |>.toIO' {fileName := "<translate>", fileMap := default} {env}
  return String.intercalate "\n\n" lines.toList

/-- Compiled module images are local to one native build. Each new module extends
    the import state by one image. AxiomGuard is a checker plugin and does not
    belong to the native program's runtime import closure. -/
structure ExecImports where
  state : ImportState
  modules : Array Import
  artifacts : NameMap ImportArtifacts := {}

private def execOptions : Options := options.setBool `compiler.postponeCompile false

def startExec (lib : System.FilePath) : IO ExecImports := do
  initSearchPath (← findSysroot) [lib]
  let modules : Array Import := #[{module := `AgdaMirror.Protocol}]
  let (_, state) ← withImporting do
    unsafe enableInitializersExecution
    (importModulesCore modules).run
  return {state, modules}

/-- Put a computational SCC in Lean's native recursion mode. The rewritten
    declarations keep their precise types and bodies. No cast or arbitrary
    inhabitant is added to either kernel environment. -/
private partial def nativeRecursion? (cmd : TSyntax `command) : Command.CommandElabM (Option (TSyntax `command)) := do
  match cmd with
  | `(mutual $members:command* end) =>
    let members ← members.mapM nativeRecursion?
    if members.any Option.isNone then return none
    let defs := members.filterMap id
    return some (← `(mutual $defs:command* end))
  | `(partial def $n:declId $bs:bracketedBinder* $[: $t:term]? := $v:term)
  | `(def $n:declId $bs:bracketedBinder* $[: $t:term]? := $v:term) =>
    return some (← `(unsafe def $n:declId $bs:bracketedBinder* $[: $t]? := $v))
  | _ => return none

private def elabExecCommand (origin : String) (cmd : TSyntax `command) : Command.CommandElabM Unit := do
  let env ← getEnv
  if (cmd.raw.find? (fun s => s.isIdent && (env.find? s.getId).any ConstantInfo.isUnsafe)).isSome then
    if let some native ← nativeRecursion? cmd then return ← elabCommand origin native
  let before ← get
  try elabCommand origin cmd
  catch e =>
    -- A productive coinductive record need not have a finite inhabitant in
    -- the inductive execution representation. Its verified corecursion still
    -- has executable code. Only retry Lean's specific inhabitance obligation.
    let missing ← (← get).messages.toList.anyM fun msg => do
      let txt ← msg.data.toString
      return txt.startsWith "failed to compile 'partial' definition" && txt.contains "is nonempty."
    unless missing do throw e
    let some native ← nativeRecursion? cmd | throw e
    set before
    elabCommand origin native

/-- Synchronous command compilation records IR.Decl and impure LCNF in the same
    environment. Lean 4.36's native C emitter consumes this resident LCNF
    directly, just as the installed compiler does for its -c option. -/
def compileExec (imports : ExecImports) (moduleName : Name) (origin : String)
    (commands : Array (TSyntax `command)) (cPath : System.FilePath) (last : Bool) : IO ExecImports := do
  let env ← withImporting do
    unsafe enableInitializersExecution
    finalizeImport imports.state imports.modules execOptions (trustLevel := 0)
      (leakEnv := false) (loadExts := true)
  let (_, env) ← runIn (env.setMainModule moduleName) (commands.forM (elabExecCommand origin)) execOptions
  let data ← Compiler.LCNF.emitC moduleName
    |>.toIO' {fileName := origin, fileMap := default, options := execOptions} {env}
  IO.FS.writeFile cPath data
  if last then return imports
  let olean := cPath.withExtension "olean"
  writeModule env olean
  let artifacts := imports.artifacts.insert moduleName (.ofArrays #[#[olean]])
  let dep : Import := {module := moduleName}
  let (_, state) ← withImporting do
    unsafe enableInitializersExecution
    (importModulesCore #[dep] (arts := artifacts)).run imports.state
  return {state, modules := imports.modules.push dep, artifacts}

def elaborate (slice : CatStructure.LeanOpenSlice)
    (deps : Array Snapshot) (terminal := false) : IO Snapshot := do
  -- A one-shot leaf with exactly one parent can extend its checked environment
  -- directly. A snapshot destined for import must keep its own module boundary.
  let base ← match terminal, deps with
    | true, #[parent] => pure parent.env
    | _, _ => parentEnvironment deps
  let k ← getResident
  let id := k.nextId
  resident.set (some {k with nextId := id + 1})
  let env := base.setMainModule (.str .anonymous s!"PrismChecked{id}")
  let (_, checked) ← runIn env do
    for cmd in slice.ordered do
      elabCommand (fullDot cmd.origin) cmd.syntaxOf
    Command.liftCoreM (slice.checkAfterElaboration (some k.base))
  return ⟨id, checked, slice.allowedBoundaryAxioms⟩

def publish (key : ModuleKey) (snap : Snapshot) : IO Unit := do
  let k ← getResident
  resident.set (some {k with modules := k.modules.insert key snap, guarded := k.guarded.erase key})

/-- Independence restricts the ordinary slice boundary to the named specification.
    Repeat this stronger check even if the module judgment came from the cache. -/
def audit (snap : Snapshot) (witnesses allowed : Array Name) : IO Unit := do
  let base := (← getResident).base
  discard <| runIn snap.env do
    let ids := allowed.map mkIdent
    for witness in witnesses do
      elabCommand witness.toString (← `(#agda_prism_guard_witness $(mkIdent witness):ident assuming [$ids:ident,*]))
    Command.liftCoreM do
      let kernel := (← getEnv).checked.get
      for a in allowed do
        unless (kernel.find? a).any (fun i => i matches .axiomInfo _) do
          throwError "{a} is not a specification assumption"
      for witness in witnesses do
        unless (kernel.find? witness).any (fun i => i matches .defnInfo _ | .thmInfo _ | .opaqueInfo _) do
          throwError "missing checked witness {witness}"
        let footprint := collectRootAxioms (← getEnv) {} witness (some base)
        unless CatStructure.guardAxiomsAssuming allowed footprint do
          throwError "{witness} depends on axioms {footprint} outside the specification"

end Prism.KernelDriver
