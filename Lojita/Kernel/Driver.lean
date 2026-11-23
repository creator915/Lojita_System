import Lojita.Kernel.ResidentImport
import Lojita.Kernel.LeanCode
import Lojita.Kernel.AxiomGuard
import Lean.Compiler.LCNF.EmitC
import Lean.Meta.Tactic.Delta

namespace Lojita.Kernel
open Lean Elab

private def options : Options := ({} : Options)
  |>.setBool `Elab.async false
  |>.setBool `autoImplicit true
  |>.setBool `genCtorIdx false
  |>.setBool `linter.all false
  |>.setBool `compiler.postponeCompile false
  |>.set `maxRecDepth (32768 : Nat)
  |>.set `maxHeartbeats (2000000 : Nat)

inductive DeclSort where
  | law | carrier
  deriving BEq, Repr

structure SemGraph where
  semArrows : List (Obj × Obj)
  sorts : List (QName × DeclSort)
  deriving Inhabited

structure Snapshot where
  id : Nat
  mod : LeanMod
  env : Environment
  graph : SemGraph
  axioms : NameSet
  declaredAxioms : NameSet
  constants : Array Name
  /-- Ownership of kernel auxiliaries, including private matchers and recursors. -/
  owners : NameMap QName
  /-- Unit signatures with object definitions unfolded in their defining snapshot. -/
  signatures : NameMap Expr
  contextModules : NameSet
  images : Array (Name × ModuleData)
  deriving Nonempty

private structure ModuleKey where
  code : String
  dependencies : Array Nat
  deriving BEq, Hashable

private structure Resident where
  lib : System.FilePath
  imports : ImportState
  base : Environment
  modules : Std.HashMap ModuleKey Snapshot := {}
  parents : Std.HashMap (Array Nat) Environment := {}
  preludeAudit : PreludeAudit := default
  nextId : Nat := 1

private initialize session : IO.Ref (Option Resident) ← IO.mkRef none
private initialize driverLock : Std.Mutex Unit ← Std.Mutex.new ()

private def contextImports : Array Import := #[{module := `LojitaCtx}]

private def start (lib : System.FilePath) : IO Resident := do
  let lib ← IO.FS.realPath lib
  let (state, base) ← withImportLock <| withImporting do
    searchPathRef.set (lib :: (← getBuiltinSearchPath toolchainRoot))
    unsafe enableInitializersExecution
    let (_, state) ← (importModulesCore contextImports).run
    let env ← finalizeImport state contextImports options (trustLevel := 0)
      (leakEnv := false) (loadExts := true)
    return (state, env)
  let r := {lib, imports := state, base : Resident}
  session.set (some r)
  return r

private def resident : IO Resident := do
  if let some r ← session.get then return r
  start ".lake/build/lib/lean"

def preload (lib : System.FilePath := ".lake/build/lib/lean") : IO Unit :=
  driverLock.atomically do
    if let some r ← session.get then
      unless (← IO.FS.realPath lib) == r.lib do throw (IO.userError "resident library path changed")
    else discard <| start lib

def close : IO Unit := driverLock.atomically do
  session.set none

private def ioChecked {α : Type} (x : Except String α) : IO α :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)

private def coreCtx (env : Environment) : Core.Context :=
  {fileName := env.mainModule.toString, fileMap := default, options}

/-- Import exact content-addressed module versions. A name alone cannot
    distinguish a child stub from its subsequently sealed implementation. -/
private def importedImages (deps : Array Snapshot) : Array (Name × ModuleData) := Id.run do
  let mut images := #[]
  let mut seen : NameSet := {}
  for dep in deps do
    for (n,data) in dep.images do
      unless seen.contains n do
        seen := seen.insert n
        images := images.push (n,data)
  return images

private def parentEnv (deps : Array Snapshot) (wrapper := false) : IO Environment := do
  let r ← resident
  let ids := deps.map (·.id)
  if !wrapper then
    if deps.isEmpty then return r.base
    if let some env := r.parents[ids]? then return env
  let images := importedImages deps
  let imports := contextImports ++ deps.map (fun d => {module := d.mod.modName.toLeanName}) ++
    (if wrapper then #[{module := `Lojita.WorldRunner}] else #[])
  let env ← withImportLock <| withImporting do
    unsafe enableInitializersExecution
    let state ← if wrapper then
        Prod.snd <$> (importModulesCore #[{module := `Lojita.WorldRunner}]).run r.imports
      else pure r.imports
    importResidentImages state images imports options
  if !wrapper then session.set <| some {r with parents := r.parents.insert ids env}
  return env

/-- Keep anonymous tests as private kernel declarations so they receive
    precisely the same footprint audit as named laws. -/
private def auditCommand (cmd : Syntax) : Command.CommandElabM Syntax := do
  let d := cmd[1]
  unless cmd.isOfKind ``Parser.Command.declaration && d.isOfKind ``Parser.Command.example do return cmd
  let id := mkIdent (← Command.liftCoreM (mkFreshUserName `objectExample))
  let sig : TSyntax ``Parser.Command.optDeclSig := ⟨d[1]⟩
  let rhs : TSyntax ``Parser.Command.declVal := ⟨d[2]⟩
  return (← `(private def $id:ident $sig:optDeclSig $rhs:declVal)).raw

private def elabCommands (env : Environment) (src : String) (cmds : Array Syntax)
    (stagedData := false) : IO (Environment × Array Environment) := do
  let ctx : Command.Context :=
    { fileName := env.mainModule.toString, fileMap := src.toFileMap, snap? := none, cancelTk? := none }
  let state := Command.mkState env {} options
  -- A conditional operation may call a child operation with no code yet.
  -- The same module is compiled normally when its dependency IDs are sealed.
  let state := {state with
    infoState := {enabled := false}
    scopes := state.scopes.map fun s => {s with isNoncomputable := stagedData}}
  let action : Command.CommandElabM (Option (Array Environment)) := do
    let mut steps := #[]
    for cmd in cmds do
      Command.elabCommandTopLevel (← auditCommand cmd)
      let log := (← get).messages
      if log.hasErrors then
        let messages ← log.toList.mapM fun m => m.toString
        throwError "{String.intercalate "\n" messages}"
      if log.toList.any (·.kind == `hasSorry) then return none
      steps := steps.push (← getEnv)
    return some steps
  match ← EIO.toIO' ((action ctx).run state) with
  | .error e => throw (IO.userError s!"ELABORATION_ERROR: {← e.toMessageData.toString}")
  | .ok (none, _) => throw (IO.userError "SORRY_AXIOM_VIOLATION: elaborated declaration uses sorryAx")
  | .ok (some steps, st) => return (st.env, steps)

private def contextClosure (base : Environment) (imports : List ImportSpec)
    (deps : Array Snapshot) : Except String NameSet := do
  let mut names := deps.foldl (fun acc d => acc ++ d.contextModules) ({} : NameSet)
  let mut todo := imports.map (·.imod.toLeanName)
  repeat
    let n :: rest := todo | break
    todo := rest
    if n.getRoot != `LojitaCtx || names.contains n then continue
    let some idx := base.getModuleIdx? n | throw s!"UNKNOWN_IMPORT: {n}"
    names := names.insert n
    todo := (base.header.moduleData[idx.toNat]!.imports.map (·.module)).toList ++ todo
  return names

/-- Locate the command which introduced a constant. Command environments are
    persistent and monotone, so this also assigns generated instances, private
    matchers and mutual recursors without naming conventions. -/
private def commandIndex (steps : Array Environment) (n : Name) : Nat := Id.run do
  let mut lo := 0
  let mut hi := steps.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if steps[mid]?.any (·.contains n) then hi := mid else lo := mid + 1
  return lo

private def extractGraph (env : Environment) (m : LeanMod) (constants : Array Name)
    (steps : Array Environment) (deps : Array Snapshot) (ctxMods : NameSet) :
    MetaM (SemGraph × NameMap QName × NameMap Expr) := do
  let firstUnit := m.opens.length + 1
  let units := m.units.toArray
  let mut owners : NameMap QName := {}
  for n in constants do
    let i := commandIndex steps n
    let unit := if i < firstUnit then none else units[i - firstUnit]?
    owners := owners.insert n ((unit.map (·.uname)).getD (QName.ofName (privateToUserName n)))
  let external := deps.foldl (fun acc d => acc.union d.owners) ({} : NameMap QName)
  let allOwners := owners.union external
  let mut signatures := deps.foldl (fun acc d => acc.union d.signatures) ({} : NameMap Expr)
  let mut sorts := #[]
  let mut edges : Std.HashSet (Obj × Obj) := {}
  for n in constants do
    let info ← getConstInfo n
    let owner := (owners.find? n).get!
    if !isPrivateName n && !n.isInternal then
      signatures := signatures.insert n (← Meta.deltaExpand info.type fun d =>
        allOwners.contains d && (env.find? d).any (· matches .defnInfo _))
      sorts := sorts.push (QName.ofName n, if ← Meta.isProp info.type then .law else .carrier)
    for used in info.getUsedConstantsAsSet do
      if let some origin := moduleOf? env used then
        if origin.getRoot == `LojitaCtx && !ctxMods.contains origin then
          throwError "UNDECLARED_IMPORT: {origin} used by {n}"
      let target := if let some q := owners.find? used then some (.unit q)
        else if let some q := external.find? used then some (.ext q)
        else if (moduleOf? env used).any (·.getRoot == `LojitaCtx) then some (.ext (QName.ofName used))
        else none
      if let some t := target then edges := edges.insert (.unit owner, t)
  return (⟨edges.toList, sorts.toList⟩, allOwners, signatures)

private def explicitAxioms (m : LeanMod) (cmds : Array Syntax) : NameSet := Id.run do
  let mut names := {}
  for cmd in cmds do
    let members := if cmd.isOfKind ``Parser.Command.mutual then cmd[1].getArgs else #[cmd]
    for member in members do
      if member.isOfKind ``Parser.Command.declaration && member[1].isOfKind ``Parser.Command.axiom then
        names := names.insert (m.modName.toLeanName ++ member[1][1][0].getId)
  return names

private def elaborate (m : LeanMod) (deps : Array Snapshot) : IO Snapshot := do
  let r ← resident
  let key := {code := encodeCanonical m, dependencies := deps.map (·.id) : ModuleKey}
  if let some snap := r.modules[key]? then return snap
  let src := renderLeanMod m
  let (parsed, cmds) ← ioChecked ((readEnvelope src).mapError toString)
  -- A decoded or hand-built carrier is untrusted as well. Kernel ownership and
  -- allowed assumptions always come from the newly parsed and checked source.
  unless parsed.modName == m.modName && parsed.imports.map (·.imod) == m.imports.map (·.imod) do
    throw (IO.userError "namespaceEnvelope: inconsistent module metadata")
  let ctxMods ← ioChecked (contextClosure r.base parsed.imports deps)
  let base ← parentEnv deps
  let explicit := explicitAxioms parsed cmds
  let staged := deps.any (fun d => d.axioms.any (!trustedBaseAxioms.contains ·)) ||
    !explicit.isEmpty
  let (env, steps) ← elabCommands (base.setMainModule parsed.modName.toLeanName) src cmds staged
  let constants := env.checked.get.constants.foldStage2 (fun a n _ => a.push n) #[]
  let (axs, preludeAudit) ← ioChecked (auditRoots env constants (some r.base) r.preludeAudit)
  -- A staged signature can withhold executable operations. Suppressing their
  -- code-generation errors must not admit an unrelated classical computation.
  if staged then
    for n in constants do
      if isNoncomputable env n && (env.find? n).any (· matches .defnInfo _) then
        let (footprint, _) ← ioChecked (auditRoots env #[n] none preludeAudit)
        let pending ← (do
          for ax in footprint do
            unless trustedBaseAxioms.contains ax || (← Meta.isProp (← getConstInfo ax).type) do
              return true
          return false : MetaM Bool).run' |>.toIO' (coreCtx env) {env}
        unless pending do throw (IO.userError s!"NONCOMPUTABLE_VIOLATION: {n}")
  let declared := constants.foldl (init := ({} : NameSet)) fun acc n =>
    if explicit.contains (privateToUserName n) && (env.find? n).any (· matches .axiomInfo _)
      then acc.insert n else acc
  let (graph, owners, signatures) ← (extractGraph env parsed constants steps deps ctxMods).run' |>.toIO' (coreCtx env) {env}
  let r ← resident
  let images := (importedImages deps).push (env.mainModule, ← mkModuleData env)
  let snap : Snapshot := {
    id := r.nextId, mod := parsed, env, graph, axioms := axs, declaredAxioms := declared
    constants, owners, signatures, contextModules := ctxMods, images}
  session.set (some {r with preludeAudit, nextId := r.nextId + 1, modules := r.modules.insert key snap})
  return snap

private abbrev Bundle := NameMap Snapshot

private partial def visit (mods : NameMap LeanMod) (path : NameSet) (n : Name) :
    StateT Bundle IO Snapshot := do
  if let some s := (← get).find? n then return s
  if path.contains n then throw (IO.userError s!"IMPORT_CYCLE: {n}")
  let some m := mods.find? n | throw (IO.userError s!"UNKNOWN_IMPORT: {n}")
  let mut deps := #[]
  for i in m.imports do
    unless i.imod.toLeanName.getRoot == `LojitaCtx do
      deps := deps.push (← visit mods (path.insert n) i.imod.toLeanName)
  let snap ← elaborate m deps
  modify (·.insert n snap)
  return snap

private def checkBundle (mods : List LeanMod) (staged : List QName) : IO Bundle := do
  let mut source := {}
  for m in mods do
    let n := m.modName.toLeanName
    if source.contains n then throw (IO.userError s!"DUPLICATE_MODULE: {n}")
    source := source.insert n m
  let (_, snaps) ← (mods.forM fun m => discard (visit source {} m.modName.toLeanName)).run {}
  let allowed := staged.foldl (fun acc q => acc ++ ((snaps.find? q.toLeanName).map (·.declaredAxioms)).getD {})
    ({} : NameSet)
  for (_, s) in snaps do ioChecked (auditAxioms s.axioms allowed)
  return snaps

private def checked (deps children : List LeanMod) (m : LeanMod) (spec : Bool) : IO Snapshot := do
  let mods := deps ++ children ++ [m]
  let snaps ← checkBundle mods ((if spec then mods else children).map (·.modName))
  -- A sealed upstream module can never borrow an assumption from a child.
  unless spec do
    for d in deps do
      if let some snap := snaps.find? d.modName.toLeanName then ioChecked (auditAxioms snap.axioms {})
  let some s := snaps.find? m.modName.toLeanName | throw (IO.userError "missing main module")
  return s

def checkClosedModule (deps : List LeanMod) (main : LeanMod) : IO Snapshot :=
  driverLock.atomically do checked deps [] main false

def checkClosedBundle (mods : List LeanMod) : IO Unit :=
  driverLock.atomically do discard <| checkBundle mods []

def checkConditionalGlue (deps childStubs : List LeanMod) (main : LeanMod) (checkingSpec := false) :
    IO Snapshot := driverLock.atomically do checked deps childStubs main checkingSpec

def checkRefutation (closedBases : List LeanMod) (specStub refuteMod : LeanMod)
    (expectedTarget : List Name := [``False]) : IO Snapshot := driverLock.atomically do
  let snap ← checked closedBases [specStub] refuteMod false
  let valid ← (do
    for q in snap.mod.units.flatMap (·.definedNames) do
      let n := q.toLeanName
      if !snap.constants.contains n || isPrivateName n then continue
      let some (.thmInfo t) := snap.env.find? n | continue
      for target in expectedTarget do
        if !snap.constants.contains target && (← getEnv).contains target &&
            (← Meta.isDefEq t.type (mkConst target)) then return true
    return false : MetaM Bool).run' |>.toIO' (coreCtx snap.env) {env := snap.env}
  unless valid do throw (IO.userError s!"REFUTATION_TARGET_MISMATCH: expected a public theorem of {expectedTarget}")
  return snap

inductive SatisfactionMode where
  | closedImplOK | subspec
  deriving BEq

/-- Interpret concrete spec helpers in their *own* environment before changing
    namespace. Otherwise a private matcher of the same name in the candidate
    could silently change the meaning of a spec body. -/
private def projectExpr (spec impl : Snapshot) (owned : NameSet) (e : Expr) : MetaM Expr := do
  let concrete (n : Name) := owned.contains n && (spec.env.find? n).any fun i =>
    i matches .defnInfo _ || (isPrivateName n && i matches .thmInfo _)
  let e ← withEnv spec.env <| Meta.deltaExpand e concrete (allowOpaque := true)
  let rename (n : Name) := if owned.contains n && !isPrivateName n then
      n.replacePrefix spec.env.mainModule impl.env.mainModule else n
  return ← Core.transform e (post := fun e => pure <| .done <| match e with
    | .const n us => .const (rename n) us
    | .proj n i val => .proj (rename n) i val
    | _ => e)

private def counterpart (spec impl : Snapshot) (n : Name) : Name :=
  let name := (privateToUserName n).replacePrefix spec.env.mainModule impl.env.mainModule
  if isPrivateName n then mkPrivateNameCore impl.env.mainModule name else name

private def convertible (levelParams : List Name) (actual expected : Expr) : CoreM Bool := do
  if actual.hasMVar || expected.hasMVar then return false
  -- Kernel.check accepts free universe parameters. Restrict the projection to
  -- the declaration's own parameters, which also instantiate the candidate.
  if expected.hasLevelParam && !(collectLevelParams {} expected).params.all levelParams.contains then
    return false
  let env ← getEnv
  unless (Lean.Kernel.check env {} expected).isOk do return false
  -- The candidate was checked in its snapshot. Kernel conversion unfolds either
  -- side, including structural recursors applied to neutral arguments.
  return Lean.Kernel.isDefEq env {} expected actual matches .ok true

/-- Private inductives are nominal too. If conversion needs their correspondence,
    enqueue their signatures and constructors as additional proof obligations. -/
private def compareExpr (a b : Snapshot) (owned : NameSet) (levelParams : List Name) (description : String)
    (actual original : Expr) : MetaM (List Name) := do
  let expected ← projectExpr a b owned original
  if ← convertible levelParams actual expected then return []
  let mut pairs : NameMap Name := {}
  for n in expected.getUsedConstantsAsSet do
    if isPrivateName n && owned.contains n then
      let target := counterpart a b n
      if b.env.contains target then pairs := pairs.insert n target
  unless pairs.isEmpty do
    let translated ← Core.transform expected (post := fun e => pure <| .done <| match e with
      | .const n us => .const ((pairs.find? n).getD n) us
      | .proj n i val => .proj ((pairs.find? n).getD n) i val
      | _ => e)
    if ← convertible levelParams actual translated then return pairs.toList.map Prod.fst
  throwError "INTERFACE_MISMATCH: {description}\nexpected {expected}\nreceived {actual}"

private def compareInterface (spec impl : Snapshot) (mode : SatisfactionMode) : MetaM Unit := do
  let owned := NameSet.ofArray spec.constants
  let provided := NameSet.ofArray impl.constants
  let explicitNames := spec.mod.units.flatMap (·.definedNames) |>.map QName.toLeanName
  let mut todo := spec.constants.toList.filter fun n =>
    !isPrivateName n && (!n.isInternalDetail || explicitNames.contains n)
  let mut visited : NameSet := {}
  repeat
    let n :: rest := todo | break
    todo := rest
    if visited.contains n then continue
    visited := visited.insert n
    let a ← withEnv spec.env (getConstInfo n)
    let target := counterpart spec impl n
    let some b := impl.env.checked.get.find? target
      | throwError "INTERFACE_MISSING: {target}"
    unless provided.contains target do throwError "INTERFACE_MISSING: {target}"
    unless a.numLevelParams == b.numLevelParams do
      throwError "INTERFACE_MISMATCH: {target} universe arity {a.numLevelParams} != {b.numLevelParams}"
    let levels := a.levelParams.map Level.param
    let inst := fun (e : Expr) => e.instantiateLevelParams b.levelParams levels
    let compare := compareExpr spec impl owned a.levelParams
    todo := (← compare s!"type of {target}" (inst b.type) a.type) ++ todo
    match a, b with
    | .axiomInfo _, .axiomInfo _ =>
      unless mode == .subspec do throwError "DISALLOWED_AXIOM_VIOLATION: {target}"
    | .axiomInfo _, .defnInfo _ | .axiomInfo _, .thmInfo _ | .axiomInfo _, .ctorInfo _ => pure ()
    | .thmInfo _, .thmInfo _ | .thmInfo _, .defnInfo _ => pure ()
    | .defnInfo av, .defnInfo bv =>
      unless ← Meta.isProp b.type do
        todo := (← compare s!"body of {target}" (inst bv.value) av.value) ++ todo
    | .defnInfo _, .thmInfo _ => pure () -- The type comparison established proof irrelevance.
    | .inductInfo av, .inductInfo bv =>
      unless av.numParams == bv.numParams && av.numIndices == bv.numIndices &&
          av.ctors.map (counterpart spec impl) == bv.ctors &&
          av.all.map (counterpart spec impl) == bv.all &&
          isStructure spec.env n == isStructure impl.env target do
        throwError "INTERFACE_MISMATCH: inductive parameters, structure or constructors of {target}"
      todo := av.ctors ++ av.all ++ todo
    | .ctorInfo av, .ctorInfo _ => todo := av.induct :: todo
    | .recInfo av, .recInfo _ => todo := av.all ++ todo
    | _, _ => throwError "INTERFACE_MISMATCH: declaration kind of {target}"

def satisfies (spec impl : LeanMod) (deps : List LeanMod := [])
    (mode := SatisfactionMode.closedImplOK) (childStubs : List LeanMod := []) : IO Unit := driverLock.atomically do
  let a ← checked deps childStubs spec true
  let b ← checked deps childStubs impl (mode == .subspec)
  if a.id == b.id then return
  let aName := a.env.mainModule
  let bName := b.env.mainModule
  let a ← if aName.isPrefixOf bName || bName.isPrefixOf aName then do
    let mut newName := Name.mkSimple s!"LojitaInterface{a.id}"
    while a.env.isNamespace newName || b.env.isNamespace newName ||
        a.env.contains newName || b.env.contains newName do newName := newName.appendAfter "_"
    let copy ← ioChecked (relocateInterface a.mod (QName.ofName newName))
    checked deps childStubs copy true
  else pure a
  -- Conversion may inspect the private matchers of either checked module.
  let joint := (← parentEnv #[a, b]).setExporting false
  (compareInterface a b mode).run' |>.toIO' (coreCtx joint) {env := joint}

def eqIface (a b : LeanMod) (deps : List LeanMod := []) : IO Unit := do
  satisfies a b deps .subspec
  satisfies b a deps .subspec

inductive ExeMode where
  | cli | reactive
  deriving BEq, Repr

private def checkEntry (snap : Snapshot) (entry : Name) (mode : ExeMode) : MetaM Unit := do
  let info ← getConstInfo entry
  let caps ← Meta.mkFreshExprMVar (mkApp (mkConst ``List [.zero]) (mkConst `LojitaCtx.World.Cap))
  let wanted ← match mode with
    | .cli => pure <| mkApp (mkConst `LojitaCtx.World.CliApp) caps
    | .reactive => do
      let state ← Meta.mkFreshExprMVar (mkSort (.succ .zero))
      pure <| mkApp2 (mkConst `LojitaCtx.World.ReactiveApp) caps state
  unless snap.constants.contains entry && !isPrivateName entry && info.levelParams.isEmpty &&
      (← Meta.isDefEq info.type wanted) && !(← instantiateMVars wanted).hasMVar do
    throwError "ENTRY_TYPE_MISMATCH: {entry} has type {info.type}, expected {wanted}"

/-- Resolve the owner and type with the same check used by the native linker. -/
private def entryOwner (bundle : Bundle) (entry : QName) (mode : ExeMode) : IO Snapshot := do
  let n := entry.toLeanName
  let some (_, owner) := bundle.toList.find? (fun (_, s) => s.constants.contains n)
    | throw (IO.userError s!"ENTRY_MISSING: {entry}")
  (checkEntry owner n mode).run' |>.toIO' (coreCtx owner.env) {env := owner.env}
  return owner

def checkVerifiedEntry (deps : List LeanMod) (entry : QName) (mode : ExeMode) : IO Unit :=
  driverLock.atomically do discard <| entryOwner (← checkBundle deps []) entry mode

/-- Compile a pure probe in a separate environment. Returning a value requires the
    caller to check the entry type before interpretation. No probe image is cached
    in the closed-world driver. -/
def elaborateProbe (src : String) : IO (Environment × Name) := driverLock.atomically do
  let (m, cmds) ← ioChecked ((readProbeEnvelope src).mapError toString)
  unless m.imports.any (·.imod.toLeanName == `Lojita.Session.SessionEnv) &&
      m.imports.all (fun i => i.imod.toLeanName == `Lojita.Session.SessionEnv ||
        i.imod.toLeanName.getRoot == `LojitaCtx) do
    throw (IO.userError "PROBE_IMPORT: import Lojita.Session.SessionEnv")
  let _ ← resident
  let base ← withImportLock do
    unsafe enableInitializersExecution
    importModules (m.imports.map (fun i => {module := i.imod.toLeanName})).toArray options (loadExts := true)
  let (env, _) ← elabCommands (base.setMainModule m.modName.toLeanName) src cmds
  let names := env.checked.get.constants.foldStage2 (fun a n _ => a.push n) #[]
  ioChecked <| auditAxioms (← ioChecked (collectRootAxioms env names)) {}
  let n := m.modName.toLeanName ++ `probe
  unless names.contains n do throw (IO.userError "PROBE_ENTRY: define probe : Probe")
  return (env, n)

private def cc (args : Array String) : IO Unit := do
  let result ← IO.Process.output {cmd := "cc", args}
  unless result.exitCode == 0 do
    throw (IO.userError s!"NATIVE_BUILD_ERROR: cc ({result.exitCode})\n{result.stderr}{result.stdout}")

private def emitSource (env : Environment) (path : System.FilePath) : IO Unit := do
  let c ← Compiler.LCNF.emitC env.mainModule |>.toIO' (coreCtx env) {env}
  IO.FS.writeFile path c

private def buildObjects (sources : Array System.FilePath) : IO (Array String) := do
  let flags := #["-O3", "-I", (toolchainRoot / "include").toString, "-ffp-contract=off",
    "-ffunction-sections", "-fdata-sections"]
  let mut objects := #[]
  for first in [0:sources.size:4] do
    let mut jobs := #[]
    for src in sources.extract first (first + 4) do
      let obj := (src.withExtension "o").toString
      jobs := jobs.push (← IO.asTask (cc (flags ++ #["-c", src.toString, "-o", obj])) .dedicated)
      objects := objects.push obj
    let results ← jobs.mapM (m := BaseIO) IO.wait
    for result in results do IO.ofExcept result
  return objects

/-- Emit the exact sealed environments. Only the trusted wrapper can import
    WorldRunner. The final rename publishes a completely linked executable. -/
def compileVerifiedExe (deps : List LeanMod) (entry : QName) (mode : ExeMode)
    (outBin : System.FilePath) : IO Unit := driverLock.atomically do
  let bundle ← checkBundle deps []
  let owner ← entryOwner bundle entry mode
  let lib := (← resident).lib / ".."
  IO.FS.withTempDir fun dir => do
    let mut sources := #[]
    for (_, snap) in bundle do
      let path := dir / s!"module-{snap.id}.c"
      emitSource snap.env path
      sources := sources.push path
    let env := (← parentEnv #[owner] (wrapper := true)).setMainModule `Main
    let runner := if mode == .cli then "runCliIO" else "runReactiveIO"
    let wrapper := s!"def main : IO UInt32 := Lojita.WorldRunner.{runner} {entry}"
    let cmd ← ioChecked (Parser.runParserCategory env `command wrapper)
    let (env, _) ← elabCommands env wrapper #[cmd]
    let mainC := dir / "main.c"
    emitSource env mainC
    let objects ← buildObjects (sources.push mainC)
    let stage := outBin.addExtension s!"{← IO.Process.getPID}.{← IO.monoNanosNow}.tmp"
    try
      cc <| #["-O3", "-static"] ++ objects ++ #[
        "-L", lib.toString, "-L", (toolchainRoot / "lib/lean").toString,
        "-L", (toolchainRoot / "lib").toString, "-Wl,--start-group",
        "-llojita_Lojita", "-llojita_LojitaCtx", "-llean_cli_host", "-lStd", "-lInit", "-lleanrt",
        "-lcadical", "-lc++", "-lc++abi", "-lunwind", "-lgmp", "-luv", "-lssl", "-lcrypto",
        "-lpthread", "-ldl", "-lrt", "-lm", "-lc", "-Wl,--end-group", "-Wl,--gc-sections",
        "-o", stage.toString]
      IO.FS.rename stage outBin
    finally
      if ← stage.pathExists then IO.FS.removeFile stage

end Lojita.Kernel
