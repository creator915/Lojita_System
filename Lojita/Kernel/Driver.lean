import Lojita.Kernel.ResidentImport
import Lojita.Kernel.KernelLimits
import Lojita.Kernel.KernelGuard
import Lojita.Kernel.AxiomGuard
import Lojita.Kernel.SyntaxTriage
import Lojita.Kernel.ElabGuard
import Lojita.Kernel.GroundEval
import Lojita.Kernel.SafeCompare
import Lojita.Kernel.CompileGuard

namespace Lojita.Kernel
open Lean Elab

private structure ModuleKey where
  mod          : LeanMod
  dependencies : Array Nat
  deriving BEq, Hashable

private structure Resident where
  lib          : System.FilePath
  imports      : ImportState
  base         : Environment
  modules      : Std.HashMap ModuleKey Snapshot := {}
  parents      : Std.HashMap (Array Nat) Environment := {}
  satisfied    : Std.HashSet (Nat × Nat × Bool) := {}
  preludeAudit : PreludeAudit := default

private initialize session : IO.Ref (Option Resident) ← IO.mkRef none
private initialize driverLock : Std.Mutex Unit ← Std.Mutex.new ()
private initialize nextSnapshotId : IO.Ref Nat ← IO.mkRef 1

private def contextImports : Array Import := #[{ module := `LojitaCtx }]

private def start (lib : System.FilePath) : IO Resident := do
  initKernelLimits
  let lib ← IO.FS.realPath lib
  let (state, base) ← withImportLock <| withImporting do
    searchPathRef.set (lib :: (← getBuiltinSearchPath toolchainRoot))
    unsafe enableInitializersExecution
    let (_, state) ← (importModulesCore contextImports).run
    let env ← finalizeImport state contextImports safeElabOptions (trustLevel := 0)
      (leakEnv := false) (loadExts := true)
    return (state, env)
  let r : Resident := { lib, imports := state, base }
  session.set (some r)
  return r

private def resident : IO Resident := do
  if let some r ← session.get then return r
  start ".lake/build/lib/lean"

def preload (lib : System.FilePath := ".lake/build/lib/lean") : IO Unit :=
  driverLock.atomically do
    initKernelLimits
    if let some r ← session.get then
      unless (← IO.FS.realPath lib) == r.lib do
        throw (IO.userError "resident library path changed")
    else
      discard <| start lib

def close : IO Unit := driverLock.atomically do
  session.set none

private def ioChecked {α : Type} (x : Except String α) : IO α :=
  match x with
  | .ok a    => pure a
  | .error e => throw (IO.userError e)

private def coreCtx (env : Environment) (opts : Options := safeElabOptions) : Core.Context := {
  fileName      := env.mainModule.toString
  fileMap       := default
  options       := opts
  maxHeartbeats := Core.getMaxHeartbeats opts
  maxRecDepth   := 2048
}

private def importedImages (deps : Array Snapshot) : Array (Name × ModuleData) :=
  dedupImages (deps.flatMap (·.images))

private def parentEnv (deps : Array Snapshot) (wrapper := false) (opts : Options := safeElabOptions) :
    IO Environment := do
  let r ← resident
  let ids := deps.map (·.id)
  if !wrapper && opts == safeElabOptions then
    if deps.isEmpty then return r.base
    if let some env := r.parents[ids]? then return env
  let images := importedImages deps
  let imports := contextImports ++ deps.map (fun d => { module := d.mod.modName.toLeanName }) ++
    (if wrapper then #[{ module := `Lojita.WorldRunner }] else #[])
  let env ← withImportLock <| withImporting do
    unsafe enableInitializersExecution
    let state ← if wrapper then
        Prod.snd <$> (importModulesCore #[{ module := `Lojita.WorldRunner }]).run r.imports
      else
        pure r.imports
    importResidentImages state images imports opts
  if !wrapper && opts == safeElabOptions then
    session.set <| some { r with parents := r.parents.insert ids env }
  return env

private def comparisonEnv (images : Array (Name × ModuleData)) (mods : Array Name) : IO Environment := do
  let r ← resident
  let imports := contextImports ++ mods.map ({ module := · })
  let env ← withImportLock <| withImporting do
    unsafe enableInitializersExecution
    importResidentImages r.imports (dedupImages images) imports safeElabOptions
  return env.setExporting false

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

/-- Resolve valid `LojitaCtx.*` module names and namespaces referenced by syntactic hints. -/
def contextHintsForRefs (refs : List QName) : IO (List QName × List QName) := driverLock.atomically do
  let r ← resident
  let mut seenMods : NameSet := {}
  let mut mods := #[]
  let mut seenNs : NameSet := {}
  let mut namespaces := #[]
  for ref in refs do
    let n := ref.toLeanName
    if let some origin := moduleOf? r.base n then
      if origin.getRoot == `LojitaCtx then
        unless seenMods.contains origin do
          seenMods := seenMods.insert origin
          mods := mods.push (QName.ofName origin)
        let mut ns := n.getPrefix
        while !ns.isAnonymous && ns.getRoot == `LojitaCtx do
          if r.base.isNamespace ns && !r.base.contains ns && !seenNs.contains ns then
            seenNs := seenNs.insert ns
            namespaces := namespaces.push (QName.ofName ns)
          ns := ns.getPrefix
    if let "LojitaCtx" :: sub :: _ := ref.segments then
      let mod := (`LojitaCtx).str sub
      if (r.base.getModuleIdx? mod).isSome && !seenMods.contains mod then
        seenMods := seenMods.insert mod
        mods := mods.push (QName.ofName mod)
  return (mods.toList, namespaces.toList)

private def extractGraph (env : Environment) (m : LeanMod) (constants : Array Name)
    (steps : Array Environment) (deps : Array Snapshot) (contextModules : NameSet) :
    MetaM (SemGraph × NameMap QName) := do
  let mut owners : NameMap QName := {}
  let mut prev := (steps[0]?.getD env).checked.get.constants
  for u in m.units, step in steps.extract (steps.size - m.units.length) steps.size do
    let now := step.checked.get.constants
    owners := now.foldStage2 (fun acc n _ =>
      if prev.contains n || acc.contains n then acc else acc.insert n u.uname) owners
    prev := now
  let external := deps.foldl (fun acc d => acc.union d.owners) ({} : NameMap QName)
  let allOwners := external.union owners
  let mut sorts := #[]
  for u in m.units do
    let named := u.definedNames.map QName.toLeanName
    let members := if !named.isEmpty then named else
      (owners.toList.filter (·.2 == u.uname)).map Prod.fst
    let mut law := !members.isEmpty
    for n in members do
      if let some info := env.find? n <|> env.find? (mkPrivateName env n) then
        if !(← Meta.isProp info.type) then law := false
    sorts := sorts.push (u.uname, if law then .law else .carrier)
  let mut edges : Std.HashSet (Obj × Obj) := {}
  for n in constants do
    let some owner := owners.find? n | continue
    let info ← getConstInfo n
    for used in info.getUsedConstantsAsSet do
      if let some origin := moduleOf? env used then
        if origin.getRoot == `LojitaCtx && !contextModules.contains origin then
          throwError "UNDECLARED_IMPORT: {origin} used by {n}"
      let target :=
        if let some q := owners.find? used then some (.unit q)
        else if let some q := external.find? used then some (.ext q)
        else if (moduleOf? env used).any (·.getRoot == `LojitaCtx) then some (.ext (QName.ofName used))
        else none
      if let some t := target then
        edges := edges.insert (.unit owner, t)
  return (⟨edges.toList, sorts.toList⟩, allOwners)

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
  let key : ModuleKey := { mod := m, dependencies := deps.map (·.id) }
  if let some snap := r.modules[key]? then return snap
  let src := renderLeanMod m
  let (parsed, cmds) ← ioChecked ((readEnvelope src).mapError toString)
  unless parsed.modName == m.modName && parsed.imports.map (·.imod) == m.imports.map (·.imod) do
    throw (IO.userError "namespaceEnvelope: inconsistent module metadata")
  let ctxMods ← ioChecked (contextClosure r.base parsed.imports deps)
  let base ← parentEnv deps
  let explicit := explicitAxioms parsed cmds
  let staged := deps.any (fun d => d.axioms.any (!trustedBaseAxioms.contains ·)) || !explicit.isEmpty
  let elabRes ← elabCommandsGuarded (base.setMainModule parsed.modName.toLeanName) src cmds staged
  let env := elabRes.env
  let constants := env.checked.get.constants.foldStage2 (fun a n _ => a.push n) #[]
  let (axs, preludeAudit) ← ioChecked (auditRoots env constants (some r.base) r.preludeAudit)
  if staged then
    for n in constants do
      if isNoncomputable env n && (env.find? n).any (· matches .defnInfo _) then
        let (footprint, _) ← ioChecked (auditRoots env #[n] none preludeAudit)
        let pending ← (do
          for ax in footprint do
            unless trustedBaseAxioms.contains ax || (← Meta.isProp (← getConstInfo ax).type) do
              return true
          return false : MetaM Bool).run' |>.toIO' (coreCtx env) { env }
        unless pending do
          throw (IO.userError s!"NONCOMPUTABLE_VIOLATION: {n}")
  let declared := constants.foldl (init := ({} : NameSet)) fun acc n =>
    if explicit.contains (privateToUserName n) && (env.find? n).any (· matches .axiomInfo _)
      then acc.insert n else acc
  let (graph, owners) ← (extractGraph env parsed constants elabRes.steps deps ctxMods).run'
    |>.toIO' (coreCtx env) { env }
  let r ← resident
  let images := (importedImages deps).push (env.mainModule, ← mkModuleData env)
  let id ← nextSnapshotId.modifyGet fun i => (i, i + 1)
  let versions := deps.foldl (fun acc d => acc.union d.versions) ({} : NameMap Nat)
  let snap : Snapshot := {
    id, mod := parsed, env, graph, axioms := axs, declaredAxioms := declared
    constants, owners, versions := versions.insert env.mainModule id
    contextModules := ctxMods, images, largeFuelDefs := elabRes.largeFuelDefs
  }
  session.set (some { r with preludeAudit, modules := r.modules.insert key snap })
  return snap

private abbrev Bundle := NameMap Snapshot

private partial def visit (mods : NameMap LeanMod) (path : NameSet) (n : Name) :
    StateT (Bundle × Array Snapshot) IO Snapshot := do
  if let some s := (← get).1.find? n then return s
  if path.contains n then throw (IO.userError s!"IMPORT_CYCLE: {n}")
  let some m := mods.find? n | throw (IO.userError s!"UNKNOWN_IMPORT: {n}")
  let mut deps := #[]
  for i in m.imports do
    unless i.imod.toLeanName.getRoot == `LojitaCtx do
      deps := deps.push (← visit mods (path.insert n) i.imod.toLeanName)
  let snap ← elaborate m deps
  modify fun (b, topo) => (b.insert n snap, topo.push snap)
  return snap

private def checkBundleOrdered (mods : List LeanMod) (staged : List QName) :
    IO (Bundle × Array Snapshot) := do
  let mut source := {}
  for m in mods do
    let n := m.modName.toLeanName
    if source.contains n then throw (IO.userError s!"DUPLICATE_MODULE: {n}")
    source := source.insert n m
  let (_, (snaps, topo)) ← (mods.forM fun m =>
    discard (visit source {} m.modName.toLeanName)).run ({}, #[])
  let allowed := staged.foldl
    (fun acc q => acc ++ ((snaps.find? q.toLeanName).map (·.declaredAxioms)).getD {})
    ({} : NameSet)
  for (_, s) in snaps do
    ioChecked (auditAxioms s.axioms allowed)
  return (snaps, topo)

private def checkBundle (mods : List LeanMod) (staged : List QName) : IO Bundle :=
  Prod.fst <$> checkBundleOrdered mods staged

private def checked (deps children : List LeanMod) (m : LeanMod) (spec : Bool) : IO Snapshot := do
  let mods := deps ++ children ++ [m]
  let snaps ← checkBundle mods ((if spec then mods else children).map (·.modName))
  unless spec do
    for d in deps do
      if let some snap := snaps.find? d.modName.toLeanName then
        ioChecked (auditAxioms snap.axioms {})
  let some s := snaps.find? m.modName.toLeanName
    | throw (IO.userError "missing main module")
  return s

def checkClosedModule (deps : List LeanMod) (main : LeanMod) : IO Snapshot :=
  driverLock.atomically do checked deps [] main false

def checkClosedBundle (mods : List LeanMod) : IO Unit :=
  driverLock.atomically do discard <| checkBundle mods []

def checkConditionalGlue (deps childStubs : List LeanMod) (main : LeanMod) (checkingSpec := false) :
    IO Snapshot :=
  driverLock.atomically do checked deps childStubs main checkingSpec

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
            (← Meta.isDefEq t.type (mkConst target)) then
          return true
    return false : MetaM Bool).run' |>.toIO' (coreCtx snap.env) { env := snap.env }
  unless valid do
    throw (IO.userError s!"REFUTATION_TARGET_MISMATCH: expected a public theorem of {expectedTarget}")
  return snap

def satisfies (spec impl : LeanMod) (deps : List LeanMod := [])
    (mode := SatisfactionMode.closedImplOK) (childStubs : List LeanMod := []) : IO Unit :=
  driverLock.atomically do
    let origA ← checked deps childStubs spec true
    let b ← checked deps childStubs impl (mode == .subspec)
    if origA.id == b.id then return
    let verdict := (origA.id, b.id, mode == .subspec)
    if (← resident).satisfied.contains verdict then return
    -- `b.env` already contains `Init`, `LojitaCtx`, `deps`, `childStubs`, and `b`'s own constants;
    -- `SafeCompare` reads `origA` from `origA.env.checked.get` and replays any unpaired `origA`
    -- private helpers under fresh names into `b.env.toKernelEnv` via `addDeclGuarded`, avoiding
    -- a redundant 40,000-constant `finalizeImport` on every `satisfies` call!
    let joint := b.env.setExporting false
    let isSpecStruct := isStructure origA.env
    -- Run Stage 3 comparison inside a 64 MiB worker thread with bounded `coreCtx`
    let compareTask ← IO.asTask do
      (compareInterfaceSafe origA b mode isSpecStruct).run' |>.toIO' (coreCtx joint) { env := joint }
    IO.ofExcept (← IO.wait compareTask)
    let r ← resident
    session.set (some { r with satisfied := r.satisfied.insert verdict })

def eqIface (a b : LeanMod) (deps : List LeanMod := []) : IO Unit := do
  satisfies a b deps .subspec
  satisfies b a deps .subspec

private def entryOwner (bundle : Bundle) (entry : QName) (mode : ExeMode) : IO Snapshot := do
  let n := entry.toLeanName
  let some (_, owner) := bundle.toList.find? (fun (_, s) => s.constants.contains n)
    | throw (IO.userError s!"ENTRY_MISSING: {entry}")
  (checkEntryType owner n mode).run' |>.toIO' (coreCtx owner.env) { env := owner.env }
  return owner

def checkVerifiedEntry (deps : List LeanMod) (entry : QName) (mode : ExeMode) : IO Unit :=
  driverLock.atomically do
    discard <| entryOwner (← checkBundle deps []) entry mode

/-- Stage 4: On-demand topological LCNF + IR compilation and adaptive `-O2`/`-O1` native linking.
    Daily `checkClosedModule`/`satisfies` never runs LCNF passes; codegen runs exclusively here! -/
def compileVerifiedExeWithReport (deps : List LeanMod) (entry : QName) (mode : ExeMode)
    (outBin : System.FilePath) (ccTimeoutSec : Nat := 30) :
    IO (Array (Name × String)) := driverLock.atomically do
  let (bundle, topoSnaps) ← checkBundleOrdered deps []
  let owner ← entryOwner bundle entry mode
  let r ← resident
  let lib := r.lib / ".."
  IO.FS.withTempDir fun dir => do
    let mut sources : Array System.FilePath := #[]
    let mut compiledImages : NameMap (Array (Name × ModuleData)) := {}
    let mut compiledEnvs : NameMap Environment := {}
    for snap in topoSnaps do
      let modName := snap.env.mainModule
      let userDeps := snap.mod.imports.filterMap fun imp =>
        if imp.imod.toLeanName.getRoot == `LojitaCtx then none
        else some imp.imod.toLeanName
      let cPath := dir / s!"module-{snap.id}.c"
      let envForC ← if userDeps.isEmpty then do
          -- Fast path: zero re-elaboration needed; materialize deferred LCNF + IR directly on `snap.env`!
          let (compiledEnv, _, _) ← materializeAndEmitC snap.env cPath
          pure compiledEnv
        else do
          -- Upstream user modules exist: import their compiled `ModuleData` (with `.impure` IR)
          let upImgs := dedupImages (userDeps.toArray.flatMap fun dn => (compiledImages.find? dn).getD #[])
          let imports := contextImports ++ userDeps.toArray.map ({ module := · })
          let base ← withImportLock <| withImporting do
            unsafe enableInitializersExecution
            importResidentImages r.imports upImgs imports codeGenOptions
          let src := renderLeanMod snap.mod
          let (_, cmds) ← ioChecked ((readEnvelope src).mapError toString)
          let elabRes ← elabCommandsGuarded (base.setMainModule modName) src cmds false codeGenOptions
          let cSrc ← (Compiler.LCNF.emitC modName).toIO' (coreCtx elabRes.env codeGenOptions) { env := elabRes.env }
          IO.FS.writeFile cPath cSrc
          pure elabRes.env
      let md ← mkModuleData envForC
      let allImgs := dedupImages ((userDeps.toArray.flatMap fun dn => (compiledImages.find? dn).getD #[]).push (modName, md))
      compiledImages := compiledImages.insert modName allImgs
      compiledEnvs := compiledEnvs.insert modName envForC
      sources := sources.push cPath

    -- Emit `Main` wrapper calling `Lojita.WorldRunner.{runCliIO | runReactiveIO}`
    let ownerName := owner.env.mainModule
    let ownerImgs := (compiledImages.find? ownerName).getD owner.images
    let wrapperImports := contextImports ++ #[{ module := ownerName }, { module := `Lojita.WorldRunner }]
    let mainBase ← withImportLock <| withImporting do
      unsafe enableInitializersExecution
      let state ← Prod.snd <$> (importModulesCore #[{ module := `Lojita.WorldRunner }]).run r.imports
      importResidentImages state ownerImgs wrapperImports codeGenOptions
    let runner := if mode == .cli then "runCliIO" else "runReactiveIO"
    let wrapper := s!"def main : IO UInt32 := Lojita.WorldRunner.{runner} {entry}"
    let cmd ← ioChecked (Parser.runParserCategory mainBase `command wrapper)
    let mainRes ← elabCommandsGuarded (mainBase.setMainModule `Main) wrapper #[cmd] false codeGenOptions
    let mainC := dir / "main.c"
    let mainCSrc ← (Compiler.LCNF.emitC `Main).toIO' (coreCtx mainRes.env codeGenOptions) { env := mainRes.env }
    IO.FS.writeFile mainC mainCSrc

    let allSources := sources.push mainC
    let built ← buildObjectsAdaptive allSources ccTimeoutSec
    let objPaths := built.map Prod.fst
    let report := topoSnaps.zipIdx.map fun (s, idx) =>
      (s.env.mainModule, (built[idx]?.map Prod.snd).getD "-O2")

    let stage := outBin.addExtension s!"{← IO.Process.getPID}.{← IO.monoNanosNow}.tmp"
    try
      runCcBounded (#["-O2", "-static"] ++ objPaths ++ #[
        "-L", lib.toString,
        "-L", (toolchainRoot / "lib/lean").toString,
        "-L", (toolchainRoot / "lib").toString,
        "-Wl,--start-group",
        "-llojita_Lojita", "-llojita_LojitaCtx", "-llean_cli_host",
        "-lStd", "-lInit", "-lleanrt", "-lcadical",
        "-lc++", "-lc++abi", "-lunwind", "-lgmp", "-luv", "-lssl", "-lcrypto",
        "-lpthread", "-ldl", "-lrt", "-lm", "-lc",
        "-Wl,--end-group", "-Wl,--gc-sections",
        "-o", stage.toString
      ]) ccTimeoutSec
      IO.FS.rename stage outBin
    finally
      if ← stage.pathExists then IO.FS.removeFile stage
    return report

def compileVerifiedExe (deps : List LeanMod) (entry : QName) (mode : ExeMode)
    (outBin : System.FilePath) : IO Unit :=
  discard <| compileVerifiedExeWithReport deps entry mode outBin

end Lojita.Kernel
