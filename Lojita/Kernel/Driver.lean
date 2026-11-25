import Lojita.Kernel.ResidentImport
import Lojita.Kernel.LeanCode
import Lojita.Kernel.AxiomGuard
import Lean.Compiler.LCNF.EmitC
import Lean.Meta.Transform

namespace Lojita.Kernel
open Lean Elab

private def options : Options := ({} : Options)
  |>.setBool `Elab.async false
  |>.setBool `autoImplicit true
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
  /-- Exact versions of this module and its transitive object imports. -/
  versions : NameMap Nat
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
  /-- Successful interface comparisons of immutable, content-addressed
      snapshots `(spec id, impl id, subspec mode)`. Only verdicts are kept;
      the one-off comparison environments are dropped after each call. -/
  satisfied : Std.HashSet (Nat × Nat × Bool) := {}
  preludeAudit : PreludeAudit := default

private initialize session : IO.Ref (Option Resident) ← IO.mkRef none
private initialize driverLock : Std.Mutex Unit ← Std.Mutex.new ()
private initialize nextSnapshotId : IO.Ref Nat ← IO.mkRef 1

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
private def dedupImages (all : Array (Name × ModuleData)) : Array (Name × ModuleData) := Id.run do
  let mut images := #[]
  let mut seen : NameSet := {}
  for (n,data) in all do
    unless seen.contains n do
      seen := seen.insert n
      images := images.push (n,data)
  return images

private def importedImages (deps : Array Snapshot) : Array (Name × ModuleData) :=
  dedupImages (deps.flatMap (·.images))

private def parentEnv (deps : Array Snapshot) (wrapper := false) : IO Environment := do
  let r ← resident
  let ids := deps.map (·.id)
  if !wrapper then
    if deps.isEmpty then return r.base
    if let some env := r.parents[ids]? then return env
  let images := importedImages deps
  let imports := contextImports ++ deps.map (fun d => {module := d.mod.modName.toLeanName}) ++
    (if wrapper then #[{module := `Lojita.WorldRunner}, {module := `Lojita.Runtime.WorldRunner}] else #[])
  let env ← withImportLock <| withImporting do
    unsafe enableInitializersExecution
    let state ← if wrapper then
        Prod.snd <$> (importModulesCore #[{module := `Lojita.WorldRunner}, {module := `Lojita.Runtime.WorldRunner}]).run r.imports
      else pure r.imports
    importResidentImages state images imports options
  if !wrapper then session.set <| some {r with parents := r.parents.insert ids env}
  return env

/-- A one-off comparison environment. It is never cached in `Resident.parents`:
    its images are specific to a single `satisfies` call. -/
private def comparisonEnv (images : Array (Name × ModuleData)) (mods : Array Name) : IO Environment := do
  let r ← resident
  let imports := contextImports ++ mods.map ({module := ·})
  let env ← withImportLock <| withImporting do
    unsafe enableInitializersExecution
    importResidentImages r.imports (dedupImages images) imports options
  return env.setExporting false

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

/-- Resolve valid `LojitaCtx.*` module names and namespaces referenced by syntactic hints
    against the resident context environment, ignoring non-module guesses such as `LojitaCtx.Bytes`. -/
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
    MetaM (SemGraph × NameMap QName) := do
  let firstUnit := m.opens.length + 1
  let units := m.units.toArray
  let mut owners : NameMap QName := {}
  for n in constants do
    let i := commandIndex steps n
    let unit := if i < firstUnit then none else units[i - firstUnit]?
    owners := owners.insert n ((unit.map (·.uname)).getD (QName.ofName (privateToUserName n)))
  let external := deps.foldl (fun acc d => acc.union d.owners) ({} : NameMap QName)
  let allOwners := owners.union external
  let mut sorts := #[]
  let mut edges : Std.HashSet (Obj × Obj) := {}
  for n in constants do
    let info ← getConstInfo n
    let owner := (owners.find? n).get!
    if !isPrivateName n && !n.isInternal then
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
  let (graph, owners) ← (extractGraph env parsed constants steps deps ctxMods).run' |>.toIO' (coreCtx env) {env}
  let r ← resident
  let images := (importedImages deps).push (env.mainModule, ← mkModuleData env)
  let id ← nextSnapshotId.modifyGet fun i => (i, i + 1)
  let versions := deps.foldl (fun acc d => acc.union d.versions) ({} : NameMap Nat)
  let snap : Snapshot := {
    id, mod := parsed, env, graph, axioms := axs, declaredAxioms := declared
    constants, owners, versions := versions.insert env.mainModule id, contextModules := ctxMods, images}
  session.set (some {r with preludeAudit, modules := r.modules.insert key snap})
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

/-- Substitute selected constant bodies from their defining environment and relocate
    the remaining names. Visiting the constant alone leaves applications, including
    recursors on closed numerals, unevaluated. -/
def Snapshot.mapConstants (s : Snapshot) (e : Expr) (unfold : Name → Bool)
    (rename : Name → Name) (unfoldProofs := false) : CoreM Expr :=
  Core.transform e (post := fun
    | .const n us => do
      if unfold n then
        if let some info := s.env.find? n then
          if info.isDefinition || (unfoldProofs && info matches .thmInfo _) then
            return .visit (info.instantiateValueLevelParams! us (allowOpaque := unfoldProofs))
      return .done (.const (rename n) us)
    | .proj n i val => return .done (.proj (rename n) i val)
    | e => return .done e)

private def hiddenConstants (s : Snapshot) : NameSet :=
  let explicit := NameSet.ofList (s.mod.units.flatMap (·.definedNames) |>.map QName.toLeanName)
  NameSet.ofArray <| s.constants.filter fun n => isPrivateName n || (n.isInternalDetail && !explicit.contains n)

private def projectExpr (spec impl : Snapshot) (hidden exports : NameSet) (e : Expr) : CoreM Expr :=
  -- Each exported declaration is compared separately. A generated match_1 can
  -- have a public kernel name while still being an implementation detail.
  spec.mapConstants e hidden.contains
    (fun n => if exports.contains n then
      n.replacePrefix spec.env.mainModule impl.env.mainModule else n) (unfoldProofs := true)

private def counterpart (spec impl : Snapshot) (n : Name) : Name :=
  let name := (privateToUserName n).replacePrefix spec.env.mainModule impl.env.mainModule
  if isPrivateName n then mkPrivateNameCore impl.env.mainModule name else name

/-- Closed prelude text values: `String` (0), `List Char` (1) or `Array Char`
    (2). The interpretation follows the definitions of these prelude functions
    exactly, so distinct values are never definitionally equal. -/
private def groundText? : Expr → Option (Nat × List Char)
  | .mdata _ e => groundText? e
  | .lit (.strVal s) => some (0, s.toList)
  | .app (.app (.const ``String.append _) a) b => do
    let (0, x) ← groundText? a | none
    let (0, y) ← groundText? b | none
    some (0, x ++ y)
  | .app (.app (.app (.app (.app (.app (.const ``HAppend.hAppend _) t₁) t₂) t₃) inst) a) b =>
    if isString t₁ && isString t₂ && isString t₃ && isStringAppend inst then do
      let (0, x) ← groundText? a | none
      let (0, y) ← groundText? b | none
      some (0, x ++ y)
    else none
  | .app (.const ``String.toList _) s => do
    let (0, x) ← groundText? s | none
    some (1, x)
  | .app (.const ``String.ofList _) l => do
    let (1, x) ← groundText? l | none
    some (0, x)
  | .app (.app (.const ``List.toArray _) t) l | .app (.app (.const ``Array.mk _) t) l =>
    if t.isConstOf ``Char then do
      let (1, x) ← groundText? l | none
      some (2, x)
    else none
  | .app (.const ``List.nil _) t => if t.isConstOf ``Char then some (1, []) else none
  | .app (.app (.app (.const ``List.cons _) t) (.app (.const ``Char.ofNat _) (.lit (.natVal n)))) l =>
    if t.isConstOf ``Char then do
      let (1, x) ← groundText? l | none
      some (1, Char.ofNat n :: x)
    else none
  | _ => none
where
  isString (e : Expr) : Bool := e.isConstOf ``String
  isStringAppend (e : Expr) : Bool :=
    e.isAppOfArity ``instHAppendOfAppend 2 && isString (e.getArg! 0) &&
      (e.getArg! 1).isConstOf ``instAppendString

/-- Two closed text values that evaluate to different contents. -/
private def groundDistinct? (expected actual : Expr) : Option (List Char × List Char) := do
  let (k₁, x) ← groundText? expected
  let (k₂, y) ← groundText? actual
  if k₁ == k₂ && x != y then some (x, y) else none

private def codepoint (c : Char) : String :=
  let hex := String.ofList (Nat.toDigits 16 c.toNat |>.map Char.toUpper)
  "U+" ++ String.ofList (List.replicate (4 - hex.length) '0') ++ hex

private def textDiff (x y : List Char) : String :=
  let i := ((x.zip y).findIdx? fun (a, b) => a != b).getD (min x.length y.length)
  let pointAt := fun (cs : List Char) => (cs[i]?.map codepoint).getD "end of text"
  s!"\ntext differs at index {i}: expected {pointAt x}, received {pointAt y} (lengths {x.length} and {y.length})"

private def convertible (levelParams : List Name) (actual expected : Expr) : CoreM Bool := do
  if actual.hasMVar || expected.hasMVar then return false
  -- Kernel.check accepts free universe parameters. Restrict the projection to
  -- the declaration's own parameters, which also instantiate the candidate.
  if expected.hasLevelParam && !(collectLevelParams {} expected).params.all levelParams.contains then
    return false
  if expected == actual then return true
  -- Kernel conversion would unfold large literal tables character by
  -- character. Distinct closed text values are refuted structurally; this
  -- never accepts anything.
  if (groundDistinct? expected actual).isSome then return false
  let env ← getEnv
  unless (Lean.Kernel.check env {} expected).isOk do return false
  -- The candidate was checked in its snapshot. Kernel conversion unfolds either
  -- side, including structural recursors applied to neutral arguments.
  return Lean.Kernel.isDefEq env {} expected actual matches .ok true

/-- Private inductives are nominal too. If conversion needs their correspondence,
    enqueue their signatures and constructors as additional proof obligations. -/
private def compareExpr (a b : Snapshot) (hidden exports implHidden : NameSet) (levelParams : List Name) (description : String)
    (actual original : Expr) : MetaM (List Name) := do
  let expected ← projectExpr a b hidden exports original
  -- A private structural function can itself be applied to a huge numeral.
  -- Expose the same syntax on both sides before asking for conversion.
  let actual ← b.mapConstants actual implHidden.contains id (unfoldProofs := true)
  if ← convertible levelParams actual expected then return []
  let mut pairs : NameMap Name := {}
  for n in expected.getUsedConstantsAsSet do
    if hidden.contains n then
      let target := counterpart a b n
      if b.env.contains target then pairs := pairs.insert n target
  unless pairs.isEmpty do
    let translated ← Core.transform expected (post := fun e => pure <| .done <| match e with
      | .const n us => .const ((pairs.find? n).getD n) us
      | .proj n i val => .proj ((pairs.find? n).getD n) i val
      | _ => e)
    if ← convertible levelParams actual translated then return pairs.toList.map Prod.fst
  let hint := ((groundDistinct? expected actual).map fun (x, y) => textDiff x y).getD ""
  throwError "INTERFACE_MISMATCH: {description}{hint}\nexpected {expected}\nreceived {actual}"

private def compareInterface (spec impl : Snapshot) (mode : SatisfactionMode)
    (isSpecStruct : Name → Bool) : MetaM Unit := do
  let provided := NameSet.ofArray impl.constants
  let hidden := hiddenConstants spec
  let implHidden := hiddenConstants impl
  let mut todo := spec.constants.toList.filter (!hidden.contains ·)
  let exports := NameSet.ofList todo
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
    let compare := compareExpr spec impl hidden exports implHidden a.levelParams
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
          isSpecStruct n == isStructure impl.env target do
        throwError "INTERFACE_MISMATCH: inductive parameters, structure or constructors of {target}"
      todo := av.ctors ++ av.all ++ todo
    | .ctorInfo av, .ctorInfo _ => todo := av.induct :: todo
    | .recInfo av, .recInfo _ => todo := av.all ++ todo
    | _, _ => throwError "INTERFACE_MISMATCH: declaration kind of {target}"

/-- Move a constant owned by `oldMod` into the fresh scope `newMod`. Names of
    dependencies, including child modules below the old path, are unchanged. -/
private def relocateConstName (oldMod newMod : Name) (owned : NameSet) (n : Name) : Name :=
  if owned.contains n then
    let u := privateToUserName n
    let u' := if oldMod.isPrefixOf u then u.replacePrefix oldMod newMod else newMod ++ u
    if isPrivateName n then mkPrivateNameCore newMod u' else u'
  else n

private abbrev RelocCache := Std.HashMap Expr Expr

/-- Rename constants and projection structures. Literals stay untouched, so a
    derived `Repr` keeps the string labels of the authentic module. The cache
    keeps shared proof terms shared. -/
private def relocateExprM (rn : Name → Name) : Expr → StateM RelocCache Expr
  | e@(.bvar _) | e@(.fvar _) | e@(.mvar _) | e@(.sort _) | e@(.lit _) => pure e
  | .const n us => pure (.const (rn n) us)
  | e@(.app f a) => memo e do return .app (← relocateExprM rn f) (← relocateExprM rn a)
  | e@(.lam n t b bi) => memo e do
    return .lam n (← relocateExprM rn t) (← relocateExprM rn b) bi
  | e@(.forallE n t b bi) => memo e do
    return .forallE n (← relocateExprM rn t) (← relocateExprM rn b) bi
  | e@(.letE n t v b nd) => memo e do
    return .letE n (← relocateExprM rn t) (← relocateExprM rn v) (← relocateExprM rn b) nd
  | e@(.mdata d b) => memo e do return .mdata d (← relocateExprM rn b)
  | e@(.proj s i b) => memo e do return .proj (rn s) i (← relocateExprM rn b)
where
  memo (e : Expr) (k : StateM RelocCache Expr) : StateM RelocCache Expr := do
    if let some r := (← get)[e]? then return r
    let r ← k
    modify (·.insert e r)
    return r

private def relocateConstantInfo (rn : Name → Name) (c : ConstantInfo) : StateM RelocCache ConstantInfo := do
  let ex := relocateExprM rn
  let cv := fun (v : ConstantVal) => do
    return ({v with name := rn v.name, type := ← ex v.type} : ConstantVal)
  match c with
  | .axiomInfo v => return .axiomInfo {v with toConstantVal := ← cv v.toConstantVal}
  | .defnInfo v => return .defnInfo {v with
      toConstantVal := ← cv v.toConstantVal, value := ← ex v.value, all := v.all.map rn}
  | .thmInfo v => return .thmInfo {v with
      toConstantVal := ← cv v.toConstantVal, value := ← ex v.value, all := v.all.map rn}
  | .opaqueInfo v => return .opaqueInfo {v with
      toConstantVal := ← cv v.toConstantVal, value := ← ex v.value, all := v.all.map rn}
  | .quotInfo v => return .quotInfo {v with toConstantVal := ← cv v.toConstantVal}
  | .inductInfo v => return .inductInfo {v with
      toConstantVal := ← cv v.toConstantVal, all := v.all.map rn, ctors := v.ctors.map rn}
  | .ctorInfo v => return .ctorInfo {v with toConstantVal := ← cv v.toConstantVal, induct := rn v.induct}
  | .recInfo v =>
    let rules ← v.rules.mapM fun r => do return {r with ctor := rn r.ctor, rhs := ← ex r.rhs}
    return .recInfo {v with toConstantVal := ← cv v.toConstantVal, all := v.all.map rn, rules}

/-- Give an already checked interface a fresh nominal scope at the kernel
    level. No source is elaborated again: a second elaboration would let
    deriving handlers embed the temporary module name in string literals. -/
private def relocateSnapshot (a b : Snapshot) : IO (Snapshot × (Name → Bool)) := do
  let oldMod := a.env.mainModule
  let mut newName := Name.mkSimple s!"LojitaInterface{a.id}"
  while a.env.isNamespace newName || b.env.isNamespace newName ||
      a.env.contains newName || b.env.contains newName ||
      a.images.any (·.1 == newName) || b.images.any (·.1 == newName) do
    newName := newName.appendAfter "_"
  let some (_, origData) := a.images.find? (·.1 == oldMod)
    | throw (IO.userError s!"missing module image {oldMod}")
  let owned := NameSet.ofArray origData.constNames
  let rn := relocateConstName oldMod newName owned
  let newData : ModuleData := {
    isModule := origData.isModule, imports := origData.imports
    constNames := origData.constNames.map rn
    constants := (origData.constants.mapM (relocateConstantInfo rn)).run' {}
    extraConstNames := #[], entries := #[] }
  let images := (a.images.map fun (n, d) => if n == oldMod then (newName, newData) else (n, d)) ++ b.images
  let joint ← comparisonEnv images #[newName, b.env.mainModule]
  let rq := fun (q : QName) => QName.ofName (rn q.toLeanName)
  let mod := {a.mod with
    modName := QName.ofName newName
    units := a.mod.units.map fun u => {u with uname := rq u.uname, definedNames := u.definedNames.map rq}}
  let snap := {a with
    mod, env := joint.setMainModule newName, constants := a.constants.map rn, images := dedupImages images}
  -- Structure metadata lives in environment extensions, which the relocated
  -- image omits. Read it from the original constant instead.
  let origOf : NameMap Name := origData.constNames.foldl (fun m orig => m.insert (rn orig) orig) {}
  let isSpecStruct := fun n => match origOf.find? n with
    | some orig => isStructure a.env orig
    | none => isStructure a.env n
  return (snap, isSpecStruct)

def satisfies (spec impl : LeanMod) (deps : List LeanMod := [])
    (mode := SatisfactionMode.closedImplOK) (childStubs : List LeanMod := []) : IO Unit := driverLock.atomically do
  let origA ← checked deps childStubs spec true
  let b ← checked deps childStubs impl (mode == .subspec)
  if origA.id == b.id then return
  let verdict := (origA.id, b.id, mode == .subspec)
  if (← resident).satisfied.contains verdict then return
  let aName := origA.env.mainModule
  let bName := b.env.mainModule
  let (a, isSpecStruct, joint) ← if aName.isPrefixOf bName || bName.isPrefixOf aName then do
      let (a, isSpecStruct) ← relocateSnapshot origA b
      pure (a, isSpecStruct, a.env)
    else do
      -- Conversion may inspect the private matchers of either checked module.
      let joint ← comparisonEnv (origA.images ++ b.images) #[aName, bName]
      pure (origA, isStructure origA.env, joint)
  (compareInterface a b mode isSpecStruct).run' |>.toIO' (coreCtx joint) {env := joint}
  let r ← resident
  session.set (some {r with satisfied := r.satisfied.insert verdict})

def eqIface (a b : LeanMod) (deps : List LeanMod := []) : IO Unit := do
  satisfies a b deps .subspec
  satisfies b a deps .subspec

inductive ExeMode where
  | cli | reactive | posix
  deriving BEq, Repr

private def checkEntry (snap : Snapshot) (entry : Name) (mode : ExeMode) : MetaM Unit := do
  let info ← getConstInfo entry
  let caps ← Meta.mkFreshExprMVar (mkApp (mkConst ``List [.zero]) (mkConst `LojitaCtx.World.Cap))
  let wanted ← match mode with
    | .cli => pure <| mkApp (mkConst `LojitaCtx.World.CliApp) caps
    | .posix => pure <| mkApp2 (mkConst `LojitaCtx.Posix.PosixProg) (mkConst `LojitaCtx.Posix.CoreCaps) (mkConst ``UInt32)
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
    let wrapper := if mode == .posix then
      s!"def main (args : List String) : IO UInt32 := Lojita.Runtime.WorldRunner.processMain {entry} args"
      else s!"def main : IO UInt32 := Lojita.WorldRunner.{runner} {entry}"
    let cmd ← ioChecked (Parser.runParserCategory env `command wrapper)
    let (env, _) ← elabCommands env wrapper #[cmd]
    let mainC := dir / "main.c"
    emitSource env mainC
    let objects ← buildObjects (sources.push mainC)
    let stage := outBin.addExtension s!"{← IO.Process.getPID}.{← IO.monoNanosNow}.tmp"
    try
      let startup := if mode == .posix then #["-Wl,--wrap=main"] else #[]
      cc <| #["-O3", "-static"] ++ startup ++ objects ++ #[
        "-L", lib.toString, "-L", (toolchainRoot / "lib/lean").toString,
        "-L", (toolchainRoot / "lib").toString, "-Wl,--start-group",
        "-llojita_Lojita", "-llojita_LojitaCtx", "-llean_cli_host", "-lposix_host", "-lStd", "-lInit", "-lleanrt",
        "-lcadical", "-lc++", "-lc++abi", "-lunwind", "-lgmp", "-luv", "-lssl", "-lcrypto",
        "-lpthread", "-ldl", "-lrt", "-lm", "-lc", "-Wl,--end-group", "-Wl,--gc-sections",
        "-o", stage.toString]
      IO.FS.rename stage outBin
    finally
      if ← stage.pathExists then IO.FS.removeFile stage

end Lojita.Kernel
