import Lean
import Lean.Meta.Transform
import Lojita.Kernel.KernelGuard
import Lojita.Kernel.GroundEval
import Lojita.Kernel.SyntaxTriage

namespace Lojita.Kernel
open Lean

inductive DeclSort where
  | law | carrier
  deriving BEq, Repr, Inhabited

structure SemGraph where
  semArrows : List (Obj × Obj)
  sorts     : List (QName × DeclSort)
  deriving Inhabited

structure Snapshot where
  id              : Nat
  mod             : LeanMod
  env             : Environment
  graph           : SemGraph
  axioms          : NameSet
  declaredAxioms  : NameSet
  constants       : Array Name
  owners          : NameMap QName
  versions        : NameMap Nat
  contextModules  : NameSet
  images          : Array (Name × ModuleData)
  largeFuelDefs   : NameSet := {}
  deriving Nonempty

inductive SatisfactionMode where
  | closedImplOK | subspec
  deriving BEq, Repr

/-- Hidden constants of a snapshot: `private` declarations and compiler-generated internal details
    (`match_1`, `_mutual`, `_proof_1`, `_unsafe_rec`, etc.) not explicitly declared in `SynUnit`. -/
def hiddenConstants (s : Snapshot) : NameSet :=
  let explicit := NameSet.ofList (s.mod.units.flatMap (·.definedNames) |>.map QName.toLeanName)
  NameSet.ofArray <| s.constants.filter fun n =>
    isPrivateName n || (n.isInternalDetail && !explicit.contains n)

def counterpart (spec impl : Snapshot) (n : Name) : Name :=
  let name := (privateToUserName n).replacePrefix spec.env.mainModule impl.env.mainModule
  if isPrivateName n then mkPrivateNameCore impl.env.mainModule name else name

/-! ### DAG-Preserving Kernel-Level Snapshot Relocation -/

def dedupImages (all : Array (Name × ModuleData)) : Array (Name × ModuleData) := Id.run do
  let mut images := #[]
  let mut seen : NameSet := {}
  for (n, data) in all do
    unless seen.contains n do
      seen := seen.insert n
      images := images.push (n, data)
  return images

private def relocateConstName (oldMod newMod : Name) (owned : NameSet) (n : Name) : Name :=
  if owned.contains n then
    let u := privateToUserName n
    let u' := if oldMod.isPrefixOf u then u.replacePrefix oldMod newMod else newMod ++ u
    if isPrivateName n then mkPrivateNameCore newMod u' else u'
  else n

abbrev RelocCache := Std.HashMap Expr Expr

/-- Iterative/memoized DAG-preserving constant & projection renamer.
    String literals are untouched so derived `Repr` instances retain original module labels,
    and shared proof/term DAGs stay shared in $O(|DAG|)$ memory. -/
partial def relocateExprM (rn : Name → Name) : Expr → StateM RelocCache Expr
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

def relocateExprDAG (rn : Name → Name) (e : Expr) : Expr :=
  (relocateExprM rn e).run' {}

def relocateConstantInfo (rn : Name → Name) (c : ConstantInfo) : StateM RelocCache ConstantInfo := do
  let ex := relocateExprM rn
  let cv := fun (v : ConstantVal) => do
    return ({ v with name := rn v.name, type := ← ex v.type } : ConstantVal)
  match c with
  | .axiomInfo v => return .axiomInfo { v with toConstantVal := ← cv v.toConstantVal }
  | .defnInfo v => return .defnInfo {
      v with toConstantVal := ← cv v.toConstantVal, value := ← ex v.value, all := v.all.map rn
    }
  | .thmInfo v => return .thmInfo {
      v with toConstantVal := ← cv v.toConstantVal, value := ← ex v.value, all := v.all.map rn
    }
  | .opaqueInfo v => return .opaqueInfo {
      v with toConstantVal := ← cv v.toConstantVal, value := ← ex v.value, all := v.all.map rn
    }
  | .quotInfo v => return .quotInfo { v with toConstantVal := ← cv v.toConstantVal }
  | .inductInfo v => return .inductInfo {
      v with toConstantVal := ← cv v.toConstantVal, all := v.all.map rn, ctors := v.ctors.map rn
    }
  | .ctorInfo v => return .ctorInfo {
      v with toConstantVal := ← cv v.toConstantVal, induct := rn v.induct
    }
  | .recInfo v =>
    let rules ← v.rules.mapM fun r => do
      return { r with ctor := rn r.ctor, rhs := ← ex r.rhs }
    return .recInfo { v with toConstantVal := ← cv v.toConstantVal, all := v.all.map rn, rules }

def relocateSnapshotInEnv (mkComparisonEnv : Array (Name × ModuleData) → Array Name → IO Environment)
    (a b : Snapshot) : IO (Snapshot × (Name → Bool)) := do
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
    isModule        := origData.isModule
    imports         := origData.imports
    constNames      := origData.constNames.map rn
    constants       := (origData.constants.mapM (relocateConstantInfo rn)).run' {}
    extraConstNames := #[]
    entries         := #[]
  }
  let images := (a.images.map fun (n, d) => if n == oldMod then (newName, newData) else (n, d)) ++ b.images
  let joint ← mkComparisonEnv images #[newName, b.env.mainModule]
  let rq := fun (q : QName) => QName.ofName (rn q.toLeanName)
  let mod := {
    a.mod with
    modName := QName.ofName newName
    units   := a.mod.units.map fun u =>
      { u with uname := rq u.uname, definedNames := u.definedNames.map rq }
  }
  let largeFuelDefs := a.largeFuelDefs.foldl (fun s n => s.insert (rn n)) {}
  let snap := {
    a with
    mod
    env           := joint.setMainModule newName
    constants     := a.constants.map rn
    images        := dedupImages images
    largeFuelDefs
  }
  let origOf : NameMap Name := origData.constNames.foldl (fun m orig => m.insert (rn orig) orig) {}
  let isSpecStruct := fun n =>
    match origOf.find? n with
    | some orig => isStructure a.env orig
    | none      => isStructure a.env n
  return (snap, isSpecStruct)

/-! ### Linear-Time Pointer-Pair-Memoized `Expr` DAG α-Equality -/

private unsafe def dagExprEqImpl (rootA rootB : Expr) : Bool := Id.run do
  if ptrAddrUnsafe rootA == ptrAddrUnsafe rootB then return true
  if rootA.hash != rootB.hash then return false
  let mut seen : Std.HashSet (USize × USize) := {}
  let mut stack : Array (Expr × Expr) := #[(rootA, rootB)]
  while !stack.isEmpty do
    let (a, b) := stack.back!
    stack := stack.pop
    let pa := ptrAddrUnsafe a
    let pb := ptrAddrUnsafe b
    if pa == pb then continue
    if a.hash != b.hash then return false
    let key := (pa, pb)
    if seen.contains key then continue
    seen := seen.insert key
    match a, b with
    | .bvar i, .bvar j           => if i != j then return false
    | .fvar i, .fvar j           => if i != j then return false
    | .mvar i, .mvar j           => if i != j then return false
    | .sort u, .sort v           => if u != v then return false
    | .lit x, .lit y             => if x != y then return false
    | .const n1 u1, .const n2 u2 => if n1 != n2 || u1 != u2 then return false
    | .mdata d1 e1, .mdata d2 e2 =>
      if d1 != d2 then return false
      stack := stack.push (e1, e2)
    | .proj s1 i1 e1, .proj s2 i2 e2 =>
      if s1 != s2 || i1 != i2 then return false
      stack := stack.push (e1, e2)
    | .app f1 x1, .app f2 x2 =>
      stack := (stack.push (x1, x2)).push (f1, f2)
    | .lam _ t1 b1 i1, .lam _ t2 b2 i2 =>
      if i1 != i2 then return false
      stack := (stack.push (b1, b2)).push (t1, t2)
    | .forallE _ t1 b1 i1, .forallE _ t2 b2 i2 =>
      if i1 != i2 then return false
      stack := (stack.push (b1, b2)).push (t1, t2)
    | .letE _ t1 v1 b1 n1, .letE _ t2 v2 b2 n2 =>
      if n1 != n2 then return false
      stack := ((stack.push (b1, b2)).push (v1, v2)).push (t1, t2)
    | _, _ => return false
  return true

/-- $O(|DAG|)$ explicit-stack α-equality on `Expr` (avoids $O(2^k)$ tree blowup of `lean_expr_eqv`
    when comparing two isomorphic DAGs elaborated in separate snapshots). -/
@[implemented_by dagExprEqImpl]
def dagExprEq (a b : Expr) : Bool := a == b

/-! ### Stage 3: DAG-Preserving SafeCompare Engine (`GroundEval` + Pairing + `KernelGuard`) -/

private structure CompareState where
  kenv       : Kernel.Environment
  relocated  : NameMap Name := {}
  nextTag    : Nat := 1

private def compatiblePairingKinds (ca cb : ConstantInfo) : Bool :=
  ca.numLevelParams == cb.numLevelParams &&
  match ca, cb with
  | .defnInfo _,   .defnInfo _   => true
  | .thmInfo _,    .thmInfo _    => true
  | .thmInfo _,    .defnInfo _   => true
  | .defnInfo _,   .thmInfo _    => true
  | .inductInfo a, .inductInfo b => a.numParams == b.numParams && a.numIndices == b.numIndices && a.ctors.length == b.ctors.length
  | .ctorInfo _,   .ctorInfo _   => true
  | .recInfo _,    .recInfo _    => true
  | .opaqueInfo _, .opaqueInfo _ => true
  | _,             _             => false

/-- Replay an unpaired hidden constant `h` (and any transitive hidden constants it uses) from `spec`
    into `st.kenv` via `KernelGuard.addDeclGuarded`, mapping `exports` (and `paired`) to `impl`.
    - `.thmInfo` stays a `.thmDecl` ($O(1)$ proof irrelevance in C++ kernel — zero proof unfolding!);
    - `.defnInfo` stays a `.defnDecl` with proper height hints (C++ `lazy_delta_reduction` + `equiv_manager`
      pair-cache — zero Lean-level lambda tree blowup!). -/
private partial def ensureHiddenRelocated (spec impl : Snapshot) (specHidden exports : NameSet)
    (paired : NameMap Name) (cfg : KernelLimitsConfig) (h : Name) (st : CompareState) :
    Except Kernel.Exception (Name × CompareState) := do
  if let some target := paired.find? h then
    return (target, st)
  if let some existing := st.relocated.find? h then
    return (existing, st)
  let specKEnv := spec.env.checked.get
  let some ci := specKEnv.find? h
    | throw (.other s!"missing spec hidden constant {h}")
  -- Constructors and recursors are synthesized when their parent inductive block is replayed.
  match ci with
  | .ctorInfo cv =>
    let (_, st) ← ensureHiddenRelocated spec impl specHidden exports paired cfg cv.induct st
    let some existing := st.relocated.find? h
      | throw (.other s!"missing relocated constructor {h}")
    return (existing, st)
  | .recInfo rv =>
    let mut cur := st
    for ind in rv.all do
      let (_, nextSt) ← ensureHiddenRelocated spec impl specHidden exports paired cfg ind cur
      cur := nextSt
    let some existing := cur.relocated.find? h
      | throw (.other s!"missing relocated recursor {h}")
    return (existing, cur)
  | .inductInfo iv =>
    let mut cur := st
    let mut groupMap : NameMap Name := {}
    let tag := cur.nextTag
    cur := { cur with nextTag := tag + 1 }
    let mkFresh (orig : Name) : Name :=
      Name.mkSimple s!"_lojita_reloc_{tag}" ++ privateToUserName orig
    for indName in iv.all do
      let some (.inductInfo indVal) := specKEnv.find? indName
        | throw (.other s!"missing mutual inductive {indName}")
      let newInd := mkFresh indName
      groupMap := groupMap.insert indName newInd
      groupMap := groupMap.insert (indName.appendCore `rec) (newInd.appendCore `rec)
      for ctorName in indVal.ctors do
        let shortCtor := ctorName.replacePrefix indName .anonymous
        groupMap := groupMap.insert ctorName (newInd ++ shortCtor)
    -- Ensure all external hidden dependencies of types & constructors are relocated first
    for indName in iv.all do
      let some (.inductInfo indVal) := specKEnv.find? indName
        | throw (.other s!"missing mutual inductive {indName}")
      for dep in indVal.type.getUsedConstantsAsSet do
        if specHidden.contains dep && !groupMap.contains dep then
          let (_, nextSt) ← ensureHiddenRelocated spec impl specHidden exports paired cfg dep cur
          cur := nextSt
      for ctorName in indVal.ctors do
        let some (.ctorInfo ctorVal) := specKEnv.find? ctorName
          | throw (.other s!"missing constructor {ctorName}")
        for dep in ctorVal.type.getUsedConstantsAsSet do
          if specHidden.contains dep && !groupMap.contains dep then
            let (_, nextSt) ← ensureHiddenRelocated spec impl specHidden exports paired cfg dep cur
            cur := nextSt
    let rn (c : Name) : Name :=
      if let some m := groupMap.find? c then m
      else if let some p := paired.find? c then p
      else if let some r := cur.relocated.find? c then r
      else if exports.contains c then counterpart spec impl c
      else c
    let mut types : List InductiveType := []
    for indName in iv.all do
      let some (.inductInfo indVal) := specKEnv.find? indName
        | throw (.other s!"missing mutual inductive {indName}")
      let mut ctors : List Constructor := []
      for ctorName in indVal.ctors do
        let some (.ctorInfo ctorVal) := specKEnv.find? ctorName
          | throw (.other s!"missing constructor {ctorName}")
        ctors := ctors ++ [{
          name := rn ctorName
          type := relocateExprDAG rn ctorVal.type
        }]
      types := types ++ [{
        name  := rn indName
        type  := relocateExprDAG rn indVal.type
        ctors
      }]
    let decl : Declaration := .inductDecl iv.levelParams iv.numParams types false
    let kenv' ← addDeclGuarded cur.kenv decl cfg
    let mut reloc' := cur.relocated
    for (oldN, newN) in groupMap do
      reloc' := reloc'.insert oldN newN
    let cur' := { cur with kenv := kenv', relocated := reloc' }
    let some resName := cur'.relocated.find? h
      | throw (.other s!"missing relocated inductive {h}")
    return (resName, cur')
  | _ =>
    -- `.defnInfo`, `.thmInfo`, `.axiomInfo`, `.opaqueInfo`
    -- Ignore compiler-only `_unsafe_rec` / `_impl` companions (never referenced by semantic kernel terms)
    let mut cur := st
    for dep in ci.getUsedConstantsAsSet do
      if specHidden.contains dep && dep != h then
        let (_, nextSt) ← ensureHiddenRelocated spec impl specHidden exports paired cfg dep cur
        cur := nextSt
    let tag := cur.nextTag
    let freshName := Name.mkSimple s!"_lojita_reloc_{tag}" ++ privateToUserName h
    cur := { cur with nextTag := tag + 1 }
    let rn (c : Name) : Name :=
      if c == h then freshName
      else if let some p := paired.find? c then p
      else if let some r := cur.relocated.find? c then r
      else if exports.contains c then counterpart spec impl c
      else c
    let decl : Declaration ← match ci with
      | .defnInfo dv =>
        let newType := relocateExprDAG rn dv.type
        let newVal  := relocateExprDAG rn dv.value
        let hints : ReducibilityHints :=
          match dv.hints with
          | .abbrev    => .abbrev
          | .opaque    => .opaque
          | .regular _ => .regular (getMaxHeight (Environment.ofKernelEnv cur.kenv) newVal + 1)
        pure <| .defnDecl {
          name        := freshName
          levelParams := dv.levelParams
          type        := newType
          value       := newVal
          hints       := hints
          safety      := .safe
          all         := [freshName]
        }
      | .thmInfo tv =>
        pure <| .thmDecl {
          name        := freshName
          levelParams := tv.levelParams
          type        := relocateExprDAG rn tv.type
          value       := relocateExprDAG rn tv.value
          all         := [freshName]
        }
      | .opaqueInfo ov =>
        pure <| .opaqueDecl {
          name        := freshName
          levelParams := ov.levelParams
          type        := relocateExprDAG rn ov.type
          value       := relocateExprDAG rn ov.value
          isUnsafe    := false
          all         := [freshName]
        }
      | .axiomInfo av =>
        pure <| .axiomDecl {
          name        := freshName
          levelParams := av.levelParams
          type        := relocateExprDAG rn av.type
          isUnsafe    := false
        }
      | _ => throw (.other s!"unexpected constant kind for {h}")
    let kenv' ← addDeclGuarded cur.kenv decl cfg
    let cur' := { cur with kenv := kenv', relocated := cur.relocated.insert h freshName }
    return (freshName, cur')

/-- Project an expression `origExpr` from `spec` into `st.kenv`, mapping `exports` to `impl`,
    `paired` hidden constants to `impl`'s counterparts, and relocating any remaining `specHidden`
    constants into `st.kenv` via `ensureHiddenRelocated`. -/
private def projectSpecExprWithUsed (spec impl : Snapshot) (specHidden exports : NameSet)
    (used : NameSet) (paired : NameMap Name) (cfg : KernelLimitsConfig)
    (origExpr : Expr) (st : CompareState) :
    Except Kernel.Exception (Expr × CompareState) := do
  let mut cur := st
  let mut anyRenamed := false
  for c in used do
    if specHidden.contains c && !paired.contains c && !cur.relocated.contains c then
      let (_, nextSt) ← ensureHiddenRelocated spec impl specHidden exports paired cfg c cur
      cur := nextSt
    let mapped :=
      if let some p := paired.find? c then p
      else if let some r := cur.relocated.find? c then r
      else if exports.contains c then counterpart spec impl c
      else c
    if mapped != c then
      anyRenamed := true
  if !anyRenamed then
    return (origExpr, cur)
  let rn (c : Name) : Name :=
    if let some p := paired.find? c then p
    else if let some r := cur.relocated.find? c then r
    else if exports.contains c then counterpart spec impl c
    else c
  return (relocateExprDAG rn origExpr, cur)

private inductive CheckVerdict where
  | equal
  | groundRefuted (diff : String)
  | tabooFault (te : TabooError)
  | notEqual

/-- Guarded type-level equivalence check (`actualType ≡ expectedType`). -/
private def guardedTypesCheck (joint : Environment) (kenv : Kernel.Environment)
    (levelParams : List Name) (actualType expectedType : Expr) (desc : String)
    (cfg : KernelLimitsConfig) : CheckVerdict :=
  if actualType.hasMVar || expectedType.hasMVar then .notEqual
  else if expectedType.hasLevelParam && !(collectLevelParams {} expectedType).params.all levelParams.contains then
    .notEqual
  else if dagExprEq expectedType actualType then
    .equal
  else
    match compareGroundFast joint expectedType actualType with
    | .refuted diff => .groundRefuted diff
    | _ =>
      match checkTypesDefEq kenv levelParams actualType expectedType cfg with
      | .ok () => .equal
      | .error ex =>
        match classifyKernelException ex desc with
        | some te => .tabooFault te
        | none    => .notEqual

/-- Guarded value-level equivalence check (`expectedVal ≡ actualVal : ty`) preceded by `GroundEval` fast refutation. -/
private def guardedValuesCheck (joint : Environment) (kenv : Kernel.Environment)
    (levelParams : List Name) (u : Level) (ty actualVal expectedVal : Expr) (desc : String)
    (cfg : KernelLimitsConfig) : CheckVerdict :=
  if actualVal.hasMVar || expectedVal.hasMVar || ty.hasMVar || u.hasMVar then .notEqual
  else if expectedVal.hasLevelParam && !(collectLevelParams {} expectedVal).params.all levelParams.contains then
    .notEqual
  else if dagExprEq expectedVal actualVal then
    .equal
  else
    match compareGroundFast joint expectedVal actualVal with
    | .refuted diff => .groundRefuted diff
    | .sameGround sz =>
      let tunedCfg :=
        if sz > 512 then
          { cfg with maxHeartbeats := min cfg.maxHeartbeats 2000, maxRecDepth := min cfg.maxRecDepth 128 }
        else cfg
      match checkValuesDefEq kenv levelParams u ty expectedVal actualVal tunedCfg with
      | .ok () => .equal
      | .error .deterministicTimeout | .error .deepRecursion =>
        if sz > 512 then
          .tabooFault {
            code   := .largeGroundMismatchSyntax
            detail := s!"{desc}: equal ground container of size {sz} timed out in kernel due to differing syntax"
          }
        else
          .tabooFault { code := .kernelTimeout, detail := s!"{desc}: kernel exceeded deterministic reduction limit" }
      | .error ex =>
        match classifyKernelException ex desc with
        | some te => .tabooFault te
        | none    => .notEqual
    | .unknown =>
      match checkValuesDefEq kenv levelParams u ty expectedVal actualVal cfg with
      | .ok () => .equal
      | .error ex =>
        match classifyKernelException ex desc with
        | some te => .tabooFault te
        | none    => .notEqual

/-- Collect direct counterpart candidates `(h, implTarget)` for hidden constants referenced by `e`. -/
private def findCounterpartPairsFromUsed (spec impl : Snapshot) (specHidden used : NameSet) : NameMap Name := Id.run do
  let specK := spec.env.checked.get
  let implK := impl.env.checked.get
  let mut pairs : NameMap Name := {}
  for h in used do
    if specHidden.contains h then
      let target := counterpart spec impl h
      if let (some ca, some cb) := (specK.find? h, implK.find? target) then
        if compatiblePairingKinds ca cb then
          pairs := pairs.insert h target
  return pairs

/-- Stage 3 core comparison loop:
    1. Never unfolds `.thmInfo` (`unfoldProofs = false` strictly) or `impl` private definitions;
    2. Tries counterpart pairing `(specPriv ↦ implPriv)` first (verifying paired obligations on a state snapshot),
       achieving $O(1)$ neutral-fuel comparison on `LargeFuel` and shared recursive helpers;
    3. Falls back to DAG-preserving kernel relocation (`ensureHiddenRelocated` via `addDeclGuarded`)
       when an auto-generated `match_1` differs structurally between `spec` and `impl`;
    4. Routes all kernel checks exclusively through `GroundEval` + `KernelGuard` (`addDeclCore`). -/
partial def compareInterfaceSafe (spec impl : Snapshot) (mode : SatisfactionMode)
    (isSpecStruct : Name → Bool) (cfg : KernelLimitsConfig := { maxHeartbeats := 100000, maxRecDepth := 2048 }) :
    MetaM Unit := do
  let joint ← getEnv
  let provided := NameSet.ofArray impl.constants
  let specHidden := hiddenConstants spec
  -- Exclude compiler-only `_unsafe_rec` and `_impl` companions from semantic obligations,
  -- and order top-level obligations in top-down `SynUnit` declaration order so carrier types
  -- and ground lookup tables are checked before large downstream consumers.
  let isCompilerCompanion (n : Name) : Bool :=
    (Compiler.isUnsafeRecName? n).isSome ||
    (match n with | .str _ "_impl" => true | _ => false)
  let specConstSet := NameSet.ofArray spec.constants
  let declaredOrder := (spec.mod.units.flatMap (·.definedNames) |>.map QName.toLeanName).filter fun n =>
    specConstSet.contains n && !specHidden.contains n && !isCompilerCompanion n
  let declaredSet := NameSet.ofList declaredOrder
  let extraExports := spec.constants.toList.filter fun n =>
    !declaredSet.contains n && !specHidden.contains n && !isCompilerCompanion n
  let orderedAll := declaredOrder ++ extraExports
  -- Check carrier types and 0-arity ground constants/tables first before large recursive functions!
  let specK := spec.env.checked.get
  let (carriersAndTables, funcsAndLaws) := orderedAll.partition fun n =>
    match specK.find? n with
    | some (.inductInfo _) => true
    | some (.defnInfo dv)  => !dv.type.isForall
    | _                    => false
  let initialTodo := carriersAndTables ++ funcsAndLaws
  let exports := NameSet.ofList orderedAll

  let rec checkObligations (todo : List Name) (visited : NameSet) (st : CompareState) :
      MetaM (NameSet × CompareState) := do
    match todo with
    | [] => return (visited, st)
    | n :: rest =>
      if visited.contains n || isCompilerCompanion n then
        checkObligations rest visited st
      else
        let visited := visited.insert n
        let some a := spec.env.checked.get.find? n
          | throwError "KERNEL_CONSTANT_MISSING: {n}"
        let target := counterpart spec impl n
        let some b := impl.env.checked.get.find? target
          | throwError "INTERFACE_MISSING: {target}"
        unless provided.contains target || specHidden.contains n do
          throwError "INTERFACE_MISSING: {target}"
        unless a.numLevelParams == b.numLevelParams do
          throwError "INTERFACE_MISMATCH: {target} universe arity {a.numLevelParams} != {b.numLevelParams}"
        let levels := a.levelParams.map Level.param
        let inst (e : Expr) : Expr := e.instantiateLevelParams b.levelParams levels

        -- Helper comparing one `(actual, origExpected)` pair (either type or value) with
        -- Counterpart Pairing First + Pure Relocation Fallback!
        let compareOne (isValue : Bool) (actualTy? : Option Expr) (desc : String)
            (actual origExpected : Expr) (curVisited : NameSet) (curSt : CompareState) :
            MetaM (NameSet × CompareState) := do
          let used := origExpected.getUsedConstantsAsSet
          let getValSort : MetaM (Option (Level × Expr)) := do
            if !isValue then return none
            let some ty := actualTy? | return none
            let u ← Core.withCurrHeartbeats do
              instantiateLevelMVars (← Meta.getLevel ty)
            return some (u, ty)

          let runAttempt (pairs : NameMap Name) (baseSt : CompareState) :
              MetaM (Except Kernel.Exception (CheckVerdict × Expr × CompareState)) := do
            match projectSpecExprWithUsed spec impl specHidden exports used pairs cfg origExpected baseSt with
            | .error kex => return .error kex
            | .ok (projected, st') =>
              if isValue && dagExprEq projected actual && !projected.hasMVar &&
                 (!projected.hasLevelParam || (collectLevelParams {} projected).params.all a.levelParams.contains) then
                return .ok (.equal, projected, st')
              let vSort? ← getValSort
              let verdict := match isValue, vSort? with
                | false, _ =>
                  guardedTypesCheck joint st'.kenv a.levelParams actual projected desc cfg
                | true, some (u, ty) =>
                  guardedValuesCheck joint st'.kenv a.levelParams u ty actual projected desc cfg
                | true, none => .notEqual
              return .ok (verdict, projected, st')

          let pairs := findCounterpartPairsFromUsed spec impl specHidden used
          if !pairs.isEmpty then
            -- Attempt 1: pair matching private/hidden helpers and verify their obligations recursively!
            match ← runAttempt pairs curSt with
            | .ok (.equal, _, stAfterProj) =>
              let pairedObligs := pairs.toList.map Prod.fst |>.filter (!curVisited.contains ·)
              if pairedObligs.isEmpty then
                return (curVisited, stAfterProj)
              else
                let savedMeta ← saveState
                let subRes? ← try
                    let okPair ← checkObligations pairedObligs curVisited stAfterProj
                    pure (some okPair)
                  catch _ =>
                    savedMeta.restore
                    pure none
                if let some okPair := subRes? then
                  return okPair
            | .ok (.groundRefuted diff, _, _) =>
              throwError "INTERFACE_MISMATCH: {desc}{diff}"
            | _ => pure ()

          -- Attempt 2 (or sole attempt when `pairs.isEmpty`): pure DAG-preserving kernel relocation
          match ← runAttempt {} curSt with
          | .ok (.equal, _, st') =>
            return (curVisited, st')
          | .ok (.groundRefuted diff, _, _) =>
            throwError "INTERFACE_MISMATCH: {desc}{diff}"
          | .ok (.tabooFault te, _, _) =>
            throwError "INTERFACE_MISMATCH: {desc} ({te.code.tag}: {te.detail})\n{te.code.detour}"
          | .ok (.notEqual, projected, _) =>
            match compareGroundFast joint projected actual with
            | .refuted d =>
              throwError "INTERFACE_MISMATCH: {desc}{d}"
            | _ =>
              throwError "INTERFACE_MISMATCH: {desc}\nexpected {projected}\nreceived {actual}"
          | .error kex =>
            match classifyKernelException kex desc with
            | some te =>
              throwError "INTERFACE_MISMATCH: {desc} ({te.code.tag}: {te.detail})\n{te.code.detour}"
            | none =>
              throwError "INTERFACE_MISMATCH: {desc}\nexpected {origExpected}\nreceived {actual}"

        let actualTy := inst b.type
        let (visited, st) ← compareOne false none s!"type of {target}" actualTy a.type visited st

        match a, b with
        | .axiomInfo _, .axiomInfo _ =>
          unless mode == .subspec do
            throwError "DISALLOWED_AXIOM_VIOLATION: {target}"
          checkObligations rest visited st
        | .axiomInfo _, .defnInfo _ | .axiomInfo _, .thmInfo _ | .axiomInfo _, .ctorInfo _ =>
          checkObligations rest visited st
        | .thmInfo _, .thmInfo _ | .thmInfo _, .defnInfo _ =>
          checkObligations rest visited st
        | .defnInfo _, .thmInfo _ =>
          -- Type check already established `b.type` is `Prop`; proof irrelevance holds.
          checkObligations rest visited st
        | .defnInfo av, .defnInfo bv =>
          let actualVal := inst bv.value
          if !dagExprEq actualVal av.value && (← Core.withCurrHeartbeats (Meta.isProp actualTy)) then
            checkObligations rest visited st
          else
            let (visited, st) ← compareOne true (some actualTy) s!"body of {target}"
              actualVal av.value visited st
            checkObligations rest visited st
        | .inductInfo av, .inductInfo bv =>
          let structCheck :=
            if specHidden.contains n then true
            else isSpecStruct n == isStructure impl.env target
          unless av.numParams == bv.numParams && av.numIndices == bv.numIndices &&
              av.ctors.map (counterpart spec impl) == bv.ctors &&
              av.all.map (counterpart spec impl) == bv.all &&
              structCheck do
            throwError "INTERFACE_MISMATCH: inductive parameters, structure or constructors of {target}"
          checkObligations (av.ctors ++ av.all ++ rest) visited st
        | .ctorInfo av, .ctorInfo _ =>
          checkObligations (av.induct :: rest) visited st
        | .recInfo av, .recInfo _ =>
          checkObligations (av.all ++ rest) visited st
        | .opaqueInfo _, .opaqueInfo _ =>
          if n != target then
            throwError "INTERFACE_MISMATCH: opaque declaration {target}"
          checkObligations rest visited st
        | _, _ =>
          throwError "INTERFACE_MISMATCH: declaration kind of {target}"

  discard <| checkObligations initialTodo {} { kenv := joint.toKernelEnv }

end Lojita.Kernel
