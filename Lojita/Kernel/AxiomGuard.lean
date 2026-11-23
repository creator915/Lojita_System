import Lean
import Lean.Compiler.CSimpAttr
import Lean.Compiler.Old
import Lean.Meta.Constructions.CtorIdx

namespace Lojita.Kernel
open Lean

def trustedBaseAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

/-- Lean emits a separate native recursion body for a kernel-checked total
    recursive definition. The object grammar cannot declare these companions. -/
private def nativeRecursor (env : Environment) (n : Name) : Bool := Id.run do
  let some parent := Compiler.isUnsafeRecName? n | return false
  let some (.defnInfo d) := env.checked.get.find? parent | return false
  return d.safety == .safe

/-- Lean implements a constructor index by reading the tag of its last
    argument. Recognize that exact native companion of the safe kernel index. -/
private def nativeCtorIdx (env : Environment) (n : Name) : Bool := Id.run do
  let .str index "_impl" := n | return false
  let some ind := isCtorIdxCore? env index | return false
  unless ind.numCtors != 1 && !Compiler.LCNF.isRuntimeBuiltinType ind.name &&
      Compiler.getImplementedBy? env index == some n do return false
  let some (.defnInfo d) := env.checked.get.find? index | return false
  let some (.defnInfo impl) := env.checked.get.find? n | return false
  let .app (.app (.const ``getObjTagNat _) ty) (.bvar 0) := impl.value.getLambdaBody | return false
  unless d.safety == .safe && impl.safety == .unsafe && impl.type == d.type &&
      ty.getAppFn.isConstOf ind.name do return false
  let cases := d.value.getLambdaBody
  let discr := ind.numParams + 1 + ind.numIndices
  let args := cases.getAppArgs
  unless cases.getAppFn.isConstOf (mkCasesOnName ind.name) && args.size == discr + 1 + ind.numCtors &&
      args[discr]? == some (.bvar 0) do return false
  return (args.extract (discr + 1) args.size).zipIdx.all fun (alt, i) => alt.getLambdaBody == mkRawNatLit i

/-- Only declarations from the immutable resident prelude enter this cache.
    Generated native companions have a different audit policy and never seed it. -/
structure PreludeAudit where
  private mk ::
  private footprints : NameMap NameSet
  deriving Inhabited

def auditRoots (env : Environment) (roots : Array Name) (base : Option Environment)
    (cache : PreludeAudit) : Except String (NameSet × PreludeAudit) := do
  let kernel := env.checked.get
  -- Semantic roots must never refer to an unsafe implementation. Inspect the
  -- generated native bodies separately, including all their outgoing edges.
  let (native, semantic) := roots.toList.partition fun n => nativeRecursor env n || nativeCtorIdx env n
  let mut todo := semantic
  let mut nativePhase := false
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  let mut fresh : NameMap NameSet := {}
  let mut parents : NameMap (List Name) := {}
  let mut seeds : List (Name × Name) := []
  repeat
    if todo.isEmpty && !nativePhase then
      todo := native
      nativePhase := true
    let n :: rest := todo | break
    todo := rest
    if visited.contains n then continue
    visited := visited.insert n
    if let some known := cache.footprints.find? n then
      axioms := axioms ++ known
      for ax in known do seeds := (n,ax) :: seeds
      continue
    let some info := kernel.find? n | throw s!"KERNEL_CONSTANT_MISSING: {n}"
    if n == ``sorryAx then throw s!"SORRY_AXIOM_VIOLATION: {n}"
    let tagImpl := nativePhase && nativeCtorIdx env n
    if (info.isPartial || info.isUnsafe) && !(tagImpl || (nativePhase && nativeRecursor env n)) then
      throw s!"UNSAFE_VIOLATION: {n}"
    if [`IO, `EIO, `BaseIO].contains n.getRoot then throw s!"EFFECT_VIOLATION: {n}"
    -- Init's pure primitives, including Nat.add and String operations, have
    -- runtime implementations. Object modules cannot contribute replacements.
    let isPrelude := (moduleOf? env n).any fun m => m.getRoot == `Init
    let override := (Compiler.getImplementedBy? env n).any fun impl =>
      !(impl == n.str "_impl" && nativeCtorIdx env impl)
    if !isPrelude && (isExtern env n || override ||
        Compiler.hasCSimpAttribute env n || (Compiler.CSimp.ext.getState env).map.contains n) then
      throw s!"NATIVE_OVERRIDE_VIOLATION: {n}"
    if info matches .axiomInfo _ then axioms := axioms.insert n
    -- Only this verified call site may use the compiler's unsafe tag primitive.
    let deps := info.getUsedConstantsAsSet
    let deps := if tagImpl then deps.erase ``getObjTagNat else deps
    if !nativePhase && base.any (·.contains n) then
      fresh := fresh.insert n {}
      if info matches .axiomInfo _ then seeds := (n,n) :: seeds
      for dep in deps do parents := parents.insert dep (n :: (parents.find? dep).getD [])
    todo := deps.foldl (fun pending dep => dep :: pending) todo
  -- Back-propagate axiom reachability after the whole forest passes. A cycle
  -- between an inductive and its constructors gets the same complete footprint.
  while let (n,ax) :: rest := seeds do
    seeds := rest
    if let some footprint := fresh.find? n then
      if footprint.contains ax then continue
      fresh := fresh.insert n (footprint.insert ax)
    for parent in (parents.find? n).getD [] do seeds := (parent,ax) :: seeds
  return (axioms, ⟨cache.footprints.union fresh⟩)

def collectRootAxioms (env : Environment) (roots : Array Name) : Except String NameSet :=
  Prod.fst <$> auditRoots env roots none default

def auditAxioms (axioms allowedStagedAxioms : NameSet) : Except String Unit := do
  for ax in axioms do
    unless trustedBaseAxioms.contains ax || allowedStagedAxioms.contains ax do
      throw s!"DISALLOWED_AXIOM_VIOLATION: {ax}"

end Lojita.Kernel
