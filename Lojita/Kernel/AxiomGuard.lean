import Lean
import Lean.Compiler.CSimpAttr
import Lean.Compiler.Old

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
  let (native, semantic) := roots.toList.partition (nativeRecursor env)
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
    if (info.isPartial || info.isUnsafe) && !(nativePhase && nativeRecursor env n) then
      throw s!"UNSAFE_VIOLATION: {n}"
    if [`IO, `EIO, `BaseIO].contains n.getRoot then throw s!"EFFECT_VIOLATION: {n}"
    -- Init's pure primitives, including Nat.add and String operations, have
    -- runtime implementations. Object modules cannot contribute replacements.
    let isPrelude := (moduleOf? env n).any fun m => m.getRoot == `Init
    if !isPrelude && (isExtern env n || (Compiler.getImplementedBy? env n).isSome ||
        Compiler.hasCSimpAttribute env n || (Compiler.CSimp.ext.getState env).map.contains n) then
      throw s!"NATIVE_OVERRIDE_VIOLATION: {n}"
    if info matches .axiomInfo _ then axioms := axioms.insert n
    let deps := info.getUsedConstantsAsSet
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
