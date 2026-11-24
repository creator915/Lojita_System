import Lojita.Harness.Tree
import Lojita.Transport.Lift
import Lojita.Transport.Namespace

namespace Lojita.Harness
open Lojita.Kernel Lojita.Transport

abbrev Bindings := List (Frozen × TransportSpec)

def lookupChild (f : Frozen) (q : QName) := f.children.lookup (toString q)

private def slotAlias (slot : QName) (f : Frozen) : LeanMod := Id.run do
  let src := f.code.modName
  let names := publicNames f.code
  let units := names.map fun q =>
    let localName := q.toLeanName.replacePrefix src.toLeanName .anonymous
    let target := QName.ofName (slot.toLeanName ++ localName)
    let raw := s!"abbrev {localName} := @{q}"
    {uname := target, definedNames := [target], kind := .abbrevDecl, rawSource := raw,
      sigSlice := s!"abbrev {localName}", synRefs := [q] : SynUnit}
  let children := Std.HashSet.ofList (f.children.map fun (n, _) => renameQ src slot (qualified n))
  let header := requalify src slot {f.code with opens := [], units := []}
  return ⟨slot, ⟨src, []⟩ :: header.imports.filter (children.contains ·.imod), [], units⟩

mutual
  /-- Each relocated directory exposes its original declarations and the assigned
      interfaces of its relocated children. The saved homes retain their identity. -/
  def slotAliases (slot : QName) (f : Frozen) : List LeanMod :=
    match f with
    | .frozen code _ _ kids =>
      if slot == code.modName then [] else slotAlias slot f :: childAliases code.modName slot kids
  termination_by structural f

  private def childAliases (src slot : QName) (kids : List (String × Frozen)) : List LeanMod :=
    match kids with
    | [] => []
    | (n,h) :: rest => slotAliases (renameQ src slot (qualified n)) h ++ childAliases src slot rest
  termination_by structural kids
end

mutual
  private def exportNode (f : Frozen) (acc : Array LeanMod) : Array LeanMod :=
    match f with | .frozen c _ _ cs => exportKids cs (acc.push c)
  termination_by structural f

  private def exportKids (ks : List (String × Frozen)) (acc : Array LeanMod) : Array LeanMod :=
    match ks with
    | [] => acc
    | (n,f) :: xs => exportKids xs (exportNode f ((slotAliases (qualified n) f).foldl Array.push acc))
  termination_by structural ks
end

def keeps (bs : Bindings) : List (QName × Frozen) :=
  bs.flatMap fun (h,s) =>
    let kids := Std.HashMap.ofList h.children
    (directKeeps s).filterMap fun (o,n) => (n,·) <$> kids[toString o]?

def nestedBindings (bs : Bindings) : Std.HashMap QName Bindings := Id.run do
  let mut out : Std.HashMap QName (Array (Frozen × TransportSpec)) := {}
  for (h,t) in bs do
    let kids := Std.HashMap.ofList h.children
    for move in t.childMoves do
      if let .moveChildren _ _ subs := move then
        for sub in subs do
          let some child := kids[toString sub.oldMod]? | continue
          let rename := renameQ sub.oldMod child.code.modName
          let squares := sub.squares.map fun s =>
            {s with oldUnits := s.oldUnits.map rename, requiredRefs := s.requiredRefs.map rename}
          let routed := TransportSpec.transportSpecTree child.code.modName sub.newMod sub.childMoves squares
          out := out.alter sub.newMod (fun prev => some ((prev.getD #[]).push (child,routed)))
  return out.map fun _ xs => xs.toList

def subBindings (bs : Bindings) (target : QName) : Bindings := (nestedBindings bs)[target]?.getD []

def childSources (bs : Bindings) (q : QName) :=
  bs.flatMap fun (_,s) => s.childMoves.flatMap fun c => if c.targets.contains q then c.sources else []

/-- Merge identical shared dependencies. A single namespace cannot denote
    two different module versions in one link. -/
def mergeModules (mods : List LeanMod) : Except String (List LeanMod) := do
  let mut seen : Std.HashMap QName LeanMod := {}
  let mut out := #[]
  for m in mods do
    if let some prev := seen[m.modName]? then
      unless prev == m do throw s!"DUPLICATE_MODULE: conflicting versions of {m.modName}"
    else
      seen := seen.insert m.modName m
      out := out.push m
  return out.toList

def sameModules (a b : List LeanMod) : Bool :=
  if a == b then true
  else
    let idxA := Std.HashMap.ofList (a.map fun m => (m.modName, m))
    let idxB := Std.HashMap.ofList (b.map fun m => (m.modName, m))
    idxA.size == idxB.size &&
      a.all (fun m => idxB[m.modName]? == some m) &&
      b.all (fun m => idxA[m.modName]? == some m)

def exported (f : Frozen) : List LeanMod :=
  let mods := (exportNode f #[]).toList
  -- Preserve conflicts for the linker's diagnostic, coalesce shared originals.
  (mergeModules mods).toOption.getD mods

def depsExcept (mods : List LeanMod) (m : LeanMod) := mods.filter (·.modName != m.modName)

def specAt (q : QName) (h : Frozen) := requalify h.spec.modName q h.spec

private def dependenciesOf (index : Std.HashMap QName LeanMod) (roots : List LeanMod) : List LeanMod := Id.run do
  let mut seen := Std.HashSet.ofList (roots.map (·.modName))
  let mut todo := roots.flatMap (·.imports)
  let mut deps := #[]
  while let i :: rest := todo do
    todo := rest
    if seen.contains i.imod then continue
    seen := seen.insert i.imod
    if let some m := index[i.imod]? then
      deps := deps.push m
      todo := m.imports ++ todo
  return deps.toList

/-- Rewrite the whole owned closure, including references between modules whose
    slots do not share the root prefix (such as Gen.T0.Root and Gen.T0.Doc). -/
def snapshotModules (h : Frozen) (historical live : List LeanMod) : List LeanMod := Id.run do
  let owned := exported h
  let index := Std.HashMap.ofList (historical.map fun m => (m.modName,m))
  let current := Std.HashMap.ofList (live.map fun m => (m.modName,m))
  let ancestors := dependenciesOf index owned
  -- A historical module also changes identity if one of its imports changed.
  let mut changed := Std.HashSet.ofList ((ancestors.filter fun m => current[m.modName]? != some m).map (·.modName))
  repeat
    let size := changed.size
    for m in ancestors do
      if m.imports.any (changed.contains ·.imod) then changed := changed.insert m.modName
    if size == changed.size then break
  let mods := owned ++ ancestors.filter (changed.contains ·.modName)
  let names := mods.map (·.modName)
  let roots := names.filter fun q => !names.any (fun p => p != q && under p q)
  return mods.map fun m => roots.foldl (fun m p => requalify p (oldSnapshotPrefix p) m) m

/-- A stored subtree can come from another epoch or a partial ref. Recheck the
    actual closed link and each directory's contract, including saved grandchildren. -/
def verifyClosure (bases : List LeanMod) (root : Frozen) : IO Unit := do
  let mods ← IO.ofExcept (mergeModules (bases ++ exported root))
  let index := Std.HashMap.ofList (mods.map fun m => (m.modName,m))
  discard <| checkClosedModule (depsExcept mods root.code) root.code
  let mut todo := [root]
  while let h :: rest := todo do
    todo := rest
    satisfies h.spec h.code (dependenciesOf index [h.spec,h.code])
    let imports := Std.HashMap.ofList (h.code.imports.map fun i => (toString i.imod,i))
    let kids := Std.HashSet.ofList (h.children.map Prod.fst)
    for i in h.code.imports do
      if !i.assumes.isEmpty && !kids.contains (toString i.imod) then throw (IO.userError s!"MISSING_VERIFIED_CHILD: {i.imod}")
    for (slot,child) in h.children do
      let some i := imports[slot]? | throw (IO.userError s!"UNIMPORTED_CHILD: {slot}")
      let target := specAt i.imod child
      if target.units != i.assumes then
        let assigned := {target with units := i.assumes}
        eqIface assigned target (dependenciesOf index [assigned,target])
      todo := child :: todo

def checkSaved (bases : List LeanMod) (spec : LeanMod) (h : Frozen) : IO Unit := do
  let original := specAt spec.modName h
  let mods ← IO.ofExcept (mergeModules (bases ++ exported h))
  let index := Std.HashMap.ofList (mods.map fun m => (m.modName,m))
  eqIface original spec (dependenciesOf index [original,spec])
  verifyClosure bases h

/-- Only omitted sub-lifts may infer a matching child map. Explicit descriptors
    retain their full shape and endpoint obligations, including explicit empty maps. -/
private def childObligations (s : LiftSpec) : List (LiftSpec × Bool) :=
  s.children.flatMap fun c =>
    c.subs.map (·, false) ++ (defaultChildLifts c.bases c.uppers c.subs).map (·, true)

def checkKeptLifts (bases : List LeanMod) (bs : Bindings) (ls : LiftSpec) : IO (List LiftProblem) := do
  let kept := Std.HashMap.ofList (keeps bs)
  let mut errors := #[]
  for (sub, implicitMap) in childObligations ls do
    let some h := kept[sub.upper]? | continue
    let mods ← IO.ofExcept (mergeModules (exported h ++ slotAliases sub.upper h ++ bases))
    let index := Std.HashMap.ofList (mods.map fun m => (m.modName,m))
    let mut todo := [(sub, implicitMap, h)]
    while let (s, inferChildren, home) :: rest := todo do
      todo := rest
      let some base := index[s.base]? | errors := errors.push (.missingBaseUnit s.base); continue
      let some target := index[s.upper]? | errors := errors.push (.missingChildImport s.upper); continue
      let children := home.children.map fun (n,kid) => (renameQ home.code.modName s.upper (qualified n), kid)
      let s := if inferChildren then
        let mapped := base.imports.filterMap fun i => do
          guard (!i.assumes.isEmpty)
          let (u,_) ← children.find? (fun (q,_) => q.segments.getLast? == i.imod.segments.getLast?)
          return ChildLift.mkChildLift i.imod u none
        LiftSpec.liftSpecTree s.base s.upper mapped []
      else s
      let snap ← checkClosedModule (depsExcept mods target) target
      errors := (checkLift base target target snap s (renameQ s.upper home.code.modName)).foldl Array.push errors
      for (next, auto) in childObligations s do
        if let some kid := children.lookup next.upper then todo := (next, auto, kid) :: todo
        else errors := errors.push (.missingChildImport next.upper)
  return errors.toList

end Lojita.Harness
