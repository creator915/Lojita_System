import Lojita.Harness.Tree
import Lojita.Transport.Lift
import Lojita.Transport.Namespace

namespace Lojita.Harness
open Lojita.Kernel Lojita.Transport

abbrev Bindings := List (Frozen × TransportSpec)

def lookupChild (f : Frozen) (q : QName) := f.children.lookup (toString q)

/-- A relocated identity slot exports transparent aliases to the original
    constants. Its sealed directory, including all descendants, stays intact. -/
def slotAliases (slot : QName) (f : Frozen) : List LeanMod := Id.run do
  let src := f.code.modName
  if slot == src then return []
  let names := publicNames f.code
  let units := names.map fun q =>
    let localName := q.toLeanName.replacePrefix src.toLeanName .anonymous
    let target := QName.ofName (slot.toLeanName ++ localName)
    let raw := s!"abbrev {localName} := @{q}"
    {uname := target, definedNames := [target], kind := .abbrevDecl, rawSource := raw,
      sigSlice := s!"abbrev {localName}", synRefs := [q] : SynUnit}
  return [⟨slot, [⟨src, []⟩], [], units⟩]

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

def exported (f : Frozen) := (exportNode f #[]).toList

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

private abbrev InspectLift := LiftSpec → Array LiftProblem → IO (Array LiftProblem)

mutual
  private def checkRetainedLift (inspect : InspectLift) (s : LiftSpec) (acc : Array LiftProblem) : IO (Array LiftProblem) :=
    match s with | .liftSpecTree b u cs es => do
      let acc ← inspect (.liftSpecTree b u cs es) acc
      checkRetainedChildren inspect cs acc
  termination_by structural s

  private def checkRetainedChildren (inspect : InspectLift) (cs : List ChildLift) (acc : Array LiftProblem) : IO (Array LiftProblem) :=
    match cs with
    | [] => pure acc
    | .mkChildLift b u none :: rest => do
      checkRetainedChildren inspect rest (← inspect (.liftSpecTree b u [] []) acc)
    | .mkChildLift _ _ (some s) :: rest => do
      checkRetainedChildren inspect rest (← checkRetainedLift inspect s acc)
    | .moveChildLifts bs us ss :: rest => do
      let acc ← checkRetainedSubs inspect ss acc
      let acc ← (defaultChildLifts bs us ss).foldlM (fun a s => inspect s a) acc
      checkRetainedChildren inspect rest acc
  termination_by structural cs

  private def checkRetainedSubs (inspect : InspectLift) (ss : List LiftSpec) (acc : Array LiftProblem) : IO (Array LiftProblem) :=
    match ss with
    | [] => pure acc
    | s :: rest => do checkRetainedSubs inspect rest (← checkRetainedLift inspect s acc)
  termination_by structural ss
end

def checkKeptLifts (bases : List LeanMod) (bs : Bindings) (ls : LiftSpec) : IO (List LiftProblem) := do
  let kept := Std.HashMap.ofList (keeps bs)
  let mut errors := #[]
  for sub in ls.children.flatMap ChildLift.childSpecs do
    let some h := kept[sub.upper]? | continue
    let mods ← IO.ofExcept (mergeModules (exported h ++ slotAliases sub.upper h ++ bases))
    let index := Std.HashMap.ofList (mods.map fun m => (m.modName,m))
    let inspect : InspectLift := fun s acc => do
      let some base := index[s.base]? | return acc.push (.missingBaseUnit s.base)
      let some target := index[s.upper]? | return acc.push (.missingChildImport s.upper)
      let snap ← checkClosedModule (depsExcept mods target) target
      return (checkLift base target target snap s).foldl Array.push acc
    errors ← checkRetainedLift inspect sub errors
  return errors.toList

end Lojita.Harness
