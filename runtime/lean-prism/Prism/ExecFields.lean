import Prism.CatStructure

/-! Closed-program demand for fields of authored constructors. Only the
execution image uses this layout. A nested constructor/literal pattern in
any consumer takes precedence over a wildcard in another module. -/
namespace Prism.ExecFields

private inductive Slot where
  | positional (constructor : List String) (position : Nat)
  | named (field : String)
  deriving BEq, Hashable

private def observation (used : Option (List String)) (slot : Slot) : Pat → List (Slot × Bool)
  | .wildP => [(slot, false)]
  | .varP x => if used.any (!·.contains x) then [(slot, false)] else []
  | .asP _ p => observation used slot p
  | _ => [(slot, true)]

private def observePattern (used : Option (List String)) : Pat → List (Slot × Bool)
  | .conP q args => (q.full :: q.canonAlts).flatMap fun ctor =>
      ((args.filter (·.hid == .visible)).zipIdx).flatMap fun (a,i) =>
        observation used (.positional ctor i) a.thing
  | .recP fs => fs.flatMap fun (f,p) => observation used (.named f) p
  | _ => []

private def observed : CodeVisitor (Slot × Bool) where
  name _ := []
  pattern := observePattern none
  clausePatterns? := some fun rhs localDecls =>
    let used := collectVarsRhs rhs ++ localDecls.flatMap collectVarsDecl
    observePattern (some used)

/-- A single layout for the entire linked image. Indices, proofs and recursive
    SCC fields retain the checked inductive representation. A skipped binding
    or a projection of a sibling field provides evidence of selective demand. -/
def layout (modules : List (CodeMod × SlicePlan)) : DeferredFields := Id.run do
  let uses := modules.flatMap fun (cm,_) => cm.decls.flatMap (CodeVisitor.decl observed)
  let forced := Std.HashSet.ofList <| uses.filterMap fun (k,p) => if p then some k else none
  let skipped := Std.HashSet.ofList <| uses.filterMap fun (k,p) => if p then none else some k
  let units := modules.flatMap (·.2.units)
  let references := Std.HashSet.ofList <| units.flatMap fun u => u.sigQNames ++ u.bodyQNames
  let synonyms := Std.HashSet.ofList <| units.flatMap fun u => match u.kind with
    | .patSynUnit _ _ p _ => collectPatQNames p
    | _ => []
  let mut result := {}
  for (cm,plan) in modules do
    let us := plan.units.toArray
    for ids in plan.sccs do
      let group := ids.filterMap (us[·]?)
      let recursiveTypes := group.filterMap fun u => match u.kind with
        | .dataUnit n .. | .recUnit n .. => some (cm.modName.full ++ [n])
        | _ => none
      let eligible (t : Expr) := !CatStructure.erasedDomain t &&
        !(collectExprQNames t).any recursiveTypes.contains
      for u in group do
        match u.kind with
        | .dataUnit n _ (.set _) _ constructors =>
          for (c,ty) in constructors do
            let path := cm.modName.full ++ [n,c]
            let ds := CatStructure.portDomains ty
            if !synonyms.contains path && ds.all (fun a => a.hid == .visible && a.label.isNone) then
              let lazyFields := ds.zipIdx.filterMap fun (a,i) => do
                let key := Slot.positional path i
                guard (eligible a.thing && skipped.contains key && !forced.contains key)
                return i
              if !lazyFields.isEmpty then result := result.insert path lazyFields
        | .recUnit n _ _ _ rd fs =>
          let path := cm.modName.full ++ [n]
          let ctor := rd.constr.map (fun c => cm.modName.full ++ [c])
          unless rd.coind || ctor.any synonyms.contains || hasDependentRecordFields path fs do
            let project (f : String) := references.contains (path ++ [f])
            let projected := fs.filterMap fun (f,_) => if project f then some f else none
            let lazyFields := fs.zipIdx.filterMap fun ((f,t),i) => do
              let pos := ctor.map (Slot.positional · i)
              let named := Slot.named f
              -- A function-valued field already stores its body under a closure.
              guard ((CatStructure.portDomains t).isEmpty && eligible t)
              guard (!forced.contains named && !pos.any forced.contains)
              guard (projected.any (· != f) || skipped.contains named || pos.any skipped.contains)
              return i
            if !lazyFields.isEmpty then
              result := result.insert path lazyFields
              if let some c := ctor then result := result.insert c lazyFields
        | _ => pure ()
  return result

end Prism.ExecFields
