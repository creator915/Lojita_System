import Lojita.Harness.Protocol
import Lojita.Transport.Countermodel

namespace Lojita.Harness
open Lojita.Kernel Lojita.Transport Lojita.Store

structure Candidate where
  code : LeanMod
  specs : List LeanMod
  deps : List LeanMod
  plan : Plan
  kept : List (QName × Frozen)
  childLifts : Std.HashMap QName (Array (LeanMod × LiftSpec))

structure GateReport where
  passed : Array String := #[]
  frontier : List String := []
  certificate : Option NarrowingCertificate := none
  deriving BEq, Repr, Lean.ToJson

private abbrev GateM := ExceptT NarrowingCertificate (StateT GateReport IO)

private def passed (name : String) : GateM Unit := modify fun r => {r with passed := r.passed.push name}

def problem (kind : String) (w : QName) (cause detour : String) : NarrowingCertificate :=
  ⟨kind,toString w,cause,detour⟩

private def checked {α : Type} (act : IO α) (cert : String → NarrowingCertificate) : GateM α := do
  match ← act.toBaseIO with
  | .ok a => return a
  | .error e => throw (cert (toString e))

private def kernelError (m : LeanMod) (msg : String) :=
  problem ((msg.splitOn ":").headD "KERNEL_ERROR") m.modName msg "Correct the declaration identified by the kernel."

def childPermissions (t : NodeTask) : QName → Option (List QName) := Id.run do
  let some allowed := t.allowedAncestors | return fun _ => none
  if t.transports.isEmpty && t.lifts.isEmpty then return fun _ => some allowed
  let mut sources : Std.HashMap QName (Array QName) := {}
  for (_,s) in t.transports do
    for move in s.childMoves do
      for q in move.targets do sources := sources.alter q fun xs => some (move.sources.foldl Array.push (xs.getD #[]))
  for (_,s) in t.lifts do
    for child in s.children do
      for q in child.uppers do sources := sources.alter q fun xs => some (child.bases.foldl Array.push (xs.getD #[]))
  let index := Std.HashMap.ofList (t.baseModules.map fun m => (m.modName,m))
  let allowedSet := Std.HashSet.ofList allowed
  return fun q => some <| Id.run do
    let mut todo := (sources[q]?.getD #[]).toList
    let mut seen : Std.HashSet QName := {}
    let mut visible := #[]
    while let n :: rest := todo do
      todo := rest
      if seen.contains n || !allowedSet.contains n then continue
      let some m := index[n]? | continue
      seen := seen.insert n
      visible := visible.push n
      todo := m.imports.map (·.imod) ++ todo
    return visible.toList

def depthCertificate (q : QName) : Option NarrowingCertificate :=
  if q.segments.head? == some "Gen" && q.segments.length > 5 then
    some (problem "subspec_depth_cap" q "The child is below the grandchild ownership level." "Split the work into sibling modules.")
  else none

def launderingCertificate (s : Snapshot) : Option NarrowingCertificate := Id.run do
  let carriers := Lean.NameSet.ofList (s.graph.sorts.filterMap fun (q,k) =>
    if k == .carrier then some q.toLeanName else none)
  let sorts := Std.HashMap.ofList s.graph.sorts
  for n in s.declaredAxioms do
    let q := QName.ofName n
    let some info := s.env.find? n | continue
    let isLaw : Bool := match sorts[q]? with
      | some k => k == .law
      | none => (Lean.Kernel.check s.env {} info.type).toOption.any (·.isProp)
    unless isLaw do continue
    unless info.type.getUsedConstantsAsSet.any carriers.contains do
      return some (problem "subspec_laundering" q "The assumed law mentions no child-owned carrier or operation."
        "State the obligation over a carrier or operation declared by this child.")
  return none

private def planCertificate (p : PlanProblem) : NarrowingCertificate :=
  match p with
  | .unsettled o => ⟨"frontier_incomplete", (encObj o).canonical,
      "This dependent uses an endpoint whose interface changed.", "Supply an outgoing move for this dependent."⟩
  | _ => ⟨p.code, reprStr p,
      "The move does not account for the source and target declarations.", "Align the plan with the old module and the submitted draft."⟩

/-- Cheap gates are ordinary short-circuiting Except computations. -/
def planError (problems : List PlanProblem) : Except NarrowingCertificate Unit := do
  if let some err := problems.head? then throw (planCertificate err)

private def checkFrontier (problems : List PlanProblem) : GateM Unit := do
  if let .error cert := planError problems then
    let pending := problems.filterMap fun | .unsettled o => some (encObj o).canonical | _ => none
    modify fun r => {r with frontier := pending}
    throw cert

private def plain {α : Type} (x : Except NarrowingCertificate α) : GateM α := match x with | .ok a => pure a | .error e => throw e

private def routeLifts (t : NodeTask) (deps : List LeanMod) (owned : Std.HashSet QName) :
    Except NarrowingCertificate (Std.HashMap QName (Array (LeanMod × LiftSpec))) := do
  let modules := Std.HashMap.ofList (deps.map fun m => (m.modName,m))
  let mut routed := {}
  for (_,ls) in t.lifts do
    for child in ls.children do
      for q in child.uppers do
        unless owned.contains q do
          throw (problem "missingChildImport" q "The mapped target has no child slot." "Supply its child specification.")
      for sub in child.childSpecs do
        let some base := modules[sub.base]? |
          throw (problem "missingBaseUnit" sub.base "The child lift has no closed base." "Supply the source child's implementation.")
        routed := routed.alter sub.upper fun prev => some ((prev.getD #[]).push (base,sub))
  return routed

private def isSnapshot (q : QName) := q.segments.head? == some "Old"

/-- Retain any square reached from the contract or another surviving declaration.
    Kernel edges include dependencies introduced by tactics and generated helpers. -/
private def sealedCode (t : NodeTask) (m : LeanMod) (snap : Snapshot) : LeanMod := Id.run do
  if t.transports.isEmpty then return m
  let squares := Std.HashSet.ofList (t.transports.flatMap fun (_,ts) => ts.squares.map (·.squareUnit))
  let contract := Std.HashSet.ofList (t.delta.newIface.units.flatMap (·.definedNames))
  let mut transient := Std.HashSet.ofList ((m.units.filter fun u =>
    u.kind == .theoremDecl && squares.contains u.uname && !contract.contains u.uname).map (·.uname))
  let edges := snap.graph.semArrows
  repeat
    let size := transient.size
    for edge in edges do
      let (.unit user, .unit dep) := edge | continue
      unless transient.contains user do transient := transient.erase dep
    if size == transient.size then break
  let peers := t.transports.map (·.1.code.modName)
  let bases := t.baseModules.map (·.modName)
  let removed := m.imports.filterMap fun i =>
    let peer := peers.contains i.imod && !bases.contains i.imod && !squares.isEmpty &&
      !edges.any (fun | (.unit u, .ext q) => !transient.contains u && under i.imod q | _ => false)
    if isSnapshot i.imod || peer then some i.imod else none
  return {m with
    units := m.units.filter (!transient.contains ·.uname)
    imports := m.imports.filter (!removed.contains ·.imod)
    opens := opensAfterRemoval m (if removed.any isSnapshot then qualified "Old" :: removed else removed)}

private def gatePipeline (t : NodeTask) (old : Frozen) (p : Plan) (subs : List LeanMod) : GateM Candidate := do
  let kept := keeps t.transports
  let keptSpecs := kept.map fun (q,h) => specAt q h
  let oldSpecs := old.children.map fun (n,h) => specAt (qualified n) h
  let declared := Std.HashMap.ofList ((oldSpecs ++ keptSpecs ++ subs).map fun s => (s.modName,s))
  let cand := apply p old.code
  let specs := cand.imports.filterMap fun i =>
    declared[i.imod]? <|> (if i.assumes.isEmpty then none else some ⟨i.imod, [], [], i.assumes⟩)
  let cand := withChildIfaces cand specs
  checkFrontier (validate old.code p cand)
  passed "frontier"
  let owner := t.delta.child
  let owned := specs.map (·.modName)
  let ownedSet := Std.HashSet.ofList owned
  let permissions := childPermissions t
  let allowed := t.allowedImports
  let scope := fun (q : QName) (msg : String) => problem "namespace" q msg "Import a declared base or a directly owned child."
  unless cand.modName == owner && t.delta.newIface.modName == owner do throw (scope owner "Wrong task module")
  if let some q := (duplicates (subs.map (·.modName))).head? then throw (scope q "Duplicate named subspec")
  let retained := t.transports.flatMap fun (_,s) => (directKeeps s).filterMap fun (o,n) => if o == n then some n else none
  if let some err := (checkOwnedImports owner owned retained allowed cand).head? then throw (scope owner (reprStr err))
  for s in subs do
    unless ownedSet.contains s.modName do throw (scope s.modName "Subspec has no child import")
  for s in specs do
    if let some cert := depthCertificate s.modName then throw cert
    if let some err := (checkTaskImports s.modName [] ((permissions s.modName).getD allowed) s).head? then
      throw (scope s.modName (reprStr err))
  for (h,ts) in t.transports do
    let kids := Std.HashSet.ofList (h.children.map Prod.fst)
    let srcs := ts.childMoves.flatMap ChildMove.sources
    let srcSet := Std.HashSet.ofList (srcs.map toString)
    for (n,_) in h.children do
      unless srcSet.contains n do throw (problem "unaccountedOldChild" (qualified n) "Old slot has no move." "Cover the source slot.")
    for q in srcs do unless kids.contains (toString q) do throw (scope q "No such saved source slot")
    for q in ts.childMoves.flatMap ChildMove.targets do unless ownedSet.contains q do
      throw (problem "missingTargetChildImport" q "Missing owned target." "Import the target and supply its specification.")
  passed "Namespace"
  for (h,ts) in t.transports do
    if let some err := (polyShapeProblems h.code cand ts).head? then
      throw (problem err.code owner (reprStr err) "Repair the horizontal child map.")
  for (base,ls) in t.lifts do
    if let some err := (liftShapeProblems base cand ls).head? then
      throw (problem err.code owner (reprStr err) "Repair the vertical child map.")
  let deps ← plain ((t.checkingDeps owner owned).mapError (scope owner))
  let childLifts ← plain (routeLifts t deps ownedSet)
  for s in specs do
    let snap ← checked (checkConditionalGlue deps [] s true) (kernelError s)
    if let some cert := launderingCertificate snap then throw cert
  let tests := withTests cand t.delta.newIface
  let stubs := specs.map stubOf
  let proofDeps ← if tests.imports.any (isSnapshot ·.imod) then
    plain ((mergeModules (deps ++ t.snapshotModules)).mapError (scope owner)) else pure deps
  let snap ← checked (checkConditionalGlue proofDeps stubs tests) (kernelError cand)
  passed "checkConditionalGlue"
  if !p.moves.isEmpty && !old.code.units.isEmpty then
    let saved := Std.HashMap.ofList (oldSpecs.map fun s => (s.modName,s))
    let oldStubs := old.code.imports.filterMap fun i => if i.assumes.isEmpty then none else
      some (saved[i.imod]?.getD ⟨i.imod, [], [], i.assumes⟩)
    let stubNames := Std.HashSet.ofList (oldStubs.map (·.modName))
    let histDeps := (t.oldBaseModules.getD deps).filter fun m => !stubNames.contains m.modName
    let oldSnap ← (checkConditionalGlue histDeps oldStubs old.code).toBaseIO
    checkFrontier (validate old.code p cand oldSnap.toOption snap)
  checked (satisfies t.delta.newIface tests proofDeps .closedImplOK stubs) fun msg =>
    problem "interface_mismatch" owner msg "Implement the specification's public signatures and concrete helpers."
  passed "satisfies"
  for (h,ts) in t.transports do
    if let some err := (checkPolyTransport h.code cand t.delta.newIface snap ts).head? then
      throw (problem err.code owner (reprStr err) "Repair the horizontal square or child map.")
  for (q,h) in kept do
    let some target := declared[q]? | throw (scope q "Missing kept specification")
    checked (checkSaved deps target h) fun msg =>
      problem "interface_mismatch" q msg "Use a child move for a changed interface."
  passed "PolyTransport"
  for (base,ls) in t.lifts do
    if let some err := (checkLift base cand t.delta.newIface snap ls).head? then
      throw (problem err.code owner (reprStr err) "Repair the vertical endpoint square or child map.")
    let errors ← checked (checkKeptLifts deps t.transports ls) (kernelError cand)
    if let some err := errors.head? then throw (problem err.code owner (reprStr err) "Repair the retained child's lift.")
  passed "Lift"
  let code := sealedCode t tests snap
  if code != tests then
    discard <| checked (checkConditionalGlue deps stubs code) (kernelError code)
    checked (satisfies t.delta.newIface code deps .closedImplOK stubs) (kernelError code)
  return ⟨code, specs, deps, p, kept, childLifts⟩

def checkCandidateGates (t : NodeTask) (old : Frozen) (p : Plan) (subs : List LeanMod := []) :
    IO (GateReport × Option Candidate) := do
  let (res, report) ← ((gatePipeline t old p subs).run).run {}
  match res with
  | .error cert => return ({report with certificate := some cert}, none)
  | .ok cand => return (report, some cand)

end Lojita.Harness
