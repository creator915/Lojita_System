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

private def unitModules (snap : Snapshot) : Std.HashMap QName Lean.NameSet := Id.run do
  let mut mods : Std.HashMap QName Lean.NameSet := {}
  for n in snap.constants do
    let some u := snap.owners.find? n | continue
    let some info := snap.env.find? n | continue
    let mut used := mods[u]?.getD {}
    for c in info.getUsedConstantsAsSet do
      if let some origin := moduleOf? snap.env c then
        used := used.insert origin
    mods := mods.insert u used
  return mods

/-- All non-base, non-owned modules exported by non-base horizontal peer trees
    (both peer roots and their transitive child modules). -/
private def transientPeerModules (t : NodeTask) (m : LeanMod) (stubs : List LeanMod) : Std.HashSet Lean.Name := Id.run do
  let bases := Std.HashSet.ofList (t.baseModules.map (·.modName))
  let owned := Std.HashSet.ofList (m.modName :: stubs.map (·.modName) ++
    m.imports.filterMap fun i => if i.assumes.isEmpty then none else some i.imod)
  let mut out : Std.HashSet Lean.Name := {}
  for (h, _) in t.transports do
    if bases.contains h.code.modName then continue
    for em in exported h do
      unless bases.contains em.modName || owned.contains em.modName do
        out := out.insert em.modName.toLeanName
  return out

/-- Retain any square or private Old.*/peer helper reached from the contract or another
    surviving declaration. Kernel edges include dependencies introduced by tactics and
    generated helpers. -/
def sealedCode (t : NodeTask) (m : LeanMod) (snap : Snapshot) (stubs : List LeanMod := []) :
    LeanMod × List QName × List QName := Id.run do
  if t.transports.isEmpty then return (m, [], [])
  let squares := Std.HashSet.ofList (t.transports.flatMap fun (_,ts) => ts.squares.map (·.squareUnit))
  let contract := Std.HashSet.ofList (t.delta.newIface.units.flatMap (·.definedNames))
  let pub := Std.HashSet.ofList (publicNames m)
  let transientPeers := transientPeerModules t m stubs
  let uMods := unitModules snap
  let edges := snap.graph.semArrows
  let transientSquares := Std.HashSet.ofList ((m.units.filter fun u =>
    u.kind == .theoremDecl && squares.contains u.uname && !contract.contains u.uname).map (·.uname))
  let mut touchesTransient : Std.HashSet QName := transientSquares
  for u in m.units do
    let mods := uMods[u.uname]?.getD {}
    if mods.any (fun mod => mod.getRoot == `Old || transientPeers.contains mod) then
      touchesTransient := touchesTransient.insert u.uname
  repeat
    let size := touchesTransient.size
    for edge in edges do
      let (.unit user, .unit dep) := edge | continue
      if touchesTransient.contains dep then touchesTransient := touchesTransient.insert user
    if size == touchesTransient.size then break
  let mut transient := Std.HashSet.ofList ((m.units.filter fun u =>
    transientSquares.contains u.uname ||
      (u.definedNames.all (!pub.contains ·) && touchesTransient.contains u.uname)).map (·.uname))
  repeat
    let size := transient.size
    for edge in edges do
      let (.unit user, .unit dep) := edge | continue
      unless transient.contains user do transient := transient.erase dep
    if size == transient.size then break
  let mut survivingMods : Lean.NameSet := {}
  for u in m.units do
    unless transient.contains u.uname do
      survivingMods := survivingMods ++ (uMods[u.uname]?.getD {})
  let leakedSnapshots := distinct (survivingMods.toList.filterMap fun mod =>
    if mod.getRoot == `Old then some (QName.ofName mod) else none)
  let leakedPeers := distinct (survivingMods.toList.filterMap fun mod =>
    if transientPeers.contains mod then some (QName.ofName mod) else none)
  let removed := m.imports.filterMap fun i =>
    let peer := transientPeers.contains i.imod.toLeanName && !survivingMods.contains i.imod.toLeanName
    if isSnapshot i.imod || peer then some i.imod else none
  let cleaned : LeanMod := {m with
    units := m.units.filter (!transient.contains ·.uname)
    imports := m.imports.filter (!removed.contains ·.imod)
    opens := opensAfterRemoval m (if removed.any isSnapshot then qualified "Old" :: removed else removed)}
  return (cleaned, leakedSnapshots, leakedPeers)

def verifySealed (t : NodeTask) (deps stubs : List LeanMod) (tests : LeanMod) (snap : Snapshot) :
    IO (Except NarrowingCertificate LeanMod) := do
  let owner := t.delta.child
  let (code, leakedSnapshots, leakedPeers) := sealedCode t tests snap stubs
  if let mod :: _ := leakedSnapshots then
    return .error (problem "transient_snapshot_leak" owner
      s!"Surviving declaration depends on read-only snapshot module {mod}."
      "Reference Old.* only inside declared horizontal transport squares or private helper lemmas used exclusively by those squares.")
  if let mod :: _ := leakedPeers then
    return .error (problem "transient_peer_leak" mod
      s!"Surviving declaration depends on non-base horizontal peer {mod}, which is retired at seal."
      "Reference the horizontal peer only inside declared transport squares or private helper lemmas used exclusively by those squares.")
  if code != tests then
    let transientPeers := transientPeerModules t tests stubs
    let sealedDeps := deps.filter fun m => !transientPeers.contains m.modName.toLeanName
    if let .error e ← (checkConditionalGlue sealedDeps stubs code).toBaseIO then
      return .error (kernelError code (toString e))
    if let .error e ← (satisfies t.delta.newIface code sealedDeps .closedImplOK stubs).toBaseIO then
      return .error (kernelError code (toString e))
  return .ok code

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
      unless isNestedDescendant h.code.modName (qualified n) || srcSet.contains n do
        throw (problem "unaccountedOldChild" (qualified n)
          "Saved source child slot is not covered by the TransportSpec child map."
          "The TransportSpec descriptor (set by SESSION_ROOT for the root tree, or by the parent node for nested slots) must cover every saved source child slot via keep or move.")
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
    let stubNames := Std.HashSet.ofList (old.code.imports.filterMap fun i =>
      if i.assumes.isEmpty then none else some i.imod)
    let historicalBases := if t.currentOnLiveBases then none else t.oldBaseModules
    let histDeps := (historicalBases.getD deps).filter fun m => !stubNames.contains m.modName
    let histNames := Std.HashSet.ofList (histDeps.map (·.modName))
    let mut oldStubs := #[]
    let openTokens := fun (raw : String) =>
      (raw.map fun c => if c.isWhitespace || c == '(' || c == ')' then ' ' else c).splitOn " "
    let opensCover := fun (opens : List String) (ns : QName) =>
      opens.any fun raw => (openTokens raw).contains (toString ns)
    let isHistAllowed := fun (q : QName) => q.toLeanName.getRoot == `LojitaCtx || histNames.contains q
    for i in old.code.imports do
      if i.assumes.isEmpty then continue
      let (ctxFromRefs, ctxNsFromRefs) ← contextHintsForRefs (i.assumes.flatMap (·.synRefs))
      let histRefMods := histDeps.filterMap fun m =>
        if i.assumes.any (fun u => u.synRefs.any (under m.modName ·)) then some m.modName else none
      let needsOpen := fun (ns : QName) =>
        i.assumes.any fun u =>
          let refSet := Std.HashSet.ofList u.synRefs
          u.synRefs.any fun r => under ns r && r.segments.length > ns.segments.length &&
            refSet.contains ⟨r.segments.drop ns.segments.length⟩
      let neededNs := distinct (ctxNsFromRefs.filter needsOpen ++ histRefMods.filter needsOpen)
      let mut chosen : Option LeanMod := none
      if let some s := saved[i.imod]? then
        if s.imports.all (fun j => isHistAllowed j.imod) then
          if s.units == i.assumes then
            chosen := some s
          else if neededNs.all (opensCover s.opens) &&
              histRefMods.all (fun m => s.imports.any (·.imod == m)) &&
              (ctxFromRefs.isEmpty || s.imports.any (·.imod.toLeanName.getRoot == `LojitaCtx)) then
            let candidateStub : LeanMod := ⟨i.imod, s.imports, s.opens, i.assumes⟩
            if (← (checkConditionalGlue histDeps [] candidateStub true).toBaseIO).isOk then
              chosen := some candidateStub
      if let some stub := chosen then
        oldStubs := oldStubs.push stub
        continue
      let savedMods := (saved[i.imod]?.map (·.imports) |>.getD []).filterMap fun j =>
        if isHistAllowed j.imod then some j.imod else none
      let oldCtxMods := old.code.imports.filterMap fun j =>
        if j.imod.toLeanName.getRoot == `LojitaCtx &&
            (saved[i.imod]?.isNone || i.assumes.any (fun u => u.synRefs.any (under j.imod ·))) then
          some j.imod
        else none
      let fallbackImports := (distinct (savedMods ++ ctxFromRefs ++ oldCtxMods ++ histRefMods)).map (⟨·, []⟩)
      let carriedOpens := match saved[i.imod]? with
        | some s => opensAfterRemoval s (s.imports.filterMap fun j => if isHistAllowed j.imod then none else some j.imod)
        | none => opensAfterRemoval old.code (old.code.imports.filterMap fun j => if isHistAllowed j.imod then none else some j.imod)
      let missingNs := neededNs.filter (!opensCover carriedOpens ·)
      let missingOpens := if missingNs.isEmpty then [] else
        ["open " ++ String.intercalate " " (missingNs.map toString)]
      let openCandidates := (if missingOpens.isEmpty then [carriedOpens]
        else [distinct (carriedOpens ++ missingOpens), missingOpens, carriedOpens]).filter (!·.isEmpty)
      let mut fallbackStub : LeanMod := ⟨i.imod, fallbackImports, [], i.assumes⟩
      for opens in distinct openCandidates do
        let tryStub : LeanMod := ⟨i.imod, fallbackImports, opens, i.assumes⟩
        if (← (checkConditionalGlue histDeps [] tryStub true).toBaseIO).isOk then
          fallbackStub := tryStub
          break
      oldStubs := oldStubs.push fallbackStub
    match ← (checkConditionalGlue histDeps oldStubs.toList old.code).toBaseIO with
    | .ok oldSnap =>
      checkFrontier (validate old.code p cand (some oldSnap) (some snap))
    | .error err =>
      if historicalBases.isSome then
        throw (problem "historical_elaboration_failed" owner (toString err)
          "Pinned historical base modules could not elaborate CURRENT CODE; ensure upstream ancestry is consistent before re-driving.")
      checkFrontier (validate old.code p cand none (some snap))
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
    if let some err := errors.head? then
      throw (problem err.code owner (reprStr err)
        "The retained child's LiftSpec obligation failed against the vertical base; update the LiftSpec or replace (keep ...) with (move ...) in the transport descriptor (set by SESSION_ROOT for the root tree, or by the parent node for nested slots).")
  passed "Lift"
  let code ← plain (← verifySealed t deps stubs tests snap)
  return ⟨code, specs, deps, p, kept, childLifts⟩

def checkCandidateGates (t : NodeTask) (old : Frozen) (p : Plan) (subs : List LeanMod := []) :
    IO (GateReport × Option Candidate) := do
  let (res, report) ← ((gatePipeline t old p subs).run).run {}
  match res with
  | .error cert => return ({report with certificate := some cert}, none)
  | .ok cand => return (report, some cand)

end Lojita.Harness
