import Lojita.Transport.PolyTransport

namespace Lojita.Transport
open Lean Lojita.Kernel Lojita.Store

structure EndpointLift where
  polyEndpointLiftRefs ::
  baseUnits : List QName
  upperUnits : List QName
  squareUnit : QName
  requiredRefs : List QName := []
  deriving BEq, Repr

export EndpointLift (polyEndpointLiftRefs)
def endpointLift (b u sq : QName) : EndpointLift := ⟨[b], [u], sq, []⟩

mutual
  inductive LiftSpec where
    | liftSpecTree (base upper : QName) (children : List ChildLift) (endpoints : List EndpointLift)
  inductive ChildLift where
    | mkChildLift (base upper : QName) (sub : Option LiftSpec)
    | moveChildLifts (bases uppers : List QName) (subs : List LiftSpec)
end

deriving instance BEq for LiftSpec, ChildLift

def mkChildLift (base : QName) (targets : List QName) (subs : List LiftSpec := []) : ChildLift :=
  .moveChildLifts [base] targets subs

def LiftSpec.base : LiftSpec → QName | .liftSpecTree b _ _ _ => b
def LiftSpec.upper : LiftSpec → QName | .liftSpecTree _ u _ _ => u
def LiftSpec.children : LiftSpec → List ChildLift | .liftSpecTree _ _ cs _ => cs
def LiftSpec.endpoints : LiftSpec → List EndpointLift | .liftSpecTree _ _ _ es => es

def ChildLift.bases : ChildLift → List QName | .mkChildLift b _ _ => [b] | .moveChildLifts bs _ _ => bs
def ChildLift.uppers : ChildLift → List QName | .mkChildLift _ u _ => [u] | .moveChildLifts _ us _ => us
def ChildLift.subs : ChildLift → List LiftSpec | .mkChildLift _ _ s => s.toList | .moveChildLifts _ _ ss => ss

def defaultChildLifts (bases uppers : List QName) (explicit : List LiftSpec) : List LiftSpec :=
  match bases with
  | [b] =>
    let assigned := Std.HashSet.ofList (explicit.map (·.upper))
    uppers.filterMap fun u => if assigned.contains u then none else some (.liftSpecTree b u [] [])
  | _ => []

def ChildLift.childSpecs (c : ChildLift) :=
  c.subs ++ defaultChildLifts c.bases c.uppers c.subs

inductive LiftProblem where
  | wrongBase | wrongUpper
  | missingChildMap (q : QName)
  | missingChildImport (q : QName)
  | duplicateUpperChild (q : QName)
  | invalidChildLift (q : QName)
  | emptyLiftEndpoints (q : QName)
  | missingBaseUnit (q : QName)
  | missingUpperUnit (q : QName)
  | missingSquare (q : QName)
  | invalidSquare (q : QName)
  deriving BEq, Repr

def liftShapeProblems (baseImpl upperCand : LeanMod) (ls : LiftSpec) : List LiftProblem := Id.run do
  let mut errors := #[]
  if baseImpl.modName != ls.base then errors := errors.push .wrongBase
  if upperCand.modName != ls.upper then errors := errors.push .wrongUpper
  let mapped := Std.HashSet.ofList (ls.children.flatMap ChildLift.bases)
  for i in baseImpl.imports do
    if !i.assumes.isEmpty && !mapped.contains i.imod then errors := errors.push (.missingChildMap i.imod)
  let targets := ls.children.flatMap ChildLift.uppers
  for q in duplicates targets do errors := errors.push (.duplicateUpperChild q)
  let imports := Std.HashSet.ofList (upperCand.imports.map (·.imod))
  for q in distinct targets do unless imports.contains q do errors := errors.push (.missingChildImport q)
  for c in ls.children do
    for s in c.subs do
      unless c.bases.contains s.base && c.uppers.contains s.upper do errors := errors.push (.invalidChildLift s.upper)
  return errors.toList

def checkLift (baseImpl upperCand upperSpec : LeanMod) (upperSnap : Snapshot) (ls : LiftSpec)
    (upperOrigin : QName → QName := id) : List LiftProblem := Id.run do
  let mut errors := (liftShapeProblems baseImpl upperCand ls).toArray
  let tested := withTests upperCand upperSpec
  if renderLeanMod upperSnap.mod != renderLeanMod tested then return (errors.push .wrongUpper).toList
  let before := endpointNames baseImpl
  let after := endpointNames tested
  let relations := [`LojitaCtx.Blueprint.PortLift, `LojitaCtx.Blueprint.Commutes₁,
    `LojitaCtx.Blueprint.Commutes₂, `LojitaCtx.Blueprint.Commutes₃] ++ polyRelations
  for e in ls.endpoints do
    if e.baseUnits.isEmpty || e.upperUnits.isEmpty then errors := errors.push (.emptyLiftEndpoints e.squareUnit)
    let info := publicSquare upperSnap e.squareUnit
    -- A forwarding alias inherits its theorem type from the retained implementation.
    let required := e.requiredRefs.map upperOrigin
    let refs := info.map fun c => typeMentions upperSnap c.type (e.baseUnits ++ e.upperUnits.map upperOrigin ++ required)
    for q in e.baseUnits do
      unless before.contains q && refs.all (·.contains q.toLeanName) do errors := errors.push (.missingBaseUnit q)
    for q in e.upperUnits do
      unless after.contains q && refs.all (·.contains (upperOrigin q).toLeanName) do errors := errors.push (.missingUpperUnit q)
    let some c := info | errors := errors.push (.missingSquare e.squareUnit); continue
    unless validSquareType upperSnap c relations required && required.all (fun q => refs.any (·.contains q.toLeanName)) do
      errors := errors.push (.invalidSquare e.squareUnit)
  return errors.toList

private def usedRefutationUnits (units : List SynUnit) (refuteSnap : Snapshot) (targets : List Name) :
    List QName := Id.run do
  let direct := units.foldl (init := ({} : NameMap QName)) fun names u =>
    u.definedNames.foldl (init := names) fun acc q => acc.insert q.toLeanName u.uname
  let mut todo := (refuteSnap.mod.units.flatMap (·.definedNames)).map QName.toLeanName |>.filter fun n =>
    !isPrivateName n && refuteSnap.constants.contains n && (refuteSnap.env.find? n).any fun
      | .thmInfo t => targets.any fun target => refuteSnap.env.contains target &&
          Lean.Kernel.isDefEqGuarded refuteSnap.env {} t.type (mkConst target)
      | _ => false
  let mut seen : NameSet := {}
  let mut hit : Std.HashSet QName := {}
  while let n :: rest := todo do
    todo := rest
    if seen.contains n then continue
    seen := seen.insert n
    if let some owner := refuteSnap.owners.find? n then hit := hit.insert owner
    if let some info := refuteSnap.env.find? n then
      if info matches .axiomInfo _ then
        if let some owner := direct.find? (privateToUserName n) then hit := hit.insert owner
      todo := info.getUsedConstantsAsSet.foldl (fun acc q => q :: acc) todo
  let culprits := distinct ((units.map (·.uname)).filter hit.contains)
  return culprits.mergeSort (fun a b => a.toLeanName.lt b.toLeanName)

/-- Follow public False proofs through private lemmas and kernel auxiliaries to their base units. -/
def extractCulpritBaseUnits (bases : List LeanMod) (refuteSnap : Snapshot) : List QName :=
  usedRefutationUnits (bases.flatMap (·.units)) refuteSnap [``False]

/-- Project the checked witness back onto exactly the child interface units it used. -/
def extractCulpritAssumptions (specMod : LeanMod) (refuteSnap : Snapshot) (targets : List Name := [``False]) :
    List QName :=
  usedRefutationUnits specMod.units refuteSnap targets

/-- Re-parse at the boundary even when the submitted carrier was decoded from a store. -/
def witnessBoundary (bases : List LeanMod) (spec witness : LeanMod) : IO Unit := do
  let m ← IO.ofExcept (parseLeanMod (renderLeanMod witness))
  unless m.modName != spec.modName && !bases.any (·.modName == m.modName) do
    throw (IO.userError "WITNESS_NAMESPACE: witness shadows a dependency")
  let allowed := Std.HashSet.ofList (spec.modName :: bases.map (·.modName))
  for i in m.imports do
    unless i.imod.toLeanName.getRoot == `LojitaCtx || allowed.contains i.imod do
      throw (IO.userError s!"UNAUTHORIZED_IMPORT: {i.imod}")

def checkLiftRefutation (closedBases : List LeanMod) (upperSpec refuteMod : LeanMod) : IO (List QName) := do
  witnessBoundary closedBases upperSpec refuteMod
  let snap ← checkRefutation closedBases (stubOf upperSpec) refuteMod [``False]
  unless snap.declaredAxioms.isEmpty do throw (IO.userError "DISALLOWED_AXIOM_VIOLATION: refutation")
  let culprits := extractCulpritBaseUnits closedBases snap
  if culprits.isEmpty then throw (IO.userError "NO_BASE_CULPRIT: proof does not depend on a base unit")
  return culprits

private def encEndpoint (e : EndpointLift) : SExpr :=
  .list [encNames e.baseUnits, encNames e.upperUnits, encName e.squareUnit, encNames e.requiredRefs]

private def decEndpoint : SExpr → Option EndpointLift
  | .list (bs :: us :: sq :: rest) => do
    let names := fun e => decNames e <|> (([·]) <$> decName e)
    let rs ← match rest with | [] => some [] | [r] => decNames r | _ => none
    return ⟨← names bs, ← names us, ← decName sq, rs⟩
  | _ => none

mutual
  def encodeLiftSpec (s : LiftSpec) : SExpr :=
    match s with
    | .liftSpecTree b u cs es => .list [.sym "lift", encName b, encName u, .list (encLifts cs), .list (es.map encEndpoint)]
  termination_by structural s

  private def encLifts (cs : List ChildLift) : List SExpr :=
    match cs with
    | [] => []
    | .mkChildLift b u none :: xs => .list [encName b, encName u] :: encLifts xs
    | .mkChildLift b u (some s) :: xs => .list [encName b, encName u, encodeLiftSpec s] :: encLifts xs
    | .moveChildLifts bs us ss :: xs => .list [.sym "move", encNames bs, encNames us, .list (encSubLifts ss)] :: encLifts xs
  termination_by structural cs

  private def encSubLifts (ss : List LiftSpec) : List SExpr :=
    match ss with | [] => [] | s :: xs => encodeLiftSpec s :: encSubLifts xs
  termination_by structural ss
end

mutual
  def decodeLiftSpec (e : SExpr) : Option LiftSpec :=
    match e with
    | .list [.sym tag, b, u, .list cs, .list es] => do
      guard (tag == "lift" || tag == "lift-spec")
      return .liftSpecTree (← decName b) (← decName u) (← decLifts cs) (← es.mapM decEndpoint)
    | _ => none
  termination_by structural e

  private def decLifts (cs : List SExpr) : Option (List ChildLift) :=
    match cs with
    | [] => some []
    | .list [b,u] :: xs => return .mkChildLift (← decName b) (← decName u) none :: (← decLifts xs)
    | .list [b,u,s] :: xs => return .mkChildLift (← decName b) (← decName u) (some (← decodeLiftSpec s)) :: (← decLifts xs)
    | .list [.sym "move", bs, us, .list ss] :: xs => return .moveChildLifts (← decNames bs) (← decNames us) (← decSubLifts ss) :: (← decLifts xs)
    | _ => none
  termination_by structural cs

  private def decSubLifts (es : List SExpr) : Option (List LiftSpec) :=
    match es with | [] => some [] | x :: xs => return (← decodeLiftSpec x) :: (← decSubLifts xs)
  termination_by structural es
end

def LiftProblem.code : LiftProblem → String
  | .wrongBase => "wrongBase"
  | .wrongUpper => "wrongUpper"
  | .missingChildMap _ => "missingChildMap"
  | .missingChildImport _ => "missingChildImport"
  | .duplicateUpperChild _ => "duplicateUpperChild"
  | .invalidChildLift _ => "invalidChildLift"
  | .emptyLiftEndpoints _ => "emptyLiftEndpoints"
  | .missingBaseUnit _ => "missingBaseUnit"
  | .missingUpperUnit _ => "missingUpperUnit"
  | .missingSquare _ => "missingSquare"
  | .invalidSquare _ => "invalidSquare"

end Lojita.Transport
