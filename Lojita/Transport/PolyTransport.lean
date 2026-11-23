import Lojita.Transport.Plan

namespace Lojita.Transport
open Lean Lojita.Kernel Lojita.Store

structure PolySquareSpec where
  polySquareRefs ::
  oldUnits : List QName
  newUnits : List QName
  squareUnit : QName
  requiredRefs : List QName := []
  deriving BEq, Repr

def polySquare (os ns : List QName) (sq : QName) : PolySquareSpec := ⟨os, ns, sq, []⟩

mutual
  inductive TransportSpec where
    | transportSpecTree (oldMod newMod : QName) (children : List ChildMove) (squares : List PolySquareSpec)
  inductive ChildMove where
    | keepChild (oldChild newChild : QName)
    | moveChildren (sources targets : List QName) (subs : List TransportSpec)
end

def TransportSpec.oldMod : TransportSpec → QName | .transportSpecTree o _ _ _ => o
def TransportSpec.newMod : TransportSpec → QName | .transportSpecTree _ n _ _ => n
def TransportSpec.childMoves : TransportSpec → List ChildMove | .transportSpecTree _ _ cs _ => cs
def TransportSpec.squares : TransportSpec → List PolySquareSpec | .transportSpecTree _ _ _ ss => ss

def ChildMove.sources : ChildMove → List QName
  | .keepChild o _ => [o]
  | .moveChildren os _ _ => os

def ChildMove.targets : ChildMove → List QName
  | .keepChild _ n => [n]
  | .moveChildren _ ns _ => ns

def directKeeps (t : TransportSpec) : List (QName × QName) :=
  t.childMoves.filterMap fun | .keepChild o n => some (o,n) | _ => none

mutual
  private def collectKeeps (s : TransportSpec) (acc : Array (QName × QName)) : Array (QName × QName) :=
    match s with | .transportSpecTree _ _ cs _ => collectKeptChildren cs acc
  termination_by structural s

  private def collectKeptChildren (cs : List ChildMove) (acc : Array (QName × QName)) : Array (QName × QName) :=
    match cs with
    | [] => acc
    | .keepChild o n :: rest => collectKeptChildren rest (acc.push (o,n))
    | .moveChildren _ _ ss :: rest => collectKeptChildren rest (collectKeptSubs ss acc)
  termination_by structural cs

  private def collectKeptSubs (ss : List TransportSpec) (acc : Array (QName × QName)) : Array (QName × QName) :=
    match ss with | [] => acc | s :: rest => collectKeptSubs rest (collectKeeps s acc)
  termination_by structural ss
end

def keptPairs (t : TransportSpec) := (collectKeeps t #[]).toList

inductive PolyTransportProblem where
  | wrongOldMod | wrongNewMod
  | unaccountedOldChild (q : QName)
  | missingTargetChildImport (q : QName)
  | duplicateTargetChild (q : QName)
  | invalidChildMove (q : QName)
  | emptySquareEndpoints (q : QName)
  | missingOldEndpoint (q : QName)
  | missingNewEndpoint (q : QName)
  | missingPolySquare (q : QName)
  | invalidPolySquare (q : QName)
  deriving BEq, Repr

def duplicates {α : Type} [BEq α] [Hashable α] (xs : List α) : List α := Id.run do
  let mut once : Std.HashSet α := {}
  let mut repeated := #[]
  for x in xs do
    if once.contains x then repeated := repeated.push x else once := once.insert x
  return distinct repeated.toList

def endpointNames (m : LeanMod) := Std.HashSet.ofList ((m.units ++ externalUnits m).flatMap (·.definedNames))

def polyRelations : List Name := [``Eq, `LojitaCtx.PolyTransport.PortRel,
  `LojitaCtx.PolyTransport.TransportsPoly, `LojitaCtx.PolyTransport.Transports₁, `LojitaCtx.PolyTransport.Transports₂]

/-- Follow definitions mentioned by the type, including generated equation helpers.
    Proof bodies of the square itself cannot supply missing endpoints. -/
def typeMentions (snap : Snapshot) (ty : Expr) (required : List QName) : NameSet := Id.run do
  let mut todo := ty.getUsedConstantsAsSet.toList
  let mut seen : NameSet := {}
  let mut missing := NameSet.ofList (required.map QName.toLeanName)
  while !missing.isEmpty do
    let n :: rest := todo | break
    todo := rest
    if seen.contains n then continue
    seen := seen.insert n
    missing := missing.erase n
    if snap.owners.contains n || n.getRoot == `LojitaCtx then
      if let some info := snap.env.find? n then
        todo := info.getUsedConstantsAsSet.foldl (fun acc c => c :: acc) todo
  return seen

/-- Open the telescope with real local declarations before asking the kernel
    about its result. This also handles a dependent codomain and local lets. -/
private def squareResult (env : Environment) (ty : Expr) : Bool × Option Name := go ty {} #[]
where
  go (e : Expr) (lctx : LocalContext) (xs : Array Expr) : Bool × Option Name :=
    match e with
    | .forallE n t b bi =>
      let id : FVarId := ⟨Name.num `square xs.size⟩
      go b (lctx.mkLocalDecl id n (t.instantiateRev xs) bi) (xs.push (.fvar id))
    | .letE _ _ v b _ => go b lctx (xs.push (v.instantiateRev xs))
    | e =>
      let e := e.instantiateRev xs
      let head := e.getAppFn.constName?
      let wh := (Lean.Kernel.whnf env lctx e).toOption
      let prop := ((Lean.Kernel.check env lctx e) >>= Lean.Kernel.whnf env lctx).toOption.any (·.isProp)
      (prop && wh.any (fun t => !t.isSort && !t.getAppFn.constName?.any [``True, ``PUnit, ``Unit].contains), head)
  termination_by structural e

def validSquareType (snap : Snapshot) (c : ConstantInfo) (relations : List Name) (refs : List QName) :=
  let (prop, head) := squareResult snap.env c.type
  prop && (!refs.isEmpty || head.any relations.contains)

def publicSquare (snap : Snapshot) (q : QName) : Option ConstantInfo := do
  let n := q.toLeanName
  guard (!isPrivateName n && snap.constants.contains n && !snap.declaredAxioms.contains n)
  snap.env.find? n

def polyShapeProblems (oldImpl candImpl : LeanMod) (ts : TransportSpec) :
    List PolyTransportProblem := Id.run do
  let mut errors := #[]
  if ts.oldMod != oldImpl.modName then errors := errors.push .wrongOldMod
  if ts.newMod != candImpl.modName then errors := errors.push .wrongNewMod
  let os := Std.HashSet.ofList (ts.childMoves.flatMap ChildMove.sources)
  let ns := ts.childMoves.flatMap ChildMove.targets
  for i in oldImpl.imports do
    if !i.assumes.isEmpty && !os.contains i.imod then errors := errors.push (.unaccountedOldChild i.imod)
  let available := Std.HashSet.ofList (candImpl.imports.map (·.imod))
  for q in distinct ns do unless available.contains q do errors := errors.push (.missingTargetChildImport q)
  for q in duplicates ns do errors := errors.push (.duplicateTargetChild q)
  for move in ts.childMoves do
    if let .moveChildren src tgt subs := move then
      for s in subs do
        unless src.contains s.oldMod && tgt.contains s.newMod do errors := errors.push (.invalidChildMove s.newMod)
  return errors.toList

def checkPolyTransport (oldImpl candImpl specMod : LeanMod) (candSnap : Snapshot) (ts : TransportSpec) :
    List PolyTransportProblem := Id.run do
  let mut errors := (polyShapeProblems oldImpl candImpl ts).toArray
  let tested := withTests candImpl specMod
  if renderLeanMod candSnap.mod != renderLeanMod tested then return (errors.push .wrongNewMod).toList
  let before := endpointNames oldImpl
  let after := endpointNames tested
  for s in ts.squares do
    if s.oldUnits.isEmpty || s.newUnits.isEmpty then errors := errors.push (.emptySquareEndpoints s.squareUnit)
    let info := publicSquare candSnap s.squareUnit
    let refs := info.map (fun c => typeMentions candSnap c.type (s.oldUnits ++ s.newUnits ++ s.requiredRefs))
    for q in s.oldUnits do
      unless before.contains q && refs.all (·.contains q.toLeanName) do errors := errors.push (.missingOldEndpoint q)
    for q in s.newUnits do
      unless after.contains q && refs.all (·.contains q.toLeanName) do errors := errors.push (.missingNewEndpoint q)
    let some c := info | errors := errors.push (.missingPolySquare s.squareUnit); continue
    unless validSquareType candSnap c polyRelations s.requiredRefs &&
        s.requiredRefs.all (fun q => refs.any (·.contains q.toLeanName)) do
      errors := errors.push (.invalidPolySquare s.squareUnit)
  return errors.toList

private def encSquare (s : PolySquareSpec) : SExpr :=
  .list [.sym "square", encNames s.oldUnits, encNames s.newUnits, encName s.squareUnit, encNames s.requiredRefs]

private def decSquare : SExpr → Option PolySquareSpec
  | .list [.sym "square", os, ns, sq, rs] => return ⟨← decNames os, ← decNames ns, ← decName sq, ← decNames rs⟩
  | _ => none

mutual
  def encodeTransportSpec (s : TransportSpec) : SExpr :=
    match s with
    | .transportSpecTree o n cs ss =>
      .list [.sym "poly-transport", encName o, encName n, .list (encChildren cs), .list (ss.map encSquare)]
  termination_by structural s

  private def encChildren (cs : List ChildMove) : List SExpr :=
    match cs with
    | [] => []
    | .keepChild o n :: rest => .list [.sym "keep", encName o, encName n] :: encChildren rest
    | .moveChildren os ns subs :: rest =>
      .list [.sym "move", encNames os, encNames ns, .list (encTransports subs)] :: encChildren rest
  termination_by structural cs

  private def encTransports (ss : List TransportSpec) : List SExpr :=
    match ss with
    | [] => []
    | s :: rest => encodeTransportSpec s :: encTransports rest
  termination_by structural ss
end

mutual
  def decodeTransportSpec (e : SExpr) : Option TransportSpec :=
    match e with
    | .list [.sym tag, o, n, .list cs, .list ss] => do
      guard (tag == "poly-transport" || tag == "transport-spec")
      return .transportSpecTree (← decName o) (← decName n) (← decChildren cs) (← ss.mapM decSquare)
    | _ => none
  termination_by structural e

  private def decChildren (es : List SExpr) : Option (List ChildMove) :=
    match es with
    | [] => some []
    | .list [.sym "keep", o, n] :: xs => return .keepChild (← decName o) (← decName n) :: (← decChildren xs)
    | .list [.sym "move", os, ns, .list ss] :: xs =>
      return .moveChildren (← decNames os) (← decNames ns) (← decTransports ss) :: (← decChildren xs)
    | _ => none
  termination_by structural es

  private def decTransports (es : List SExpr) : Option (List TransportSpec) :=
    match es with
    | [] => some []
    | x :: xs => return (← decodeTransportSpec x) :: (← decTransports xs)
  termination_by structural es
end

def PolyTransportProblem.code : PolyTransportProblem → String
  | .wrongOldMod => "wrongOldMod"
  | .wrongNewMod => "wrongNewMod"
  | .unaccountedOldChild _ => "unaccountedOldChild"
  | .missingTargetChildImport _ => "missingTargetChildImport"
  | .duplicateTargetChild _ => "duplicateTargetChild"
  | .invalidChildMove _ => "invalidChildMove"
  | .emptySquareEndpoints _ => "emptySquareEndpoints"
  | .missingOldEndpoint _ => "missingOldEndpoint"
  | .missingNewEndpoint _ => "missingNewEndpoint"
  | .missingPolySquare _ => "missingPolySquare"
  | .invalidPolySquare _ => "invalidPolySquare"

end Lojita.Transport
