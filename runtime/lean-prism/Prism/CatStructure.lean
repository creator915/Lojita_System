import Lean
import Prism.AxiomFootprint
import Prism.DecodeSExpr
import Prism.LensSlice
import Prism.LoweringContext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Prism.CatStructure

inductive BasePt where | star

inductive BasePolyOp : List BasePt → BasePt → Type where
  | idOp : BasePolyOp [.star] .star
  | splitOp : BasePolyOp [.star] .star
  | gluePushoutOp : BasePolyOp [.star, .star, .star] .star
  | projectShellOp : BasePolyOp [.star] .star
  | consOp : BasePolyOp [.star, .star] .star
  | stepOp : BasePolyOp [.star] .star
  | compOp {xs ys zs : List BasePt} :
    BasePolyOp xs .star → BasePolyOp (ys ++ .star :: zs) .star → BasePolyOp (ys ++ xs ++ zs) .star

inductive SliceColor where | sharedBase | sweetMod | exoMod | mixMod
  deriving BEq, Repr
inductive DeclSort where | baseTypeDecl | pureSigHelperDecl | sweetBodyDecl | exoBodyDecl | boundaryHoleDecl
  deriving BEq, Repr
inductive EvalColor where | ghost | thunked | strictVal
  deriving BEq, Repr

/-- Include omitted implicits in declaration order, as in TranscodeIR.domains. -/
def portDomains : Expr → List (Arg Expr)
  | .pi (.bind h names t) body => names.map (fun n => ⟨h, some n, t⟩) ++ portDomains body
  | .fun_ a body => a :: portDomains body
  | _ => []

def erasedDomain : Expr → Bool
  | .pi _ body | .fun_ _ body => erasedDomain body
  | t => match (unrollApps t).1 with
    | .set _ => true
    | .def_ q => q.full == ["Agda","Primitive","Prop"] || q.full == ["Agda","Builtin","Equality","_≡_"]
    | _ => false

private def clausePorts : LHS → List (Arg Pat)
  | .head _ ps => ps
  | .with_ l _ _ | .proj _ l _ => clausePorts l

private def alignPorts (ps : List (Arg Pat)) : List (Arg Expr) → List (Option Pat)
  | [] => []
  | a :: tail =>
    if let p :: rest := ps then
      if p.hid == a.hid && (p.label.isNone || p.label == a.label) then
        some p.thing :: alignPorts rest tail
      else none :: alignPorts ps tail
    else none :: tail.map fun _ => none

private def forcesPattern : Pat → Bool
  | .conP .. | .litP _ | .recP _ | .absurdP => true
  | .asP _ p => forcesPattern p
  | _ => false

/-- The operand positions unconditionally demanded by native scalar primitives.
    Conditional and short-circuit operators demand only their test. -/
private def demandedOperand (q : List String) (i : Nat) : Bool :=
  if q == ["Data","Bool","Base","if_then_else_"] || q == ["Data","Bool","Base","_∧_"] ||
      q == ["Data","Bool","Base","_∨_"] then i == 0
  else [["Agda","Builtin","Nat"], ["Agda","Builtin","Char"],
        ["Agda","Builtin","String"]].any (·.isPrefixOf q) ||
    [["Data","Bool","Base","not"], ["Data","String","Base","_++_"],
     ["Data","Nat","Base","_≤ᵇ_"], ["Data","Nat","Base","pred"]].contains q

private partial def strictScalarUse (x : String) (e : Expr) : Bool := Id.run do
  if let .var y := e then return x == y
  let (hd, args) := unrollApps e
  let q := match hd with | .def_ q | .con q => q.full | _ => []
  return (args.filter (·.hid == .visible)).zipIdx.any fun (a,i) =>
    demandedOperand q i && strictScalarUse x a.thing

/-- A source equation can return a primitive or a partial application of one.
    Its remaining function ports inherit demand at the corresponding position
    of that primitive, even when the equation binds no variables at all. -/
private def etaPrimitiveDemand (cs : List Clause) (port : Nat) : Bool := Id.run do
  let [.clause (.head _ ps) (.rhs e) []] := cs | return false
  let bound := (ps.filter (·.hid == .visible)).length
  if port < bound then return false
  let (.def_ q,args) := unrollApps e | return false
  return demandedOperand q.full ((args.filter (·.hid == .visible)).length + (port - bound))

/-- Positions where an ordered clause can return before a later clause
    inspects the argument. A constructor in the first row with an irrefutable
    prefix is invariably tested and needs no thunk. -/
structure DemandSplit where
  arity : Nat
  delayed : List Nat
  tests : Array (Array Bool)

def branchDemand (ty : Expr) (cs : List Clause) : Option DemandSplit := do
  let domains := portDomains ty
  let typedUses := collectVarsExpr ty
  guard (!(domains.any fun a => a.hid == .visible && a.label.any typedUses.contains))
  let tests ← cs.toArray.mapM fun
    | .clause (.head _ ps) (.rhs _) _ | .clause (.head _ ps) (.withRHS ..) _ =>
      let vs := ps.dropWhile (·.hid != .visible)
      if vs.all (·.hid == .visible) then some (vs.toArray.map (forcesPattern ·.thing)) else none
    | _ => none
  let first ← tests[0]?
  let arity := first.size
  guard (tests.all (·.size == arity) && (domains.filter (·.hid == .visible)).length == arity)
  let delayed := (List.range arity).filter fun k =>
    tests.any (fun row => row[k]? == some true) &&
    tests.any (fun row => row[k]? == some false) &&
    !(first[k]? == some true && !(first.extract 0 k).any id)
  guard (!delayed.isEmpty)
  return ⟨arity,delayed,tests⟩

/-- The checking projection describes each port even when the argument is absent.
    A single pattern match or a direct return witnesses demand in a single clause. -/
def formalPorts (ty : Expr) (clauses : List Clause := []) : Array EvalColor := Id.run do
  let domains := portDomains ty
  let (ps, returned) := match clauses with
    | [.clause lhs (.rhs e) _] =>
      (alignPorts (clausePorts lhs) domains, match e with | .var x => some x | _ => none)
    | _ => ([], none)
  return domains.zipIdx.toArray.map fun (a,i) =>
    if a.hid != .visible || erasedDomain a.thing then .ghost
    else if (ps[i]?.join).any (fun p => forcesPattern p ||
      (match p with | .varP x => returned == some x | _ => false)) then .strictVal
    else .thunked

/-- Execution exposes strict constructors to Lean's pattern compiler. Variables
    and wildcards on other ports retain their delayed representation through
    clause selection. Named indices occurring in subsequent types must remain
    available during dependent elaboration. -/
def executionPorts (ty : Expr) (clauses : List Clause) : Array EvalColor := Id.run do
  let domains := portDomains ty
  let patterns := clauses.map fun (.clause lhs _ _) => alignPorts (clausePorts lhs) domains
  let usedInType := collectVarsExpr ty
  let delayed := (branchDemand ty clauses).map (·.delayed) |>.getD []
  return (formalPorts ty clauses).zipIdx.map fun (c,i) =>
    let port := ((domains.take i).filter (·.hid == .visible)).length
    if c != .thunked then c
    else if etaPrimitiveDemand clauses port || (!delayed.contains port &&
        patterns.any (fun ps => (ps[i]?.join).any forcesPattern)) ||
        (domains[i]?.bind (·.label)).any usedInType.contains ||
        (!clauses.isEmpty && (patterns.zip clauses).all (fun (ps,clause) =>
          match ps[i]?.join, clause with
          | some (.varP x), .clause _ (.rhs e) _ => strictScalarUse x e
          | _, _ => false)) then .strictVal
    else .thunked

inductive T1Color where
  | moduleColor (slice : SliceColor)
  | portColor (port : EvalColor)
  deriving BEq, Repr

/-- All source ports carry their pre-typecheck argument, including erased arguments. -/
structure ExprPort (color : EvalColor) where
  argument : Arg Expr
  expectedType : Option Expr

namespace TotalPorts

def Fiber (sliceIR : SliceColor → Type) (portIR : EvalColor → Type) : T1Color → Type
  | .moduleColor c => sliceIR c
  | .portColor c => portIR c

abbrev SourceFiber (sliceIR : SliceColor → Type) := Fiber sliceIR ExprPort

end TotalPorts

/-- Parenthesized typed contexts retain the order of both input and output ports. -/
inductive Ports (Color : Type) where
  | empty
  | port (c : Color)
  | tensor (left right : Ports Color)

namespace Ports
variable {Color : Type}

def values (fiber : Color → Type) : Ports Color → Type
  | .empty => Unit
  | .port c => fiber c
  | .tensor s t => values fiber s × values fiber t

def bases : Ports Color → List BasePt
  | .empty => []
  | .port _ => [.star]
  | .tensor s t => s.bases ++ t.bases

abbrev Arrow (fiber : Color → Type) (s t : Ports Color) := s.values fiber → t.values fiber

structure Lifted (fiber : Color → Type) (s t : Ports Color) (_op : BasePolyOp s.bases .star) where
  apply : Arrow fiber s t

def cut {fiber : Color → Type} {p q r s : Ports Color} {c : Color}
    (f : Arrow fiber p (.tensor q (.port c))) (g : Arrow fiber (.tensor (.port c) r) s) :
    Arrow fiber (.tensor p r) (.tensor q s) :=
  fun (x,other) => let (y,v) := f x; (y, g (v,other))

end Ports

def PreTCPoint.canonicalRoundtrip (p : PreTCPoint) (dump : String → Option CodeMod) : Bool :=
  let src := match p.surface with | .authored s | .synthesized s => s
  (dump src).any fun decoded => encodeCanonicalMod decoded == encodeCanonicalMod p.code

structure LeanPreTCCmd where
  syntaxOf : Lean.TSyntax `command
  origin : QName
  declSort : DeclSort
  ports : Array EvalColor

structure LeanBaseSlice where
  commands : Array LeanPreTCCmd

/-- Compare canonical names obtained from the kernel. A forbidden axiom wins
    even if a malformed caller includes it in its boundary declarations. -/
def guardAxiomsAssuming (allowed footprint : Array Lean.Name) : Bool :=
  let forbidden : Array Lean.Name :=
    #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx, `trustMeAx, `unsafePrimAx,
      `primTrustMe, `Agda.Builtin.TrustMe.primTrustMe]
  footprint.all fun ax => !forbidden.contains ax && allowed.contains ax

/-- Guard obligations refer to the declaration produced by elaborating this command.
    The footprint is read from the kernel environment when discharging the obligation. -/
structure GuardedFastCmd (originModule : QName) (allowedBoundaryAxioms : Array Lean.Name) extends LeanPreTCCmd

private def kernelNameOf? (originModule q : QName) : Option Lean.Name := do
  guard (originModule.full.isPrefixOf q.full && originModule.full.length < q.full.length)
  let ns := Lean.Name.str .anonymous (leanModNamespace originModule.full)
  if let [anon] := q.full.drop originModule.full.length then
    if anon.startsWith "_#" then
      if let some i := (anon.drop 2).toString.toNat? then return ns.str ("_ag_anon_test_" ++ toString i)
  return (q.full.drop originModule.full.length).foldl (fun n s => Lean.Name.str n (leanMangleIdent s)) ns

private def GuardedFastCmd.checkWithRoots {originModule : QName} {allowed : Array Lean.Name}
    (d : GuardedFastCmd originModule allowed) (base? : Option Lean.Environment)
    (complete : Lean.NameMap (Array Lean.Name)) :
    Lean.CoreM (Lean.NameMap (Array Lean.Name)) := do
  let some kernelName := kernelNameOf? originModule d.origin |
    throwError "declaration outside its originating module: {fullDot d.origin}"
  let env ← Lean.getEnv
  let some info := env.checked.get.find? kernelName | throwError "missing kernel declaration {kernelName}"
  -- The partial recursor is a separate declaration. Its public name has an
  -- opaque inhabited value in the kernel and can have an empty axiom footprint.
  let partialRec := env.find? (Lean.Compiler.mkUnsafeRecName kernelName)
  unless !info.isUnsafe && !info.isPartial && !partialRec.any Lean.ConstantInfo.isPartial &&
      (match info with
       | .inductInfo _ => d.declSort == .baseTypeDecl
       | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
       | _ => false) do
    throwError "missing checked fast declaration {kernelName}"
  let footprint := collectRootAxioms env complete kernelName base?
  unless guardAxiomsAssuming allowed footprint do
    throwError "disallowed axiom in {kernelName}: {footprint}"
  return complete.insert kernelName footprint

def GuardedFastCmd.checkAfterElaboration {originModule : QName} {allowed : Array Lean.Name}
    (d : GuardedFastCmd originModule allowed) : Lean.CoreM Unit :=
  discard <| d.checkWithRoots none {}

structure LeanOpenSlice where
  originModule : QName
  sharedBase : LeanBaseSlice
  boundaryDecls : Array LeanPreTCCmd
  allowedBoundaryAxioms : Array Lean.Name
  fast : Array (GuardedFastCmd originModule allowedBoundaryAxioms)
  /-- Elaboration order of the SCCs; guards refer to the resulting kernel declarations. -/
  ordered : Array LeanPreTCCmd := #[]

def LeanOpenSlice.checkAfterElaboration (s : LeanOpenSlice)
    (base? : Option Lean.Environment := none) : Lean.CoreM Unit :=
  discard <| s.fast.foldlM (fun complete d => d.checkWithRoots base? complete) {}

structure AgdaResidualPoint where
  residualCode : CodeMod
  upstreamShells : Array CodeMod
  sharedBodies : List QName := []

structure PushoutSplitPlan where
  sharedBase : CodeMod
  leanSliceSpec : CodeMod
  agdaResidual? : Option AgdaResidualPoint
  boundaryLeanAssumes : List QName
  boundaryAgdaAssumes : List QName
  /-- Agda record constructors live beside the record. Their public Lean
      declarations live inside its namespace. Both paths come from the
      scoped declaration of the owning record. -/
  leanRecordConstructors : List (List String × List String) := []

private abbrev Path := List String

structure ImportScope where
  moduleName : QName
  isOpen : Bool
  directive : Directive

/-- Declaration fragments sharing a canonical owner, with dependencies of their
    enclosing module parameters. Display spellings do not participate in lookup. -/
structure UnitInfo where
  name : QName
  decls : List Decl
  contextRefs : List (List String)
  imports : List ImportScope
  imported : Bool

private inductive Fragment where
  | owned (key : Path) (decl : Decl)
  | ambient (decl : Decl)
  | imported (scope : ImportScope) (assumptions : List Fragment)
  | section_ (key : Path) (name : String) (params : List Bind) (children : List Fragment)

private def named : Decl → Option String
  | .sig _ n _ | .fun_ _ n _ | .dataSig _ n _ _ | .dataDef _ n _ _
  | .recSig _ n _ _ | .recDef _ n _ _ _ | .patSyn n _ _ _ => some n
  | _ => none

private def isOptions (s : String) := (s.splitOn " ").head? == some "OPTIONS"

private partial def indexBlock (scope : Path) (ds : List Decl) : List Fragment := Id.run do
  let mut anon := 0
  let mut fragments := #[]
  for (d, i) in ds.zipIdx do
    let key (n : String) := scope ++ [n]
    match d with
    | .module_ n bs sub => fragments := fragments.push (.section_ (key n) n bs (indexBlock (key n) sub))
    | .import_ q isOpen dir ds =>
      fragments := fragments.push (.imported ⟨q,isOpen,dir⟩ (indexBlock q.full ds))
    | .variable_ vs =>
      for (n, t) in vs do fragments := fragments.push (.owned (key n) (.variable_ [(n,t)]))
    | .sig _ "_" _ =>
      fragments := fragments.push (.owned (key s!"_#{anon}") d)
      anon := anon + 1
    | .fun_ _ "_" _ => fragments := fragments.push (.owned (key s!"_#{anon-1}") d)
    | .unsupported _ => fragments := fragments.push (.owned (scope ++ ["", toString i]) d)
    | .pragma s =>
      if isOptions s then fragments := fragments.push (.ambient d)
      else fragments := fragments.push (.owned (scope ++ ["", toString i]) d)
    | _ =>
      fragments := fragments.push (match named d with | some n => .owned (key n) d | none => .ambient d)
  return fragments.toList

private structure UnitIndex where
  entries : Array UnitInfo := #[]
  positions : Std.HashMap Path Nat := ∅

private partial def gather (fs : List Fragment) (ctx : List Path) (enclosing : List ImportScope)
    (interface : Bool) (acc : UnitIndex) : UnitIndex :=
  let imports := fs.filterMap (fun | .imported i _ => some i | _ => none) ++ enclosing
  fs.foldl (init := acc) fun us f =>
    match f with
    | .ambient _ => us
    | .imported _ sub => gather sub [] imports true us
    | .section_ _ _ bs sub => gather sub (ctx ++ bs.flatMap collectBindQNames) imports interface us
    | .owned key d =>
      if interface && (match d with | .fun_ .. => true | _ => false) then us
      else if let some i := us.positions[key]? then
        {us with entries := us.entries.modify i (fun u => {u with decls := u.decls ++ [d]})}
      else
        ⟨us.entries.push ⟨mkQ key, [d], ctx, imports, interface⟩, us.positions.insert key us.entries.size⟩

private def isBody : Decl → Bool | .fun_ .. => true | _ => false

private def sigRefs (u : UnitInfo) : List Path :=
  u.contextRefs ++ u.decls.flatMap fun d => match d with
    | .fun_ .. => []
    | .variable_ vs => vs.flatMap (collectExprQNames ·.2)
    | _ => collectDeclQNames d

private def ownedPaths (u : UnitInfo) : List Path :=
  u.name.full :: u.decls.flatMap fun d => match d with
    | .dataDef _ _ _ cs => cs.map fun (c,_) => u.name.full ++ [c]
    | .recDef _ _ _ rd fs => (fs.map fun (f,_) => u.name.full ++ [f]) ++
        (rd.constr.toList.map fun c => u.name.full.dropLast ++ [c])
    | _ => []

private def lhsName : LHS → Path
  | .head q _ => q.full
  | .proj _ l _ | .with_ l _ _ => lhsName l

-- Dumped heads carry the actual anonymous/named where-module path.
private partial def whereNames (scope : Path) (ds : List Decl) : List Path :=
  let heads := ds.flatMap fun
    | .fun_ _ n cs => cs.filterMap fun (.clause lhs _ _) =>
      let p := lhsName lhs
      if p.getLast? == some n then some p else none
    | _ => []
  let inferred := (heads.head?.map List.dropLast).getD scope
  heads ++ ds.flatMap fun d => match d with
    | .module_ n _ sub => whereNames (inferred ++ [n]) sub
    | _ => (named d).toList.flatMap fun n => ownedPaths ⟨mkQ (inferred ++ [n]), [d], [], [], false⟩

mutual
  private partial def freeClauseRefs (scope : Path) : Clause → List Path
    | .clause lhs rhs ws =>
      let locals := whereNames (scope ++ ["_"]) ws
      (collectLHSQNames lhs ++ freeRhsRefs scope rhs ++ ws.flatMap (freeDeclRefs scope)).filter (!locals.contains ·)

  private partial def freeRhsRefs (scope : Path) : RHS → List Path
    | .withRHS es cs => es.flatMap collectExprQNames ++ cs.flatMap (freeClauseRefs scope)
    | .rewriteRHS es r => es.flatMap collectExprQNames ++ freeRhsRefs scope r
    | r => collectRHSQNames r

  private partial def freeDeclRefs (scope : Path) : Decl → List Path
    | .fun_ _ _ cs => cs.flatMap (freeClauseRefs scope)
    | .module_ n bs ds => bs.flatMap collectBindQNames ++ ds.flatMap (freeDeclRefs (scope ++ [n]))
    | d => collectDeclQNames d
end

private def bodyRefs (u : UnitInfo) :=
  (u.decls.filter isBody).flatMap (freeDeclRefs u.name.full.dropLast)

private def copattern : LHS → Bool
  | .proj .. => true
  | .head _ ps => ps.any fun p => match p.thing with | .projP .. => true | _ => false
  | .with_ l _ _ => copattern l

mutual
  private partial def exoticDecl : Decl → Bool
    | .unsupported _ => true
    | .pragma s => !isOptions s
    | .sig m _ _ | .dataSig m _ _ _ | .dataDef m _ _ _ | .recSig m _ _ _ => m.termCheck != .check
    | .recDef m _ _ rd _ => rd.coind || m.termCheck != .check
    | .fun_ m _ cs => m.termCheck != .check || cs.any exoticClause
    | .module_ _ _ ds => ds.any exoticDecl
    | _ => false

  private partial def exoticClause : Clause → Bool
    | .clause lhs rhs ws => copattern lhs || exoticRhs rhs || ws.any exoticDecl

  private partial def exoticRhs : RHS → Bool
    | .withRHS _ cs => cs.any exoticClause
    | .rewriteRHS _ r => exoticRhs r
    | _ => false
end

private def initialSort (pred : UnitInfo → Option String) (u : UnitInfo) : DeclSort :=
  let needsFoetus := u.decls.any fun
    | .fun_ _ n cs => match analyzeFunctionRecursion u.name.full.dropLast n cs with
        | .translated _ => false
        | _ => true
    | _ => false
  if u.imported && u.decls.any exoticDecl then .boundaryHoleDecl
  else if !u.imported && (needsFoetus || u.decls.any exoticDecl || (pred u).isSome) then .exoBodyDecl
  else if u.decls.any (fun | .recSig .. | .recDef .. | .dataDef .. | .dataSig .. => true | _ => false) then .baseTypeDecl
  else if u.decls.any (fun | .patSyn .. => true | _ => false) then .pureSigHelperDecl
  else if u.decls.any isBody then .sweetBodyDecl
  else .boundaryHoleDecl

private def sharedSort : DeclSort → Bool | .baseTypeDecl | .pureSigHelperDecl => true | _ => false

/-- Index owners before taking closures. A constructor or record projection is
    a reference to its declaring unit. Repeated occurrences cost one graph edge. -/
private structure DependencyGraph where
  owners : Std.HashMap Path Path := ∅
  signatures : Std.HashMap Path (List Path) := ∅
  bodies : Std.HashMap Path (List Path) := ∅
  externalSignatures : Std.HashMap Path (List Path) := ∅
  externalBodies : Std.HashMap Path (List Path) := ∅

private def dependencies (us : List UnitInfo) : DependencyGraph := Id.run do
  let mut owners := ∅
  let mut locals : Std.HashSet Path := ∅
  for u in us do
    for k in ownedPaths u do
      owners := owners.insert k u.name.full
      if !u.imported then locals := locals.insert k
  let resolve (refs : List Path) := (refs.filterMap (fun p => owners[p]?)).eraseDups
  let external (refs : List Path) := (refs.filter (!locals.contains ·)).eraseDups
  let mut graph : DependencyGraph := {owners}
  for u in us do
    let key := u.name.full
    let sig := sigRefs u
    let body := bodyRefs u
    graph := {graph with
      signatures := graph.signatures.insert key (resolve sig)
      bodies := graph.bodies.insert key (resolve body)
      externalSignatures := graph.externalSignatures.insert key (external sig)
      externalBodies := graph.externalBodies.insert key (external body)}
  return graph

private def DependencyGraph.reachable (g : DependencyGraph) (seeds : List Path)
    (openBody : Path → Bool) : Std.HashSet Path := Id.run do
  let mut pending := seeds.filterMap fun p => g.owners[p]?
  let mut seen := ∅
  while let p :: rest := pending do
    pending := rest
    unless seen.contains p do
      seen := seen.insert p
      pending := g.signatures.getD p [] ++ pending
      if openBody p then pending := g.bodies.getD p [] ++ pending
  return seen

private def stdProofHead (q : Path) : Bool :=
  [["Agda", "Builtin", "Equality"], ["Relation", "Binary"], ["Relation", "Unary"],
   ["Data", "List", "Relation"]].any (·.isPrefixOf q) ||
  [["Data", "Nat", "Base", "_<_"], ["Data", "Nat", "Base", "_≤_"],
   ["Data", "Integer", "Base", "_<_"], ["Data", "Integer", "Base", "_≤_"],
   ["Data", "Bool", "Base", "T"], ["Data", "Empty", "⊥"]].contains q

/-- A constructor with a visible payload (for instance an indexed table's
    entry) computes data. Recursive evidence and equality premises do not
    by themselves give an indexed family a payload. -/
private def proofConstructor (self : Path) : Expr → Bool
  | .pi (.bind hid _ ty) rest =>
    (hid != .visible || (resultHeadCanon ty).any (fun p => p == self || stdProofHead p)) &&
      proofConstructor self rest
  | .fun_ arg rest =>
    (arg.hid != .visible || (resultHeadCanon arg.thing).any (fun p => p == self || stdProofHead p)) &&
      proofConstructor self rest
  | _ => true

private def proofFamilies (us : List UnitInfo) (g : DependencyGraph) : Std.HashSet Path := Id.run do
  let indexed := us.filter fun u => u.decls.any
    (fun | .dataSig _ _ _ (.pi ..) | .dataSig _ _ _ (.fun_ ..) => true | _ => false)
  let candidates := Std.HashSet.ofList ((indexed.filter fun u => u.decls.any fun
    | .dataDef _ _ _ cs => cs.all (fun (_,ty) => proofConstructor u.name.full ty)
    | _ => false).map (·.name.full))
  -- Evidence inspected to return a value is computational. For example lookup
  -- in a suffix table follows the Suffix constructors supplied by joinSuffix.
  let mut families := candidates
  for u in us do
    let value := u.decls.any fun
      | .sig _ _ ty => !(resultHeadCanon ty).any (fun p => candidates.contains p || stdProofHead p)
      | _ => false
    if value then
      for d in u.decls do
        if let .fun_ _ _ cs := d then
          for .clause lhs _ _ in cs do
            for q in collectLHSQNames lhs do
              if let some owner := g.owners[q]? then families := families.erase owner
  return families

private def computational (evidence : Std.HashSet Path) (u : UnitInfo) : Bool :=
  u.decls.any fun
    | .sig _ _ ty => !(resultHeadCanon ty).any (fun p => evidence.contains p || stdProofHead p)
    | _ => false

private structure Analysis where
  fragments : List Fragment
  units : List UnitInfo
  byName : Std.HashMap Path UnitInfo
  graph : DependencyGraph
  sorts : Std.HashMap Path DeclSort
  evidence : Std.HashSet Path
  base : Std.HashSet Path

private def Analysis.sortOf (a : Analysis) (u : UnitInfo) : DeclSort :=
  a.sorts.getD u.name.full .boundaryHoleDecl

private def analyze (cm : CodeMod) (pred : UnitInfo → Option String) (demand : List Path := []) : Analysis := Id.run do
  let fs := indexBlock cm.modName.full cm.decls
  let us := (gather fs (cm.params.flatMap collectBindQNames) [] false {}).entries.toList
  let byName := Std.HashMap.ofList (us.map fun u => (u.name.full, u))
  let graph := dependencies us
  let raw := Std.HashMap.ofList (us.map fun u => (u.name.full, initialSort pred u))
  let evidence := proofFamilies us graph
  let canCopy := Std.HashSet.ofList ((us.filter fun u =>
    raw[u.name.full]? == some .sweetBodyDecl && computational evidence u).map (·.name.full))
  let exotic := (us.filter fun u => raw[u.name.full]? == some .exoBodyDecl).map (·.name.full)
  let active := graph.reachable (demand ++ exotic ++ us.flatMap (fun u => graph.signatures.getD u.name.full [])) fun p =>
    raw[p]? == some .exoBodyDecl || canCopy.contains p
  let sorts := us.foldl (init := raw) fun acc u =>
    if canCopy.contains u.name.full && active.contains u.name.full then
      acc.insert u.name.full .pureSigHelperDecl else acc
  -- A shared declaration must be independent of the omitted ports. Propagate
  -- exclusion through the graph, once per edge, rather than closing every unit.
  let mut reverse : Std.HashMap Path (List Path) := ∅
  for u in us do
    for d in graph.signatures.getD u.name.full [] ++ graph.bodies.getD u.name.full [] do
      reverse := reverse.insert d (u.name.full :: reverse.getD d [])
  let mut blocked := (us.filter fun u => !sharedSort (sorts.getD u.name.full .boundaryHoleDecl)).map (·.name.full)
  let mut base := Std.HashSet.ofList (us.map (·.name.full))
  while let p :: rest := blocked do
    blocked := rest
    if base.contains p then
      base := base.erase p
      blocked := reverse.getD p [] ++ blocked
  return ⟨fs, us, byName, graph, sorts, evidence, base⟩

private inductive Keep where | full | hole | drop
  deriving BEq

private def telescope (params : List Bind) (result : Expr) := params.foldr Expr.pi result

private def appliedType (key : Path) (params : List Bind) : Expr :=
  params.foldl (init := .def_ (mkQ key)) fun ty (.bind hid ns _) =>
    ns.foldl (init := ty) fun f x => .app f ⟨hid, none, .var x⟩

private def hiddenParams (params : List Bind) :=
  params.map fun (.bind _ xs ty) => Bind.bind .hidden xs ty

-- In a record field telescope the Abstract AST refers to earlier fields by
-- canonical QName. Instantiate those field occurrences when abstracting a record.
private partial def instantiateFields (bindings : List (Path × Expr)) (e : SExpr) : SExpr :=
  match e with
  | .list [.sym "def", q] =>
    ((decQ q).bind fun n => bindings.lookup n.full).map encExpr |>.getD e
  | .list xs => .list (xs.map (instantiateFields bindings))
  | _ => e

def fieldTy (bindings : List (Path × Expr)) (e : Expr) : Expr :=
  if bindings.isEmpty then e else (decExpr (instantiateFields bindings (encExpr e))).getD e

private def boundaryDecls (u : UnitInfo) (d : Decl) : List Decl := Id.run do
  let typeParams := u.decls.findSome? fun
    | .dataSig _ _ bs _ | .recSig _ _ bs _ => some bs
    | _ => none
  let params := typeParams.getD []
  let key := u.name.full
  let applied := appliedType key params
  match d with
  | .sig m n ty => return [.sig {m with termCheck := .check} n ty]
  | .variable_ vs => return [.variable_ vs]
  | .dataSig m n bs sort | .recSig m n bs sort => return [.sig {m with termCheck := .check} n (telescope bs sort)]
  | .dataDef m n _ cs =>
    let ctors := cs.map (fun (x,t) => Decl.sig {m with termCheck := .check} x (telescope (hiddenParams params) t))
    return if ctors.isEmpty then [] else [.module_ n [] ctors]
  | .recDef m n _ rd fields =>
    let m := {m with termCheck := TermCheck.check}
    -- A module parameter binds the receiver once for the entire field telescope.
    -- Inside the namespace, later field signatures can mention earlier fields.
    let projections := fields.map fun (f,ty) => Decl.sig m f ty
    let fieldModule := Decl.module_ n (hiddenParams params ++ [.bind .visible ["_"] applied]) projections
    let mut ctorBindings := []
    let mut ctorParams := #[]
    for (f,ty) in fields do
      ctorParams := ctorParams.push (.bind .visible [f] (fieldTy ctorBindings ty))
      ctorBindings := (key ++ [f], Expr.var f) :: ctorBindings
    let ctor := rd.constr.toList.map fun c => Decl.sig m c (telescope (hiddenParams params ++ ctorParams.toList) applied)
    return [fieldModule] ++ ctor
  | _ => return []

private def importUsed (refs : List Path) (q : QName) : Bool :=
  refs.any (q.full.isPrefixOf ·) ||
    match lookupStdModule (fullDot q) with
    | some syms => syms.any fun s => refs.contains s.canonPath
    | none => !refs.isEmpty -- an external interface may re-export any canonical name

private partial def renderFragments (a : Analysis) (take : UnitInfo → Keep) (scope : Path)
    (refs : List Path) (interface : Bool) (fs : List Fragment) : List Decl :=
  let keptOwner (key : Path) := (a.graph.owners[key]? >>= fun p => a.byName[p]?).any
    (fun u => take u != .drop)
  fs.flatMap fun f => match f with
    | .section_ key n bs sub =>
      let ds := renderFragments a take key refs interface sub
      if ds.isEmpty then [] else [.module_ n bs ds]
    | .imported i sub =>
      let ds := renderFragments a take i.moduleName.full refs true sub
      if !ds.isEmpty || importUsed refs i.moduleName then
        [.import_ i.moduleName i.isOpen i.directive ds]
      else []
    | .owned key d =>
      if interface && isBody d then [] else
      match a.byName[key]? with
      | none => []
      | some u => match take u with
        | .full => if interface && a.sortOf u == .boundaryHoleDecl then boundaryDecls u d else [d]
        | .hole => boundaryDecls u d
        | .drop => []
    | .ambient d =>
      match d with
      | .fixity _ _ x =>
        let exports := a.units.any fun u => u.name.full.dropLast == scope && take u != .drop &&
          (ownedPaths u).any (fun k => k.getLast? == some x)
        if exports then [d] else []
      | .open_ q _ =>
        if a.graph.owners.contains q.full then (if keptOwner q.full then [d] else [])
        else if a.units.any (fun u => q.full.isPrefixOf u.name.full) then
          (if a.units.any (fun u => q.full.isPrefixOf u.name.full && take u != .drop) then [d] else [])
        else if importUsed refs q then [d] else []
      | _ => [d]

private def externalRefs (cm : CodeMod) (a : Analysis) (take : UnitInfo → Keep) : List Path :=
  let params := (cm.params.flatMap collectBindQNames).filter fun q =>
    !(a.graph.owners[q]? >>= fun p => a.byName[p]?).any (!·.imported)
  (params ++ a.units.flatMap fun u =>
    let sig := a.graph.externalSignatures.getD u.name.full []
    match take u with
    | .full => sig ++ a.graph.externalBodies.getD u.name.full []
    | .hole => sig
    | .drop => []).eraseDups

private def slice (cm : CodeMod) (a : Analysis) (take : UnitInfo → Keep)
    (reexports : List Path := []) : CodeMod :=
  let refs := reexports ++ externalRefs cm a take
  {cm with decls := renderFragments a take cm.modName.full refs false a.fragments}

private def boundaryNames (a : Analysis) (take : UnitInfo → Keep) : List QName :=
  a.units.flatMap fun u =>
    if u.imported || u.decls.any (fun d => named d == some "_") then [] else
    match take u with
    | .hole => if u.decls.any (fun d => !(boundaryDecls u d).isEmpty) then (ownedPaths u).map mkQ else []
    | .full => if a.sortOf u == .boundaryHoleDecl && u.decls.any (fun d => d matches .sig ..) then [u.name] else []
    | .drop => []

private def visibleImport (i : ImportScope) (q : Path) : Bool :=
  let dir := i.directive
  let selected (n : String) := !(dir.dhiding.contains n) && (dir.dusing.all (·.contains n) || dir.drenaming.any (·.1 == n))
  i.moduleName.full.isPrefixOf q || i.isOpen &&
    (match lookupStdModule (fullDot i.moduleName) with
     | some syms => syms.any (fun s => s.canonPath == q && selected s.localName)
     | none => selected (q.getLastD ""))

private def validate (cm : CodeMod) (a : Analysis) : Except String Unit := do
  for u in a.units do
    for ref in sigRefs u ++ bodyRefs u do
      let localOwner := a.graph.owners[ref]?
      if cm.modName.full.isPrefixOf ref then
        unless localOwner.isSome do
          throw s!"undeclared local dependency {String.intercalate "." ref} in {fullDot u.name}"
      else unless ["Agda","Primitive"].isPrefixOf ref || u.imports.any (visibleImport · ref) do
        throw s!"out-of-scope dependency {String.intercalate "." ref} in {fullDot u.name}"

def requiresSafeAgda (cm : CodeMod) :=
  cm.decls.any fun | .pragma s => (s.splitOn " ").contains "--safe" | _ => false

private def splitAnalyzed (cm : CodeMod) (a : Analysis) : PushoutSplitPlan :=
  let exotics := (a.units.filter fun u => a.sortOf u == .exoBodyDecl).map (·.name.full)
  let active := a.graph.reachable exotics fun p => a.sorts[p]? != some .sweetBodyDecl
  let leanSide (u : UnitInfo) := if a.sortOf u == .exoBodyDecl then Keep.hole else .full
  let agdaSide (u : UnitInfo) :=
    if !active.contains u.name.full then Keep.drop
    else if a.sortOf u == .sweetBodyDecl then .hole else .full
  let sharedBodies := (a.units.filter (fun u => !u.imported && a.sortOf u == .pureSigHelperDecl)).map (·.name)
  let residual := if exotics.isEmpty then none else some ⟨slice cm a agdaSide, #[], sharedBodies⟩
  let recordCtors := a.units.flatMap fun u =>
    if u.imported || leanSide u != .hole then [] else
    u.decls.filterMap fun d => do
      let .recDef m _ _ rd _ := d | none
      guard (!m.isPrivate)
      let c ← rd.constr
      return (u.name.full.dropLast ++ [c], u.name.full ++ [c])
  ⟨slice cm a (fun u => if a.base.contains u.name.full then .full else .drop),
   slice cm a leanSide, residual, boundaryNames a leanSide, boundaryNames a agdaSide, recordCtors⟩

/-- Raw caller-constructed ASTs must satisfy the local and imported dependency obligations. -/
def checkedPushoutSplit (cm : CodeMod) (exoPred : UnitInfo → Option String) : Except String PushoutSplitPlan := do
  let a := analyze cm exoPred
  validate cm a
  return splitAnalyzed cm a

private def shellSelection (a : Analysis) (needed : List Path) : UnitInfo → Keep :=
  let otherBodies := Std.HashSet.ofList <| (a.units.filter fun u =>
    a.sortOf u == .exoBodyDecl && (computational a.evidence u || u.decls.any
      (fun | .dataDef .. | .recDef .. => true | _ => false))).map (·.name.full)
  let fullBody (p : Path) := sharedSort (a.sorts.getD p .boundaryHoleDecl) || otherBodies.contains p
  let active := a.graph.reachable needed fullBody
  fun u =>
    if !active.contains u.name.full then .drop
    else if fullBody u.name.full then .full else .hole

def projectUpstreamBaseShell (up : CodeMod) (needed : List QName) : CodeMod :=
  let a := analyze up (fun _ => none) (needed.map (·.full))
  slice up a (shellSelection a (needed.map (·.full)))

/-- A safe shell abstracts a referenced proof as a typed section parameter.
    A fresh one-field record lets Agda pass that parameter implicitly across
    module boundaries, including when two ports have the same signature. -/
private structure SafePort where
  origin : Path
  wrapper : String
  parameter : String
  deriving BEq

def kernelResidual (r : AgdaResidualPoint) (specification : Option (List String) := none) : AgdaResidualPoint := Id.run do
  let modules := r.upstreamShells.toList ++ [r.residualCode]
  let holesIn (cm : CodeMod) :=
    let bodies := cm.decls.filterMap fun | .fun_ _ n _ => some n | _ => none
    if specification.elim (requiresSafeAgda cm) (· == cm.modName.full) then cm.decls.filterMap (fun
      | .sig _ n _ => if bodies.contains n then none else some n
      | _ => none) else []
  if !modules.any (fun m => !(holesIn m).isEmpty) then return r
  let text := String.join (modules.map (renderSExpr ∘ encodeCodeMod))
  let mut fresh := "PrismCheckPort"
  while text.contains fresh do fresh := fresh ++ "X"
  let mut count := 0
  let mut available : List (Path × List SafePort) := []
  let mut executable := #[]
  for (cm, i) in modules.zipIdx do
    let imports := (cm.decls.flatMap allImportsInDecl).map (·.full)
    let incoming := ((available.filter fun (m,_) => imports.contains m).flatMap Prod.snd).eraseDups
    let holes := holesIn cm
    let mut ports := #[]
    for n in holes do
      let port : SafePort := ⟨cm.modName.full, fresh ++ toString count, fresh ++ "Arg" ++ toString count⟩
      ports := ports.push (n, port)
      count := count + 1
    let mut ds := []
    for d in cm.decls.reverse do
      match d with
      | .sig mods n ty =>
        if let some (_, port) := ports.find? (·.1 == n) then
          let wrapper := mkQ (cm.modName.full ++ [port.wrapper])
          let field := fresh ++ "Value"
          let param := Expr.var port.parameter
          let rhs := Expr.app (.def_ ⟨wrapper.full ++ [field], port.wrapper ++ "." ++ field, []⟩) (visArg param)
          let alias := Decl.fun_ mods n [.clause (.head (mkQ (cm.modName.full ++ [n])) []) (.rhs rhs) []]
          let section_ := Decl.module_ "_" [.bind .inst [port.parameter] (.def_ wrapper)] (d :: alias :: ds)
          let sort := Expr.def_ ⟨["Agda","Primitive","Setω"], fresh ++ "Prim.Setω", []⟩
          ds := [.recSig {} port.wrapper [] sort, .recDef {} port.wrapper [] {} [(field,ty)], section_]
        else ds := d :: ds
      | _ => ds := d :: ds
    if !incoming.isEmpty then
      let mut extra := #[]
      let mut binders := #[]
      for p in incoming do
        let alias := fresh ++ "From" ++ p.wrapper
        extra := extra.push (.import_ ⟨p.origin, alias, []⟩ false {} [])
        let wrapper := Expr.def_ ⟨p.origin ++ [p.wrapper], alias ++ "." ++ p.wrapper, []⟩
        binders := binders.push (.bind .inst [p.parameter] wrapper)
      let (options, rest) := ds.partition fun | .pragma s => isOptions s | _ => false
      ds := options ++ extra.toList ++ [.module_ "_" binders.toList rest]
    if !ports.isEmpty then
      ds := .import_ ⟨["Agda","Primitive"], fresh ++ "Prim", []⟩ false {} [] :: ds
    available := (cm.modName.full, incoming ++ ports.toList.map Prod.snd) :: available
    let cm := {cm with decls := ds}
    if i == r.upstreamShells.size then return {r with residualCode := cm, upstreamShells := executable}
    executable := executable.push cm
  return r

/-- Split a canonical pre-typecheck module supplied by the scope checker. For
    a standalone safe module, materialize the residual as a section telescope. -/
def computePushoutSplit (cm : CodeMod) (exoPred : UnitInfo → Option String)
    (forSafeKernel : Bool := false) : PushoutSplitPlan :=
  let split := splitAnalyzed cm (analyze cm exoPred)
  if forSafeKernel then {split with agdaResidual? := split.agdaResidual?.map kernelResidual} else split

private partial def pruneShellImports (known : List Path) (live : List (Path × Option (List String))) :
    List Decl → List Decl := fun ds => ds.filterMap fun d =>
  let directive (q : Path) (dir : Directive) : Option Directive := do
    if !known.contains q then return dir
    let names ← live.lookup q
    let some ns := names | return dir
    return {dir with dusing := dir.dusing.map (·.filter ns.contains),
                     dhiding := dir.dhiding.filter ns.contains,
                     drenaming := dir.drenaming.filter (ns.contains ·.1)}
  match d with
  | .import_ q o dir ds => (directive q.full dir).map fun dir => .import_ q o dir ds
  | .open_ q dir => (directive q.full dir).map fun dir => .open_ q dir
  | .module_ n bs ds => some (.module_ n bs (pruneShellImports known live ds))
  | _ => some d

def AgdaResidualPoint.projectImports (r : AgdaResidualPoint) (upstream : Array CodeMod)
    (forSafeKernel : Bool := false) : AgdaResidualPoint := Id.run do
  let downstream := analyze r.residualCode (fun _ => none) (r.sharedBodies.map (·.full))
  let mut demand := externalRefs r.residualCode downstream (fun _ => .full)
  let mut shells := []
  let mut exports := []
  for up in upstream do
    if let .translated exp := synthesizeExportedModule exports up then exports := exp :: exports
  let mut imports := (r.residualCode.decls.flatMap allImportsInDecl).map (·.full)
  let mut live := []
  -- Walking in reverse dependency order also handles re-exporting modules
  -- whose only contribution is the path through which a symbol is in scope.
  for up in upstream.toList.reverse do
    if imports.contains up.modName.full then
      let symbols := (exports.find? (·.modPath == up.modName.full)).map (·.symbols)
      let reexports := demand.filter fun q => !up.modName.full.isPrefixOf q &&
        symbols.any (fun syms => syms.any (·.canonPath == q))
      if !reexports.isEmpty || demand.any (up.modName.full.isPrefixOf ·) then
        let a := analyze up (fun _ => none) demand
        let take := shellSelection a demand
        let shell := slice up a take reexports
        let preserved := reexports ++ (a.units.filter (fun u => take u != .drop)).flatMap ownedPaths
        let names := symbols.map fun syms =>
          (syms.filter fun s => preserved.contains s.canonPath).map (·.localName)
        shells := shell :: shells
        live := (up.modName.full, names) :: live
        imports := (shell.decls.flatMap allImportsInDecl).map (·.full) ++ imports
        demand := (demand ++ externalRefs up a take).eraseDups
  let known := upstream.toList.map (·.modName.full)
  let trim (m : CodeMod) := {m with decls := pruneShellImports known live m.decls}
  let projected := {r with residualCode := trim r.residualCode, upstreamShells := shells.toArray.map trim}
  return if forSafeKernel then kernelResidual projected else projected

def PushoutSplitPlan.leanBoundaryPorts (p : PushoutSplitPlan) : Array (List String × Lean.Name) :=
  p.boundaryLeanAssumes.toArray.filterMap fun q => do
    let origin := p.leanSliceSpec.modName
    let canonical ← kernelNameOf? origin q
    let some mapped := p.leanRecordConstructors.lookup q.full | return (q.full,canonical)
    let name ← kernelNameOf? origin (mkQ mapped)
    return (q.full,name)

def PushoutSplitPlan.allowedBoundaryAxioms (p : PushoutSplitPlan) : Array Lean.Name :=
  p.leanBoundaryPorts.map Prod.snd

private def loadFixture (dir dump : System.FilePath) (name : String) : IO CodeMod := do
  let src := dir / (name ++ ".agda")
  let stdlib := (← IO.getEnv "AGDA_STDLIB").getD "/usr/share/agda-stdlib"
  let result ← IO.Process.output {
    cmd := dump.toString
    args := #["-i", dir.toString, "-i", stdlib, src.toString]
    env := #[("AGDA_DIR", some dir.toString), ("TMPDIR", some dir.toString)]}
  unless result.exitCode == 0 do throw <| IO.userError s!"dump of {name} failed: {result.stderr}"
  let some cm := parseSExprText result.stdout >>= decodeCodeMod
    | throw <| IO.userError s!"invalid pre-typecheck dump for {name}"
  unless cm.modName.full == [name] do throw <| IO.userError s!"unexpected module in {name} dump"
  return cm

private def assertCheck (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw <| IO.userError s!"categorical self-check failed: {label}"

private def checkShared (cm : CodeMod) : IO PushoutSplitPlan := do
  let plan ← IO.ofExcept (checkedPushoutSplit cm (fun _ => none))
  let some r := plan.agdaResidual? | throw <| IO.userError "missing exotic residual"
  let body (m : CodeMod) (n : String) := m.decls.filterMap fun
    | d@(.fun_ _ x _) => if x == n then some (encDecl d) else none
    | _ => none
  let h := body cm "h"
  assertCheck (!h.isEmpty && [plan.sharedBase, plan.leanSliceSpec, r.residualCode].all
    (fun m => body m "h" == h)) "shared helper clauses"
  assertCheck (!(body cm "f").isEmpty && !(body cm "g").isEmpty && body plan.leanSliceSpec "f" == body cm "f" &&
    (body plan.leanSliceSpec "g").isEmpty && (body r.residualCode "f").isEmpty &&
    body r.residualCode "g" == body cm "g") "fast and exotic bodies"
  return plan

-- In this variant h occurs exclusively in the copattern body. No declaration
-- signature can promote it on behalf of the residual.
private def checkBodyDemand (cm : CodeMod) : IO Unit := do
  let boolTrue := Expr.con (mkQ ["Agda","Builtin","Bool","Bool","true"])
  let stream := Expr.def_ (mkQ (cm.modName.full ++ ["Stream"]))
  let decls := cm.decls.filterMap fun
    | .sig _ "f" _ | .fun_ _ "f" _ => none
    | .sig m "g" (.pi b _) => some (.sig m "g" (.pi b (.app stream (visArg boolTrue))))
    | d => some d
  let cm := {cm with decls}
  let plan := computePushoutSplit cm (fun _ => none)
  let some r := plan.agdaResidual? | throw (IO.userError "missing copattern residual")
  let some h := cm.decls.find? (fun | .fun_ _ "h" _ => true | _ => false)
    | throw (IO.userError "missing h clauses")
  assertCheck ([plan.sharedBase, plan.leanSliceSpec, r.residualCode].all fun m =>
    m.decls.any (fun d => encDecl d == encDecl h)) "body-only demand shares the computational helper"

private def checkScopedNames : IO Unit := do
  let q := mkQ ["Scope","f"]
  let missing := mkQ ["Scope","f","missing"]
  let clause (d : QName) (e : Expr) (ds : List Decl) := Clause.clause (.head d []) (.rhs e) ds
  let check (ref : QName) (ds : List Decl) :=
    let cm := CodeMod.mk (mkQ ["Scope"]) [] [.sig {} "f" (.set 1), .fun_ {} "f" [clause q (.def_ ref) ds]]
    match checkedPushoutSplit cm (fun _ => none) with | .ok _ => true | .error _ => false
  assertCheck (!check missing []) "undeclared child of the current name"
  let h := mkQ ["Scope","_","helper"]
  let ws := [Decl.sig {} "helper" (.set 1), .fun_ {} "helper" [clause h (.set 0) []]]
  assertCheck (check h ws && !check missing ws) "only declared where-local names discharge references"
  let nested := mkQ ["M","N","f"]
  assertCheck ((kernelNameOf? (mkQ ["M"]) nested) != (kernelNameOf? (mkQ ["M","N"]) nested) &&
    (kernelNameOf? (mkQ ["Other"]) nested).isNone) "nested canonical namespaces"

private def checkForeignBoundaries (foreignMod : CodeMod) : IO Unit := do
  let cm := CodeMod.mk (mkQ ["Importer"]) [] [.import_ foreignMod.modName false {} foreignMod.decls]
  let plan := computePushoutSplit cm (fun _ => none)
  assertCheck (plan.boundaryLeanAssumes.isEmpty && plan.allowedBoundaryAxioms.isEmpty &&
    plan.agdaResidual?.isNone) "an imported coinductive interface cannot discharge local Lean axioms"
  let foreignName := mkQ (foreignMod.modName.full ++ ["Stream"])
  assertCheck ({plan with boundaryLeanAssumes := [foreignName]}.allowedBoundaryAxioms.isEmpty)
    "foreign boundary names cannot be mapped into the local namespace"

private def checkImportedHelper (up down : CodeMod) : IO Unit := do
  let k := mkQ ["Types","idTy"]
  let h := mkQ (up.modName.full ++ ["h"])
  let a := mkQ (up.modName.full ++ ["A"])
  let klhs := LHS.head k [visArg (.varP "X")]
  let kBody := Decl.fun_ {} "idTy" [.clause klhs (.rhs (.var "X")) []]
  let lib := CodeMod.mk (mkQ ["Types"]) [] [.sig {} "idTy" (.fun_ (visArg (.set 0)) (.set 0)), kBody]
  let hBody := Decl.fun_ {} "h" [.clause (.head h []) (.rhs (.app (.def_ k) (visArg (.def_ a)))) []]
  let up' := {up with decls := [.import_ lib.modName false {} []] ++ up.decls ++ [.sig {} "h" (.set 0), hBody]}
  let down' := {down with decls := down.decls.map fun
    | .sig m "g" (.fun_ domain result) => .sig m "g" (.fun_ {domain with thing := .def_ h} result)
    | d => d}
  let some r := (computePushoutSplit down' (fun _ => none)).agdaResidual?
    | throw <| IO.userError "g requires an exotic slice"
  let shells := (r.projectImports #[lib,up']).upstreamShells
  let member (m : CodeMod) (d : Decl) :=
    shells.any fun shell => shell.modName.full == m.modName.full && shell.decls.any (fun x => encDecl x == encDecl d)
  assertCheck (member up hBody && member lib kBody) "downstream index unfolds upstream helpers across two imports"

private def checksFrom (repo stage : System.FilePath) : IO Unit := do
  let fixture := loadFixture stage (repo / "dump/dump")
  let ref := "(q \"Agda.Builtin.List.List._∷_\" \"_∷_\" \"Data.List.Relation.Unary.All.All._∷_\")"
  let wire := s!"(module \"Candidate\" (params) (sig (mods) \"x\" (con {ref})))"
  let some point := (parseSExprText wire >>= (decodeSurfacePoint · (.authored "module Candidate where")))
    | throw (IO.userError "invalid overloaded QName dump")
  let [overload] := point.ambTable | throw (IO.userError "missing overloaded QName in surface IR")
  assertCheck (fullDot overload.primaryQ == "Agda.Builtin.List.List._∷_" &&
    overload.canonAlts == [["Data", "List", "Relation", "Unary", "All", "All", "_∷_"]] &&
    (renderSExpr (encodeCodeMod point.code)).contains ref &&
    !(encodeCanonicalMod point.code).contains "Data.List.Relation.Unary.All")
    "preserve overloaded constructor candidates outside canonical equality"
  checkScopedNames
  let specName := mkQ ["Spec"]
  let spec : CodeMod := ⟨specName, [], [.sig {} "A" (.set 0),
    .recSig {} "Stream" [] (.set 0),
    .recDef {} "Stream" [] {coind := true, constr := some "build"} [("tail",.def_ (mkQ ["Spec","Stream"]))]]⟩
  let ports := (computePushoutSplit spec (fun _ => none)).leanBoundaryPorts
  let expected := [(["Spec","A"],["Spec","A"]), (["Spec","Stream"],["Spec","Stream"]),
    (["Spec","build"],["Spec","Stream","build"]), (["Spec","Stream","tail"],["Spec","Stream","tail"])]
  assertCheck (ports.size == expected.length && expected.all (fun (path, kernel) =>
    ports.toList.lookup path == kernelNameOf? specName (mkQ kernel))) "exact authored and generated kernel ports"
  let dangling : CodeMod := ⟨mkQ ["Dangling"], [], [.sig {} "f" (.def_ (mkQ ["Dangling","A"]))]⟩
  assertCheck (match checkedPushoutSplit dangling (fun _ => none) with | .error _ => true | .ok _ => false) "missing local dependency"
  let shared ← fixture "SharedPureHelperSig"
  let _ ← checkShared shared
  checkBodyDemand shared
  let up ← fixture "M0"
  let down ← fixture "M1"
  checkForeignBoundaries down
  checkImportedHelper up down
  let some r := (computePushoutSplit down (fun _ => none)).agdaResidual?
    | throw <| IO.userError "M1 residual missing"
  let #[shell] := (r.projectImports #[up]).upstreamShells
    | throw <| IO.userError "M1 must have one upstream shell"
  let dataA (m : CodeMod) := m.decls.filterMap fun
    | d@(.dataSig _ "A" ..) | d@(.dataDef _ "A" ..) => some (encDecl d)
    | _ => none
  let proofBody (m : CodeMod) := m.decls.any fun | .fun_ _ "surrogateBound" _ => true | _ => false
  assertCheck (proofBody up && (dataA up).length == 2 && dataA shell == dataA up &&
    !shell.decls.any (fun d => named d == some "surrogateBound")) "minimal upstream shell"
  -- Explicit import metadata may come from a full upstream AST. It is an interface:
  -- its fast clauses cannot flow back into a residual, even through nested imports.
  let withAssumes := {down with decls := down.decls.map fun
    | .import_ q o d _ => Decl.import_ q o d (if q.full == up.modName.full then up.decls else [])
    | d => d}
  let some r' := (computePushoutSplit withAssumes (fun _ => none)).agdaResidual?
    | throw <| IO.userError "missing residual for explicit import interface"
  let assumptions := r'.residualCode.decls.findSome? fun
    | .import_ q _ _ ds => if q.full == up.modName.full then some ds else none
    | _ => none
  assertCheck (assumptions.any (fun ds => !(proofBody {up with decls := ds}) &&
    (dataA {up with decls := ds}) == dataA up)) "bodyless imported assumptions"
  let proofShell := projectUpstreamBaseShell up [mkQ ["M0","surrogateBound"]]
  assertCheck (!proofBody proofShell && proofShell.decls.any (fun | .sig _ "surrogateBound" _ => true | _ => false) &&
    (dataA proofShell).isEmpty) "explicitly requested fast theorem is bodyless"
  let plan ← checkShared (← fixture "HybridDirtyAxiomNeg")
  let modPath := plan.leanSliceSpec.modName.full
  let names := plan.boundaryLeanAssumes.map (·.full)
  let expected := [["Stream"], ["Stream","head"], ["Stream","tail"], ["g"]].map (modPath ++ ·)
  assertCheck (names.length == expected.length && expected.all names.contains) "exact hybrid boundary names"
  let allowed := plan.allowedBoundaryAxioms
  assertCheck (guardAxiomsAssuming allowed allowed &&
    !guardAxiomsAssuming allowed (allowed.push ``Classical.choice) &&
    !guardAxiomsAssuming (allowed.push `trustMeAx) #[`trustMeAx] &&
    !guardAxiomsAssuming allowed #[`unrelatedBoundary]) "hybrid axiom guard"

/-- The command may run outside the checkout's current directory. The built Prism
    executable and the corpus belong to the same checkout. -/
def runCatSelfChecks : IO Unit := do
  let exe ← IO.appPath
  let rec findRoot : List System.FilePath → IO System.FilePath
    | [] => throw <| IO.userError "cannot locate the CodeTransport fixture directory"
    | p :: ps => do
      if ← (p / "Test/gron-stress/corpus/curated/hybrid").isDir then return p
      findRoot ps
  let cwd ← IO.currentDir
  let mut candidates := [cwd]
  let mut parent := exe.parent
  while let some p := parent do
    candidates := p :: candidates
    parent := p.parent
  let repo ← findRoot candidates
  let tmp := repo / "tmp"
  IO.FS.createDirAll tmp
  let staging ← IO.Process.output {cmd := "mktemp", args := #["-d", (tmp / "cat-self.XXXXXXXX").toString]}
  unless staging.exitCode == 0 do throw <| IO.userError staging.stderr
  let stage := System.FilePath.mk staging.stdout.trimAscii.toString
  try
    for name in ["SharedPureHelperSig", "M0", "M1", "HybridDirtyAxiomNeg"] do
      let f := name ++ ".agda"
      IO.FS.writeFile (stage / f) (← IO.FS.readFile (repo / "Test/gron-stress/corpus/curated/hybrid" / f))
    checksFrom repo stage
  finally
    IO.FS.removeDirAll stage

end Prism.CatStructure
