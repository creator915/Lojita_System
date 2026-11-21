import Std.Data.HashMap
import Prism.StdScope
import Prism.TermMatrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.LensSlice`: Unit-SCC Optic Lens (`Lens.get`) & `--safe` Parameterized `SlowSlice.agda` Generator

Implements the module-internal unit decomposition
  `Whole ≅ FastFocus (F₁, F₂) ×_∂ SlowResidual (S)`
so that a single `coinductive` record, copattern definition, `with`-clause, or
multi-argument Foetus-recursive function no longer forces the rest of the file
(or downstream importing modules via `--guardedness` infection) off the Lean 4
fast lane:

1. **Unit Extraction**: Groups declarations of `CodeMod` into self-contained semantic
   units (`dataUnit`, `recUnit`, `funUnit`, `anonUnit`), keeping attached `open` /
   `fixity` directives with their owning type/record.
2. **Signature vs Body Dependency Graph & Condensation SCCs**: Tracks `sigRefs`
   (occurrences in type signatures, where definitional unfolding may be needed)
   separately from `bodyRefs` (term-level calls), and condenses mutual cycles into SCCs.
3. **Parameterized Residual Generation (`SlowSlice_<Mod>.agda`)**:
   - Drops 100% of downstream `F₂` units and unreferenced `F₁` units;
   - Abstracts term-only `F₁` computational dependencies as **Agda module parameters**
     `module _SlowResidual (f₁ : T₁) ... where` (`--safe`-compatible, zero `postulate`,
     zero re-typechecking of `F₁` bodies!);
   - Prunes unused `import`s (such as `IO` used only by `main` in `F₂`).
-/

namespace Prism

inductive UnitKind : Type where
  | dataUnit      : String → List Bind → Expr → List String → List (String × Expr) → UnitKind
  | recUnit       : String → List Bind → Expr → List String → RecDir → List (String × Expr) → UnitKind
  | funUnit       : Mods → String → Expr → List Clause → UnitKind
  | postulateUnit : Mods → String → Expr → UnitKind
  | patSynUnit    : String → List String → Pat → Expr → UnitKind
  | anonUnit      : Nat → Expr → List Clause → UnitKind

structure ModUnit : Type where
  uid           : Nat
  kind          : UnitKind
  definedCanons : List (List String)   -- all canonical paths introduced by this unit
  valueCanons   : List (List String)   -- functions + constructors + projections (unfoldable/callable)
  rawDecls      : List Decl            -- original declarations including trailing `open R`
  sigQNames     : List (List String)   -- canonical QNames referenced in type signatures
  bodyQNames    : List (List String)   -- canonical QNames referenced in clause LHS/RHS/`where`

-- §1 Collect Canonical `QName` References & Coinductive Construction Checks

/-- Traverse scoped terms, including patterns underneath lambdas, lets, with
    clauses and local declarations. Both name dependencies and field demand
    must see these nested consumers. -/
structure CodeVisitor (α : Type) where
  name : QName → List α
  pattern : Pat → List α := fun _ => []
  clausePatterns? : Option (RHS → List Decl → Pat → List α) := none

namespace CodeVisitor
variable {α : Type}
mutual
  partial def expr (v : CodeVisitor α) : Expr → List α
    | .def_ q      => v.name q
    | .con q       => v.name q
    | .app f a     => expr v f ++ expr v a.thing
    | .lam _ e     => expr v e
    | .lamT b e    => bind v b ++ expr v e
    | .lamCase cs  => cs.flatMap (clause v)
    | .pi b e      => bind v b ++ expr v e
    | .fun_ a e    => expr v a.thing ++ expr v e
    | .let_ bs e   => bs.flatMap (letBind v) ++ expr v e
    | .rec_ fs     => fs.flatMap (fun (_, val) => expr v val)
    | .recUpd r fs => expr v r ++ fs.flatMap (fun (_, val) => expr v val)
    | .dot e       => expr v e
    | _            => []

  partial def bind (v : CodeVisitor α) : Bind → List α
    | .bind _ _ t => expr v t

  partial def letBind (v : CodeVisitor α) : LetBind → List α
    | .letBind _ t e => expr v t ++ expr v e
    | .letPat p e    => pat v p ++ expr v e

  partial def pat (v : CodeVisitor α) : Pat → List α
    | p@(.conP q ps) => v.pattern p ++ v.name q ++ ps.flatMap (fun a => pat v a.thing)
    | .dotP e    => expr v e
    | .asP _ p   => pat v p
    | .projP q   => v.name q
    | p@(.recP fs) => v.pattern p ++ fs.flatMap (fun (_, p) => pat v p)
    | _          => []

  partial def lhs (v : CodeVisitor α) : LHS → List α
    | .head _ ps        => ps.flatMap (fun a => pat v a.thing)
    | .proj d inner ps  => v.name d ++ lhs v inner ++ ps.flatMap (fun a => pat v a.thing)
    | .with_ inner w ps =>
        lhs v inner ++
        w.flatMap (fun a => pat v a.thing) ++
        ps.flatMap (fun a => pat v a.thing)

  partial def rhs (v : CodeVisitor α) : RHS → List α
    | .rhs e           => expr v e
    | .absurdRHS       => []
    | .withRHS es cs   => es.flatMap (expr v) ++ cs.flatMap (clause v)
    | .rewriteRHS es r => es.flatMap (expr v) ++ rhs v r

  partial def clause (v : CodeVisitor α) : Clause → List α
    | .clause l r ws =>
      let patterns := v.clausePatterns?.map fun observe => { v with pattern := observe r ws }
      lhs (patterns.getD v) l ++ rhs v r ++ ws.flatMap (decl v)

  partial def decl (v : CodeVisitor α) : Decl → List α
    | .sig _ _ e         => expr v e
    | .fun_ _ _ cs       => cs.flatMap (clause v)
    | .dataSig _ _ bs e  => bs.flatMap (bind v) ++ expr v e
    | .dataDef _ _ _ cs  => cs.flatMap (fun (_, e) => expr v e)
    | .recSig _ _ bs e   => bs.flatMap (bind v) ++ expr v e
    | .recDef _ _ _ _ fs => fs.flatMap (fun (_, e) => expr v e)
    | .module_ _ bs ds   => bs.flatMap (bind v) ++ ds.flatMap (decl v)
    | .patSyn _ _ p e    => pat v p ++ expr v e
    | _                  => []
end

end CodeVisitor

private def nameVisitor : CodeVisitor (List String) where
  name q := q.full :: q.canonAlts
def collectExprQNames := CodeVisitor.expr nameVisitor
def collectBindQNames := CodeVisitor.bind nameVisitor
def collectLetQNames := CodeVisitor.letBind nameVisitor
def collectPatQNames := CodeVisitor.pat nameVisitor
def collectLHSQNames := CodeVisitor.lhs nameVisitor
def collectRHSQNames := CodeVisitor.rhs nameVisitor
def collectClauseQNames := CodeVisitor.clause nameVisitor
def collectDeclQNames := CodeVisitor.decl nameVisitor

mutual
  partial def exprHasRecLit : Expr → Bool
    | .rec_ _ | .recUpd _ _ => true
    | .app f a     => exprHasRecLit f || exprHasRecLit a.thing
    | .lam _ e     => exprHasRecLit e
    | .lamT b e    => bindHasRecLit b || exprHasRecLit e
    | .lamCase cs  => cs.any clauseHasRecLit
    | .pi b e      => bindHasRecLit b || exprHasRecLit e
    | .fun_ a e    => exprHasRecLit a.thing || exprHasRecLit e
    | .let_ bs e   => bs.any letHasRecLit || exprHasRecLit e
    | .dot e       => exprHasRecLit e
    | _            => false

  partial def bindHasRecLit : Bind → Bool
    | .bind _ _ t => exprHasRecLit t

  partial def letHasRecLit : LetBind → Bool
    | .letBind _ t e => exprHasRecLit t || exprHasRecLit e
    | .letPat _ e    => exprHasRecLit e

  partial def rhsHasRecLit : RHS → Bool
    | .rhs e           => exprHasRecLit e
    | .absurdRHS       => false
    | .withRHS es cs   => es.any exprHasRecLit || cs.any clauseHasRecLit
    | .rewriteRHS es r => es.any exprHasRecLit || rhsHasRecLit r

  partial def clauseHasRecLit : Clause → Bool
    | .clause _ r ws => rhsHasRecLit r || ws.any declHasRecLit

  partial def declHasRecLit : Decl → Bool
    | .sig _ _ e   => exprHasRecLit e
    | .fun_ _ _ cs => cs.any clauseHasRecLit
    | _            => false
end

def isMetaExpr : Expr → Bool
  | .meta_ => true
  | _      => false

-- Extract return target head canonical path of a type `T₁ → ... → R args`
partial def resultHeadCanon : Expr → Option (List String)
  | .pi _ body  => resultHeadCanon body
  | .fun_ _ body => resultHeadCanon body
  | e =>
      let (hd, _) := unrollApps e
      match hd with
      | .def_ q => some q.full
      | .con q  => some q.full
      | _       => none

-- §2 Partition `CodeMod.decls` into Header + Ordered `ModUnit`s

def extractModUnits (cm : CodeMod) : PrismOutcome (List Decl × List ModUnit) := do
  let pfx := cm.modName.full
  let mut sigMap : List (String × Mods × Expr) := []
  let mut dataSigMap : List (String × Mods × List Bind × Expr) := []
  let mut recSigMap : List (String × Mods × List Bind × Expr) := []
  let mut fixityMap : List (String × Decl) := []
  let mut funNames : List String := []

  for d in cm.decls do
    match d with
    | .sig m nm ty =>
        if nm != "_" then sigMap := (nm, m, ty) :: sigMap
    | .fun_ _ nm _ =>
        funNames := nm :: funNames
    | .dataSig m nm bs sortE =>
        dataSigMap := (nm, m, bs, sortE) :: dataSigMap
    | .recSig m nm bs sortE =>
        recSigMap := (nm, m, bs, sortE) :: recSigMap
    | .fixity a n op =>
        fixityMap := (op, .fixity a n op) :: fixityMap
    | _ => pure ()

  let lookupFixes (names : List String) : List Decl :=
    fixityMap.reverse.filterMap fun (op, fd) =>
      if names.contains op then some fd else none

  -- Collect local record/data opens (`open Stream public`) to attach to their owning `recUnit`/`dataUnit`
  let localOpenMap : List (String × List Decl) :=
    cm.decls.foldl (fun acc d =>
      match d with
      | .open_ q dir =>
          if q.full.take pfx.length == pfx && q.full.length == pfx.length + 1 then
            let targetNm := q.full.getLastD ""
            let prev := (acc.find? (fun (k, _) => k == targetNm)).map Prod.snd |>.getD []
            (targetNm, prev ++ [.open_ q dir]) :: acc.filter (fun (k, _) => k != targetNm)
          else acc
      | _ => acc) []

  let rec walk (rem : List Decl) (hdrAcc : List Decl) (uAcc : List ModUnit)
      (nextUid anonCnt : Nat) : PrismOutcome (List Decl × List ModUnit) :=
    match rem with
    | [] => .translated (hdrAcc.reverse, uAcc.reverse)
    | .pragma s :: rest =>
        walk rest (.pragma s :: hdrAcc) uAcc nextUid anonCnt
    | .import_ m o dir a :: rest =>
        walk rest (.import_ m o dir a :: hdrAcc) uAcc nextUid anonCnt
    | .open_ q dir :: rest =>
        -- Keep module opens of external modules in headers; local record opens attach to `recUnit`
        let hdrNext :=
          if !(q.full.take pfx.length == pfx && q.full.length == pfx.length + 1) then
            .open_ q dir :: hdrAcc
          else hdrAcc
        walk rest hdrNext uAcc nextUid anonCnt
    | .fixity _ _ _ :: rest =>
        walk rest hdrAcc uAcc nextUid anonCnt
    | .sig _ "_" ty :: .fun_ _ "_" cs :: rest =>
        let sRefs := (collectExprQNames ty).eraseDups
        let bRefs := (cs.flatMap collectClauseQNames).eraseDups
        let u : ModUnit :=
          { uid           := nextUid
          , kind          := .anonUnit anonCnt ty cs
          , definedCanons := []
          , valueCanons   := []
          , rawDecls      := [.sig plainMods "_" ty, .fun_ plainMods "_" cs]
          , sigQNames     := sRefs
          , bodyQNames    := bRefs }
        walk rest hdrAcc (u :: uAcc) (nextUid + 1) (anonCnt + 1)
    | .sig m nm ty :: rest =>
        if nm == "_" then
          let sRefs := (collectExprQNames ty).eraseDups
          let u : ModUnit :=
            { uid           := nextUid
            , kind          := .postulateUnit m s!"_anon_post_{nextUid}" ty
            , definedCanons := []
            , valueCanons   := []
            , rawDecls      := [.sig m "_" ty]
            , sigQNames     := sRefs
            , bodyQNames    := [] }
          walk rest hdrAcc (u :: uAcc) (nextUid + 1) anonCnt
        else if !funNames.contains nm then
          let canon := pfx ++ [nm]
          let fixes := lookupFixes [nm]
          let sRefs := (collectExprQNames ty).eraseDups
          let u : ModUnit :=
            { uid           := nextUid
            , kind          := .postulateUnit m nm ty
            , definedCanons := [canon]
            , valueCanons   := [canon]
            , rawDecls      := fixes ++ [.sig m nm ty]
            , sigQNames     := sRefs
            , bodyQNames    := [] }
          walk rest hdrAcc (u :: uAcc) (nextUid + 1) anonCnt
        else
          walk rest hdrAcc uAcc nextUid anonCnt
    | .dataSig _ _ _ _ :: rest | .recSig _ _ _ _ :: rest =>
        walk rest hdrAcc uAcc nextUid anonCnt
    | .dataDef m dNm pNames cons :: rest =>
        match dataSigMap.find? (fun (k, _, _, _) => k == dNm) with
        | none => .syntaxErr s!"missing data signature for '{dNm}'"
        | some (_, ms, params, sortE) =>
            let dCanon := pfx ++ [dNm]
            let cCanons := cons.map (fun (cNm, _) => dCanon ++ [cNm])
            let fixes := lookupFixes (dNm :: cons.map Prod.fst)
            let opens := (localOpenMap.find? (fun (k, _) => k == dNm)).map Prod.snd |>.getD []
            let sRefs :=
              (params.flatMap collectBindQNames ++ collectExprQNames sortE ++
               cons.flatMap (fun (_, cTy) => collectExprQNames cTy)).eraseDups
            let u : ModUnit :=
              { uid           := nextUid
              , kind          := .dataUnit dNm params sortE pNames cons
              , definedCanons := dCanon :: cCanons
              , valueCanons   := cCanons
              , rawDecls      := fixes ++ [.dataSig ms dNm params sortE, .dataDef m dNm pNames cons] ++ opens
              , sigQNames     := sRefs
              , bodyQNames    := [] }
            walk rest hdrAcc (u :: uAcc) (nextUid + 1) anonCnt
    | .recDef m rNm pNames rd flds :: rest =>
        match recSigMap.find? (fun (k, _, _, _) => k == rNm) with
        | none => .syntaxErr s!"missing record signature for '{rNm}'"
        | some (_, ms, params, sortE) =>
            let rCanon := pfx ++ [rNm]
            let cCanons := match rd.constr with
              | some cNm => [pfx ++ [cNm]]
              | none     => []
            let fCanons := flds.map (fun (fNm, _) => rCanon ++ [fNm])
            let fixes := lookupFixes (rNm :: (rd.constr.toList ++ flds.map Prod.fst))
            let opens := (localOpenMap.find? (fun (k, _) => k == rNm)).map Prod.snd |>.getD []
            let sRefs :=
              (params.flatMap collectBindQNames ++ collectExprQNames sortE ++
               flds.flatMap (fun (_, fTy) => collectExprQNames fTy)).eraseDups
            let u : ModUnit :=
              { uid           := nextUid
              , kind          := .recUnit rNm params sortE pNames rd flds
              , definedCanons := rCanon :: (cCanons ++ fCanons)
              , valueCanons   := cCanons ++ fCanons
              , rawDecls      := fixes ++ [.recSig ms rNm params sortE, .recDef m rNm pNames rd flds] ++ opens
              , sigQNames     := sRefs
              , bodyQNames    := [] }
            walk rest hdrAcc (u :: uAcc) (nextUid + 1) anonCnt
    | .patSyn synNm args rPat rExpr :: rest =>
        let sCanon := pfx ++ [synNm]
        let fixes := lookupFixes [synNm]
        let sRefs := (collectPatQNames rPat ++ collectExprQNames rExpr).eraseDups
        let u : ModUnit :=
          { uid           := nextUid
          , kind          := .patSynUnit synNm args rPat rExpr
          , definedCanons := [sCanon]
          , valueCanons   := [sCanon]
          , rawDecls      := fixes ++ [.patSyn synNm args rPat rExpr]
          , sigQNames     := sRefs
          , bodyQNames    := [] }
        walk rest hdrAcc (u :: uAcc) (nextUid + 1) anonCnt
    | .fun_ m fNm cs :: rest =>
        let (ms, sigTy, hasExplicitSig) : Mods × Expr × Bool :=
          match sigMap.find? (fun (k, _, _) => k == fNm) with
          | some (_, ms0, ty0) => (ms0, ty0, !isMetaExpr ty0)
          | none               => (plainMods, .meta_, false)
        if !hasExplicitSig && (cs.length != 1 || !(match cs.head? with | some (.clause (.head _ []) _ _) => true | _ => false)) then
          .syntaxErr s!"missing signature for '{fNm}'"
        else
          let fCanon := pfx ++ [fNm]
          let fixes := lookupFixes [fNm]
          let sRefs := (collectExprQNames sigTy).eraseDups
          let bRefs := (cs.flatMap collectClauseQNames).eraseDups
          let combinedMods : Mods :=
            { isPrivate  := m.isPrivate || ms.isPrivate
            , isInstance := m.isInstance || ms.isInstance
            , isAbstract := m.isAbstract || ms.isAbstract
            , termCheck  := if m.termCheck != .check then m.termCheck else ms.termCheck }
          let rawSig : List Decl := if hasExplicitSig then [.sig combinedMods fNm sigTy] else []
          let u : ModUnit :=
            { uid           := nextUid
            , kind          := .funUnit combinedMods fNm sigTy cs
            , definedCanons := [fCanon]
            , valueCanons   := [fCanon]
            , rawDecls      := fixes ++ rawSig ++ [.fun_ combinedMods fNm cs]
            , sigQNames     := sRefs
            , bodyQNames    := bRefs }
          walk rest hdrAcc (u :: uAcc) (nextUid + 1) anonCnt
    | .unsupported _ :: rest =>
        walk rest hdrAcc uAcc nextUid anonCnt
    | _ :: _ =>
        .bot "unsupported top-level declaration construct routed to Agda"

  let (headers, units) ← walk cm.decls [] [] 0 0
  -- Preserve top-level fixities not claimed by a local unit in headers
  let claimedFixes := units.flatMap (fun u => u.rawDecls.filterMap fun | .fixity _ _ op => some op | _ => none)
  let unclaimedFixes := fixityMap.reverse.filterMap fun (op, fd) =>
    if claimedFixes.contains op then none else some fd
  .translated (headers ++ unclaimedFixes, units)

-- §3 Unit Dependency Graph & Kosaraju Strongly Connected Components

structure UnitGraph where
  signatures : Array (List Nat)
  dependencies : Array (List Nat)
  dependents : Array (List Nat)

def unitGraph (units : List ModUnit) : UnitGraph := Id.run do
  let owners := Std.HashMap.ofList <| units.flatMap fun u => u.definedCanons.map (·, u.uid)
  let mut signatures := #[]
  let mut dependencies := #[]
  let mut dependents := Array.replicate units.length []
  for u in units do
    let resolve (names : List (List String)) :=
      (names.filterMap (owners[·]?)).filter (· != u.uid) |>.eraseDups
    let sig := resolve u.sigQNames
    let both := (sig ++ resolve u.bodyQNames).eraseDups
    signatures := signatures.push sig
    dependencies := dependencies.push both
    for target in both do dependents := dependents.modify target (u.uid :: ·)
  return ⟨signatures, dependencies, dependents.map List.reverse⟩

-- Kosaraju components in dependency order. Both DFS passes reuse the same index.
partial def UnitGraph.sccs (g : UnitGraph) : List (List Nat) :=
  let n := g.dependencies.size
  let adj (v : Nat) := g.dependencies[v]?.getD []
  let rec dfsPost (v : Nat) (vis : List Nat) (order : List Nat) : List Nat × List Nat :=
    if vis.contains v then (vis, order)
    else
      let vis1 := v :: vis
      let (vis2, order2) := (adj v).foldl (fun (vs, ord) d => dfsPost d vs ord) (vis1, order)
      (vis2, v :: order2)
  let (_, postOrder) := (List.range n).foldl (fun (vs, ord) v => dfsPost v vs ord) ([], [])
  let revAdj (d : Nat) := g.dependents[d]?.getD []
  let rec collectComp (v : Nat) (vis : List Nat) (comp : List Nat) : List Nat × List Nat :=
    if vis.contains v then (vis, comp)
    else
      let vis1 := v :: vis
      let (vis2, comp2) := (revAdj v).foldl (fun (vs, cp) w => collectComp w vs cp) (vis1, v :: comp)
      (vis2, comp2)
  let sortNats (xs : List Nat) : List Nat :=
    xs.foldl (fun acc x =>
      let (lt, ge) := acc.span (· < x)
      lt ++ (x :: ge)) []
  let (_, sccsRev) := postOrder.foldl (fun (vis, acc) v =>
    if vis.contains v then (vis, acc)
    else
      let (vis', comp) := collectComp v vis []
      (vis', sortNats comp :: acc)) ([], [])
  sccsRev

def computeUnitSCCs (units : List ModUnit) := (unitGraph units).sccs

structure SlicePlan : Type where
  headers          : List Decl
  units            : List ModUnit
  sccs             : List (List Nat)
  slowUnitIds      : List Nat
  fastUnitIds      : List Nat
  slowExportCanons : List (List String)  -- slow value/projection canons (tainting downstream `sigRefs`)
  coindRecCanons   : List (List String)  -- all coinductive record canons in scope
  checkedVariable? : Option String := none

def SlicePlan.hasSlowUnits (p : SlicePlan) : Bool :=
  !p.slowUnitIds.isEmpty

end Prism
