import Prism.Parser
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

mutual
  partial def collectExprQNames : Expr → List (List String)
    | .def_ q      => [q.full]
    | .con q       => [q.full]
    | .app f a     => collectExprQNames f ++ collectExprQNames a.thing
    | .lam _ e     => collectExprQNames e
    | .lamT b e    => collectBindQNames b ++ collectExprQNames e
    | .lamCase cs  => cs.flatMap collectClauseQNames
    | .pi b e      => collectBindQNames b ++ collectExprQNames e
    | .fun_ a e    => collectExprQNames a.thing ++ collectExprQNames e
    | .let_ bs e   => bs.flatMap collectLetQNames ++ collectExprQNames e
    | .rec_ fs     => fs.flatMap (fun (_, v) => collectExprQNames v)
    | .recUpd r fs => collectExprQNames r ++ fs.flatMap (fun (_, v) => collectExprQNames v)
    | .dot e       => collectExprQNames e
    | _            => []

  partial def collectBindQNames : Bind → List (List String)
    | .bind _ _ t => collectExprQNames t

  partial def collectLetQNames : LetBind → List (List String)
    | .letBind _ t e => collectExprQNames t ++ collectExprQNames e
    | .letPat p e    => collectPatQNames p ++ collectExprQNames e

  partial def collectPatQNames : Pat → List (List String)
    | .conP q ps => q.full :: ps.flatMap (fun a => collectPatQNames a.thing)
    | .dotP e    => collectExprQNames e
    | .asP _ p   => collectPatQNames p
    | .projP q   => [q.full]
    | .recP fs   => fs.flatMap (fun (_, p) => collectPatQNames p)
    | _          => []

  partial def collectLHSQNames : LHS → List (List String)
    | .head _ ps        => ps.flatMap (fun a => collectPatQNames a.thing)
    | .proj d inner ps  => d.full :: collectLHSQNames inner ++ ps.flatMap (fun a => collectPatQNames a.thing)
    | .with_ inner w ps =>
        collectLHSQNames inner ++
        w.flatMap (fun a => collectPatQNames a.thing) ++
        ps.flatMap (fun a => collectPatQNames a.thing)

  partial def collectRHSQNames : RHS → List (List String)
    | .rhs e           => collectExprQNames e
    | .absurdRHS       => []
    | .withRHS es cs   => es.flatMap collectExprQNames ++ cs.flatMap collectClauseQNames
    | .rewriteRHS es r => es.flatMap collectExprQNames ++ collectRHSQNames r

  partial def collectClauseQNames : Clause → List (List String)
    | .clause l r ws => collectLHSQNames l ++ collectRHSQNames r ++ ws.flatMap collectDeclQNames

  partial def collectDeclQNames : Decl → List (List String)
    | .sig _ _ e         => collectExprQNames e
    | .fun_ _ _ cs       => cs.flatMap collectClauseQNames
    | .dataSig _ _ bs e  => bs.flatMap collectBindQNames ++ collectExprQNames e
    | .dataDef _ _ _ cs  => cs.flatMap (fun (_, e) => collectExprQNames e)
    | .recSig _ _ bs e   => bs.flatMap collectBindQNames ++ collectExprQNames e
    | .recDef _ _ _ _ fs => fs.flatMap (fun (_, e) => collectExprQNames e)
    | .module_ _ bs ds   => bs.flatMap collectBindQNames ++ ds.flatMap collectDeclQNames
    | .patSyn _ _ p e    => collectPatQNames p ++ collectExprQNames e
    | _                  => []
end

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

def lhsHasCopatternOrWith : LHS → Bool
  | .head _ ps => ps.any (fun a => match a.thing with | .projP _ => true | _ => false)
  | .proj _ _ _ => true
  | .with_ _ _ _ => true

def isMetaExpr : Expr → Bool
  | .meta_ => true
  | _      => false

def clauseUsesExoticLHSOrRHS : Clause → Bool
  | .clause l r _ =>
      lhsHasCopatternOrWith l ||
      match r with
      | .withRHS _ _ | .rewriteRHS _ _ => true
      | _ => false

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

def findOwningUnit (units : List ModUnit) (qCanon : List String) : Option Nat :=
  units.findSome? fun u =>
    if u.definedCanons.contains qCanon then some u.uid else none

def unitLocalSigDeps (units : List ModUnit) (u : ModUnit) : List Nat :=
  (u.sigQNames.filterMap (findOwningUnit units)).filter (· != u.uid) |>.eraseDups

def unitLocalBodyDeps (units : List ModUnit) (u : ModUnit) : List Nat :=
  (u.bodyQNames.filterMap (findOwningUnit units)).filter (· != u.uid) |>.eraseDups

def unitLocalAllDeps (units : List ModUnit) (u : ModUnit) : List Nat :=
  (unitLocalSigDeps units u ++ unitLocalBodyDeps units u).eraseDups

-- Compute topological SCCs (dependencies come BEFORE dependents; mutual cycles grouped together)
partial def computeUnitSCCs (units : List ModUnit) : List (List Nat) :=
  let n := units.length
  let adj (v : Nat) : List Nat :=
    match units.find? (·.uid == v) with
    | some u => unitLocalAllDeps units u
    | none   => []
  let rec dfsPost (v : Nat) (vis : List Nat) (order : List Nat) : List Nat × List Nat :=
    if vis.contains v then (vis, order)
    else
      let vis1 := v :: vis
      let (vis2, order2) := (adj v).foldl (fun (vs, ord) d => dfsPost d vs ord) (vis1, order)
      (vis2, v :: order2)
  let (_, postOrder) := (List.range n).foldl (fun (vs, ord) v => dfsPost v vs ord) ([], [])
  let revAdj (d : Nat) : List Nat :=
    (List.range n).filter (fun v => (adj v).contains d)
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

structure SlicePlan : Type where
  headers          : List Decl
  units            : List ModUnit
  sccs             : List (List Nat)
  slowUnitIds      : List Nat
  fastUnitIds      : List Nat
  slowExportCanons : List (List String)  -- slow value/projection canons (tainting downstream `sigRefs`)
  coindRecCanons   : List (List String)  -- all coinductive record canons in scope

def SlicePlan.hasSlowUnits (p : SlicePlan) : Bool :=
  !p.slowUnitIds.isEmpty

-- §4 Agda Code Renderer for Minimal Parameterized `SlowSlice_<Mod>.agda`
--    (Mirrors `Code/Render.agda` 1-to-1; 100% `--safe` & `--guardedness` compatible!)

private def agdaIndent (n : Nat) (s : String) : String :=
  String.ofList (List.replicate n ' ') ++ s

private def agdaNameParts (s : String) : List String :=
  -- Strip optional qualifier prefix `Qual.` onto the first non-empty part
  let parts := s.splitOn "."
  match parts.reverse with
  | [] => [s]
  | lastSeg :: revQuals =>
      let rawParts := lastSeg.splitOn "_"
      if revQuals.isEmpty then rawParts
      else
        let qualPfx := String.intercalate "." revQuals.reverse ++ "."
        let rec attachQual : List String → List String
          | [] => []
          | "" :: rest => "" :: attachQual rest
          | p :: rest  => (qualPfx ++ p) :: rest
        attachQual rawParts

private def agdaOpHoles (s : String) : Nat :=
  (agdaNameParts s).length - 1

private def agdaMixfixFill (op : String) (args : List String) : Option String :=
  let h := agdaOpHoles op
  if h >= 1 && args.length == h then
    let rec go : List String → List String → String
      | p :: ps, a :: as =>
          let headPart := if p.isEmpty then a else p ++ " " ++ a
          let tailPart := go ps as
          if tailPart.isEmpty then headPart else headPart ++ " " ++ tailPart
      | [p], [] => p
      | _, _    => ""
    some (go (agdaNameParts op) args)
  else none

private def agdaSubscript (n : Nat) : String :=
  String.ofList ((toString n).toList.map fun c => Char.ofNat (c.toNat - 48 + 8320))

private def agdaEscapeStr (s : String) : String :=
  let rec go : List Char → List Char
    | [] => []
    | '"' :: cs  => '\\' :: '"' :: go cs
    | '\\' :: cs => '\\' :: '\\' :: go cs
    | '\n' :: cs => '\\' :: 'n' :: go cs
    | '\r' :: cs => '\\' :: 'r' :: go cs
    | '\t' :: cs => '\\' :: 't' :: go cs
    | c :: cs    => c :: go cs
  String.ofList (go s.toList)

private def renderAgdaLit : Lit → String
  | .natL n  => toString n
  | .strL s  => "\"" ++ agdaEscapeStr s ++ "\""
  | .charL c => if c == '\'' then "'\\''" else "'" ++ agdaEscapeStr (String.singleton c) ++ "'"

private def agdaBraces (h : Hiding) (lbl : Option String) (s : String) : String :=
  match h, lbl with
  | .visible, none   => s
  | .visible, some l => "(" ++ l ++ " = " ++ s ++ ")"
  | .hidden,  none   => "{" ++ s ++ "}"
  | .hidden,  some l => "{" ++ l ++ " = " ++ s ++ "}"
  | .inst,    none   => "{{" ++ s ++ "}}"
  | .inst,    some l => "{{" ++ l ++ " = " ++ s ++ "}}"

private def isAtomicAgdaExpr : Expr → Bool
  | .var _ | .def_ _ | .con _ | .lit _ | .set _ | .hole | .meta_ => true
  | _ => false

private def isAtomicAgdaPat : Pat → Bool
  | .varP _ | .wildP | .litP _ | .absurdP | .conP _ [] => true
  | _ => false

private def isInfixAgdaApp (e : Expr) : Bool :=
  let (hd, as) := unrollApps e
  let headOp : Option String := match hd with
    | .def_ q => some q.shown
    | .con q  => some q.shown
    | _       => none
  match headOp with
  | some op =>
      as.all (fun a => a.hid == .visible && a.label.isNone) &&
      agdaOpHoles op >= 1 && as.length == agdaOpHoles op
  | none => false

private def needsAgdaOperandParen : Expr → Bool
  | e@(.app _ _) => isInfixAgdaApp e
  | e            => !isAtomicAgdaExpr e

mutual
  partial def renderAgdaExpr (ind : Nat) : Expr → String
    | .var x       => x
    | .def_ q      => q.shown
    | .con q       => q.shown
    | .lit l       => renderAgdaLit l
    | .set 0       => "Set"
    | .set n       => "Set" ++ agdaSubscript n
    | .hole        => "?"
    | .meta_       => "_"
    | .dot e       => "." ++ renderAgdaArgPos ind e
    | .absurdLam .visible => "λ ()"
    | .absurdLam .hidden  => "λ {}"
    | .absurdLam .inst    => "λ {{}}"
    | .lamCase cs  =>
        let cLines := cs.flatMap (fun c =>
          match renderAgdaClause (ind + 4) false c with
          | l0 :: ls => (l0.replace " = " " → ") :: ls
          | []       => [])
        "λ where\n" ++ String.intercalate "\n" cLines
    | e@(.app _ _) =>
        let (hd, as) := unrollApps e
        let headOp : Option String := match hd with
          | .def_ q => some q.shown
          | .con q  => some q.shown
          | _       => none
        let allVis := as.all (fun a => a.hid == .visible && a.label.isNone)
        let opArgs := as.map (fun a => renderAgdaOperandPos ind a.thing)
        match headOp.bind (fun op => if allVis then agdaMixfixFill op opArgs else none) with
        | some mx => mx
        | none =>
            let hdStr := renderAgdaArgPos ind hd
            let argStrs := as.map (renderAgdaArgE ind)
            String.intercalate " " (hdStr :: argStrs)
    | .lam a body =>
        "λ " ++ agdaBraces a.hid a.label a.thing ++ " → " ++ renderAgdaExpr ind body
    | .lamT b body =>
        "λ " ++ renderAgdaBind ind b ++ " → " ++ renderAgdaExpr ind body
    | .pi b body =>
        renderAgdaBind ind b ++ " → " ++ renderAgdaExpr ind body
    | .fun_ a body =>
        let domS :=
          if a.hid == .visible && a.label.isNone then renderAgdaOperandPos ind a.thing
          else agdaBraces a.hid a.label (renderAgdaArgPos ind a.thing)
        domS ++ " → " ++ renderAgdaExpr ind body
    | .let_ bs body =>
        let bStrs := bs.map fun
          | .letBind x .meta_ rhs => x ++ " = " ++ renderAgdaExpr ind rhs
          | .letBind x ty rhs =>
              x ++ " : " ++ renderAgdaExpr ind ty ++ " ; " ++ x ++ " = " ++ renderAgdaExpr ind rhs
          | .letPat p rhs =>
              let pS := if isAtomicAgdaPat p then renderAgdaPat ind p else "(" ++ renderAgdaPat ind p ++ ")"
              pS ++ " = " ++ renderAgdaExpr ind rhs
        "let " ++ String.intercalate " ; " bStrs ++ " in " ++ renderAgdaExpr ind body
    | .rec_ fs =>
        let fStrs := fs.map (fun (n, v) => n ++ " = " ++ renderAgdaExpr ind v)
        "record { " ++ String.intercalate " ; " fStrs ++ " }"
    | .recUpd r fs =>
        let fStrs := fs.map (fun (n, v) => n ++ " = " ++ renderAgdaExpr ind v)
        "record " ++ renderAgdaArgPos ind r ++ " { " ++ String.intercalate " ; " fStrs ++ " }"

  partial def renderAgdaArgPos (ind : Nat) (e : Expr) : String :=
    if isAtomicAgdaExpr e then renderAgdaExpr ind e else "(" ++ renderAgdaExpr ind e ++ ")"

  partial def renderAgdaOperandPos (ind : Nat) (e : Expr) : String :=
    if needsAgdaOperandParen e then "(" ++ renderAgdaExpr ind e ++ ")" else renderAgdaExpr ind e

  partial def renderAgdaArgE (ind : Nat) (a : Arg Expr) : String :=
    agdaBraces a.hid a.label (renderAgdaArgPos ind a.thing)

  partial def renderAgdaBind (ind : Nat) : Bind → String
    | .bind h xs ty =>
        let inner := String.intercalate " " xs ++ " : " ++ renderAgdaExpr ind ty
        match h with
        | .visible => "(" ++ inner ++ ")"
        | .hidden  => "{" ++ inner ++ "}"
        | .inst    => "{{" ++ inner ++ "}}"

  partial def renderAgdaPat (ind : Nat) : Pat → String
    | .varP x    => x
    | .wildP     => "_"
    | .litP l    => renderAgdaLit l
    | .dotP e    => "." ++ renderAgdaArgPos ind e
    | .absurdP   => "()"
    | .asP x p   =>
        let pS := if isAtomicAgdaPat p then renderAgdaPat ind p else "(" ++ renderAgdaPat ind p ++ ")"
        x ++ "@" ++ pS
    | .projP q   => "." ++ q.shown
    | .conP q [] => q.shown
    | .conP q ps =>
        let pStrs := ps.map (renderAgdaArgP ind)
        let allVis := ps.all (fun a => a.hid == .visible && a.label.isNone)
        match if allVis then agdaMixfixFill q.shown pStrs else none with
        | some mx => mx
        | none    => String.intercalate " " (q.shown :: pStrs)
    | .recP fs =>
        let fStrs := fs.map (fun (n, p) => n ++ " = " ++ renderAgdaPat ind p)
        "record { " ++ String.intercalate " ; " fStrs ++ " }"

  partial def renderAgdaArgP (ind : Nat) (a : Arg Pat) : String :=
    let pS := if isAtomicAgdaPat a.thing then renderAgdaPat ind a.thing else "(" ++ renderAgdaPat ind a.thing ++ ")"
    agdaBraces a.hid a.label pS

  partial def renderAgdaLHS (ind : Nat) (showHead : Bool) : LHS → String
    | .head f ps =>
        let pStrs := ps.map (renderAgdaArgP ind)
        let allVis := ps.all (fun a => a.hid == .visible && a.label.isNone)
        if !showHead then String.intercalate " " pStrs
        else
          match if allVis then agdaMixfixFill f.shown pStrs else none with
          | some mx => mx
          | none    => String.intercalate " " (f.shown :: pStrs)
    | .proj d inner ps =>
        let focus := match inner with
          | .head x [] => x.shown
          | _          => "(" ++ renderAgdaLHS ind showHead inner ++ ")"
        let pStrs := ps.map (renderAgdaArgP ind)
        String.intercalate " " (d.shown :: focus :: pStrs)
    | .with_ inner ws ps =>
        let base := renderAgdaLHS ind showHead inner
        let wStrs := ws.map (fun w => "| " ++ renderAgdaArgP ind w)
        let pStrs := ps.map (renderAgdaArgP ind)
        String.intercalate " " (base :: (wStrs ++ pStrs))

  partial def renderAgdaRHS (ind : Nat) (showHead : Bool) : RHS → String × List String
    | .rhs e        => (" = " ++ renderAgdaExpr ind e, [])
    | .absurdRHS    => ("", [])
    | .withRHS es cs =>
        let eStrs := es.map (renderAgdaOperandPos ind)
        let subLines := cs.flatMap (renderAgdaClause ind showHead)
        (" with " ++ String.intercalate " | " eStrs, subLines)
    | .rewriteRHS es r =>
        let eStrs := es.map (renderAgdaOperandPos ind)
        let (tl, more) := renderAgdaRHS ind showHead r
        (" rewrite " ++ String.intercalate " | " eStrs ++ tl, more)

  partial def renderAgdaClause (ind : Nat) (showHead : Bool) : Clause → List String
    | .clause l r ws =>
        let lhsS := renderAgdaLHS ind showHead l
        let (rhsHead, moreLines) := renderAgdaRHS ind showHead r
        let wLines :=
          if ws.isEmpty then []
          else agdaIndent (ind + 2) "where" :: renderAgdaDeclGroup (ind + 4) ws
        (agdaIndent ind (lhsS ++ rhsHead)) :: (wLines ++ moreLines)

  partial def renderAgdaDirective (d : Directive) : String :=
    let uS := match d.dusing with
      | none    => ""
      | some ns => " using (" ++ String.intercalate "; " ns ++ ")"
    let hS := if d.dhiding.isEmpty then "" else " hiding (" ++ String.intercalate "; " d.dhiding ++ ")"
    let rS :=
      if d.drenaming.isEmpty then ""
      else
        let ps := d.drenaming.map (fun (a, b) => a ++ " to " ++ b)
        " renaming (" ++ String.intercalate "; " ps ++ ")"
    let pS := if d.dpublic then " public" else ""
    uS ++ hS ++ rS ++ pS

  partial def renderAgdaDeclSingle (ind : Nat) : Decl → List String
    | .pragma s => [agdaIndent ind ("{-# " ++ s ++ " #-}")]
    | .import_ m isOpen dir _ =>
        let fullS := String.intercalate "." m.full
        let modS := if m.shown == fullS then fullS else fullS ++ " as " ++ m.shown
        let pfx := if isOpen then "open import " else "import "
        [agdaIndent ind (pfx ++ modS ++ renderAgdaDirective dir)]
    | .open_ m dir =>
        [agdaIndent ind ("open " ++ m.shown ++ renderAgdaDirective dir)]
    | .fixity a n op =>
        let kw := match a with | .infixL => "infixl" | .infixR => "infixr" | .infixN => "infix"
        [agdaIndent ind (kw ++ " " ++ toString n ++ " " ++ op)]
    | .sig m x e =>
        if isMetaExpr e then []
        else
          let tc := match m.termCheck with
            | .check => []
            | .nonTerminating => [agdaIndent ind "{-# NON_TERMINATING #-}"]
            | .terminating    => [agdaIndent ind "{-# TERMINATING #-}"]
          tc ++ [agdaIndent ind (x ++ " : " ++ renderAgdaExpr ind e)]
    | .fun_ _ _ cs =>
        cs.flatMap (renderAgdaClause ind true)
    | .dataSig _ x bs sortE =>
        let bS := String.join (bs.map (fun b => " " ++ renderAgdaBind ind b))
        [agdaIndent ind ("data " ++ x ++ bS ++ " : " ++ renderAgdaExpr ind sortE)]
    | .dataDef _ x ps cons =>
        let hd := agdaIndent ind ("data " ++ String.intercalate " " (x :: ps) ++ " where")
        let cLines := cons.map (fun (cNm, cTy) => agdaIndent (ind + 2) (cNm ++ " : " ++ renderAgdaExpr (ind + 2) cTy))
        hd :: cLines
    | .recSig _ x bs sortE =>
        let bS := String.join (bs.map (fun b => " " ++ renderAgdaBind ind b))
        [agdaIndent ind ("record " ++ x ++ bS ++ " : " ++ renderAgdaExpr ind sortE)]
    | .recDef _ x ps rd fs =>
        let hd := agdaIndent ind ("record " ++ String.intercalate " " (x :: ps) ++ " where")
        let coLine := if rd.coind then [agdaIndent (ind + 2) "coinductive"] else []
        let cnLine := match rd.constr with
          | some c => [agdaIndent (ind + 2) ("constructor " ++ c)]
          | none   => []
        let fldLines :=
          if fs.isEmpty then []
          else
            agdaIndent (ind + 2) "field" ::
            fs.map (fun (fNm, fTy) => agdaIndent (ind + 4) (fNm ++ " : " ++ renderAgdaExpr (ind + 4) fTy))
        hd :: (coLine ++ cnLine ++ fldLines)
    | .variable_ vs =>
        agdaIndent ind "variable" ::
        vs.map (fun (vNm, vTy) => agdaIndent (ind + 2) (vNm ++ " : " ++ renderAgdaExpr (ind + 2) vTy))
    | .module_ x bs ds =>
        let bS := String.join (bs.map (fun b => " " ++ renderAgdaBind ind b))
        agdaIndent ind ("module " ++ x ++ bS ++ " where") :: renderAgdaDeclGroup (ind + 2) ds
    | .patSyn x args rPat _ =>
        let aPart := if args.isEmpty then "" else " " ++ String.intercalate " " args
        [agdaIndent ind ("pattern " ++ x ++ aPart ++ " = " ++ renderAgdaPat ind rPat)]
    | .unsupported s => [agdaIndent ind ("-- [unsupported] " ++ s)]

  partial def renderAgdaDeclGroup (ind : Nat) : List Decl → List String
    | [] => []
    | .dataSig _ x bs sortE :: .dataDef _ x2 _ cons :: rest =>
        if x == x2 then
          let bS := String.join (bs.map (fun b => " " ++ renderAgdaBind ind b))
          let hd := agdaIndent ind ("data " ++ x ++ bS ++ " : " ++ renderAgdaExpr ind sortE ++ " where")
          let cLines := cons.map (fun (cNm, cTy) => agdaIndent (ind + 2) (cNm ++ " : " ++ renderAgdaExpr (ind + 2) cTy))
          hd :: cLines ++ renderAgdaDeclGroup ind rest
        else
          renderAgdaDeclSingle ind (.dataSig plainMods x bs sortE) ++
          renderAgdaDeclGroup ind (.dataDef plainMods x2 [] cons :: rest)
    | .recSig _ x bs sortE :: .recDef _ x2 _ rd fs :: rest =>
        if x == x2 then
          let bS := String.join (bs.map (fun b => " " ++ renderAgdaBind ind b))
          let hd := agdaIndent ind ("record " ++ x ++ bS ++ " : " ++ renderAgdaExpr ind sortE ++ " where")
          let coLine := if rd.coind then [agdaIndent (ind + 2) "coinductive"] else []
          let cnLine := match rd.constr with
            | some c => [agdaIndent (ind + 2) ("constructor " ++ c)]
            | none   => []
          let fldLines :=
            if fs.isEmpty then []
            else
              agdaIndent (ind + 2) "field" ::
              fs.map (fun (fNm, fTy) => agdaIndent (ind + 4) (fNm ++ " : " ++ renderAgdaExpr (ind + 4) fTy))
          hd :: (coLine ++ cnLine ++ fldLines) ++ renderAgdaDeclGroup ind rest
        else
          renderAgdaDeclSingle ind (.recSig plainMods x bs sortE) ++
          renderAgdaDeclGroup ind (.recDef plainMods x2 [] rd fs :: rest)
    | d :: rest =>
        renderAgdaDeclSingle ind d ++ renderAgdaDeclGroup ind rest
end

private def renderSingleModUnitAgda (ind : Nat) (u : ModUnit) : List String :=
  match u.kind with
  | .postulateUnit _ nm ty =>
      let fixes := u.rawDecls.filter (fun | .fixity _ _ _ => true | _ => false)
      fixes.flatMap (renderAgdaDeclSingle ind) ++
      [agdaIndent ind "postulate", agdaIndent (ind + 2) (nm ++ " : " ++ renderAgdaExpr (ind + 2) ty)]
  | _ => renderAgdaDeclGroup ind u.rawDecls

private def renderUnitSCCAgda (ind : Nat) (sccUnits : List ModUnit) : List String :=
  if sccUnits.length <= 1 then
    sccUnits.flatMap (renderSingleModUnitAgda ind)
  else
    -- Multi-unit mutual SCC: emit all signatures/fixities first, then all definitions/opens!
    let isSigDecl : Decl → Bool
      | .sig _ _ _ | .dataSig _ _ _ _ | .recSig _ _ _ _ | .fixity _ _ _ => true
      | _ => false
    let sigs := sccUnits.flatMap (fun u => u.rawDecls.filter isSigDecl)
    let defs := sccUnits.flatMap (fun u => u.rawDecls.filter (fun d => !isSigDecl d))
    renderAgdaDeclGroup ind sigs ++ renderAgdaDeclGroup ind defs

-- Build the minimal, `--safe`-compatible parameterized Agda residual module `SlowSlice`!
partial def renderAgdaSlowSlice (depExps : List ExportedModule) (cm : CodeMod)
    (plan : SlicePlan) : String :=
  let units := plan.units
  let getUnit (uid : Nat) : Option ModUnit := units.find? (·.uid == uid)

  -- Step 1: Compute which `Fast` units (`F₁`) MUST be concrete (`concreteFast`) vs
  --         which `Fast` computational functions can be passed as abstract module parameters (`paramFast`)!
  --         - Any `dataUnit`/`recUnit` needed by `Slow` -> concrete (so constructors/projections exist).
  --         - Any `funUnit` needed in `sigRefs` (type-level unfolding!), or mixfix operator (`_`),
  --           or mentioning `Agda.Primitive.Level` without `Level` in scope -> concrete.
  --         - All other `Fast` `funUnit`s referenced in `bodyRefs` of `Slow` -> **abstract module parameters**
  --           `(f : T_f)` on `module _SlowResidual` (skipping 100% of `f`'s body and `f`'s own body-callees!).
  let canAbstractAsParam (u : ModUnit) : Bool :=
    match u.kind with
    | .funUnit m fNm sigTy _ =>
        !isMetaExpr sigTy && !fNm.contains '_' && !m.isInstance &&
        !(collectExprQNames sigTy).contains ["Agda", "Primitive", "Level"]
    | _ => false

  let rec closureConcrete (worklist : List Nat) (concrete : List Nat) : List Nat :=
    match worklist with
    | [] => concrete
    | uid :: rest =>
        if concrete.contains uid || plan.slowUnitIds.contains uid then
          closureConcrete rest concrete
        else
          match getUnit uid with
          | none => closureConcrete rest concrete
          | some u =>
              -- If `uid` is concrete, both its `sigDeps` and `bodyDeps` (unless abstractable!) are needed:
              let sDeps := unitLocalSigDeps units u
              let bDeps := unitLocalBodyDeps units u
              let mustConcreteFromBody := bDeps.filter fun d =>
                match getUnit d with
                | some du => !canAbstractAsParam du
                | none    => false
              closureConcrete (sDeps ++ mustConcreteFromBody ++ rest) (uid :: concrete)

  -- Direct dependencies of `slowUnitIds`:
  let slowUnits := plan.slowUnitIds.filterMap getUnit
  let directSigFromSlow := (slowUnits.flatMap (unitLocalSigDeps units)).filter (!plan.slowUnitIds.contains ·) |>.eraseDups
  let directBodyFromSlow := (slowUnits.flatMap (unitLocalBodyDeps units)).filter (!plan.slowUnitIds.contains ·) |>.eraseDups

  -- Any `directBodyFromSlow` unit that CANNOT be abstracted (e.g. `dataUnit`, `recUnit`, mixfix op) goes into `concrete`:
  let nonParamBody := directBodyFromSlow.filter fun uid =>
    match getUnit uid with
    | some u => !canAbstractAsParam u
    | none   => false

  let concreteInit := closureConcrete (directSigFromSlow ++ nonParamBody) []

  -- Candidate module parameters: fast `funUnit`s referenced in bodies of `slowUnits` U `concreteInit`
  let allActiveCallers := slowUnits ++ concreteInit.filterMap getUnit
  let rawParamCands :=
    (allActiveCallers.flatMap (unitLocalBodyDeps units)).eraseDups.filter fun uid =>
      !plan.slowUnitIds.contains uid && !concreteInit.contains uid

  -- Ensure all types mentioned in signatures of `rawParamCands` have their `sigDeps` in `concreteFinal`!
  let paramSigDeps :=
    rawParamCands.flatMap fun uid =>
      match getUnit uid with
      | some u => unitLocalSigDeps units u
      | none   => []
  let concrete0 := closureConcrete paramSigDeps concreteInit
  let param0 :=
    rawParamCands.filter (fun uid => !concrete0.contains uid) |>.eraseDups

  -- Partition concrete units into:
  -- 1) `preConcrete`: concrete units whose entire local dependency cone lies strictly inside `preConcrete`
  --    (safe to emit at top level ABOVE `module _SlowResidual (...) where`), and
  -- 2) `inModConcrete`: concrete units that depend on an earlier `slowUnit` or on a `_SlowResidual` parameter
  --    (MUST be emitted INSIDE `module _SlowResidual` interleaved with `slowUnitIds` in `plan.sccs` order!).
  let preConcrete := plan.sccs.foldl (fun (acc : List Nat) scc =>
    let allInConcrete := scc.all (concrete0.contains ·) && scc.all (!plan.slowUnitIds.contains ·)
    let depsInPre := scc.all fun uid =>
      match getUnit uid with
      | some u => (unitLocalAllDeps units u).all (fun d => acc.contains d || scc.contains d)
      | none   => true
    if allInConcrete && depsInPre then acc ++ scc else acc) []

  -- Any parameter candidate whose type signature mentions a unit NOT in `preConcrete` cannot sit in
  -- `module _SlowResidual`'s header; promote it (and its full concrete body closure) into `concreteFinal`.
  let badParams := param0.filter fun uid =>
    match getUnit uid with
    | some u => !(unitLocalSigDeps units u).all (preConcrete.contains ·)
    | none   => false

  let rec closureFullConcrete (worklist : List Nat) (concrete : List Nat) : List Nat :=
    match worklist with
    | [] => concrete
    | uid :: rest =>
        if concrete.contains uid || plan.slowUnitIds.contains uid then
          closureFullConcrete rest concrete
        else
          match getUnit uid with
          | none => closureFullConcrete rest concrete
          | some u =>
              closureFullConcrete (unitLocalAllDeps units u ++ rest) (uid :: concrete)

  let concreteFinal :=
    if badParams.isEmpty then concrete0
    else closureFullConcrete badParams concrete0
  let paramFinal :=
    param0.filter (fun uid => !badParams.contains uid && !concreteFinal.contains uid) |>.eraseDups
  let inModConcrete :=
    concreteFinal.filter (!preConcrete.contains ·)

  -- Step 2: Prune unused `import_` declarations so unused heavy modules (like `IO` for `F₂.main`) are skipped!
  let concreteUnits := concreteFinal.filterMap getUnit
  let paramUnits := paramFinal.filterMap getUnit
  let usedQNames : List (List String) :=
    (concreteUnits.flatMap (fun u => u.sigQNames ++ u.bodyQNames) ++
     paramUnits.flatMap (fun u => u.sigQNames) ++
     slowUnits.flatMap (fun u => u.sigQNames ++ u.bodyQNames)).eraseDups

  let lookupImportExports (modQ : QName) : Option (List SymInfo) :=
    match depExps.find? (fun m => m.modPath == modQ.full) with
    | some m => some m.symbols
    | none   => lookupStdModule (String.intercalate "." modQ.full)

  let isPragmaOptions : Decl → Bool
    | .pragma s => s.startsWith "OPTIONS"
    | _         => false

  let optPragmas := plan.headers.filter isPragmaOptions
  let otherHeaders := plan.headers.filter (fun d => !isPragmaOptions d)
  let keptHeaders := otherHeaders.filter fun
    | .import_ modQ _ _ _ =>
        match lookupImportExports modQ with
        | some syms => syms.any (fun s => usedQNames.contains s.canonPath)
        | none      => true
    | _ => true

  -- Step 3: Emit `SlowSlice` in exact SCC topological order!
  let pragmaLines := optPragmas.flatMap (renderAgdaDeclSingle 0)
  let modHeader := "module " ++ String.intercalate "." cm.modName.full ++ " where"
  let headerLines := keptHeaders.flatMap (renderAgdaDeclSingle 2)

  let preConcreteSCCs := plan.sccs.filterMap fun scc =>
    let kept := scc.filter (preConcrete.contains ·) |>.filterMap getUnit
    if kept.isEmpty then none else some kept
  let preConcreteLines := preConcreteSCCs.flatMap (renderUnitSCCAgda 2)

  let residualSCCs := plan.sccs.filterMap fun scc =>
    let kept := scc.filter (fun uid => plan.slowUnitIds.contains uid || inModConcrete.contains uid) |>.filterMap getUnit
    if kept.isEmpty then none else some kept

  let slowBodyLines :=
    if paramUnits.isEmpty then
      residualSCCs.flatMap (renderUnitSCCAgda 2)
    else
      -- Order `paramUnits` by `uid` and emit `module _SlowResidual (f₁ : T₁) ... where`!
      let sortedParams := units.filter (fun u => paramFinal.contains u.uid)
      let paramBindStrs := sortedParams.filterMap fun u =>
        match u.kind with
        | .funUnit _ fNm sigTy _ =>
            some ("(" ++ fNm ++ " : " ++ renderAgdaExpr 4 sigTy ++ ")")
        | _ => none
      let subModHdr :=
        "  module _SlowResidual " ++ String.intercalate " " paramBindStrs ++ " where"
      subModHdr :: residualSCCs.flatMap (renderUnitSCCAgda 4)

  let allLines :=
    pragmaLines ++ [modHeader, ""] ++ headerLines ++
    (if preConcreteLines.isEmpty then [] else "" :: preConcreteLines) ++
    ("" :: slowBodyLines)
  String.intercalate "\n" allLines ++ "\n"

end Prism