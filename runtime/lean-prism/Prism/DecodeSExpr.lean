import Prism.StdScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.DecodeSExpr`: Canonical `Dump.hs` S-Expression Decoder & Scope Validator

Decodes scope-checked `CodeMod` S-expressions emitted by `dump/dump` (exact inverse of
`Prism.Outcome.encodeCodeMod`) and synthesizes `ExportedModule` metadata while enforcing
the backend mirror whitelist and supported compiler options.
-/

namespace Prism

private def wireSpace (c : Char) := c == ' ' || c == '\n' || c == '\r' || c == '\t'

private partial def quotedAtom (txt : String) (start : String.Pos.Raw) :
    Option (String × String.Pos.Raw) := do
  let rec loop (pos : String.Pos.Raw) (out : String) : Option (String × String.Pos.Raw) := do
    let stop := String.Pos.Raw.nextUntil txt (fun c => c == '"' || c == '\\') pos
    if stop.atEnd txt then none else
      let part := String.Pos.Raw.extract txt pos stop
      let next := stop.next txt
      if stop.get txt == '"' then return (out ++ part, next)
      if next.atEnd txt then none else
        let c := match next.get txt with
          | 'n' => '\n' | 'r' => '\r' | 't' => '\t' | escaped => escaped
        loop (next.next txt) ((out ++ part).push c)
  loop start ""

/-- Scan the wire once, retaining a stack of open lists. Qualified names and
    unescaped literals are sliced directly from the UTF-8 input. -/
partial def parseSExprText (txt : String) : Option SExpr := do
  let mut parents : List (List SExpr) := []
  let mut items : List SExpr := []
  let mut pos : String.Pos.Raw := 0
  while !pos.atEnd txt do
    let c := pos.get txt
    if wireSpace c then
      pos := pos.next txt
    else if c == '(' then
      parents := items :: parents
      items := []
      pos := pos.next txt
    else if c == ')' then
      let prev :: outer := parents | return ← none
      items := .list items.reverse :: prev
      parents := outer
      pos := pos.next txt
    else if c == '"' then
      let (value, next) ← quotedAtom txt (pos.next txt)
      items := .str value :: items
      pos := next
    else
      let stop := String.Pos.Raw.nextUntil txt
        (fun ch => wireSpace ch || ch == '(' || ch == ')' || ch == '"') (pos.next txt)
      let word := String.Pos.Raw.extract txt pos stop
      items := (match word.toNat? with | some n => .num n | none => .sym word) :: items
      pos := stop
  let [result] := items | none
  if parents.isEmpty then some result else none

-- §2 Decode `SExpr` → `CodeMod` (exact mirror of `Code/Parse.agda` & `Dump.hs`)

private def splitDotsStr (s : String) : List String :=
  if s.isEmpty then [""] else s.splitOn "."

def decQ : SExpr → Option QName
  | .str s => some (mkQ (splitDotsStr s))
  | .list (.sym "q" :: .str f :: .str sh :: alts) => do
      let paths ← alts.mapM fun | .str path => some (splitDotsStr path) | _ => none
      some { full := splitDotsStr f, shown := sh, canonAlts := paths }
  | _ => none

private def decHid : SExpr → Option Hiding
  | .sym "vis"  => some .visible
  | .sym "hid"  => some .hidden
  | .sym "inst" => some .inst
  | _ => none

private def decLabel : SExpr → Option (Option String)
  | .sym "_" => some none
  | .str s   => some (some s)
  | _        => none

private def decLit : SExpr → Option Lit
  | .list [.sym "nat", .num n] => some (.natL n)
  | .list [.sym "str", .str s] => some (.strL s)
  | .list [.sym "chr", .str s] =>
      match s.toList with
      | c :: _ => some (.charL c)
      | []     => none
  | _ => none

private def decMods : SExpr → Option Mods
  | .list (.sym "mods" :: flags) =>
      some <| flags.foldl (fun m f =>
        match f with
        | .sym "private"        => { m with isPrivate := true }
        | .sym "instance"       => { m with isInstance := true }
        | .sym "abstract"       => { m with isAbstract := true }
        | .sym "nonterminating" => { m with termCheck := .nonTerminating }
        | .sym "terminating"    => { m with termCheck := .terminating }
        | _                     => m) plainMods
  | _ => none

private def decAssoc : SExpr → Option Assoc
  | .sym "l" => some .infixL
  | .sym "r" => some .infixR
  | .sym "n" => some .infixN
  | _        => none

private def decStrList : List SExpr → Option (List String)
  | [] => some []
  | .str s :: rest => do
      let xs ← decStrList rest
      some (s :: xs)
  | _ => none

private def decDir : SExpr → Option Directive
  | .list [.sym "dir", uS, .list (.sym "hiding" :: hS), .list (.sym "renaming" :: rS), pubS] => do
      let uOpt ← match uS with
        | .sym "everything" => some (none : Option (List String))
        | .list (.sym "using" :: us) => do
            let ns ← decStrList us
            some (some ns)
        | _ => none
      let hs ← decStrList hS
      let rs ← rS.mapM fun
        | .list [.str a, .str b] => some (a, b)
        | _ => none
      let pub ← match pubS with
        | .sym "public"  => some true
        | .sym "private" => some false
        | _              => none
      some { dusing := uOpt, dhiding := hs, drenaming := rs, dpublic := pub }
  | _ => none

private instance : Inhabited Expr := ⟨.meta_⟩

private partial def patternBuilder : Pat → Expr
  | .varP x => .var x
  | .conP q ps => ps.foldl (fun e a => .app e ⟨a.hid, a.label, patternBuilder a.thing⟩) (.con q)
  | .litP l => .lit l
  | .dotP e => e
  | .recP fs => .rec_ (fs.map fun (n, p) => (n, patternBuilder p))
  | .asP x _ => .var x
  | .wildP | .absurdP | .projP _ => .meta_

mutual
  partial def decExpr : SExpr → Option Expr
    | .list [.sym "var", .str x] => some (.var x)
    | .list [.sym "def", qS]     => Expr.def_ <$> decQ qS
    | .list [.sym "con", qS]     => Expr.con <$> decQ qS
    | .list [.sym "lit", lS]     => Expr.lit <$> decLit lS
    | .list [.sym "set", .num n] => some (.set n)
    | .sym "hole"                => some .hole
    | .sym "meta"                => some .meta_
    | .list [.sym "app", fS, aS] => do
        let f ← decExpr fS
        let a ← decArgExpr aS
        some (.app f a)
    | .list [.sym "lam", .list [.sym "arg", hS, lS, .str x], eS] => do
        let h ← decHid hS
        let l ← decLabel lS
        let e ← decExpr eS
        some (.lam { hid := h, label := l, thing := x } e)
    | .list [.sym "lamT", bS, eS] => do
        let b ← decBind bS
        let e ← decExpr eS
        some (.lamT b e)
    | .list [.sym "absurdlam", hS] => Expr.absurdLam <$> decHid hS
    | .list (.sym "lamcase" :: cSs) => do
        let cs ← cSs.mapM decClause
        some (.lamCase cs)
    | .list [.sym "pi", bS, eS] => do
        let b ← decBind bS
        let e ← decExpr eS
        some (.pi b e)
    | .list [.sym "fun", aS, eS] => do
        let a ← decArgExpr aS
        let e ← decExpr eS
        some (.fun_ a e)
    | .list [.sym "let", .list lbSs, eS] => do
        let lbs ← lbSs.mapM decLetBind
        let e ← decExpr eS
        some (.let_ lbs e)
    | .list [.sym "rec", .list fSs] => do
        let fs ← fSs.mapM fun
          | .list [.sym "fld", .str n, vS] => do
              let v ← decExpr vS
              some (n, v)
          | _ => none
        some (.rec_ fs)
    | .list [.sym "recupd", rS, .list fSs] => do
        let r ← decExpr rS
        let fs ← fSs.mapM fun
          | .list [.sym "fld", .str n, vS] => do
              let v ← decExpr vS
              some (n, v)
          | _ => none
        some (.recUpd r fs)
    | .list [.sym "dot", eS] => Expr.dot <$> decExpr eS
    | _ => none

  partial def decArgExpr : SExpr → Option (Arg Expr)
    | .list [.sym "arg", hS, lS, eS] => do
        let h ← decHid hS
        let l ← decLabel lS
        let e ← decExpr eS
        some { hid := h, label := l, thing := e }
    | _ => none

  partial def decBind : SExpr → Option Bind
    | .list [.sym "bind", hS, .list xSs, tS] => do
        let h ← decHid hS
        let xs ← decStrList xSs
        let t ← decExpr tS
        some (.bind h xs t)
    | _ => none

  partial def decLetBind : SExpr → Option LetBind
    | .list [.sym "letbind", .str x, tS, eS] => do
        let t ← decExpr tS
        let e ← decExpr eS
        some (.letBind x t e)
    | .list [.sym "letpat", pS, eS] => do
        let p ← decPat pS
        let e ← decExpr eS
        some (.letPat p e)
    | _ => none

  partial def decPat : SExpr → Option Pat
    | .list [.sym "varp", .str x] => some (.varP x)
    | .list (.sym "conp" :: qS :: pSs) => do
        let q ← decQ qS
        let ps ← pSs.mapM decArgPat
        some (.conP q ps)
    | .sym "wildp" => some .wildP
    | .list [.sym "litp", lS] => Pat.litP <$> decLit lS
    | .list [.sym "dotp", eS] => Pat.dotP <$> decExpr eS
    | .sym "absurdp" => some .absurdP
    | .list [.sym "asp", .str x, pS] => do
        let p ← decPat pS
        some (.asP x p)
    | .list [.sym "projp", qS] => Pat.projP <$> decQ qS
    | .list [.sym "recp", .list fSs] => do
        let fs ← fSs.mapM fun
          | .list [.sym "fld", .str n, pS] => do
              let p ← decPat pS
              some (n, p)
          | _ => none
        some (.recP fs)
    | _ => none

  partial def decArgPat : SExpr → Option (Arg Pat)
    | .list [.sym "arg", hS, lS, pS] => do
        let h ← decHid hS
        let l ← decLabel lS
        let p ← decPat pS
        some { hid := h, label := l, thing := p }
    | _ => none

  partial def decLHS : SExpr → Option LHS
    | .list (.sym "head" :: qS :: pSs) => do
        let q ← decQ qS
        let ps ← pSs.mapM decArgPat
        some (.head q ps)
    | .list (.sym "proj" :: dS :: lS :: pSs) => do
        let d ← decQ dS
        let l ← decLHS lS
        let ps ← pSs.mapM decArgPat
        some (.proj d l ps)
    | .list [.sym "with", lS, .list wSs, .list pSs] => do
        let l ← decLHS lS
        let ws ← wSs.mapM decArgPat
        let ps ← pSs.mapM decArgPat
        some (.with_ l ws ps)
    | _ => none

  partial def decRHS : SExpr → Option RHS
    | .list [.sym "rhs", eS] => RHS.rhs <$> decExpr eS
    | .sym "absurdrhs"       => some .absurdRHS
    | .list [.sym "withrhs", .list eSs, .list cSs] => do
        let es ← eSs.mapM decExpr
        let cs ← cSs.mapM decClause
        some (.withRHS es cs)
    | .list [.sym "rewriterhs", .list eSs, rS] => do
        let es ← eSs.mapM decExpr
        let r ← decRHS rS
        some (.rewriteRHS es r)
    | _ => none

  partial def decClause : SExpr → Option Clause
    | .list [.sym "clause", lS, rS, .list (.sym "where" :: wSs)] => do
        let l ← decLHS lS
        let r ← decRHS rS
        let wsList ← wSs.mapM decDecls
        some (.clause l r wsList.flatten)
    | _ => none

  partial def decDecls : SExpr → Option (List Decl)
    | .list [.sym "pragma", .str s] => some [.pragma s]
    | .list [.sym "import", mS, oS, dS, .list (.sym "assumes" :: aSs)] => do
        let m ← decQ mS
        let o ← match oS with | .sym "open" => some true | .sym "noopen" => some false | _ => none
        let d ← decDir dS
        let asList ← aSs.mapM decDecls
        some [.import_ m o d asList.flatten]
    | .list [.sym "open", mS, dS] => do
        let m ← decQ mS
        let d ← decDir dS
        some [.open_ m d]
    | .list [.sym "fixity", aS, .num n, .str x] => do
        let a ← decAssoc aS
        some [.fixity a n x]
    | .list [.sym "sig", mS, .str x, eS] => do
        let m ← decMods mS
        let e ← decExpr eS
        some [.sig m x e]
    | .list (.sym "fun" :: mS :: .str x :: cSs) => do
        let m ← decMods mS
        let cs ← cSs.mapM decClause
        some [.fun_ m x cs]
    | .list [.sym "datasig", mS, .str x, .list (.sym "params" :: bSs), eS] => do
        let m ← decMods mS
        let bs ← bSs.mapM decBind
        let e ← decExpr eS
        some [.dataSig m x bs e]
    | .list (.sym "datadef" :: mS :: .str x :: .list pSs :: itemSs) => do
        let m ← decMods mS
        let ps ← decStrList pSs
        let mut cons : List (String × Expr) := []
        let mut fixes : List Decl := []
        for it in itemSs do
          match it with
          | .list [.sym "con", .str cNm, eS] =>
              let e ← decExpr eS
              cons := cons ++ [(cNm, e)]
          | .list [.sym "fixity", aS, .num prec, .str op] =>
              let a ← decAssoc aS
              fixes := fixes ++ [.fixity a prec op]
          | _ => none
        some (.dataDef m x ps cons :: fixes)
    | .list [.sym "recsig", mS, .str x, .list (.sym "params" :: bSs), eS] => do
        let m ← decMods mS
        let bs ← bSs.mapM decBind
        let e ← decExpr eS
        some [.recSig m x bs e]
    | .list (.sym "recdef" :: mS :: .str x :: .list pSs :: .list [.sym "recdir", indS, cS] :: itemSs) => do
        let m ← decMods mS
        let ps ← decStrList pSs
        let co ← match indS with
          | .sym "coinductive" => some true
          | .sym "inductive"   => some false
          | _                  => none
        let cn ← decLabel cS
        let mut flds : List (String × Expr) := []
        let mut fixes : List Decl := []
        for it in itemSs do
          match it with
          | .list [.sym "field", .str fNm, eS] =>
              let e ← decExpr eS
              flds := flds ++ [(fNm, e)]
          | .list [.sym "fixity", aS, .num prec, .str op] =>
              let a ← decAssoc aS
              fixes := fixes ++ [.fixity a prec op]
          | _ => none
        some (.recDef m x ps { coind := co, constr := cn } flds :: fixes)
    | .list (.sym "variable" :: vSs) => do
        let vs ← vSs.mapM fun
          | .list [.sym "var", .str n, eS] => do
              let e ← decExpr eS
              some (n, e)
          | _ => none
        some [.variable_ vs]
    | .list (.sym "module" :: .str x :: .list (.sym "params" :: bSs) :: dSs) => do
        let bs ← bSs.mapM decBind
        let dsList ← dSs.mapM decDecls
        some [.module_ x bs dsList.flatten]
    | .list [.sym "patsyn", .str name, .list args, term] => do
        let ps ← decStrList args
        let pat ← decPat term
        some [.patSyn name ps pat (patternBuilder pat)]
    | .list [.sym "unsupported", .str s] =>
        some [.unsupported s]
    | _ => none
end

def decodeCodeMod (s : SExpr) : Option CodeMod :=
  match s with
  | .list (.sym "module" :: nmS :: .list (.sym "params" :: pSs) :: dSs) => do
      let nm ← decQ nmS
      let ps ← pSs.mapM decBind
      let dsList ← dSs.mapM decDecls
      some { modName := nm, params := ps, decls := dsList.flatten }
  | _ => none

/-- Keep authored bytes alongside the authoritative AST. The same wire tree
    supplies each occurrence's ambiguity metadata, without another scope pass. -/
partial def decodeSurfacePoint (wire : SExpr) (surface : CatStructure.SurfaceView) :
    Option CatStructure.PreTCPoint := do
  let code ← decodeCodeMod wire
  let rec gather : List SExpr → List CatStructure.AmbQ → List CatStructure.AmbQ
    | [], acc => acc.reverse
    | (.list (.sym "q" :: .str name :: .str shown :: alts)) :: rest, acc =>
      let paths := alts.filterMap fun | .str s => some (splitDotsStr s) | _ => none
      let q : QName := {full := splitDotsStr name, shown, canonAlts := paths}
      gather rest (if paths.isEmpty then acc else ⟨q, paths⟩ :: acc)
    | (.list xs) :: rest, acc => gather (xs ++ rest) acc
    | _ :: rest, acc => gather rest acc
  return ⟨code, gather [wire] [], surface⟩

-- §3 Synthesize `ExportedModule` & Enforce Closed Whitelist / Pragma Gates on Decoded `CodeMod`

private partial def countVisibleConArgs : Expr → Nat
  | .pi (.bind .visible xs _) rest => xs.length + countVisibleConArgs rest
  | .pi (.bind _ _ _) rest         => countVisibleConArgs rest
  | .fun_ { hid := .visible, .. } rest => 1 + countVisibleConArgs rest
  | .fun_ _ rest                       => countVisibleConArgs rest
  | _ => 0

mutual
  partial def allImportsInDecl : Decl → List QName
    | .import_ m _ _ _ => [m]
    | .fun_ _ _ cs     => cs.flatMap allImportsInClause
    | .module_ _ _ ds  => ds.flatMap allImportsInDecl
    | _                => []

  private partial def allImportsInClause : Clause → List QName
    | .clause _ r ws => allImportsInRHS r ++ ws.flatMap allImportsInDecl

  private partial def allImportsInRHS : RHS → List QName
    | .rhs e           => allImportsInExpr e
    | .absurdRHS       => []
    | .withRHS es cs   => es.flatMap allImportsInExpr ++ cs.flatMap allImportsInClause
    | .rewriteRHS es r => es.flatMap allImportsInExpr ++ allImportsInRHS r

  private partial def allImportsInExpr : Expr → List QName
    | .app f a     => allImportsInExpr f ++ allImportsInExpr a.thing
    | .lam _ e     => allImportsInExpr e
    | .lamT _ e    => allImportsInExpr e
    | .lamCase cs  => cs.flatMap allImportsInClause
    | .pi _ e      => allImportsInExpr e
    | .fun_ a e    => allImportsInExpr a.thing ++ allImportsInExpr e
    | .let_ _ e    => allImportsInExpr e
    | _            => []
end

-- A scoped bodyless signature represents a postulate in a Code bundle.
-- Verify it in each declaration scope, including local where blocks.
private partial def safeDeclError (ds : List Decl) : Option String :=
  let bodies := ds.filterMap fun | .fun_ _ name _ => some name | _ => none
  let rec clauses : List Clause → Option String
    | [] => none
    | .clause _ rhs localDs :: rest =>
      safeDeclError localDs <|> (match rhs with | .withRHS _ cs => clauses cs | _ => none) <|> clauses rest
  ds.findSome? fun
    | .sig _ name _ => if bodies.contains name then none else some s!"cannot postulate {name} with --safe"
    | .module_ _ _ body => safeDeclError body
    | .fun_ m name cs =>
      if m.termCheck != .check then some s!"termination pragma on {name} forbidden with --safe"
      else clauses cs
    | _ => none

def synthesizeExportedModule (deps : List ExportedModule) (cm : CodeMod) (forExe := false) : PrismOutcome ExportedModule := do
  if !cm.params.isEmpty then
    .bot "parameterized top-level module routed to Agda"
  let pfx := cm.modName.full
  let ns := leanModNamespace pfx
  let mut selfSafe := false
  let mut selfGuarded := false
  for d in cm.decls do
    if let .pragma s := d then
      if s.startsWith "FOREIGN" || s.startsWith "COMPILE" then
        PrismOutcome.bot s!"GHC FFI pragma '{s}' routed to Agda"
      checkOptionsPragma s forExe
      let toks := s.splitOn " "
      if toks.contains "--safe" then selfSafe := true
      if toks.contains "--guardedness" then selfGuarded := true
    if let .unsupported u := d then
      PrismOutcome.bot s!"unsupported construct '{u}' routed to Agda"

  if selfSafe then
    if let some err := safeDeclError cm.decls then PrismOutcome.syntaxErr err

  -- Validate all imports (including `where`-scoped imports) against `deps` U `StdScope`!
  let mut depCoinds : List (List String) := []
  for impQ in cm.decls.flatMap allImportsInDecl do
    let rawMod := String.intercalate "." impQ.full
    match deps.find? (fun m => m.modPath == impQ.full) with
    | some dm =>
        if selfSafe && !dm.hasSafe then
          PrismOutcome.syntaxErr s!"--safe module cannot import non-safe module '{rawMod}'"
        if dm.hasGuardedness && !selfGuarded then
          PrismOutcome.syntaxErr s!"importing --guardedness module '{rawMod}' requires --guardedness"
        depCoinds := (dm.coindRecords ++ depCoinds).eraseDups
    | none =>
        match lookupStdModule rawMod with
        | some _ =>
            if selfSafe && !isStdModuleSafe rawMod then
              PrismOutcome.syntaxErr s!"--safe module cannot import non-safe module '{rawMod}'"
            if isStdModuleGuarded rawMod && !selfGuarded then
              PrismOutcome.syntaxErr s!"importing --guardedness module '{rawMod}' requires --guardedness"
        | none =>
            PrismOutcome.bot s!"import '{rawMod}' is outside Lean 4 mirror whitelist"

  let fixMap : List (String × FixLevel) :=
    cm.decls.filterMap fun
      | .fixity a n op =>
          let ma := match a with | .infixL => .infixL | .infixR => .infixR | .infixN => .infixN
          some (op, .related (Int.ofNat n) ma)
      | _ => none
  let lookupFix (nm : String) : FixLevel :=
    (fixMap.find? (fun (k, _) => k == nm)).map Prod.snd |>.getD defaultAgdaFixity

  let applyDir (syms : List SymInfo) (dir : Directive) : List SymInfo :=
    let afterUsing := match dir.dusing with
      | none    => syms
      | some us => syms.filter (fun s => us.contains s.localName)
    let afterHiding := afterUsing.filter (fun s => !dir.dhiding.contains s.localName)
    afterHiding.map fun s =>
      match dir.drenaming.find? (fun (fromNm, _) => fromNm == s.localName) with
      | some (_, toNm) => { s with localName := toNm }
      | none           => s

  let mut localSyms : List SymInfo := []
  let mut recSubSyms : List (String × List SymInfo) := []
  let mut ownCoinds : List (List String) := []

  for d in cm.decls do
    match d with
    | .dataDef m dNm _ cons =>
        if !m.isPrivate then
          let dCanon := pfx ++ [dNm]
          let leanD := ns ++ "." ++ leanMangleIdent dNm
          localSyms := localSyms ++ [{
            localName := dNm, canonPath := dCanon, kind := .typeSym,
            fixity := lookupFix dNm, leanName := leanD
          }]
          for (cNm, cTy) in cons do
            localSyms := localSyms ++ [{
              localName := cNm, canonPath := dCanon ++ [cNm], kind := .conSym,
              fixity := lookupFix cNm, leanName := leanD ++ "." ++ leanMangleIdent cNm,
              conArity := countVisibleConArgs cTy
            }]
    | .recDef m rNm pNames rd flds =>
        let rCanon := pfx ++ [rNm]
        if rd.coind then ownCoinds := rCanon :: ownCoinds
        let leanR := ns ++ "." ++ leanMangleIdent rNm
        let fSyms := flds.map fun (fNm, _) => {
          localName := fNm, canonPath := rCanon ++ [fNm], kind := .projSym pNames.length,
          fixity := lookupFix fNm, leanName := leanR ++ "." ++ leanMangleIdent fNm
        }
        recSubSyms := (rNm, fSyms) :: recSubSyms
        if !m.isPrivate then
          localSyms := localSyms ++ [{
            localName := rNm, canonPath := rCanon, kind := .typeSym,
            fixity := lookupFix rNm, leanName := leanR
          }]
          if let some cNm := rd.constr then
            localSyms := localSyms ++ [{
              localName := cNm, canonPath := pfx ++ [cNm], kind := .conSym,
              fixity := lookupFix cNm, leanName := leanR ++ "." ++ leanMangleIdent cNm,
              conArity := flds.length
            }]
          for fs in fSyms do
            localSyms := localSyms ++ [{ fs with localName := rNm ++ "." ++ fs.localName }]
    | .patSyn name args _ _ =>
        localSyms := localSyms ++ [{
            localName := name, canonPath := pfx ++ [name], kind := .conSym,
            leanName := ns ++ "." ++ leanMangleIdent name, conArity := args.length }]
    | .sig m fNm _ =>
        if !m.isPrivate && fNm != "_" && !(localSyms.any (·.localName == fNm)) then
          localSyms := localSyms ++ [{
            localName := fNm, canonPath := pfx ++ [fNm], kind := .defSym,
            fixity := lookupFix fNm, leanName := ns ++ "." ++ leanMangleIdent fNm
          }]
    | .fun_ m fNm _ =>
        if !m.isPrivate && fNm != "_" && !(localSyms.any (·.localName == fNm)) then
          localSyms := localSyms ++ [{
            localName := fNm, canonPath := pfx ++ [fNm], kind := .defSym,
            fixity := lookupFix fNm, leanName := ns ++ "." ++ leanMangleIdent fNm
          }]
    | .import_ modQ true dir _ =>
        if dir.dpublic then
          let rawMod := String.intercalate "." modQ.full
          let modSyms :=
            match deps.find? (fun dm => dm.modPath == modQ.full) with
            | some dm => dm.symbols
            | none    => (lookupStdModule rawMod).getD []
          localSyms := localSyms ++ applyDir modSyms dir
    | .open_ q dir =>
        if dir.dpublic then
          if q.full.take pfx.length == pfx && q.full.length == pfx.length + 1 then
            let rNm := q.full.getLastD ""
            let rSyms := (recSubSyms.find? (fun (k, _) => k == rNm)).map Prod.snd |>.getD []
            localSyms := localSyms ++ applyDir rSyms dir
          else
            let rawMod := String.intercalate "." q.full
            let modSyms :=
              match deps.find? (fun dm => dm.modPath == q.full) with
              | some dm => dm.symbols
              | none    => (lookupStdModule rawMod).getD []
            localSyms := localSyms ++ applyDir modSyms dir
    | _ => pure ()

  .translated {
    modPath        := pfx
    symbols        := localSyms
    hasSafe        := selfSafe
    hasGuardedness := selfGuarded
    coindRecords   := (ownCoinds ++ depCoinds).eraseDups
  }

end Prism
