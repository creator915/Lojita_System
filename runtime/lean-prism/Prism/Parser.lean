import Prism.Lexer
import Prism.StdScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.Parser`: Closed-Scope, Layout-Sensitive, Mixfix-DAG Agda Parser

Guarantees in `O(n)` without running Agda's typechecker:
1. Off-side layout alignment is strictly enforced (`col < blockCol` or unaligned
   top-level tokens produce `.syntaxErr`).
2. Every identifier and mixfix operator is resolved against the closed symbol
   table (glued tokens like `x:ℕ`, `1,`, `λx`, `[1]`, `a+b`, typos like `Nta`,
   and forward references outside `mutual`/pre-signatures immediately fail with
   `.syntaxErr`).
3. Mixfix expressions and patterns enforce Agda's partial-order precedence DAG
   (`Prism.MixfixDAG`), rejecting unrelated or non-associative operator chains
   with `.syntaxErr`.
4. Valid long-tail Agda constructs (`coinductive`, `--without-K`, `with`,
   `rewrite`, `variable`, unwhitelisted `import`, etc.) deterministically return
   `.bot` so `leanPrism` routes them to `LegacyAgda`.
-/

namespace Prism

structure ExportedModule : Type where
  modPath        : List String
  symbols        : List SymInfo
  hasSafe        : Bool := false
  hasGuardedness : Bool := false
  coindRecords   : List (List String) := []
  slowExports    : List (List String) := []
  deriving Repr

structure ScopeEnv : Type where
  modPrefix      : List String
  selfSafe       : Bool := false
  selfGuarded    : Bool := false
  unqualified    : List (String × SymInfo)        -- visible bare names
  qualified      : List (String × SymInfo)        -- `Alias.name` -> SymInfo
  locals         : List String                    -- bound pattern/lambda/let/telescope variables
  levelVars      : List String                    -- bound universe level variables (`Level`)
  knownModules   : List ExportedModule            -- dependency modules in bundle
  recordFields   : List (String × List String × Option String × Nat) -- recFullDot -> (fieldNames, constr?, numParams)
  coindRecords   : List (List String) := []       -- canonical paths of coinductive records in scope

def emptyScope (modPrefix : List String) (deps : List ExportedModule) : ScopeEnv :=
  { modPrefix    := modPrefix
  , unqualified  := []
  , qualified    := []
  , locals       := []
  , levelVars    := []
  , knownModules := deps
  , recordFields := []
  , coindRecords := [] }

def lookupVarOrSym (sc : ScopeEnv) (name : String) : Option (Sum String SymInfo) :=
  if sc.locals.contains name || sc.levelVars.contains name then
    some (.inl name)
  else if name.contains '.' then
    match sc.qualified.find? (fun (k, _) => k == name) with
    | some (_, info) => some (.inr info)
    | none           => none
  else
    match sc.unqualified.find? (fun (k, _) => k == name) with
    | some (_, info) => some (.inr info)
    | none           => none

def activeMixfixOps (sc : ScopeEnv) : List OpEntry :=
  let fromLocals := sc.locals.filterMap fun locName =>
    -- Local mixfix variable (e.g., `_≈_` in `Commutes₁ p q Dom _≈_ f g`) has Agda default `infix 20`!
    let q : QName := { full := ["__local_var__", locName], shown := locName }
    analyzeMixfix locName q false defaultAgdaFixity
  let fromUnqual := sc.unqualified.filterMap fun (visName, info) =>
    if sc.locals.contains visName then none
    else
      let q : QName := { full := info.canonPath, shown := visName }
      analyzeMixfix visName q (info.kind == .conSym) info.fixity
  let rec dedupQual : List (String × SymInfo) → List String → List (String × SymInfo)
    | [], _ => []
    | (k, i) :: rest, seen =>
        if !i.localName.contains '_' || i.localName.contains '.' || seen.contains k then
          dedupQual rest seen
        else
          (k, i) :: dedupQual rest (k :: seen)
  let fromQual := (dedupQual sc.qualified []).filterMap fun (qKey, info) =>
    let parts := qKey.splitOn "."
    if parts.length < 2 || parts.getLastD "" != info.localName then none
    else
      let qualPrefix := String.intercalate "." parts.dropLast
      let qualMixOpt : Option String :=
        if info.localName.startsWith "_" then
          let afterU := String.ofList (info.localName.toList.drop 1)
          if afterU.isEmpty || afterU.startsWith "_" then none
          else some ("_" ++ qualPrefix ++ "." ++ afterU)
        else
          some (qualPrefix ++ "." ++ info.localName)
      match qualMixOpt with
      | none => none
      | some qualMix =>
          let q : QName := { full := info.canonPath, shown := qKey }
          analyzeMixfix qualMix q (info.kind == .conSym) info.fixity
  fromLocals ++ fromUnqual ++ fromQual

def addSymUnqual (sc : ScopeEnv) (visName : String) (info : SymInfo) : ScopeEnv :=
  let qKey := String.intercalate "." sc.modPrefix ++ "." ++ visName
  { sc with
    unqualified := (visName, info) :: sc.unqualified.filter (fun (k, _) => k != visName)
    qualified   := (qKey, info) :: sc.qualified }

def addLocalVars (sc : ScopeEnv) (xs : List String) : ScopeEnv :=
  { sc with locals := xs.reverse ++ sc.locals }

def addLevelVars (sc : ScopeEnv) (xs : List String) : ScopeEnv :=
  { sc with levelVars := xs.reverse ++ sc.levelVars }

-- §1 Layout Splitting (Agda Off-Side Rule)

-- Split tokens of an indented layout block into individual declaration token slices.
-- Every declaration starts at column `blockCol` when delimiter nesting depth == 0.
partial def splitLayoutBlock (toks : List Token) : PrismOutcome (List (List Token)) :=
  let toks := toks.filter (fun t => t.kind != .eof)
  match toks with
  | [] => .translated []
  | firstTok :: _ =>
      let blockCol := firstTok.col
      let rec loop (rem : List Token) (pDepth bDepth letDepth : Nat)
          (cur : List Token) (acc : List (List Token)) : PrismOutcome (List (List Token)) :=
        match rem with
        | [] =>
            let acc' := if cur.isEmpty then acc else cur.reverse :: acc
            .translated acc'.reverse
        | t :: rest =>
            let openBoundary :=
              pDepth == 0 && bDepth == 0 && letDepth == 0 && !cur.isEmpty
            if openBoundary && t.firstOnLine && t.col < blockCol then
              .syntaxErr s!"line {t.line}, col {t.col}: layout indentation error (expected column >= {blockCol})"
            else if openBoundary && t.kind == .semi then
              loop rest 0 0 0 [] (cur.reverse :: acc)
            else if openBoundary && t.firstOnLine && t.col == blockCol then
              loop (t :: rest) 0 0 0 [] (cur.reverse :: acc)
            else
              let pDepth' := match t.kind with
                | .lparen => pDepth + 1
                | .rparen => pDepth - 1
                | _       => pDepth
              let bDepth' := match t.kind with
                | .lbrace | .lbrace2 => bDepth + 1
                | .rbrace | .rbrace2 => bDepth - 1
                | _                  => bDepth
              let letDepth' := match t.kind with
                | .kwLet => letDepth + 1
                | .kwIn  => letDepth - 1
                | _      => letDepth
              if (t.kind == .rparen && pDepth == 0) ||
                 ((t.kind == .rbrace || t.kind == .rbrace2) && bDepth == 0) then
                .syntaxErr s!"line {t.line}, col {t.col}: unmatched closing delimiter"
              else
                loop rest pDepth' bDepth' letDepth' (t :: cur) acc
      loop toks 0 0 0 [] []

-- Check balanced parens/braces in a token slice before expression parsing.
def checkBalancedDelims (toks : List Token) : PrismOutcome Unit :=
  let rec go (rem : List Token) (stack : List (TokKind × Nat × Nat)) : PrismOutcome Unit :=
    match rem with
    | [] =>
        match stack with
        | [] => .translated ()
        | (_, ln, cl) :: _ => .syntaxErr s!"line {ln}, col {cl}: unclosed delimiter"
    | t :: rest =>
        match t.kind with
        | .lparen  => go rest ((.rparen, t.line, t.col) :: stack)
        | .lbrace  => go rest ((.rbrace, t.line, t.col) :: stack)
        | .lbrace2 => go rest ((.rbrace2, t.line, t.col) :: stack)
        | .rparen | .rbrace | .rbrace2 =>
            match stack with
            | (expected, _, _) :: s' =>
                if expected == t.kind then go rest s'
                else .syntaxErr s!"line {t.line}, col {t.col}: mismatched closing delimiter"
            | [] => .syntaxErr s!"line {t.line}, col {t.col}: unexpected closing delimiter"
        | _ => go rest stack
  go toks []

-- Split top-level tokens on a specific token kind outside `()`, `{}`, `⦃⦄`, `let..in`.
partial def splitTopOn (pred : TokKind → Bool) (toks : List Token) : Option (List Token × Token × List Token) :=
  let rec go (rem : List Token) (d : Nat) (letD : Nat) (left : List Token) :
      Option (List Token × Token × List Token) :=
    match rem with
    | [] => none
    | t :: rest =>
        if d == 0 && letD == 0 && pred t.kind then
          some (left.reverse, t, rest)
        else
          let d' := match t.kind with
            | .lparen | .lbrace | .lbrace2 => d + 1
            | .rparen | .rbrace | .rbrace2 => d - 1
            | _ => d
          let letD' := match t.kind with
            | .kwLet => letD + 1
            | .kwIn  => letD - 1
            | _      => letD
          go rest d' letD' (t :: left)
  go toks 0 0 []

partial def splitAllTopOn (pred : TokKind → Bool) (toks : List Token) : List (List Token) :=
  match splitTopOn pred toks with
  | none => if toks.isEmpty then [] else [toks]
  | some (l, _, r) =>
      let rest := splitAllTopOn pred r
      if l.isEmpty then rest else l :: rest

-- Split a function clause on its clause-level `where` keyword without mistaking
-- `λ where` (extended pattern-matching lambda) for a clause `where` block.
partial def splitClauseWhere (toks : List Token) : PrismOutcome (List Token × List Token) :=
  let rec go (rem : List Token) (d : Nat) (letD : Nat) (seenLamWhere : Bool) (left : List Token) :
      PrismOutcome (List Token × List Token) :=
    match rem with
    | [] => .translated (left.reverse, [])
    | t :: rest =>
        let prevIsLam : Bool := match left.head? with | some p => p.kind == .kwLambda | none => false
        if d == 0 && letD == 0 && t.kind == .kwWhere then
          if prevIsLam then
            go rest d letD true (t :: left)
          else if seenLamWhere then
            .bot "clause combining 'λ where' and 'where' routed to Agda"
          else
            .translated (left.reverse, rest)
        else
          let d' := match t.kind with
            | .lparen | .lbrace | .lbrace2 => d + 1
            | .rparen | .rbrace | .rbrace2 => d - 1
            | _ => d
          let letD' := match t.kind with
            | .kwLet => letD + 1
            | .kwIn  => letD - 1
            | _      => letD
          go rest d' letD' seenLamWhere (t :: left)
  go toks 0 0 false []

-- §2 Expression & Pattern Mixfix + Recursive-Descent Parser

private def tokDesc (t : Token) : String :=
  s!"line {t.line}, col {t.col}"

private def makeNameRef (sc : ScopeEnv) (raw : String) : PrismOutcome Expr :=
  match lookupVarOrSym sc raw with
  | some (.inl v) => .translated (.var v)
  | some (.inr info) =>
      let q : QName := { full := info.canonPath, shown := raw }
      match info.kind with
      | .conSym => .translated (.con q)
      | _       => .translated (.def_ q)
  | none => .syntaxErr s!"not in scope: '{raw}'"

private def applyOpExpr (op : OpEntry) (args : List Expr) : Expr :=
  let hd : Expr :=
    match op.qname.full with
    | ["__local_var__", locName] => .var locName
    | _ => if op.isCon then .con op.qname else .def_ op.qname
  args.foldl (fun acc a => .app acc (visArg a)) hd

private def applyOpPat (op : OpEntry) (args : List Pat) : PrismOutcome Pat :=
  if !op.isCon then
    .syntaxErr s!"non-constructor operator '{op.opName}' cannot appear in pattern"
  else
    .translated (.conP op.qname (args.map visArg))

-- Extract matched parenthesized/braced prefix from a token list.
partial def takeMatchedGroup (openK closeK : TokKind) (toks : List Token) :
    PrismOutcome (List Token × List Token) :=
  match toks with
  | [] => .syntaxErr "unexpected end of input while reading group"
  | t :: rest =>
      if t.kind != openK then
        .syntaxErr s!"{tokDesc t}: expected opening group delimiter"
      else
        let rec go (rem : List Token) (depth : Nat) (acc : List Token) :
            PrismOutcome (List Token × List Token) :=
          match rem with
          | [] => .syntaxErr s!"{tokDesc t}: unclosed group"
          | x :: xs =>
              if x.kind == openK then go xs (depth + 1) (x :: acc)
              else if x.kind == closeK then
                if depth == 1 then .translated (acc.reverse, xs)
                else go xs (depth - 1) (x :: acc)
              else go xs depth (x :: acc)
        go rest 1 []

-- Match internal keyword parts of a multi-part operator like `if` _ `then` _ `else` _
partial def matchInternalParts (parts : List String) (toks : List Token) :
    Option (List (List Token) × List Token) :=
  match parts with
  | [] => some ([], toks)
  | p :: ps =>
      let findPart := splitTopOn (fun k => k == .ident p) toks
      match findPart with
      | none => none
      | some (holeToks, _, afterToks) =>
          if holeToks.isEmpty then none
          else
            match matchInternalParts ps afterToks with
            | none => none
            | some (moreHoles, tailToks) => some (holeToks :: moreHoles, tailToks)

inductive MixItem (α : Type) : Type where
  | operand : α → MixItem α
  | binOp   : OpEntry → List α → FixLevel → Token → MixItem α
  | preOp   : OpEntry → List α → FixLevel → Token → MixItem α

-- Reduce mixfix operator/operand stream enforcing Agda's exact partial-order precedence DAG.
mutual
  partial def mixFoldItems {α : Type} (mkApp : OpEntry → List α → PrismOutcome α)
      (stk : List (MixItem α)) (rem : List (MixItem α)) : PrismOutcome α :=
    match rem with
    | [] => mixUnwindAll mkApp stk
    | item :: rest =>
        match item with
        | .operand _ => mixFoldItems mkApp (item :: stk) rest
        | .preOp _ _ _ _ => mixFoldItems mkApp (item :: stk) rest
        | .binOp op2 mid2 fx2 tok2 =>
            mixPushBinOp mkApp stk op2 mid2 fx2 tok2 rest

  partial def mixPushBinOp {α : Type} (mkApp : OpEntry → List α → PrismOutcome α)
      (stk : List (MixItem α)) (op2 : OpEntry) (mid2 : List α)
      (fx2 : FixLevel) (tok2 : Token) (rest : List (MixItem α)) : PrismOutcome α :=
    match stk with
    | [.operand _] => mixFoldItems mkApp (.binOp op2 mid2 fx2 tok2 :: stk) rest
    | .operand rhs1 :: .binOp op1 mid1 fx1 _ :: tail =>
        match compareInfixPrec fx1 fx2 with
        | .leftTighter => do
            match tail with
            | .operand lhs1 :: tail' =>
                let combined ← mkApp op1 ([lhs1] ++ mid1 ++ [rhs1])
                mixPushBinOp mkApp (.operand combined :: tail') op2 mid2 fx2 tok2 rest
            | _ => .syntaxErr s!"{tokDesc tok2}: malformed binary mixfix expression"
        | .rightTighter =>
            mixFoldItems mkApp (.binOp op2 mid2 fx2 tok2 :: stk) rest
        | .ambiguous =>
            .syntaxErr s!"{tokDesc tok2}: ambiguous mixfix precedence between '{op1.opName}' and '{op2.opName}'"
    | .operand rhs1 :: .preOp op1 mid1 fx1 _ :: tail =>
        match comparePrefixInfix fx1 fx2 with
        | .leftTighter => do
            let combined ← mkApp op1 (mid1 ++ [rhs1])
            mixPushBinOp mkApp (.operand combined :: tail) op2 mid2 fx2 tok2 rest
        | .rightTighter =>
            mixFoldItems mkApp (.binOp op2 mid2 fx2 tok2 :: stk) rest
        | .ambiguous =>
            .syntaxErr s!"{tokDesc tok2}: ambiguous mixfix precedence between prefix '{op1.opName}' and '{op2.opName}'"
    | _ => .syntaxErr s!"{tokDesc tok2}: binary operator '{op2.opName}' missing left operand"

  partial def mixUnwindAll {α : Type} (mkApp : OpEntry → List α → PrismOutcome α)
      (stk : List (MixItem α)) : PrismOutcome α :=
    match stk with
    | [.operand x] => .translated x
    | .operand rhs :: .preOp op mid _ _ :: tail => do
        let combined ← mkApp op (mid ++ [rhs])
        mixUnwindAll mkApp (.operand combined :: tail)
    | .operand rhs :: .binOp op mid _ _ :: .operand lhs :: tail => do
        let combined ← mkApp op ([lhs] ++ mid ++ [rhs])
        mixUnwindAll mkApp (.operand combined :: tail)
    | _ => .syntaxErr "malformed mixfix operator expression (missing operand)"
end

partial def reduceMixfix {α : Type} (mkApp : OpEntry → List α → PrismOutcome α)
    (items : List (MixItem α)) : PrismOutcome α :=
  mixFoldItems mkApp [] items

private def splitQualIdent (w : String) : Option (String × String) :=
  let parts := w.splitOn "."
  if parts.length >= 2 then
    some (String.intercalate "." parts.dropLast, parts.getLastD "")
  else
    none

private def lookupBinaryInfixForSection (sc : ScopeEnv) (fullOpName : String) : Option (QName × Bool) :=
  match lookupVarOrSym sc fullOpName with
  | some (.inl v) =>
      let q : QName := { full := ["__local_var__", v], shown := v }
      match analyzeMixfix v q false defaultAgdaFixity with
      | some { shape := .infixOp [_] _, .. } => some (q, false)
      | _ => none
  | some (.inr info) =>
      let q : QName := { full := info.canonPath, shown := fullOpName }
      match analyzeMixfix info.localName q (info.kind == .conSym) info.fixity with
      | some { shape := .infixOp [_] _, .. } => some (q, info.kind == .conSym)
      | _ => none
  | none => none

private def resolveLeftSectionOp (sc : ScopeEnv) (w : String) : Option (QName × Bool) :=
  if (lookupVarOrSym sc w).isSome then none
  else
    let candOpt : Option String :=
      match splitQualIdent w with
      | none =>
          if !w.startsWith "_" && w.endsWith "_" && w.toList.length >= 2 then
            some ("_" ++ w)
          else none
      | some (qual, loc) =>
          if !loc.startsWith "_" && loc.endsWith "_" && loc.toList.length >= 2 then
            some (qual ++ "._" ++ loc)
          else none
    candOpt.bind (lookupBinaryInfixForSection sc)

private def resolveRightSectionOp (sc : ScopeEnv) (w : String) : Option (QName × Bool) :=
  if (lookupVarOrSym sc w).isSome then none
  else
    let candOpt : Option String :=
      match splitQualIdent w with
      | none =>
          if w.startsWith "_" && !w.endsWith "_" && w.toList.length >= 2 then
            some (w ++ "_")
          else none
      | some (qual, loc) =>
          if loc.startsWith "_" && !loc.endsWith "_" && loc.toList.length >= 2 then
            some (qual ++ "." ++ loc ++ "_")
          else none
    candOpt.bind (lookupBinaryInfixForSection sc)

mutual
  partial def parseExpr (sc : ScopeEnv) (toks : List Token) : PrismOutcome Expr := do
    if toks.isEmpty then
      .syntaxErr "expected expression, found empty token sequence"
    else
      checkBalancedDelims toks
      -- Check top-level `let ... in ...`
      match toks.head? with
      | some { kind := .kwLet, .. } => parseLetExpr sc (toks.drop 1)
      | some { kind := .kwDo, .. } => .bot "do-notation block requires Agda desugarer"
      | some { kind := .kwLambda, line := ln, col := cl, .. } =>
          parseLambdaExpr sc ln cl (toks.drop 1)
      | some { kind := .kwForall, .. } =>
          match splitTopOn (· == .symArrow) (toks.drop 1) with
          | none => .syntaxErr "expected '→' after '∀' binder"
          | some (bindToks, _, bodyToks) => do
              let (binds, sc') ← parseForallBinds sc bindToks
              let body ← parseExpr sc' bodyToks
              .translated (binds.foldr Expr.pi body)
      | _ =>
          -- Function arrow `→` binds looser than all mixfix operators and is right-associative,
          -- EXCEPT any `→` occurring after an unparenthesized top-level `λ` / `∀` / `let`,
          -- which always extends to the end of `toks` (`e >>= λ r → body`)!
          match splitTopOn (· == .symArrow) toks with
          | some (lhsToks, arrowTok, rhsToks) =>
              if (splitTopOn (fun k => k == .kwLambda || k == .kwForall || k == .kwLet) lhsToks).isSome then
                parseMixfixExpr sc toks
              else if lhsToks.isEmpty || rhsToks.isEmpty then
                .syntaxErr s!"{tokDesc arrowTok}: missing domain or codomain around '→'"
              else
                parsePiOrFun sc lhsToks rhsToks
          | none =>
              parseMixfixExpr sc toks

  partial def parsePiOrFun (sc : ScopeEnv) (lhsToks rhsToks : List Token) : PrismOutcome Expr := do
    -- Check if `lhsToks` is one or more typed telescope groups `(x y : A)` / `{x : A}` / `{{x : A}}`
    match tryParseTeleGroups sc lhsToks with
    | some (.translated (binds, sc')) => do
        let cod ← parseExpr sc' rhsToks
        .translated (binds.foldr Expr.pi cod)
    | some (.syntaxErr e) => .syntaxErr e
    | some (.bot r)       => .bot r
    | none =>
        -- Check single hidden/instance unnamed domain `{A} → B` or `{{A}} → B`
        match lhsToks with
        | { kind := .lbrace, .. } :: _ =>
            let (inner, rest) ← takeMatchedGroup .lbrace .rbrace lhsToks
            if rest.isEmpty then do
              let dom ← parseExpr sc inner
              let cod ← parseExpr sc rhsToks
              .translated (.fun_ { hid := .hidden, label := none, thing := dom } cod)
            else do
              let dom ← parseExpr sc lhsToks
              let cod ← parseExpr sc rhsToks
              .translated (.fun_ (visArg dom) cod)
        | { kind := .lbrace2, .. } :: _ =>
            let (inner, rest) ← takeMatchedGroup .lbrace2 .rbrace2 lhsToks
            if rest.isEmpty then do
              let dom ← parseExpr sc inner
              let cod ← parseExpr sc rhsToks
              .translated (.fun_ { hid := .inst, label := none, thing := dom } cod)
            else do
              let dom ← parseExpr sc lhsToks
              let cod ← parseExpr sc rhsToks
              .translated (.fun_ (visArg dom) cod)
        | _ => do
            let dom ← parseExpr sc lhsToks
            let cod ← parseExpr sc rhsToks
            .translated (.fun_ (visArg dom) cod)

  partial def tryParseTeleGroups (sc : ScopeEnv) (toks : List Token) :
      Option (PrismOutcome (List Bind × ScopeEnv)) :=
    let rec collectGroups (curSc : ScopeEnv) (rem : List Token) (acc : List Bind) :
        Option (PrismOutcome (List Bind × ScopeEnv)) :=
      match rem with
      | [] =>
          if acc.isEmpty then none
          else some (.translated (acc.reverse, curSc))
      | { kind := .lparen, .. } :: _ =>
          match takeMatchedGroup .lparen .rparen rem with
          | .translated (inner, after) =>
              match splitTopOn (· == .symColon) inner with
              | none => none
              | some (namesToks, _, tyToks) =>
                  match parseBinderNames namesToks with
                  | none => none
                  | some xs =>
                      match parseBinderTypeAndExtend curSc .visible xs tyToks with
                      | .translated (b, nextSc) => collectGroups nextSc after (b :: acc)
                      | .syntaxErr e => some (.syntaxErr e)
                      | .bot r       => some (.bot r)
          | _ => none
      | { kind := .lbrace, .. } :: _ =>
          match takeMatchedGroup .lbrace .rbrace rem with
          | .translated (inner, after) =>
              match splitTopOn (· == .symColon) inner with
              | none => none
              | some (namesToks, _, tyToks) =>
                  match parseBinderNames namesToks with
                  | none => none
                  | some xs =>
                      match parseBinderTypeAndExtend curSc .hidden xs tyToks with
                      | .translated (b, nextSc) => collectGroups nextSc after (b :: acc)
                      | .syntaxErr e => some (.syntaxErr e)
                      | .bot r       => some (.bot r)
          | _ => none
      | { kind := .lbrace2, .. } :: _ =>
          match takeMatchedGroup .lbrace2 .rbrace2 rem with
          | .translated (inner, after) =>
              match splitTopOn (· == .symColon) inner with
              | none => none
              | some (namesToks, _, tyToks) =>
                  match parseBinderNames namesToks with
                  | none => none
                  | some xs =>
                      match parseBinderTypeAndExtend curSc .inst xs tyToks with
                      | .translated (b, nextSc) => collectGroups nextSc after (b :: acc)
                      | .syntaxErr e => some (.syntaxErr e)
                      | .bot r       => some (.bot r)
          | _ => none
      | _ => none
    collectGroups sc toks []

  partial def parseBinderNames (toks : List Token) : Option (List String) :=
    if toks.isEmpty then none
    else
      let rec go : List Token → List String → Option (List String)
        | [], acc => some acc.reverse
        | { kind := .ident s, .. } :: rest, acc =>
            if s.contains '.' then none else go rest (s :: acc)
        | { kind := .underscore, .. } :: rest, acc => go rest ("_" :: acc)
        | _, _ => none
      go toks []

  partial def parseBinderTypeAndExtend (sc : ScopeEnv) (h : Hiding) (xs : List String)
      (tyToks : List Token) : PrismOutcome (Bind × ScopeEnv) := do
    -- Detect universe `Level` binder `{a : Level}` -> extend `levelVars`
    match tyToks with
    | [{ kind := .ident "Level", .. }] =>
        .translated (.bind h xs (.def_ (mkQ ["Agda", "Primitive", "Level"])), addLevelVars sc xs)
    | _ =>
        let ty ← parseExpr sc tyToks
        .translated (.bind h xs ty, addLocalVars sc xs)

  partial def parseForallBinds (sc : ScopeEnv) (toks : List Token) :
      PrismOutcome (List Bind × ScopeEnv) := do
    if toks.isEmpty then
      .syntaxErr "empty binder list after '∀'"
    else
      let rec loop (curSc : ScopeEnv) (rem : List Token) (acc : List Bind) :
          PrismOutcome (List Bind × ScopeEnv) :=
        match rem with
        | [] => .translated (acc.reverse, curSc)
        | { kind := .lparen, .. } :: _ => do
            let (inner, after) ← takeMatchedGroup .lparen .rparen rem
            match splitTopOn (· == .symColon) inner with
            | some (ns, _, tyT) =>
                match parseBinderNames ns with
                | some xs => do
                    let (b, nextSc) ← parseBinderTypeAndExtend curSc .visible xs tyT
                    loop nextSc after (b :: acc)
                | none => .syntaxErr "invalid binder names in '∀ (...)'"
            | none =>
                match parseBinderNames inner with
                | some xs =>
                    let b := Bind.bind .visible xs .meta_
                    loop (addLocalVars curSc xs) after (b :: acc)
                | none => .syntaxErr "invalid untyped binder in '∀ (...)'"
        | { kind := .lbrace, .. } :: _ => do
            let (inner, after) ← takeMatchedGroup .lbrace .rbrace rem
            match splitTopOn (· == .symColon) inner with
            | some (ns, _, tyT) =>
                match parseBinderNames ns with
                | some xs => do
                    let (b, nextSc) ← parseBinderTypeAndExtend curSc .hidden xs tyT
                    loop nextSc after (b :: acc)
                | none => .syntaxErr "invalid binder names in '∀ {...}'"
            | none =>
                match parseBinderNames inner with
                | some xs =>
                    let b := Bind.bind .hidden xs .meta_
                    loop (addLocalVars curSc xs) after (b :: acc)
                | none => .syntaxErr "invalid untyped binder in '∀ {...}'"
        | { kind := .lbrace2, .. } :: _ => do
            let (inner, after) ← takeMatchedGroup .lbrace2 .rbrace2 rem
            match splitTopOn (· == .symColon) inner with
            | some (ns, _, tyT) =>
                match parseBinderNames ns with
                | some xs => do
                    let (b, nextSc) ← parseBinderTypeAndExtend curSc .inst xs tyT
                    loop nextSc after (b :: acc)
                | none => .syntaxErr "invalid binder names in '∀ {{...}}'"
            | none => .syntaxErr "instance binder in '∀' requires explicit type"
        | { kind := .ident x, line := ln, col := cl, .. } :: after =>
            if x.contains '.' then
              .syntaxErr s!"line {ln}, col {cl}: qualified name '{x}' in binder"
            else
              let b := Bind.bind .visible [x] .meta_
              loop (addLocalVars curSc [x]) after (b :: acc)
        | { kind := .underscore, .. } :: after =>
            let b := Bind.bind .visible ["_"] .meta_
            loop curSc after (b :: acc)
        | t :: _ => .syntaxErr s!"{tokDesc t}: unexpected token in '∀' binder"
      loop sc toks []

  partial def parseLambdaExpr (sc : ScopeEnv) (ln cl : Nat) (toks : List Token) : PrismOutcome Expr :=
    match toks with
    | [{ kind := .lparen, .. }, { kind := .rparen, .. }] =>
        .translated (.absurdLam .visible)
    | [{ kind := .lbrace, .. }, { kind := .lparen, .. }, { kind := .rparen, .. }, { kind := .rbrace, .. }] =>
        .translated (.absurdLam .hidden)
    | { kind := .kwWhere, .. } :: afterWhere => do
        let armSlices ← splitLayoutBlock afterWhere
        if armSlices.isEmpty then
          .syntaxErr s!"line {ln}, col {cl}: empty 'λ where' block"
        else do
          let cs ← armSlices.mapM (parseLamCaseClause sc)
          .translated (.lamCase cs)
    | { kind := .lbrace, .. } :: _ =>
        -- Check `λ { x → e ; ... }` pattern-matching lambda vs `λ {x} → e` hidden arg lambda vs `λ {x} ()`!
        match splitTopOn (· == .symArrow) toks with
        | some (bindToks, _, bodyToks) => do
            let (binds, sc') ← parseForallBinds sc bindToks
            let body ← parseExpr sc' bodyToks
            .translated (binds.foldr wrapLamBind body)
        | none =>
            match parseTrailingAbsurd toks with
            | some (preToks, absHid) => do
                let (binds, _) ← parseForallBinds sc preToks
                .translated (binds.foldr wrapLamBind (.absurdLam absHid))
            | none => do
                let (braceInner, afterBrace) ← takeMatchedGroup .lbrace .rbrace toks
                if !afterBrace.isEmpty || braceInner.isEmpty then
                  .syntaxErr s!"line {ln}, col {cl}: malformed brace lambda"
                else do
                  let armSlices := splitAllTopOn (· == .semi) braceInner
                  let cs ← armSlices.mapM (parseLamCaseClause sc)
                  .translated (.lamCase cs)
    | _ =>
        match splitTopOn (· == .symArrow) toks with
        | none =>
            match parseTrailingAbsurd toks with
            | some (preToks, absHid) => do
                let (binds, _) ← parseForallBinds sc preToks
                .translated (binds.foldr wrapLamBind (.absurdLam absHid))
            | none => .syntaxErr s!"line {ln}, col {cl}: lambda missing '→'"
        | some (bindToks, _, bodyToks) => do
            let (binds, sc') ← parseForallBinds sc bindToks
            let body ← parseExpr sc' bodyToks
            .translated (binds.foldr wrapLamBind body)
    where
      hasAbsurdInPat : Pat → Bool
        | .absurdP     => true
        | .conP _ args => args.any (fun a => hasAbsurdInPat a.thing)
        | .asP _ p     => hasAbsurdInPat p
        | .recP fs     => fs.any (fun (_, p) => hasAbsurdInPat p)
        | _            => false

      parseLamArmPats (curSc : ScopeEnv) (rem : List Token) (acc : List (Arg Pat))
          (vars : List String) : PrismOutcome (List (Arg Pat) × List String) :=
        match rem with
        | [] => .translated (acc.reverse, vars)
        | t :: _ =>
            match t.kind with
            | .symDot | .dotIdent _ =>
                .bot "dot/copattern in extended lambda routed to Agda"
            | .lbrace => do
                let (inner, after) ← takeMatchedGroup .lbrace .rbrace rem
                match splitTopOn (· == .symEq) inner with
                | some ([{ kind := .ident lbl, .. }], _, pToks) => do
                    let (p, pv) ← parsePat curSc pToks
                    if pv.any (vars.contains ·) then
                      .syntaxErr s!"{tokDesc t}: duplicate pattern variable in extended lambda"
                    else
                      parseLamArmPats curSc after ({ hid := .hidden, label := some lbl, thing := p } :: acc) (vars ++ pv)
                | none => do
                    let (p, pv) ← parsePat curSc inner
                    if pv.any (vars.contains ·) then
                      .syntaxErr s!"{tokDesc t}: duplicate pattern variable in extended lambda"
                    else
                      parseLamArmPats curSc after ({ hid := .hidden, label := none, thing := p } :: acc) (vars ++ pv)
                | _ => .syntaxErr s!"{tokDesc t}: malformed implicit pattern in extended lambda"
            | .lbrace2 =>
                .bot "instance pattern in extended lambda routed to Agda"
            | .lparen => do
                let (inner, after) ← takeMatchedGroup .lparen .rparen rem
                if inner.isEmpty then
                  parseLamArmPats curSc after (visArg .absurdP :: acc) vars
                else do
                  let (p, pv) ← parsePat curSc inner
                  if pv.any (vars.contains ·) then
                    .syntaxErr s!"{tokDesc t}: duplicate pattern variable in extended lambda"
                  else
                    parseLamArmPats curSc after (visArg p :: acc) (vars ++ pv)
            | _ => do
                let (rawP, afterP) ← parseAtomicPat curSc rem
                let (p, pv) ← validateLinearPat rawP
                if pv.any (vars.contains ·) then
                  .syntaxErr s!"{tokDesc t}: duplicate pattern variable in extended lambda"
                else
                  parseLamArmPats curSc afterP (visArg p :: acc) (vars ++ pv)

      parseLamCaseClause (curSc : ScopeEnv) (armToks : List Token) : PrismOutcome Clause := do
        if (splitTopOn (fun k => k == .kwWith || k == .kwWhere || k == .kwRewrite) armToks).isSome then
          .bot "complex extended-lambda clause routed to Agda"
        else
          match splitTopOn (· == .symArrow) armToks with
          | some (patToks, arrowTok, rhsToks) =>
              if patToks.isEmpty || rhsToks.isEmpty then
                .syntaxErr s!"{tokDesc arrowTok}: malformed pattern-matching lambda clause"
              else do
                let (ps, pVars) ← parseLamArmPats curSc patToks [] []
                let rhsE ← parseExpr (addLocalVars curSc pVars) rhsToks
                .translated (.clause (.head (mkQ ["_lam_"]) ps) (.rhs rhsE) [])
          | none => do
              let (ps, _) ← parseLamArmPats curSc armToks [] []
              if ps.any (fun a => hasAbsurdInPat a.thing) then
                .translated (.clause (.head (mkQ ["_lam_"]) ps) .absurdRHS [])
              else
                .syntaxErr s!"line {ln}, col {cl}: pattern-matching lambda clause missing '→'"

      parseTrailingAbsurd (ts : List Token) : Option (List Token × Hiding) :=
        if ts.length >= 4 then
          let suf4 := ts.drop (ts.length - 4)
          match suf4 with
          | [{ kind := .lbrace, .. }, { kind := .lparen, .. }, { kind := .rparen, .. }, { kind := .rbrace, .. }] =>
              some (ts.take (ts.length - 4), .hidden)
          | _ =>
              let suf2 := ts.drop (ts.length - 2)
              match suf2 with
              | [{ kind := .lparen, .. }, { kind := .rparen, .. }] =>
                  some (ts.take (ts.length - 2), .visible)
              | _ => none
        else if ts.length >= 2 then
          let suf2 := ts.drop (ts.length - 2)
          match suf2 with
          | [{ kind := .lparen, .. }, { kind := .rparen, .. }] =>
              some (ts.take (ts.length - 2), .visible)
          | _ => none
        else none

      wrapLamBind (b : Bind) (body : Expr) : Expr :=
        match b with
        | .bind h xs .meta_ => xs.foldr (fun x acc => .lamT (.bind h [x] .meta_) acc) body
        | _                 => .lamT b body

  partial def parseLetExpr (sc : ScopeEnv) (toks : List Token) : PrismOutcome Expr := do
    match splitTopOn (· == .kwIn) toks with
    | none => .syntaxErr "'let' expression missing matching 'in'"
    | some (bindsToks, _, bodyToks) => do
        let declSlices ← splitLayoutBlock bindsToks
        if declSlices.isEmpty then
          .syntaxErr "empty 'let' binding block"
        else
          let rec parseLetItems (curSc : ScopeEnv) (slices : List (List Token))
              (acc : List LetBind) : PrismOutcome (List LetBind × ScopeEnv) :=
            match slices with
            | [] => .translated (acc.reverse, curSc)
            | s :: rest =>
                match splitTopOn (· == .symEq) s with
                | none =>
                    -- Signature-separated typed let: `x : T` followed by `x = e`!
                    match splitTopOn (· == .symColon) s with
                    | some ([{ kind := .ident x, .. }], colTok, tyT) =>
                        if tyT.isEmpty then
                          .syntaxErr s!"{tokDesc colTok}: empty type in 'let' signature"
                        else
                          match rest with
                          | nextS :: afterNext =>
                              match splitTopOn (· == .symEq) nextS with
                              | some ([{ kind := .ident x2, .. }], _, rhsT) =>
                                  if x == x2 && !rhsT.isEmpty then do
                                    let ty ← parseExpr curSc tyT
                                    let rhs ← parseExpr curSc rhsT
                                    parseLetItems (addLocalVars curSc [x]) afterNext (.letBind x ty rhs :: acc)
                                  else
                                    .bot "multi-clause or recursive 'let' item routed to Agda"
                              | _ => .bot "multi-clause 'let' item routed to Agda"
                          | [] => .syntaxErr s!"{tokDesc colTok}: 'let' type signature '{x} : ...' lacks definition"
                    | _ => .syntaxErr "malformed 'let' item (missing '=' or ':')"
                | some (lhsT, eqT, rhsT) =>
                    if lhsT.isEmpty || rhsT.isEmpty then
                      .syntaxErr s!"{tokDesc eqT}: malformed 'let' binding"
                    else
                      match splitTopOn (· == .symColon) lhsT with
                      | some (_, colTok, _) =>
                          -- In Agda concrete syntax, `let x : T = e` on one clause is a PARSE ERROR!
                          .syntaxErr s!"{tokDesc colTok}: inline 'let x : T = e' is invalid Agda syntax (use 'x : T ; x = e')"
                      | none =>
                          match lhsT with
                          | [{ kind := .ident x, .. }] => do
                              let rhs ← parseExpr curSc rhsT
                              parseLetItems (addLocalVars curSc [x]) rest (.letBind x .meta_ rhs :: acc)
                          | _ => do
                              let (pat, pVars) ← parsePat curSc lhsT
                              let rhs ← parseExpr curSc rhsT
                              parseLetItems (addLocalVars curSc pVars) rest (.letPat pat rhs :: acc)
          let (lbs, sc') ← parseLetItems sc declSlices []
          let body ← parseExpr sc' bodyToks
          .translated (.let_ lbs body)

  -- Parse a mixfix + application spine expression
  partial def parseMixfixExpr (sc : ScopeEnv) (toks : List Token) : PrismOutcome Expr := do
    -- Handle binary operator sections: `(_op rhs)`, `(Qual._op rhs)`, `(lhs op_)`, `(lhs Qual.op_)`!
    if toks.length >= 2 then
      if let some { kind := .ident wFirst, .. } := toks.head? then
        if let some (opQ, isCon) := resolveRightSectionOp sc wFirst then do
          let rhsE ← parseExpr sc (toks.drop 1)
          let hd : Expr := match opQ.full with
            | ["__local_var__", v] => .var v
            | _ => if isCon then .con opQ else .def_ opQ
          let secVar := if sc.locals.contains "section" then "_ag_sec" else "section"
          return .lamT (.bind .visible [secVar] .meta_) (.app (.app hd (visArg (.var secVar))) (visArg rhsE))
      if let some { kind := .ident wLast, .. } := toks.getLast? then
        if let some (opQ, isCon) := resolveLeftSectionOp sc wLast then do
          let lhsE ← parseExpr sc (toks.take (toks.length - 1))
          let hd : Expr := match opQ.full with
            | ["__local_var__", v] => .var v
            | _ => if isCon then .con opQ else .def_ opQ
          let secVar := if sc.locals.contains "section" then "_ag_sec" else "section"
          return .lamT (.bind .visible [secVar] .meta_) (.app (.app hd (visArg lhsE)) (visArg (.var secVar)))
    let ops := activeMixfixOps sc
    let rec scanItems (rem : List Token) (curApp : List (Arg Expr))
        (items : List (MixItem Expr)) : PrismOutcome Expr := do
      let flushApp (itemsAcc : List (MixItem Expr)) : PrismOutcome (List (MixItem Expr)) :=
        match curApp with
        | [] => .translated itemsAcc
        | hd :: args =>
            if hd.hid != .visible || hd.label.isSome then
              .syntaxErr "unexpected implicit argument in head position"
            else
              let e := args.foldl Expr.app hd.thing
              .translated (.operand e :: itemsAcc)
      match rem with
      | [] => do
          let allItems ← flushApp items
          reduceMixfix (fun op as => .translated (applyOpExpr op as)) allItems.reverse
      | t :: rest =>
          -- Check if `t` starts a known prefix, infix, or closed mixfix operator!
          match t.kind with
          | .ident w =>
              -- 1. Closed mixfix `[` ... `]`
              let closedMatch := ops.find? fun op =>
                match op.shape with
                | .closedOp (p0 :: _) => p0 == w
                | _ => false
              let prefixMatch := ops.find? fun op =>
                match op.shape with
                | .prefixOp (p0 :: _) _ => p0 == w
                | _ => false
              let infixMatch := ops.find? fun op =>
                match op.shape with
                | .infixOp (p0 :: _) _ => p0 == w
                | _ => false
              if let some op := closedMatch then
                match op.shape with
                | .closedOp (_ :: innerParts) =>
                    match matchInternalParts innerParts rest with
                    | none => .syntaxErr s!"{tokDesc t}: unclosed mixfix operator '{op.opName}'"
                    | some (holeSlices, afterOp) => do
                        let holeExprs ← holeSlices.mapM (parseExpr sc)
                        let atom := applyOpExpr op holeExprs
                        scanItems afterOp (curApp ++ [visArg atom]) items
                | _ => .syntaxErr "internal mixfix error"
              else if let some op := prefixMatch then
                match op.shape with
                | .prefixOp (_ :: innerParts) fx => do
                    let items' ← flushApp items
                    -- Note: in Agda, a prefix operator can only appear where an operand is expected
                    -- (start of expression, after binary op, or after another prefix op)!
                    match items' with
                    | .operand _ :: _ =>
                        .syntaxErr s!"{tokDesc t}: prefix operator '{op.opName}' applied as argument without parentheses"
                    | _ =>
                        match matchInternalParts innerParts rest with
                        | none => .syntaxErr s!"{tokDesc t}: incomplete mixfix operator '{op.opName}'"
                        | some (holeSlices, afterOp) => do
                            let holeExprs ← holeSlices.mapM (parseExpr sc)
                            scanItems afterOp [] (.preOp op holeExprs fx t :: items')
                | _ => .syntaxErr "internal mixfix error"
              else if let some op := infixMatch then
                match op.shape with
                | .infixOp (_ :: innerParts) fx => do
                    let items' ← flushApp items
                    match matchInternalParts innerParts rest with
                    | none => .syntaxErr s!"{tokDesc t}: incomplete mixfix operator '{op.opName}'"
                    | some (holeSlices, afterOp) => do
                        let holeExprs ← holeSlices.mapM (parseExpr sc)
                        scanItems afterOp [] (.binOp op holeExprs fx t :: items')
                | _ => .syntaxErr "internal mixfix error"
              else do
                let atom ← makeNameRef sc w
                scanItems rest (curApp ++ [visArg atom]) items
          | .kwRecord => do
              -- `record { f = e ; ... }` or `record base { f = e ; ... }`
              match rest with
              | { kind := .lbrace, .. } :: _ => do
                  let (braceInner, afterBrace) ← takeMatchedGroup .lbrace .rbrace rest
                  let flds ← parseRecFieldAssigns sc braceInner
                  scanItems afterBrace (curApp ++ [visArg (.rec_ flds)]) items
              | _ => do
                  let (baseArg, afterBase) ← parseSingleAtom sc rest
                  match afterBase with
                  | { kind := .lbrace, .. } :: _ => do
                      let (braceInner, afterBrace) ← takeMatchedGroup .lbrace .rbrace afterBase
                      let flds ← parseRecFieldAssigns sc braceInner
                      scanItems afterBrace (curApp ++ [visArg (.recUpd baseArg flds)]) items
                  | _ => .syntaxErr (tokDesc t ++ ": expected '{ ... }' in record expression/update")
          | .lparen => do
              let (inner, after) ← takeMatchedGroup .lparen .rparen rem
              if inner.isEmpty then
                .syntaxErr s!"{tokDesc t}: unexpected '()' in expression"
              else do
                let e ← parseExpr sc inner
                scanItems after (curApp ++ [visArg e]) items
          | .lbrace => do
              let (inner, after) ← takeMatchedGroup .lbrace .rbrace rem
              if inner.isEmpty then
                .syntaxErr (tokDesc t ++ ": empty hidden argument '{}'")
              else
                match splitTopOn (· == .symEq) inner with
                | some ([{ kind := .ident lbl, .. }], _, valToks) => do
                    let v ← parseExpr sc valToks
                    scanItems after (curApp ++ [{ hid := .hidden, label := some lbl, thing := v }]) items
                | none => do
                    let v ← parseExpr sc inner
                    scanItems after (curApp ++ [{ hid := .hidden, label := none, thing := v }]) items
                | _ => .syntaxErr s!"{tokDesc t}: malformed named implicit argument"
          | .lbrace2 => do
              let (inner, after) ← takeMatchedGroup .lbrace2 .rbrace2 rem
              if inner.isEmpty then
                .syntaxErr s!"{tokDesc t}: empty instance argument"
              else do
                let v ← parseExpr sc inner
                scanItems after (curApp ++ [{ hid := .inst, label := none, thing := v }]) items
          | .natLit n   => scanItems rest (curApp ++ [visArg (.lit (.natL n))]) items
          | .strLit s   => scanItems rest (curApp ++ [visArg (.lit (.strL s))]) items
          | .charLit c  => scanItems rest (curApp ++ [visArg (.lit (.charL c))]) items
          | .kwSet lvl  => scanItems rest (curApp ++ [visArg (.set lvl)]) items
          | .kwProp     => .bot "Agda Prop universe requires Agda typechecker"
          | .underscore => scanItems rest (curApp ++ [visArg .meta_]) items
          | .question | .holeLit => scanItems rest (curApp ++ [visArg .hole]) items
          | .kwLambda => do
              -- Trailing lambda argument `f λ x → e` or `m >>= λ x → e` (valid in Agda!)
              let lamE ← parseLambdaExpr sc t.line t.col rest
              scanItems [] (curApp ++ [visArg lamE]) items
          | .kwLet => do
              let letE ← parseLetExpr sc rest
              scanItems [] (curApp ++ [visArg letE]) items
          | .kwForall => do
              let faE ← parseExpr sc rem
              scanItems [] (curApp ++ [visArg faE]) items
          | _ => .syntaxErr s!"{tokDesc t}: unexpected token in expression"
    scanItems toks [] []

  partial def parseSingleAtom (sc : ScopeEnv) (toks : List Token) : PrismOutcome (Expr × List Token) :=
    match toks with
    | [] => .syntaxErr "expected atomic expression"
    | t :: rest =>
        match t.kind with
        | .lparen => do
            let (inner, after) ← takeMatchedGroup .lparen .rparen toks
            let e ← parseExpr sc inner
            .translated (e, after)
        | .ident w => do
            let e ← makeNameRef sc w
            .translated (e, rest)
        | _ => .syntaxErr s!"{tokDesc t}: expected record base expression"

  partial def parseRecFieldAssigns (sc : ScopeEnv) (toks : List Token) :
      PrismOutcome (List (String × Expr)) := do
    if toks.isEmpty then .translated []
    else
      let parts := splitAllTopOn (· == .semi) toks
      parts.mapM fun item =>
        match splitTopOn (· == .symEq) item with
        | some ([{ kind := .ident f, .. }], _, valToks) => do
            let e ← parseExpr sc valToks
            .translated (f, e)
        | _ => .syntaxErr "malformed field assignment inside 'record { ... }'"

  -- §3 Pattern Parser (enforces constructor-only application, mixfix DAG, and linear pattern variables)
  partial def validateLinearPat (pat : Pat) : PrismOutcome (Pat × List String) :=
    let rec collectLinearVars : Pat → List String
      | .varP x      => [x]
      | .conP _ args => args.flatMap (fun a => collectLinearVars a.thing)
      | .asP x p     => x :: collectLinearVars p
      | .recP fs     => fs.flatMap (fun (_, p) => collectLinearVars p)
      | _            => []
    let rec checkNoDupVars : List String → List String → Option String
      | [], _ => none
      | x :: xs, seen =>
          if seen.contains x then some x else checkNoDupVars xs (x :: seen)
    let vars := collectLinearVars pat
    match checkNoDupVars vars [] with
    | some dup => .syntaxErr s!"duplicate pattern variable '{dup}' (non-linear pattern)"
    | none     => .translated (pat, vars)

  partial def parsePat (sc : ScopeEnv) (toks : List Token) : PrismOutcome (Pat × List String) := do
    let pat ← parseMixfixPat sc toks
    validateLinearPat pat

  partial def parseMixfixPat (sc : ScopeEnv) (toks : List Token) : PrismOutcome Pat := do
    if toks.isEmpty then .syntaxErr "empty pattern"
    checkBalancedDelims toks
    let ops := activeMixfixOps sc
    let rec scanPat (rem : List Token) (curCon : Option QName) (curArgs : List (Arg Pat))
        (curAtom : Option Pat) (items : List (MixItem Pat)) : PrismOutcome Pat := do
      let flushPat (itemsAcc : List (MixItem Pat)) : PrismOutcome (List (MixItem Pat)) :=
        match curCon, curAtom with
        | some cq, none => .translated (.operand (.conP cq curArgs) :: itemsAcc)
        | none, some p  =>
            if curArgs.isEmpty then .translated (.operand p :: itemsAcc)
            else .syntaxErr "non-constructor pattern cannot be applied to arguments"
        | none, none    => .translated itemsAcc
        | _, _          => .syntaxErr "internal pattern state error"
      let pushAtomPat (p : Pat) (after : List Token) (itemsAcc : List (MixItem Pat)) : PrismOutcome Pat :=
        match curCon, curAtom with
        | some cq, none => scanPat after (some cq) (curArgs ++ [visArg p]) none itemsAcc
        | none, none    => scanPat after none [] (some p) itemsAcc
        | _, _          => .syntaxErr "non-constructor pattern applied to argument"
      match rem with
      | [] => do
          let allItems ← flushPat items
          reduceMixfix applyOpPat allItems.reverse
      | t :: rest =>
          match t.kind with
          | .symDot | .dotIdent _ =>
              .bot "dot/copattern in LHS requires Agda unifier/forced-pattern check"
          | .ident w =>
              let infixMatch := ops.find? fun op =>
                match op.shape with
                | .infixOp (p0 :: _) _ => p0 == w
                | _ => false
              if let some op := infixMatch then
                match op.shape with
                | .infixOp (_ :: innerParts) fx => do
                    let items' ← flushPat items
                    match matchInternalParts innerParts rest with
                    | none => .syntaxErr s!"{tokDesc t}: incomplete mixfix pattern '{op.opName}'"
                    | some (holeSlices, afterOp) => do
                        let holePats ← holeSlices.mapM (parseMixfixPat sc)
                        scanPat afterOp none [] none (.binOp op holePats fx t :: items')
                | _ => .syntaxErr "internal mixfix pattern error"
              else
                -- Check `@` as-pattern: `x@(...)` or `x @ p` -> Agda writes `x@p` without spaces (`@` is a delimiter!)
                match rest with
                | { kind := .atSign, .. } :: afterAt => do
                    if w.contains '.' then
                      .syntaxErr s!"{tokDesc t}: qualified name before '@' in pattern"
                    let (subP, afterSub) ← parseAtomicPat sc afterAt
                    pushAtomPat (.asP w subP) afterSub items
                | _ =>
                    match lookupVarOrSym sc w with
                    | some (.inr info) =>
                        if info.kind == .conSym then
                          let cq : QName := { full := info.canonPath, shown := w }
                          match curCon, curAtom with
                          | none, none => scanPat rest (some cq) [] none items
                          | some headCon, none =>
                              -- Zero-argument constructor argument to `headCon`!
                              if info.conArity == 0 then
                                scanPat rest (some headCon) (curArgs ++ [visArg (.conP cq [])]) none items
                              else
                                .syntaxErr s!"{tokDesc t}: constructor '{w}' with arguments must be parenthesized in pattern"
                          | _, _ => .syntaxErr s!"{tokDesc t}: non-constructor applied in pattern"
                        else if w.contains '.' then
                          .syntaxErr s!"{tokDesc t}: '{w}' is not a constructor"
                        else
                          -- Unqualified non-constructor name in pattern shadows as a pattern variable in Agda!
                          pushAtomPat (.varP w) rest items
                    | _ =>
                        if w.contains '.' then
                          .syntaxErr s!"{tokDesc t}: unknown constructor '{w}' in pattern"
                        else
                          pushAtomPat (.varP w) rest items
          | _ => do
              -- Check hidden/instance pattern arguments `{p}` or `{{p}}` when under a constructor or top-level
              match t.kind with
              | .lbrace => do
                  let (inner, after) ← takeMatchedGroup .lbrace .rbrace rem
                  match curCon with
                  | some cq =>
                      match splitTopOn (· == .symEq) inner with
                      | some ([{ kind := .ident lbl, .. }], _, pToks) => do
                          let p ← parseMixfixPat sc pToks
                          scanPat after (some cq) (curArgs ++ [{ hid := .hidden, label := some lbl, thing := p }]) none items
                      | none => do
                          let p ← parseMixfixPat sc inner
                          scanPat after (some cq) (curArgs ++ [{ hid := .hidden, label := none, thing := p }]) none items
                      | _ => .syntaxErr s!"{tokDesc t}: malformed implicit pattern"
                  | none => .syntaxErr s!"{tokDesc t}: unexpected implicit pattern outside constructor/head"
              | _ => do
                  let (atomP, after) ← parseAtomicPat sc rem
                  pushAtomPat atomP after items
    scanPat toks none [] none []

  partial def parseAtomicPat (sc : ScopeEnv) (toks : List Token) : PrismOutcome (Pat × List Token) :=
    match toks with
    | [] => .syntaxErr "expected atomic pattern"
    | t :: rest =>
        match t.kind with
        | .lparen => do
            let (inner, after) ← takeMatchedGroup .lparen .rparen toks
            if inner.isEmpty then
              .translated (.absurdP, after)
            else do
              let p ← parseMixfixPat sc inner
              .translated (p, after)
        | .underscore => .translated (.wildP, rest)
        | .natLit n   => .translated (.litP (.natL n), rest)
        | .strLit s   => .translated (.litP (.strL s), rest)
        | .charLit c  => .translated (.litP (.charL c), rest)
        | .ident w =>
            match rest with
            | { kind := .atSign, .. } :: afterAt => do
                if w.contains '.' then
                  .syntaxErr s!"{tokDesc t}: qualified name before '@' in pattern"
                let (subP, afterSub) ← parseAtomicPat sc afterAt
                .translated (.asP w subP, afterSub)
            | _ =>
                match lookupVarOrSym sc w with
                | some (.inr info) =>
                    if info.kind == .conSym then
                      let cq : QName := { full := info.canonPath, shown := w }
                      .translated (.conP cq [], rest)
                    else if w.contains '.' then
                      .syntaxErr s!"{tokDesc t}: '{w}' is not a constructor"
                    else
                      .translated (.varP w, rest)
                | _ =>
                    if w.contains '.' then
                      .syntaxErr s!"{tokDesc t}: unknown qualified constructor '{w}'"
                    else
                      .translated (.varP w, rest)
        | _ => .syntaxErr s!"{tokDesc t}: invalid pattern token"
end

-- §4 Top-Level LHS (including Prefix & Postfix Copatterns), Import Directives, and Module Declarations

def isActiveProjSym (sc : ScopeEnv) (pendingSigs : List String) (nm : String) : Option SymInfo :=
  if pendingSigs.contains nm then none
  else
    match lookupVarOrSym sc nm with
    | some (.inr info) =>
        match info.kind with
        | .projSym _ => some info
        | _          => none
    | _ => none

partial def peelPrefixProjToks (sc : ScopeEnv) (pendingSigs : List String) (toks : List Token) : List Token :=
  match toks with
  | { kind := .ident h, .. } :: rest =>
      if (isActiveProjSym sc pendingSigs h).isSome then
        let rec skipHid : List Token → List Token
          | rem@({ kind := .lbrace, .. } :: _) =>
              match takeMatchedGroup .lbrace .rbrace rem with
              | .translated (_, after) => skipHid after
              | _ => rem
          | rem => rem
        match skipHid rest with
        | rem@({ kind := .lparen, .. } :: _) =>
            match takeMatchedGroup .lparen .rparen rem with
            | .translated (inner, _) => peelPrefixProjToks sc pendingSigs inner
            | _ => toks
        | (t0@{ kind := .ident _, .. }) :: _ => [t0]
        | _ => toks
      else toks
  | _ => toks

private def appendArgToLHS (l : LHS) (a : Arg Pat) : LHS :=
  match l with
  | .head f ps        => .head f (ps ++ [a])
  | .proj d inner ps  => .proj d inner (ps ++ [a])
  | .with_ inner w ps => .with_ inner w (ps ++ [a])

partial def parsePostfixSpine (sc : ScopeEnv) (initLhs : LHS) (initVars : List String)
    (rem : List Token) : PrismOutcome (LHS × List String) :=
  let rec loop (ts : List Token) (curLhs : LHS) (vars : List String) :
      PrismOutcome (LHS × List String) :=
    match ts with
    | [] => .translated (curLhs, vars)
    | t :: rest =>
        match t.kind with
        | .dotIdent projRaw =>
            match lookupVarOrSym sc projRaw with
            | some (.inr info) =>
                match info.kind with
                | .projSym _ =>
                    let pq : QName := { full := info.canonPath, shown := projRaw }
                    loop rest (.proj pq curLhs []) vars
                | _ => do
                    let dotE ← parseExpr (addLocalVars sc vars)
                      [{ kind := .ident projRaw, line := t.line, col := t.col, firstOnLine := false }]
                    loop rest (appendArgToLHS curLhs (visArg (.dotP dotE))) vars
            | _ => do
                let dotE ← parseExpr (addLocalVars sc vars)
                  [{ kind := .ident projRaw, line := t.line, col := t.col, firstOnLine := false }]
                loop rest (appendArgToLHS curLhs (visArg (.dotP dotE))) vars
        | .symDot => do
            let (dotE, afterDot) ← parseSingleAtom (addLocalVars sc vars) rest
            loop afterDot (appendArgToLHS curLhs (visArg (.dotP dotE))) vars
        | .lbrace => do
            let (inner, after) ← takeMatchedGroup .lbrace .rbrace ts
            match splitTopOn (· == .symEq) inner with
            | some ([{ kind := .ident lbl, .. }], _, pToks) => do
                let (p, pv) ← parsePat sc pToks
                if pv.any (vars.contains ·) then
                  .syntaxErr s!"{tokDesc t}: duplicate pattern variable"
                else
                  loop after (appendArgToLHS curLhs { hid := .hidden, label := some lbl, thing := p }) (vars ++ pv)
            | none => do
                let (p, pv) ← parsePat sc inner
                if pv.any (vars.contains ·) then
                  .syntaxErr s!"{tokDesc t}: duplicate pattern variable"
                else
                  loop after (appendArgToLHS curLhs { hid := .hidden, label := none, thing := p }) (vars ++ pv)
            | _ => .syntaxErr s!"{tokDesc t}: malformed implicit pattern"
        | .lbrace2 => do
            let (inner, after) ← takeMatchedGroup .lbrace2 .rbrace2 ts
            let (p, pv) ← parsePat sc inner
            if pv.any (vars.contains ·) then
              .syntaxErr s!"{tokDesc t}: duplicate pattern variable"
            else
              loop after (appendArgToLHS curLhs { hid := .inst, label := none, thing := p }) (vars ++ pv)
        | .lparen => do
            let (inner, after) ← takeMatchedGroup .lparen .rparen ts
            if inner.isEmpty then
              loop after (appendArgToLHS curLhs (visArg .absurdP)) vars
            else do
              let (p, pv) ← parsePat sc inner
              if pv.any (vars.contains ·) then
                .syntaxErr s!"{tokDesc t}: duplicate pattern variable"
              else
                loop after (appendArgToLHS curLhs (visArg p)) (vars ++ pv)
        | _ => do
            let (rawP, afterP) ← parseAtomicPat sc ts
            let (p, pv) ← validateLinearPat rawP
            if pv.any (vars.contains ·) then
              .syntaxErr s!"{tokDesc t}: duplicate pattern variable"
            else
              loop afterP (appendArgToLHS curLhs (visArg p)) (vars ++ pv)
  loop rem initLhs initVars

partial def parseClauseLHS (sc : ScopeEnv) (pendingSigs : List String) (expectedName : String)
    (modPrefix : List String) (toks : List Token) : PrismOutcome (LHS × List String) := do
  match toks with
  | [] => .syntaxErr s!"empty clause LHS for '{expectedName}'"
  | { kind := .underscore, .. } :: [] =>
      if expectedName == "_" then
        .translated (.head (mkQ (modPrefix ++ ["_"])) [], [])
      else
        .syntaxErr s!"expected clause head '{expectedName}', found '_'"
  | { kind := .ident headTok, line := ln, col := cl, .. } :: argToks =>
      if let some pInfo := isActiveProjSym sc pendingSigs headTok then
        -- Prefix copattern projection: `proj (f ...) extraPats` or `proj zeroArgFn extraPats`
        let projQ : QName := { full := pInfo.canonPath, shown := headTok }
        match argToks with
        | { kind := .lparen, .. } :: _ => do
            let (focusToks, afterFocus) ← takeMatchedGroup .lparen .rparen argToks
            let (innerLhs, innerVars) ← parseClauseLHS sc pendingSigs expectedName modPrefix focusToks
            parsePostfixSpine sc (.proj projQ innerLhs []) innerVars afterFocus
        | (t0@{ kind := .ident _, .. }) :: afterFocus => do
            let (innerLhs, innerVars) ← parseClauseLHS sc pendingSigs expectedName modPrefix [t0]
            parsePostfixSpine sc (.proj projQ innerLhs []) innerVars afterFocus
        | _ => .syntaxErr s!"line {ln}, col {cl}: malformed copattern focus after projection '{headTok}'"
      else if headTok == expectedName then
        let baseHead := LHS.head { full := modPrefix ++ [expectedName], shown := expectedName } []
        parsePostfixSpine sc baseHead [] argToks
      else
        -- Check binary infix LHS `p₁ op p₂` when `expectedName == "_" ++ op ++ "_"`
        let midMatch := splitTopOn (fun
          | .ident s => ("_" ++ s ++ "_") == expectedName
          | _ => false) toks
        match midMatch with
        | some (lToks, _, rToks) =>
            if !lToks.isEmpty && !rToks.isEmpty then do
              let (p1, v1) ← parsePat sc lToks
              let (p2, v2) ← parsePat sc rToks
              match v1.find? (fun v => v2.contains v) with
              | some dup => .syntaxErr s!"line {ln}: duplicate variable '{dup}' in infix LHS"
              | none =>
                  .translated (.head { full := modPrefix ++ [expectedName], shown := expectedName }
                    [visArg p1, visArg p2], v1 ++ v2)
            else
              .syntaxErr s!"line {ln}, col {cl}: malformed operator LHS for '{expectedName}'"
        | none =>
            .syntaxErr s!"line {ln}, col {cl}: clause head '{headTok}' does not match '{expectedName}'"
  | _ =>
      -- Check parenthesized left pattern `(c x) op p₂` for infix definition
      let midMatch := splitTopOn (fun
        | .ident s => ("_" ++ s ++ "_") == expectedName
        | _ => false) toks
      match midMatch with
      | some (lToks, _, rToks) => do
          let (p1, v1) ← parsePat sc lToks
          let (p2, v2) ← parsePat sc rToks
          match v1.find? (fun v => v2.contains v) with
          | some dup => .syntaxErr s!"duplicate variable '{dup}' in infix LHS"
          | none =>
              .translated (.head { full := modPrefix ++ [expectedName], shown := expectedName }
                [visArg p1, visArg p2], v1 ++ v2)
      | none => .syntaxErr s!"malformed LHS for '{expectedName}'"

partial def parseHeadLHS (sc : ScopeEnv) (expectedName : String) (modPrefix : List String)
    (toks : List Token) : PrismOutcome (LHS × List String) :=
  parseClauseLHS sc [] expectedName modPrefix toks

private partial def hasAbsurdPat : Pat → Bool
  | .absurdP     => true
  | .conP _ args => args.any (fun a => hasAbsurdPat a.thing)
  | .asP _ p     => hasAbsurdPat p
  | .recP fs     => fs.any (fun (_, p) => hasAbsurdPat p)
  | _            => false

-- Parse import/open directives: `[using (...)] [hiding (...)] [renaming (...)] [public]`
partial def parseImportDirective (toks : List Token) :
    PrismOutcome (Option String × Directive) :=
  let rec loop (rem : List Token) (alias : Option String) (dir : Directive) :
      PrismOutcome (Option String × Directive) :=
    match rem with
    | [] => .translated (alias, dir)
    | { kind := .ident "as", .. } :: { kind := .ident al, .. } :: rest =>
        loop rest (some al) dir
    | { kind := .kwPublic, .. } :: rest =>
        loop rest alias { dir with dpublic := true }
    | { kind := .kwUsing, .. } :: rest => do
        let (inner, after) ← takeMatchedGroup .lparen .rparen rest
        let items := splitAllTopOn (· == .semi) inner
        let names ← items.mapM fun
          | [{ kind := .ident n, .. }] => .translated n
          | _ => .syntaxErr "malformed item in 'using (...)'"
        loop after alias { dir with dusing := some names }
    | { kind := .kwHiding, .. } :: rest => do
        let (inner, after) ← takeMatchedGroup .lparen .rparen rest
        let items := splitAllTopOn (· == .semi) inner
        let names ← items.mapM fun
          | [{ kind := .ident n, .. }] => .translated n
          | _ => .syntaxErr "malformed item in 'hiding (...)'"
        loop after alias { dir with dhiding := names }
    | { kind := .kwRenaming, .. } :: rest => do
        let (inner, after) ← takeMatchedGroup .lparen .rparen rest
        let items := splitAllTopOn (· == .semi) inner
        let pairs ← items.mapM fun
          | [{ kind := .ident a, .. }, { kind := .ident "to", .. }, { kind := .ident b, .. }] =>
              .translated (a, b)
          | _ => .syntaxErr "malformed item in 'renaming (old to new)'"
        loop after alias { dir with drenaming := pairs }
    | t :: _ => .syntaxErr s!"{tokDesc t}: unexpected token in import/open directive"
  loop toks none {}

private def applyDirectiveToExports (isStdMod : Bool) (modName : String)
    (exports : List SymInfo) (dir : Directive) :
    PrismOutcome (List (String × SymInfo)) := do
  let missingErr (n : String) : PrismOutcome Unit :=
    if isStdMod then
      .bot s!"stdlib module '{modName}' item '{n}' outside mirror subset; routing to Agda"
    else
      .syntaxErr s!"module '{modName}' does not export '{n}'"
  if let some us := dir.dusing then
    for n in us do
      if !(exports.any (fun s => s.localName == n)) then
        missingErr n
  for n in dir.dhiding do
    if !(exports.any (fun s => s.localName == n)) then
      missingErr n
  for (oldN, _) in dir.drenaming do
    if !(exports.any (fun s => s.localName == oldN)) then
      missingErr oldN
  let renamedNames := dir.drenaming.map Prod.fst
  let baseFiltered := exports.filter fun s =>
    !dir.dhiding.contains s.localName &&
    !renamedNames.contains s.localName &&
    match dir.dusing with
    | none    => true
    | some us => us.contains s.localName
  let directPairs := baseFiltered.map (fun s => (s.localName, s))
  let renamedPairs ← dir.drenaming.mapM fun (oldN, newN) =>
    match exports.find? (fun s => s.localName == oldN) with
    | some s => .translated (newN, { s with localName := newN })
    | none   => .syntaxErr s!"module '{modName}' does not export '{oldN}'"
  .translated (directPairs ++ renamedPairs)

def checkOptionsPragma (body : String) : PrismOutcome Unit :=
  if !body.startsWith "OPTIONS" then
    .bot s!"non-OPTIONS pragma '{body}' routed to Agda"
  else
    let flags := (body.drop 7).toString.splitOn " " |>.filter (fun s => !s.isEmpty)
    let rec checkFlags : List String → PrismOutcome Unit
      | [] => .translated ()
      | "--safe" :: rest | "--guardedness" :: rest | "--exact-split" :: rest =>
          checkFlags rest
      | "--without-K" :: _ | "--cubical-compatible" :: _ | "--cubical" :: _
      | "--sized-types" :: _ | "--rewriting" :: _ | "--prop" :: _
      | "--type-in-type" :: _ | "--omega-in-omega" :: _ =>
          .bot s!"OPTIONS '{body}' uses Agda-specific type theory flag"
      | f :: _ =>
          .syntaxErr s!"unknown or unsupported OPTIONS flag '{f}'"
    checkFlags flags

-- §5 Block & Module Declaration Parser

def leanMangleIdent (s : String) : String :=
  let chars := s.toList.flatMap fun c =>
    if ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') then [c]
    else if c == '_' then ['_', 'u']
    else s!"_x{c.toNat}_".toList
  "_ag_" ++ String.ofList chars

def leanModNamespace (modPath : List String) : String :=
  "_AgMod_" ++ String.intercalate "_" (modPath.map leanMangleIdent)

private def parseConstructorArity (e : Expr) : Nat :=
  match e with
  | .fun_ a rest => (if a.hid == .visible then 1 else 0) + parseConstructorArity rest
  | .pi (.bind h xs _) rest => (if h == .visible then xs.length else 0) + parseConstructorArity rest
  | _ => 0

partial def parseDeclList (sc0 : ScopeEnv) (slices : List (List Token)) :
    PrismOutcome (List Decl × ScopeEnv × List SymInfo) := do
  -- First scan local `infix/infixl/infixr` declarations in this block so fixities
  -- apply across the block (matching Agda's block-level fixity scoping).
  let rec collectBlockFixities (sls : List (List Token)) : List (String × FixLevel) :=
    sls.flatMap fun sl =>
      match sl with
      | { kind := .kwInfix, .. }  :: { kind := .natLit n, .. } :: ops =>
          ops.filterMap fun tok =>
            match tok.kind with
            | .ident op => some (op, .related (Int.ofNat n) .infixN)
            | _ => none
      | { kind := .kwInfixL, .. } :: { kind := .natLit n, .. } :: ops =>
          ops.filterMap fun tok =>
            match tok.kind with
            | .ident op => some (op, .related (Int.ofNat n) .infixL)
            | _ => none
      | { kind := .kwInfixR, .. } :: { kind := .natLit n, .. } :: ops =>
          ops.filterMap fun tok =>
            match tok.kind with
            | .ident op => some (op, .related (Int.ofNat n) .infixR)
            | _ => none
      | { kind := .kwPrivate, .. } :: afterPriv =>
          match splitLayoutBlock afterPriv with
          | .translated inner => collectBlockFixities inner
          | _ => []
      | { kind := .kwMutual, .. } :: afterMut =>
          let mutBody := match afterMut with | { kind := .kwWhere, .. } :: xs => xs | xs => xs
          match splitLayoutBlock mutBody with
          | .translated inner => collectBlockFixities inner
          | _ => []
      | _ => []
  let localFixities : List (String × FixLevel) := (collectBlockFixities slices).reverse

  let lookupLocalFix (nm : String) : FixLevel :=
    match localFixities.find? (fun (k, _) => k == nm) with
    | some (_, fx) => fx
    | none         => defaultAgdaFixity

  -- Sequential pass with pending forward signatures (`pendingSigs`) and clause accumulation
  let rec stepSlices (sc : ScopeEnv) (rem : List (List Token))
      (pendingSigs : List String) (exported : List SymInfo) (acc : List Decl) :
      PrismOutcome (List Decl × ScopeEnv × List SymInfo) := do
    match rem with
    | [] =>
        match pendingSigs with
        | [] => .translated (acc.reverse, sc, exported.reverse)
        | fn :: _ => .syntaxErr s!"type signature for '{fn}' lacks an accompanying definition"
    | sl :: rest =>
        if sl.any (fun t => t.kind == .kwRewrite) then
          .bot "rewrite clause routed to Agda"
        else
          match sl with
          | { kind := .symEllipsis, line := ln, col := cl, .. } :: _ =>
              .syntaxErr s!"line {ln}, col {cl}: unexpected '...' outside 'with' clause"
          | [{ kind := .pragma body, .. }] => do
              checkOptionsPragma body
              stepSlices sc rest pendingSigs exported (.pragma body :: acc)
          | { kind := .kwPostulate, line := ln, col := cl, .. } :: afterPost => do
              if sc.selfSafe then
                .syntaxErr s!"line {ln}, col {cl}: 'postulate' is forbidden under OPTIONS --safe"
              else
                let postSlices ← splitLayoutBlock afterPost
                if postSlices.isEmpty then
                  .syntaxErr s!"line {ln}, col {cl}: empty 'postulate' block"
                else
                  let mut sc' := sc
                  let mut exp' := exported
                  let mut postDecls : List Decl := []
                  for psl in postSlices do
                    match splitTopOn (· == .symColon) psl with
                    | none => PrismOutcome.syntaxErr s!"line {ln}: postulate item missing ':'"
                    | some (lhsNames, pTok, tyToks) =>
                        if tyToks.isEmpty then
                          PrismOutcome.syntaxErr s!"{tokDesc pTok}: missing type in postulate"
                        else
                          match parseSigNames lhsNames with
                          | none => PrismOutcome.syntaxErr s!"{tokDesc pTok}: invalid name in postulate"
                          | some ["_"] => do
                              let ty ← parseExpr sc' tyToks
                              postDecls := .sig plainMods "_" ty :: postDecls
                          | some pNames => do
                              let ty ← parseExpr sc' tyToks
                              for nm in pNames do
                                let canon := sc'.modPrefix ++ [nm]
                                let info : SymInfo :=
                                  { localName := nm, canonPath := canon, kind := .defSym
                                  , fixity := lookupLocalFix nm
                                  , leanName := leanModNamespace sc'.modPrefix ++ "." ++ leanMangleIdent nm }
                                sc' := addSymUnqual sc' nm info
                                exp' := info :: exp'
                                postDecls := .sig plainMods nm ty :: postDecls
                  stepSlices sc' rest pendingSigs exp' (postDecls ++ acc)
          | { kind := .kwVariable, .. } :: _ =>
              .bot "generalizable variable block routed to Agda"
          | { kind := .kwSyntax, .. } :: _ =>
              .bot "syntax declaration routed to Agda"
          | { kind := .kwPattern, line := ln, .. } :: patRest => do
              match splitTopOn (· == .symEq) patRest with
              | none => .syntaxErr s!"line {ln}: 'pattern' synonym missing '='"
              | some (lhsT, _, rhsT) =>
                  match lhsT with
                  | { kind := .ident synNm, .. } :: argToks =>
                      if synNm.contains '.' || rhsT.isEmpty then
                        .syntaxErr s!"line {ln}: malformed 'pattern {synNm}' synonym"
                      else
                        match parseSigNames (if argToks.isEmpty then [{ kind := .ident "_dummy", line := 0, col := 0, firstOnLine := false }] else argToks) with
                        | none => .bot s!"line {ln}: complex pattern synonym '{synNm}' routed to Agda"
                        | some parsedArgs => do
                            let argNames := if argToks.isEmpty then [] else parsedArgs
                            let scArgs := addLocalVars sc argNames
                            let (rPat, _) ← parsePat scArgs rhsT
                            let rExpr ← parseExpr scArgs rhsT
                            let canon := sc.modPrefix ++ [synNm]
                            let info : SymInfo :=
                              { localName := synNm
                              , canonPath := canon
                              , kind      := .conSym
                              , fixity    := lookupLocalFix synNm
                              , leanName  := leanModNamespace sc.modPrefix ++ "." ++ leanMangleIdent synNm
                              , conArity  := argNames.length }
                            let sc' := addSymUnqual sc synNm info
                            let d := Decl.patSyn synNm argNames rPat rExpr
                            stepSlices sc' rest pendingSigs (info :: exported) (d :: acc)
                  | _ => .syntaxErr s!"line {ln}: expected identifier after 'pattern'"
          | { kind := .kwMutual, .. } :: afterMut => do
              if !pendingSigs.isEmpty then
                .syntaxErr "unfinished forward signature before 'mutual' block"
              else
                let mutBody :=
                  match afterMut with
                  | { kind := .kwWhere, .. } :: xs => xs
                  | xs => xs
                let innerSlices ← splitLayoutBlock mutBody
                -- Two-pass over `mutual`: collect signatures & dataSig/recSig first, then parse full block
                let mut scPre := sc
                let mut expPre := exported
                for msl in innerSlices do
                  match msl with
                  | { kind := .kwData, .. } :: { kind := .ident dName, .. } :: _ =>
                      let canon := scPre.modPrefix ++ [dName]
                      let info : SymInfo :=
                        { localName := dName, canonPath := canon, kind := .typeSym
                        , fixity := lookupLocalFix dName
                        , leanName := leanModNamespace scPre.modPrefix ++ "." ++ leanMangleIdent dName }
                      scPre := addSymUnqual scPre dName info
                      expPre := info :: expPre
                  | { kind := .kwRecord, .. } :: { kind := .ident rName, .. } :: _ =>
                      let canon := scPre.modPrefix ++ [rName]
                      let info : SymInfo :=
                        { localName := rName, canonPath := canon, kind := .typeSym
                        , fixity := lookupLocalFix rName
                        , leanName := leanModNamespace scPre.modPrefix ++ "." ++ leanMangleIdent rName }
                      scPre := addSymUnqual scPre rName info
                      expPre := info :: expPre
                  | _ =>
                      match splitTopOn (· == .symColon) msl with
                      | some (lhsNames, _, _) =>
                          if !(splitTopOn (fun k => k == .symEq || k == .kwWith || k == .kwWhere) lhsNames).isSome then
                            if let some fNames := parseSigNames lhsNames then
                              if fNames != ["_"] then
                                for fName in fNames do
                                  let canon := scPre.modPrefix ++ [fName]
                                  let info : SymInfo :=
                                    { localName := fName, canonPath := canon, kind := .defSym
                                    , fixity := lookupLocalFix fName
                                    , leanName := leanModNamespace scPre.modPrefix ++ "." ++ leanMangleIdent fName }
                                  scPre := addSymUnqual scPre fName info
                      | none => pure ()
                let (mutDecls, scPost, expPost) ← stepSlices scPre innerSlices [] expPre []
                stepSlices scPost rest [] expPost.reverse (mutDecls.reverse ++ acc)
          | { kind := .kwPrivate, .. } :: afterPriv =>
              match afterPriv with
              | [] => .syntaxErr "empty 'private' block"
              | _ => do
                  -- Private block: declarations inside do not escape to `exported`!
                  let privSlices ← splitLayoutBlock afterPriv
                  let (privDecls, scPriv, _) ← parseDeclList sc privSlices
                  let markedPriv := privDecls.map fun
                    | .sig m x e          => Decl.sig { m with isPrivate := true } x e
                    | .fun_ m x cs        => Decl.fun_ { m with isPrivate := true } x cs
                    | .dataSig m x bs e   => Decl.dataSig { m with isPrivate := true } x bs e
                    | .dataDef m x ps cs  => Decl.dataDef { m with isPrivate := true } x ps cs
                    | .recSig m x bs e    => Decl.recSig { m with isPrivate := true } x bs e
                    | .recDef m x ps rd f => Decl.recDef { m with isPrivate := true } x ps rd f
                    | d                   => d
                  stepSlices scPriv rest pendingSigs exported (markedPriv.reverse ++ acc)
          | { kind := .kwInstance, .. } :: _ =>
              .bot "instance block routed to Agda instance search"
          | { kind := .kwAbstract, .. } :: _ =>
              .bot "abstract block routed to Agda"
          | { kind := .kwInfix, .. } :: { kind := .natLit n, .. } :: ops => do
              let opDecls ← ops.mapM fun
                | { kind := .ident op, .. } => .translated (Decl.fixity .infixN n op)
                | t => .syntaxErr s!"{tokDesc t}: invalid operator in 'infix'"
              stepSlices sc rest pendingSigs exported (opDecls.reverse ++ acc)
          | { kind := .kwInfixL, .. } :: { kind := .natLit n, .. } :: ops => do
              let opDecls ← ops.mapM fun
                | { kind := .ident op, .. } => .translated (Decl.fixity .infixL n op)
                | t => .syntaxErr s!"{tokDesc t}: invalid operator in 'infixl'"
              stepSlices sc rest pendingSigs exported (opDecls.reverse ++ acc)
          | { kind := .kwInfixR, .. } :: { kind := .natLit n, .. } :: ops => do
              let opDecls ← ops.mapM fun
                | { kind := .ident op, .. } => .translated (Decl.fixity .infixR n op)
                | t => .syntaxErr s!"{tokDesc t}: invalid operator in 'infixr'"
              stepSlices sc rest pendingSigs exported (opDecls.reverse ++ acc)
          | { kind := .kwOpen, .. } :: { kind := .kwImport, .. } :: impRest => do
              let (d, sc', exp') ← parseImportDecl sc exported true impRest
              stepSlices sc' rest pendingSigs exp' (d :: acc)
          | { kind := .kwImport, .. } :: impRest => do
              let (d, sc', exp') ← parseImportDecl sc exported false impRest
              stepSlices sc' rest pendingSigs exp' (d :: acc)
          | { kind := .kwOpen, .. } :: openRest => do
              let (d, sc', exp') ← parseOpenLocalDecl sc exported openRest
              stepSlices sc' rest pendingSigs exp' (d :: acc)
          | { kind := .kwData, .. } :: dataRest => do
              let (ds, sc', exp') ← parseDataDecl sc exported lookupLocalFix dataRest
              stepSlices sc' rest pendingSigs exp' (ds.reverse ++ acc)
          | { kind := .kwRecord, .. } :: recRest => do
              let (ds, sc', exp') ← parseRecordDecl sc exported lookupLocalFix recRest
              stepSlices sc' rest pendingSigs exp' (ds.reverse ++ acc)
          | { kind := .kwModule, .. } :: _ =>
              .bot "nested parameterized sub-module routed to Agda"
          | _ =>
              -- Check type signature `x₁ x₂ : T` vs `_ : T` vs function clause `f pats = rhs`
              match splitTopOn (· == .symColon) sl with
              | some (lhsNames, colonTok, tyToks) =>
                  -- Verify `=`, `with`, or `where` does not appear BEFORE `:`!
                  let eqBefore := (splitTopOn (fun k => k == .symEq || k == .kwWith || k == .kwWhere) lhsNames).isSome
                  if !eqBefore then do
                    if tyToks.isEmpty then
                      .syntaxErr s!"{tokDesc colonTok}: missing type after ':'"
                    match parseSigNames lhsNames with
                    | none => .syntaxErr s!"{tokDesc colonTok}: invalid name(s) before ':' in signature"
                    | some ["_"] => do
                        -- Anonymous test `_ : T` must be immediately followed by `_ = rhs`!
                        let ty ← parseExpr sc tyToks
                        match rest with
                        | nextSl :: afterAnon =>
                            match splitTopOn (· == .symEq) nextSl with
                            | some ([{ kind := .underscore, .. }], _, rhsToks) => do
                                let rhsE ← parseExpr sc rhsToks
                                let dSig := Decl.sig plainMods "_" ty
                                let dFun := Decl.fun_ plainMods "_"
                                  [.clause (.head (mkQ (sc.modPrefix ++ ["_"])) []) (.rhs rhsE) []]
                                stepSlices sc afterAnon pendingSigs exported (dFun :: dSig :: acc)
                            | _ => .syntaxErr s!"{tokDesc colonTok}: anonymous '_ :' test must be followed by '_ = ...'"
                        | [] => .syntaxErr s!"{tokDesc colonTok}: anonymous '_ :' test missing '_ = ...'"
                    | some names => do
                        let ty ← parseExpr sc tyToks
                        let mut sc' := sc
                        let mut exp' := exported
                        let mut sigDecls : List Decl := []
                        for nm in names do
                          let canon := sc.modPrefix ++ [nm]
                          let info : SymInfo :=
                            { localName := nm, canonPath := canon, kind := .defSym
                            , fixity := lookupLocalFix nm
                            , leanName := leanModNamespace sc.modPrefix ++ "." ++ leanMangleIdent nm }
                          sc' := addSymUnqual sc' nm info
                          exp' := info :: exp'
                          sigDecls := .sig plainMods nm ty :: sigDecls
                        stepSlices sc' rest (pendingSigs ++ names) exp' (sigDecls ++ acc)
                  else do
                    match parseUnannotatedZeroArgDef sc exported lookupLocalFix sl with
                    | some res => do
                        let (dSig, dFun, sc', exp') ← res
                        stepSlices sc' rest pendingSigs exp' (dFun :: dSig :: acc)
                    | none => do
                        let (fnName, fnDecl, remainingSlices) ← parseFunGroup sc pendingSigs sl rest
                        if !pendingSigs.contains fnName then
                          .syntaxErr s!"{tokDesc colonTok}: function '{fnName}' lacks an explicit type signature"
                        else
                          stepSlices sc remainingSlices (pendingSigs.filter (· != fnName)) exported (fnDecl :: acc)
              | none => do
                  match parseUnannotatedZeroArgDef sc exported lookupLocalFix sl with
                  | some res => do
                      let (dSig, dFun, sc', exp') ← res
                      stepSlices sc' rest pendingSigs exp' (dFun :: dSig :: acc)
                  | none => do
                      let (fnName, fnDecl, remainingSlices) ← parseFunGroup sc pendingSigs sl rest
                      if !pendingSigs.contains fnName then
                        .syntaxErr s!"function '{fnName}' lacks an explicit preceding type signature"
                      else
                        stepSlices sc remainingSlices (pendingSigs.filter (· != fnName)) exported (fnDecl :: acc)
  stepSlices sc0 slices [] [] []
  where
    parseUnannotatedZeroArgDef (sc : ScopeEnv) (exported : List SymInfo) (lookupFix : String → FixLevel)
        (sl : List Token) : Option (PrismOutcome (Decl × Decl × ScopeEnv × List SymInfo)) :=
      let (mainToks, whereToks) :=
        match splitTopOn (· == .kwWhere) sl with
        | none => (sl, [])
        | some (b, _, w) => (b, w)
      match splitTopOn (· == .symEq) mainToks with
      | some ([{ kind := .ident nm, .. }], eqTok, rhsToks) =>
          if nm == "_" || nm.contains '.' || sc.unqualified.any (fun (k, _) => k == nm) then
            none
          else
            some do
              if rhsToks.isEmpty then
                .syntaxErr s!"{tokDesc eqTok}: empty RHS after '='"
              let (wDecls, scForRhs) ← parseWhereOpt sc whereToks
              let rhsE ← parseExpr scForRhs rhsToks
              let canon := sc.modPrefix ++ [nm]
              let info : SymInfo :=
                { localName := nm, canonPath := canon, kind := .defSym
                , fixity := lookupFix nm
                , leanName := leanModNamespace sc.modPrefix ++ "." ++ leanMangleIdent nm }
              let sc' := addSymUnqual sc nm info
              let dSig := Decl.sig plainMods nm .meta_
              let dFun := Decl.fun_ plainMods nm [.clause (.head (mkQ canon) []) (.rhs rhsE) wDecls]
              .translated (dSig, dFun, sc', info :: exported)
      | _ => none
    parseSigNames (toks : List Token) : Option (List String) :=
      if toks.isEmpty then none
      else
        let rec go : List Token → List String → Option (List String)
          | [], acc => some acc.reverse
          | { kind := .underscore, .. } :: [], [] => some ["_"]
          | { kind := .ident n, .. } :: rest, acc =>
              if n.contains '.' then none else go rest (n :: acc)
          | _, _ => none
        go toks []

    extractLHSCore (sc : ScopeEnv) (pendingSigs : List String) (sl : List Token) : List Token :=
      let beforeEqOrWith :=
        match splitTopOn (fun k => k == .kwWith || k == .symEq) sl with
        | some (l, _, _) => l
        | none           => sl
      let beforeBar :=
        match splitTopOn (· == .symBar) beforeEqOrWith with
        | some (l, _, _) => l
        | none           => beforeEqOrWith
      peelPrefixProjToks sc pendingSigs beforeBar

    clauseBelongsTo (sc : ScopeEnv) (pendingSigs : List String) (fnName : String) (sl : List Token) : Bool :=
      match sl with
      | { kind := .symEllipsis, .. } :: _ => true
      | _ =>
          let lhsPart := extractLHSCore sc pendingSigs sl
          match lhsPart with
          | { kind := .ident h, .. } :: _ =>
              if h == fnName then true
              else
                (splitTopOn (fun
                  | .ident op => ("_" ++ op ++ "_") == fnName
                  | _ => false) lhsPart).isSome
          | _ =>
              (splitTopOn (fun
                | .ident op => ("_" ++ op ++ "_") == fnName
                | _ => false) lhsPart).isSome

    detectClauseHeadName (sc : ScopeEnv) (pendingSigs : List String) (sl : List Token) : PrismOutcome String :=
      let lhsPart := extractLHSCore sc pendingSigs sl
      let findTopInfix (ts : List Token) : Option String :=
        match splitTopOn (fun
          | .ident op =>
              let mix := "_" ++ op ++ "_"
              pendingSigs.contains mix || sc.unqualified.any (fun (k, info) => k == mix && info.kind == .defSym)
          | _ => false) ts with
        | some (_, { kind := .ident op, .. }, _) => some ("_" ++ op ++ "_")
        | _ => none
      match lhsPart with
      | [] => .syntaxErr "empty declaration"
      | { kind := .ident h, line := ln, col := cl, .. } :: _ =>
          if pendingSigs.contains h then
            .translated h
          else
            match findTopInfix lhsPart with
            | some mix => .translated mix
            | none =>
                if sc.unqualified.any (fun (k, _) => k == h) then
                  .translated h
                else
                  .syntaxErr s!"line {ln}, col {cl}: unbound or malformed declaration starting with '{h}'"
      | t :: _ =>
          match findTopInfix lhsPart with
          | some mix => .translated mix
          | none     => .syntaxErr s!"{tokDesc t}: unexpected token at start of declaration"

    lhsHasAbsurd : LHS → Bool
      | .head _ ps        => ps.any (fun a => hasAbsurdPat a.thing)
      | .proj _ inner ps  => lhsHasAbsurd inner || ps.any (fun a => hasAbsurdPat a.thing)
      | .with_ inner w ps =>
          lhsHasAbsurd inner || w.any (fun a => hasAbsurdPat a.thing) || ps.any (fun a => hasAbsurdPat a.thing)

    parseWhereOpt (scWithPats : ScopeEnv) (whereToks : List Token) :
        PrismOutcome (List Decl × ScopeEnv) :=
      if whereToks.isEmpty then
        .translated ([], scWithPats)
      else do
        let wSlices ← splitLayoutBlock whereToks
        let subPrefix := scWithPats.modPrefix ++ ["_"]
        let (wDecls, scAfterW, _) ← parseDeclList { scWithPats with modPrefix := subPrefix } wSlices
        .translated (wDecls, { scAfterW with modPrefix := scWithPats.modPrefix })

    parseSingleClause (sc : ScopeEnv) (pendingSigs : List String) (fnName : String)
        (sl : List Token) : PrismOutcome Clause := do
      let (mainToks, whereToks) ← splitClauseWhere sl
      match splitTopOn (· == .symEq) mainToks with
      | some (lhsToks, eqTok, rhsToks) => do
          let (lhs, pVars) ← parseClauseLHS sc pendingSigs fnName sc.modPrefix lhsToks
          let scWithPats := addLocalVars sc pVars
          let (wDecls, scForRhs) ← parseWhereOpt scWithPats whereToks
          if rhsToks.isEmpty then
            .syntaxErr s!"{tokDesc eqTok}: empty RHS after '='"
          let rhsE ← parseExpr scForRhs rhsToks
          .translated (.clause lhs (.rhs rhsE) wDecls)
      | none => do
          let (lhs, _) ← parseClauseLHS sc pendingSigs fnName sc.modPrefix mainToks
          if !lhsHasAbsurd lhs then
            .syntaxErr s!"clause for '{fnName}' has no '= rhs' and no absurd pattern '()'"
          else
            .translated (.clause lhs .absurdRHS [])

    priorWithBars : LHS → Nat
      | .head _ _        => 0
      | .proj _ inner _  => priorWithBars inner
      | .with_ inner w _ => priorWithBars inner + w.length

    parseBarPatsFor (sc : ScopeEnv) (chunks : List (List Token)) : PrismOutcome (List Pat × List String) := do
      let mut wPats : List Pat := []
      let mut wVars : List String := []
      for ch in chunks do
        let (wp, wv) ← parsePat sc ch
        if wv.any (wVars.contains ·) then
          PrismOutcome.syntaxErr "duplicate pattern variable across 'with' patterns"
        wPats := wPats ++ [wp]
        wVars := wVars ++ wv
      .translated (wPats, wVars)

    matchWithSubLhs (sc : ScopeEnv) (pendingSigs : List String) (fnName : String)
        (baseLhs : LHS) (baseVars : List String) (numWith : Nat) (lhsPart : List Token) :
        Option (PrismOutcome (LHS × List String × List Pat × List String)) :=
      match lhsPart with
      | { kind := .symEllipsis, .. } :: { kind := .symBar, .. } :: restBars =>
          let chunks := splitAllTopOn (· == .symBar) restBars
          if chunks.length != numWith then
            some (.syntaxErr s!"'with' sub-clause expected {numWith} '|'-separated pattern(s), found {chunks.length}")
          else
            some do
              let (wPats, wVars) ← parseBarPatsFor sc chunks
              .translated (baseLhs, baseVars, wPats, wVars)
      | { kind := .symEllipsis, line := ln, col := cl, .. } :: _ =>
          some (.syntaxErr s!"line {ln}, col {cl}: expected '|' after '...' in 'with' clause")
      | _ =>
          match splitTopOn (· == .symBar) lhsPart with
          | none => none
          | some (expBaseToks, _, restBars) =>
              if !clauseBelongsTo sc pendingSigs fnName lhsPart then none
              else
                let allChunks := splitAllTopOn (· == .symBar) restBars
                let pBars := priorWithBars baseLhs
                if allChunks.length < pBars + numWith then
                  -- Belongs to an enclosing outer `with` stage!
                  none
                else if allChunks.length > pBars + numWith then
                  some (.syntaxErr s!"'with' sub-clause expected {pBars + numWith} '|'-separated pattern(s), found {allChunks.length}")
                else
                  some do
                    let (bl, bv) ← parseClauseLHS sc pendingSigs fnName sc.modPrefix expBaseToks
                    let (priorPats, priorVars) ← parseBarPatsFor sc (allChunks.take pBars)
                    let reconstructedBase :=
                      if priorPats.isEmpty then bl
                      else LHS.with_ bl (priorPats.map visArg) []
                    let (wPats, wVars) ← parseBarPatsFor sc (allChunks.drop pBars)
                    .translated (reconstructedBase, bv ++ priorVars, wPats, wVars)

    consumeWithSubSlices (sc : ScopeEnv) (pendingSigs : List String) (fnName : String)
        (baseLhs : LHS) (baseVars : List String) (numWith : Nat)
        (remSlices : List (List Token)) (acc : List Clause) :
        PrismOutcome (List Clause × List (List Token)) := do
      match remSlices with
      | [] => .translated (acc.reverse, [])
      | subSl :: restRem => do
          let (subMain, subWhereToks) ← splitClauseWhere subSl
          match splitTopOn (· == .kwWith) subMain with
          | some (subLhsToks, withTok2, weToks2) =>
              -- Nested multi-stage `... | p₁ with we₂`!
              match matchWithSubLhs sc pendingSigs fnName baseLhs baseVars numWith subLhsToks with
              | none => .translated (acc.reverse, remSlices)
              | some parsedLhs => do
                  let (subBaseLhs, subBaseVars, wPats, wVars) ← parsedLhs
                  let stageLhs := LHS.with_ subBaseLhs (wPats.map visArg) []
                  let stageVars := subBaseVars ++ wVars
                  let scStageWithPats := addLocalVars sc stageVars
                  let (wDecls2, scForWe2) ← parseWhereOpt scStageWithPats subWhereToks
                  let weSlices2 := splitAllTopOn (· == .symBar) weToks2
                  if weSlices2.isEmpty then
                    .syntaxErr s!"{tokDesc withTok2}: missing expression after nested 'with'"
                  let withExprs2 ← weSlices2.mapM (parseExpr scForWe2)
                  let scWithWhere2 := { scForWe2 with locals := sc.locals }
                  let (innerSubs, afterInner) ←
                    consumeWithSubSlices scWithWhere2 pendingSigs fnName stageLhs stageVars withExprs2.length restRem []
                  if innerSubs.isEmpty then
                    .syntaxErr s!"{tokDesc withTok2}: nested 'with' clause missing '| ...' sub-clauses"
                  let nestedClause := Clause.clause stageLhs (.withRHS withExprs2 innerSubs) wDecls2
                  consumeWithSubSlices sc pendingSigs fnName baseLhs baseVars numWith afterInner (nestedClause :: acc)
          | none =>
              match splitTopOn (· == .symEq) subMain with
              | some (subLhsToks, eqTok, subRhsToks) =>
                  match matchWithSubLhs sc pendingSigs fnName baseLhs baseVars numWith subLhsToks with
                  | none => .translated (acc.reverse, remSlices)
                  | some parsedLhs => do
                      let (subBaseLhs, subBaseVars, wPats, wVars) ← parsedLhs
                      let fullLhs := LHS.with_ subBaseLhs (wPats.map visArg) []
                      let scSub := addLocalVars sc (subBaseVars ++ wVars)
                      let (wDecls, scForRhs) ← parseWhereOpt scSub subWhereToks
                      if subRhsToks.isEmpty then
                        .syntaxErr s!"{tokDesc eqTok}: empty RHS in 'with' sub-clause"
                      let rhsE ← parseExpr scForRhs subRhsToks
                      let cl := Clause.clause fullLhs (.rhs rhsE) wDecls
                      consumeWithSubSlices sc pendingSigs fnName baseLhs baseVars numWith restRem (cl :: acc)
              | none =>
                  match matchWithSubLhs sc pendingSigs fnName baseLhs baseVars numWith subMain with
                  | none => .translated (acc.reverse, remSlices)
                  | some parsedLhs => do
                      let (subBaseLhs, _, wPats, _) ← parsedLhs
                      let fullLhs := LHS.with_ subBaseLhs (wPats.map visArg) []
                      if !lhsHasAbsurd fullLhs then
                        .syntaxErr s!"'with' sub-clause for '{fnName}' has no '= rhs' and no absurd pattern '()'"
                      else
                        let cl := Clause.clause fullLhs .absurdRHS []
                        consumeWithSubSlices sc pendingSigs fnName baseLhs baseVars numWith restRem (cl :: acc)

    parseClauseStream (sc : ScopeEnv) (pendingSigs : List String) (fnName : String)
        (slices : List (List Token)) (acc : List Clause) : PrismOutcome (List Clause) := do
      match slices with
      | [] => .translated acc.reverse
      | sl :: rem => do
          let (beforeW, whereToks) ← splitClauseWhere sl
          match splitTopOn (· == .kwWith) beforeW with
          | none => do
              let c ← parseSingleClause sc pendingSigs fnName sl
              parseClauseStream sc pendingSigs fnName rem (c :: acc)
          | some (lhsToks, withTok, weToks) => do
              let (baseLhs, baseVars) ← parseClauseLHS sc pendingSigs fnName sc.modPrefix lhsToks
              let scWithPats := addLocalVars sc baseVars
              let (wDecls, scForWe) ← parseWhereOpt scWithPats whereToks
              let weSlices := splitAllTopOn (· == .symBar) weToks
              if weSlices.isEmpty then
                .syntaxErr s!"{tokDesc withTok}: missing expression after 'with'"
              let withExprs ← weSlices.mapM (parseExpr scForWe)
              let scWithWhere := { scForWe with locals := sc.locals }
              let (subClauses, afterWith) ←
                consumeWithSubSlices scWithWhere pendingSigs fnName baseLhs baseVars withExprs.length rem []
              if subClauses.isEmpty then
                .syntaxErr s!"{tokDesc withTok}: 'with' clause missing '| ...' sub-clauses"
              let topClause := Clause.clause baseLhs (.withRHS withExprs subClauses) wDecls
              parseClauseStream sc pendingSigs fnName afterWith (topClause :: acc)

    parseFunGroup (sc : ScopeEnv) (pendingSigs : List String) (firstSl : List Token)
        (rest : List (List Token)) : PrismOutcome (String × Decl × List (List Token)) := do
      let fnName ← detectClauseHeadName sc pendingSigs firstSl
      let rec takeMatching : List (List Token) → List (List Token) × List (List Token)
        | [] => ([], [])
        | s :: rs =>
            -- Stop if `s` is a type signature `x : T`!
            let isSig := match splitTopOn (· == .symColon) s with
              | some (l, _, _) =>
                  !(splitTopOn (fun k => k == .symEq || k == .kwWith || k == .kwWhere) l).isSome
              | none => false
            if !isSig && clauseBelongsTo sc pendingSigs fnName s then
              let (m, tail) := takeMatching rs
              (s :: m, tail)
            else
              ([], s :: rs)
      let (moreSlices, afterGroup) := takeMatching rest
      let clauses ← parseClauseStream sc pendingSigs fnName (firstSl :: moreSlices) []
      .translated (fnName, .fun_ plainMods fnName clauses, afterGroup)

    parseImportDecl (sc : ScopeEnv) (exported : List SymInfo) (isOpen : Bool)
        (toks : List Token) : PrismOutcome (Decl × ScopeEnv × List SymInfo) := do
      match toks with
      | [] => .syntaxErr "missing module name after 'import'"
      | { kind := .ident rawMod, line := ln, col := cl, .. } :: rest => do
          let (aliasOpt, dir) ← parseImportDirective rest
          let modParts := rawMod.splitOn "."
          let modQ : QName := { full := modParts, shown := aliasOpt.getD rawMod }
          -- Look up in bundle dependencies first, then `StdScope`:
          let (isStd, depCoinds, foundMod) : Bool × List (List String) × Option (List SymInfo × Bool × Bool) :=
            match sc.knownModules.find? (fun m => m.modPath == modParts) with
            | some m => (false, m.coindRecords, some (m.symbols, m.hasSafe, m.hasGuardedness))
            | none   =>
                match lookupStdModule rawMod with
                | some syms => (true, [], some (syms, isStdModuleSafe rawMod, isStdModuleGuarded rawMod))
                | none      => (false, [], none)
          match foundMod with
          | none =>
              .bot s!"line {ln}, col {cl}: import '{rawMod}' is outside Lean 4 mirror whitelist; routing to Agda"
          | some (modSyms, depSafe, depGuarded) => do
              if sc.selfSafe && !depSafe then
                PrismOutcome.syntaxErr s!"line {ln}, col {cl}: --safe module cannot import non-safe module '{rawMod}'"
              if depGuarded && !sc.selfGuarded then
                PrismOutcome.syntaxErr s!"line {ln}, col {cl}: importing --guardedness module '{rawMod}' requires --guardedness"
              let activePairs ← applyDirectiveToExports isStd rawMod modSyms dir
              let unqualPairs := activePairs.filter (fun (k, _) => !k.contains '.')
              let qualPrefix := aliasOpt.getD rawMod
              let baseQual := modSyms.map (fun s => (qualPrefix ++ "." ++ s.localName, s))
              let openSubQual : List (String × SymInfo) :=
                if !isOpen then []
                else
                  unqualPairs.flatMap fun (visNm, s) =>
                    if s.kind != .typeSym then []
                    else
                      modSyms.filterMap fun sub =>
                        if sub.canonPath.length == s.canonPath.length + 1 &&
                           sub.canonPath.take s.canonPath.length == s.canonPath then
                          let leaf := sub.canonPath.getLastD ""
                          some (visNm ++ "." ++ leaf, { sub with localName := leaf })
                        else none
              let newQual := openSubQual ++ baseQual
              let newUnqual :=
                if isOpen then
                  unqualPairs ++ sc.unqualified.filter (fun (k, _) => !(unqualPairs.any (fun (k2, _) => k2 == k)))
                else
                  sc.unqualified
              let exp' :=
                if isOpen && dir.dpublic then
                  (activePairs.map Prod.snd).reverse ++ exported
                else
                  exported
              let decl := Decl.import_ modQ isOpen dir []
              let nextSc :=
                { sc with
                  qualified    := newQual ++ sc.qualified
                  unqualified  := newUnqual
                  coindRecords := (depCoinds ++ sc.coindRecords).eraseDups }
              .translated (decl, nextSc, exp')
      | t :: _ => .syntaxErr s!"{tokDesc t}: expected module name after 'import'"

    parseOpenLocalDecl (sc : ScopeEnv) (exported : List SymInfo) (toks : List Token) :
        PrismOutcome (Decl × ScopeEnv × List SymInfo) := do
      match toks with
      | { kind := .ident rawTarget, line := ln, col := cl, .. } :: rest =>
          -- Handle `open R {{...}}` -> instance open routed to Agda
          if rest.any (fun t => t.kind == .lbrace2) then
            .bot "instance module open 'open R {{...}}' routed to Agda"
          else do
            let (_, dir) ← parseImportDirective rest
            -- Resolve `rawTarget`: either local record `Mod.R` or already-imported module `M`
            let fullCand := sc.modPrefix ++ [rawTarget]
            let fullCandStr := String.intercalate "." fullCand
            let matchingQual := sc.qualified.filterMap fun (qn, info) =>
              if qn.startsWith (rawTarget ++ ".") then
                let fieldOrSym := (qn.drop (rawTarget.length + 1)).toString
                if !fieldOrSym.contains '.' then some { info with localName := fieldOrSym } else none
              else if qn.startsWith (fullCandStr ++ ".") then
                let fieldOrSym := (qn.drop (fullCandStr.length + 1)).toString
                if !fieldOrSym.contains '.' then some { info with localName := fieldOrSym } else none
              else none
            if matchingQual.isEmpty then
              .syntaxErr s!"line {ln}, col {cl}: cannot open unknown module or record '{rawTarget}'"
            else do
              let activePairs ← applyDirectiveToExports false rawTarget matchingQual dir
              let newUnqual :=
                activePairs ++ sc.unqualified.filter (fun (k, _) => !(activePairs.any (fun (k2, _) => k2 == k)))
              let exp' := if dir.dpublic then (activePairs.map Prod.snd).reverse ++ exported else exported
              let targetQ : QName :=
                if sc.recordFields.any (fun (rk, _) => rk == fullCandStr) then
                  { full := fullCand, shown := rawTarget }
                else
                  { full := rawTarget.splitOn ".", shown := rawTarget }
              .translated (.open_ targetQ dir, { sc with unqualified := newUnqual }, exp')
      | _ => .syntaxErr "expected module/record name after 'open'"

    parseTeleBinds (sc : ScopeEnv) (toks : List Token) : PrismOutcome (List Bind × ScopeEnv) :=
      if toks.isEmpty then .translated ([], sc)
      else
        match tryParseTeleGroups sc toks with
        | some res => res
        | none     => .syntaxErr "invalid parameter telescope (expected typed '(x : A)' or '{x : A}' binders)"

    parseDataDecl (sc : ScopeEnv) (exported : List SymInfo) (lookupFix : String → FixLevel)
        (toks : List Token) : PrismOutcome (List Decl × ScopeEnv × List SymInfo) := do
      match toks with
      | { kind := .ident dName, line := ln, col := cl, .. } :: afterName =>
          if dName.contains '.' then
            .syntaxErr s!"line {ln}, col {cl}: data name '{dName}' cannot be qualified"
          else
            match splitTopOn (· == .kwWhere) afterName with
            | none => do
                -- Standalone `data D params : sort` signature (used inside `mutual`)
                match splitTopOn (· == .symColon) afterName with
                | none => .syntaxErr s!"line {ln}: 'data {dName}' missing ':' sort or 'where'"
                | some (paramToks, _, sortToks) => do
                    let (params, scParams) ← parseTeleBinds sc paramToks
                    let sortE ← parseExpr scParams sortToks
                    let canon := sc.modPrefix ++ [dName]
                    let info : SymInfo :=
                      { localName := dName, canonPath := canon, kind := .typeSym
                      , fixity := lookupFix dName
                      , leanName := leanModNamespace sc.modPrefix ++ "." ++ leanMangleIdent dName }
                    let sc' := addSymUnqual sc dName info
                    .translated ([.dataSig plainMods dName params sortE], sc', info :: exported)
            | some (beforeWhere, _, conBlockToks) =>
                match splitTopOn (· == .symColon) beforeWhere with
                | some (paramToks, _, sortToks) => do
                    -- Combined `data D (params) : Sort where ...`
                    let (params, scParams) ← parseTeleBinds sc paramToks
                    let sortE ← parseExpr scParams sortToks
                    let canon := sc.modPrefix ++ [dName]
                    let leanTyName := leanModNamespace sc.modPrefix ++ "." ++ leanMangleIdent dName
                    let dInfo : SymInfo :=
                      { localName := dName, canonPath := canon, kind := .typeSym
                      , fixity := lookupFix dName, leanName := leanTyName }
                    let scWithD := addSymUnqual sc dName dInfo
                    let paramNames := params.flatMap fun (.bind _ xs _) => xs
                    let scForCons := addLocalVars scWithD paramNames
                    let conSlices ← splitLayoutBlock conBlockToks
                    let (cons, conInfos) ← parseConSlices scForCons canon leanTyName lookupFix conSlices
                    let mut scFinal := scWithD
                    let mut extraConExp : List SymInfo := []
                    for ci in conInfos do
                      scFinal := addSymUnqual scFinal ci.localName ci
                      let qKey := String.intercalate "." canon ++ "." ++ ci.localName
                      let shortKey := dName ++ "." ++ ci.localName
                      scFinal := { scFinal with qualified := (qKey, ci) :: (shortKey, ci) :: scFinal.qualified }
                      extraConExp := { ci with localName := shortKey } :: ci :: extraConExp
                    let d1 := Decl.dataSig plainMods dName params sortE
                    let d2 := Decl.dataDef plainMods dName paramNames cons
                    .translated ([d1, d2], scFinal, extraConExp ++ (dInfo :: exported))
                | none => do
                    -- Separate `data D p₁ p₂ where ...` following an earlier `dataSig`!
                    if !(sc.unqualified.any (fun (k, _) => k == dName)) then
                      .syntaxErr s!"line {ln}: 'data {dName} where' lacks preceding 'data {dName} : ...' signature"
                    let paramNames ← beforeWhere.mapM fun
                      | { kind := .ident p, .. } => .translated p
                      | t => .syntaxErr s!"{tokDesc t}: invalid parameter name in 'data {dName} where'"
                    let canon := sc.modPrefix ++ [dName]
                    let leanTyName := leanModNamespace sc.modPrefix ++ "." ++ leanMangleIdent dName
                    let scForCons := addLocalVars sc paramNames
                    let conSlices ← splitLayoutBlock conBlockToks
                    let (cons, conInfos) ← parseConSlices scForCons canon leanTyName lookupFix conSlices
                    let mut scFinal := sc
                    let mut extraConExp : List SymInfo := []
                    for ci in conInfos do
                      scFinal := addSymUnqual scFinal ci.localName ci
                      let qKey := String.intercalate "." canon ++ "." ++ ci.localName
                      let shortKey := dName ++ "." ++ ci.localName
                      scFinal := { scFinal with qualified := (qKey, ci) :: (shortKey, ci) :: scFinal.qualified }
                      extraConExp := { ci with localName := shortKey } :: ci :: extraConExp
                    .translated ([.dataDef plainMods dName paramNames cons], scFinal, extraConExp ++ exported)
      | _ => .syntaxErr "expected datatype name after 'data'"

    parseConSlices (sc : ScopeEnv) (dataCanon : List String) (leanTyName : String)
        (lookupFix : String → FixLevel) (slices : List (List Token)) :
        PrismOutcome (List (String × Expr) × List SymInfo) := do
      let mut cons : List (String × Expr) := []
      let mut infos : List SymInfo := []
      for sl in slices do
        match splitTopOn (· == .symColon) sl with
        | none => PrismOutcome.syntaxErr "constructor declaration missing ':'"
        | some (cNamesToks, cTok, cTyToks) =>
            match parseSigNames cNamesToks with
            | none | some ["_"] => PrismOutcome.syntaxErr s!"{tokDesc cTok}: invalid constructor name"
            | some cNames => do
                let cTy ← parseExpr sc cTyToks
                let ar := parseConstructorArity cTy
                for cn in cNames do
                  cons := cons ++ [(cn, cTy)]
                  let cCanon := dataCanon ++ [cn]
                  let ci : SymInfo :=
                    { localName := cn
                    , canonPath := cCanon
                    , kind      := .conSym
                    , fixity    := lookupFix cn
                    , leanName  := leanTyName ++ "." ++ leanMangleIdent cn
                    , conArity  := ar }
                  infos := infos ++ [ci]
      .translated (cons, infos)

    parseRecordDecl (sc : ScopeEnv) (exported : List SymInfo) (lookupFix : String → FixLevel)
        (toks : List Token) : PrismOutcome (List Decl × ScopeEnv × List SymInfo) := do
      match toks with
      | { kind := .ident rName, line := ln, .. } :: afterName =>
          match splitTopOn (· == .kwWhere) afterName with
          | none => .bot s!"line {ln}: split record signature without 'where' routed to Agda"
          | some (beforeWhere, _, bodyToks) =>
              match splitTopOn (· == .symColon) beforeWhere with
              | none => .syntaxErr s!"line {ln}: 'record {rName}' missing ': Set ...'"
              | some (paramToks, _, sortToks) => do
                  let isCoind := bodyToks.any (fun t => t.kind == .kwCoinductive)
                  if isCoind && !sc.selfGuarded then
                    PrismOutcome.syntaxErr s!"line {ln}: coinductive record '{rName}' requires OPTIONS --guardedness"
                  let (params, scParams) ← parseTeleBinds sc paramToks
                  let sortE ← parseExpr scParams sortToks
                  let paramNames := params.flatMap fun (.bind _ xs _) => xs
                  let canon := sc.modPrefix ++ [rName]
                  let canonDot := String.intercalate "." canon
                  let leanRecName := leanModNamespace sc.modPrefix ++ "." ++ leanMangleIdent rName
                  let rInfo : SymInfo :=
                    { localName := rName, canonPath := canon, kind := .typeSym
                    , fixity := lookupFix rName, leanName := leanRecName }
                  let scWithR := addSymUnqual sc rName rInfo
                  let scInRec := addLocalVars scWithR paramNames
                  let bodySlices ← splitLayoutBlock bodyToks
                  let mut constrOpt : Option String := none
                  let mut fields : List (String × Expr) := []
                  let mut scCur := scInRec
                  for bsl in bodySlices do
                    match bsl with
                    | [{ kind := .kwInductive, .. }] => pure ()
                    | [{ kind := .kwCoinductive, .. }] => pure ()
                    | [{ kind := .kwConstructor, .. }, { kind := .ident cName, .. }] =>
                        constrOpt := some cName
                    | { kind := .kwField, .. } :: fldToks =>
                        let fldSlices ← splitLayoutBlock fldToks
                        for fsl in fldSlices do
                          match splitTopOn (· == .symColon) fsl with
                          | none => PrismOutcome.syntaxErr s!"field in record '{rName}' missing ':'"
                          | some (fNamesT, _, fTyT) =>
                              match parseSigNames fNamesT with
                              | none | some ["_"] => PrismOutcome.syntaxErr s!"invalid field name in '{rName}'"
                              | some fNames => do
                                  let fTy ← parseExpr scCur fTyT
                                  for fn in fNames do
                                    fields := fields ++ [(fn, fTy)]
                                    -- Dependent record fields can be referenced by subsequent fields!
                                    scCur := addLocalVars scCur [fn]
                    | _ =>
                        -- Extra declarations inside `record ... where` -> route to Agda (`MAP.md §3.⑦`)
                        PrismOutcome.bot s!"record '{rName}' contains non-field declarations; routing to Agda"
                  let mut scOut := scWithR
                  let mut extraExp : List SymInfo := [rInfo]
                  if let some cn := constrOpt then
                    let cInfo : SymInfo :=
                      { localName := cn
                      , canonPath := sc.modPrefix ++ [cn]
                      , kind      := .conSym
                      , fixity    := lookupFix cn
                      , leanName  := leanRecName ++ "." ++ leanMangleIdent cn
                      , conArity  := fields.length }
                    scOut := addSymUnqual scOut cn cInfo
                    extraExp := cInfo :: extraExp
                  for (fn, _) in fields do
                    let fInfo : SymInfo :=
                      { localName := fn
                      , canonPath := canon ++ [fn]
                      , kind      := .projSym paramNames.length
                      , fixity    := lookupFix fn
                      , leanName  := leanRecName ++ "." ++ leanMangleIdent fn }
                    let qKey := canonDot ++ "." ++ fn
                    let shortKey := rName ++ "." ++ fn
                    scOut := { scOut with qualified := (qKey, fInfo) :: (shortKey, fInfo) :: scOut.qualified }
                    extraExp := { fInfo with localName := shortKey } :: extraExp
                  let nextCoind := if isCoind then canon :: scOut.coindRecords else scOut.coindRecords
                  scOut :=
                    { scOut with
                      recordFields := (canonDot, fields.map Prod.fst, constrOpt, paramNames.length) :: scOut.recordFields
                      coindRecords := nextCoind }
                  let d1 := Decl.recSig plainMods rName params sortE
                  let d2 := Decl.recDef plainMods rName paramNames { coind := isCoind, constr := constrOpt } fields
                  .translated ([d1, d2], scOut, extraExp ++ exported)
      | _ => .syntaxErr "expected record name after 'record'"

-- §6 Top-Level File Entrypoint

partial def parseAgdaModule (deps : List ExportedModule) (src : String) :
    PrismOutcome (CodeMod × ExportedModule) := do
  let allToks ← tokenizeAgda src
  let topSlices ← splitLayoutBlock allToks
  if topSlices.isEmpty then
    .syntaxErr "empty Agda file (expected 'module ... where')"
  else
    let rec splitHeaderPragmas (rem : List (List Token)) (pAcc : List Decl) :
        PrismOutcome (List Decl × List Token × List (List Token)) :=
      match rem with
      | [] => .syntaxErr "file contains pragmas only, missing 'module ... where'"
      | [{ kind := .pragma body, .. }] :: rest => do
          checkOptionsPragma body
          splitHeaderPragmas rest (.pragma body :: pAcc)
      | modSlice :: rest => .translated (pAcc.reverse, modSlice, rest)
    let (prePragmas, modSlice, extraTopSlices) ← splitHeaderPragmas topSlices []
    match modSlice with
    | { kind := .kwModule, line := ln, .. } :: { kind := .ident rawModName, .. } :: afterModName =>
        match splitTopOn (· == .kwWhere) afterModName with
        | none => .syntaxErr s!"line {ln}: 'module {rawModName}' missing 'where'"
        | some (modParamToks, _, inlineBodyToks) => do
            let modParts := rawModName.splitOn "."
            if modParts.any String.isEmpty then
              .syntaxErr s!"line {ln}: invalid module name '{rawModName}'"
            let allPragmaStrs := prePragmas.filterMap fun | .pragma s => some s | _ => none
            let selfSafe := allPragmaStrs.any (fun s => (s.splitOn " ").contains "--safe")
            let selfGuarded := allPragmaStrs.any (fun s => (s.splitOn " ").contains "--guardedness")
            let initSc := { emptyScope modParts deps with selfSafe := selfSafe, selfGuarded := selfGuarded }
            let (modParams, scWithParams) ←
              if modParamToks.isEmpty then .translated ([], initSc)
              else
                -- Parameterized top-level modules: route to Agda if non-empty to keep flat namespace simple
                .bot "parameterized top-level module routed to Agda"
            let inlineSlices ← splitLayoutBlock inlineBodyToks
            let bodySlices := inlineSlices ++ extraTopSlices
            let (bodyDecls, scFinal, exportedSyms) ← parseDeclList scWithParams bodySlices
            let codeMod : CodeMod :=
              { modName := { full := modParts, shown := rawModName }
              , params  := modParams
              , decls   := prePragmas ++ bodyDecls }
            let expMod : ExportedModule :=
              { modPath        := modParts
              , symbols        := exportedSyms
              , hasSafe        := selfSafe
              , hasGuardedness := selfGuarded
              , coindRecords   := scFinal.coindRecords }
            .translated (codeMod, expMod)
    | t :: _ =>
        .syntaxErr s!"{tokDesc t}: expected 'module <Name> where'"
    | [] => .syntaxErr "expected 'module <Name> where'"

end Prism
