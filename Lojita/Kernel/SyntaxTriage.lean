import Lean
import LojitaCtx.CharClass
import Lojita.Store.SExpr
import Lojita.Kernel.KernelLimits

namespace Lojita.Kernel
open Lean Parser
open Lojita.Store (SExpr)

structure QName where
  segments : List String
  deriving BEq, Hashable, Inhabited, Repr

def QName.toLeanName (q : QName) : Name :=
  q.segments.foldl Name.str .anonymous

def QName.ofName (n : Name) : QName :=
  ⟨n.components.map fun
    | .str _ s => s
    | .num _ i => toString i
    | .anonymous => ""⟩

def QName.dotName (q : QName) : String := q.toLeanName.toString

instance : ToString QName := ⟨QName.dotName⟩

/-- Reserved root namespaces: host/compiler internals plus prelude primitive roots. -/
def reservedPrefixes : List String := [
  "Lojita", "Lean", "Lake", "System", "Std", "IO", "Test",
  "Verification", "Main", "UI", "Unsafe", "TrustMe",
  "Nat", "String", "Char", "Bool", "Int", "UInt8", "UInt16", "UInt32", "UInt64",
  "USize", "BitVec", "Array", "ByteArray", "List", "Option", "Prod", "Sum", "Quot", "Eq"
]

private def validPart (s : String) : Bool :=
  !s.isEmpty && s != "TrustMe" && s != "Unsafe" && s != "_root_" &&
    s.toList.all fun c => !LojitaCtx.CharClass.space c && c.toNat >= 32 && !['.', '/', '\\'].contains c

def ordinaryPath (q : QName) : Bool :=
  match q.segments with
  | [] => false
  | h :: t => !reservedPrefixes.contains h && !["Init", "LojitaCtx"].contains h &&
    (h :: t).all validPart

def allowedImport (q : QName) : Bool :=
  match q.segments with
  | "LojitaCtx" :: x :: xs => (x :: xs).all validPart
  | _ => ordinaryPath q

def checkModulePaths (moduleName : QName) (imports : List QName) : Bool :=
  ordinaryPath moduleName && imports.all allowedImport

theorem ordinary_prefix_safe (moduleName : QName) (imports : List QName)
    (h : checkModulePaths moduleName imports = true) :
    moduleName.segments.headD "" ∉ reservedPrefixes := by
  obtain ⟨_ | ⟨a, as⟩⟩ := moduleName
  · simp [checkModulePaths, ordinaryPath] at h
  · change a ∉ reservedPrefixes
    intro ha
    simp [checkModulePaths, ordinaryPath, ha] at h

structure SyntaxViolation where
  code    : String
  offset  : Nat
  detail  : String
  detour? : Option String := none
  deriving Repr, Inhabited

instance : ToString SyntaxViolation where
  toString v :=
    match v.detour? with
    | some d => s!"{v.code}: byte {v.offset}: {v.detail}\n{d}"
    | none   => s!"{v.code}: byte {v.offset}: {v.detail}"

def violation (code : String) (stx : Syntax) (detail : String) : SyntaxViolation :=
  ⟨code, (stx.getPos?.getD 0).byteIdx, detail, none⟩

def tabooViolation (tc : TabooCode) (stx : Syntax) (detail : String) : SyntaxViolation :=
  ⟨tc.tag, (stx.getPos?.getD 0).byteIdx, detail, some tc.detour⟩

inductive Obj where
  | unit (q : QName) | ext (q : QName) | flags | bot
  deriving BEq, Hashable, Repr, Inhabited

inductive UnitKind where
  | inductiveDecl | structureDecl | defDecl | abbrevDecl | theoremDecl | mutualDecl | axiomDecl
  deriving BEq, Hashable, Repr, Inhabited

structure SynUnit where
  uname        : QName
  definedNames : List QName
  kind         : UnitKind
  rawSource    : String
  sigSlice     : String
  synRefs      : List QName
  deriving BEq, Hashable, Repr, Inhabited

structure ImportSpec where
  imod    : QName
  assumes : List SynUnit := []
  deriving BEq, Hashable, Repr, Inhabited

structure LeanMod where
  modName : QName
  imports : List ImportSpec
  opens   : List String
  units   : List SynUnit
  deriving BEq, Hashable, Repr, Inhabited

/-- Build toolchain path resolved at compile time (never shells out). -/
def toolchainRoot : System.FilePath := ⟨by_elab return toExpr (← getBuildDir).toString⟩

private initialize importLock : Std.Mutex Unit ← Std.Mutex.new ()

def withImportLock {α : Type} (action : IO α) : IO α :=
  importLock.atomically do action

private initialize grammarCache : Std.Mutex (Option Environment) ← Std.Mutex.new none

private def grammar : IO Environment := grammarCache.atomically do
  if let some env ← get then return env
  initKernelLimits
  let env ← withImportLock do
    let original ← searchPathRef.get
    try
      searchPathRef.set (← getBuiltinSearchPath toolchainRoot)
      unsafe enableInitializersExecution
      importModules #[{ module := `Init }] {} (loadExts := true)
    finally
      searchPathRef.set original
  set (some env)
  return env

private def syntaxError (original : FileMap) (log : MessageLog) : IO SyntaxViolation := do
  let msg := log.toList.head!
  return ⟨"parseError", (original.ofPosition msg.pos).byteIdx, ← msg.toString, none⟩

/-! ### 100% Explicit-Stack Iterative AST Walkers (Zero C++ Call-Stack Recursion) -/

private inductive SpanFrame where
  | enter (s : Syntax)
  | assemble (info : SourceInfo) (kind : SyntaxNodeKind) (arity : Nat)
  deriving Inhabited

/-- Iterative post-order span rewriter for CRLF sources (safe at arbitrary AST depth). -/
def restoreOriginalSpans (normalized original : FileMap) (root : Syntax) : Syntax := Id.run do
  let pos := fun p => original.ofPosition (normalized.toPosition p)
  let sub := fun (v : Substring.Raw) => {
    v with str := original.source, startPos := pos v.startPos, stopPos := pos v.stopPos
  }
  let mapInfo := fun
    | .original l p t e => SourceInfo.original (sub l) (pos p) (sub t) (pos e)
    | .synthetic p e c  => .synthetic (pos p) (pos e) c
    | .none             => .none
  let mut work : Array SpanFrame := #[.enter root]
  let mut out  : Array Syntax := #[]
  while !work.isEmpty do
    let frame := work.back!
    work := work.pop
    match frame with
    | .enter .missing =>
      out := out.push .missing
    | .enter (.ident i raw n pre) =>
      out := out.push (.ident (mapInfo i) (sub raw) n pre)
    | .enter (.atom i a) =>
      out := out.push (.atom (mapInfo i) a)
    | .enter (.node i k args) =>
      work := work.push (.assemble (mapInfo i) k args.size)
      let mut idx := args.size
      while idx > 0 do
        idx := idx - 1
        work := work.push (.enter args[idx]!)
    | .assemble info kind arity =>
      let start := out.size - arity
      let children := out.extract start out.size
      out := (out.shrink start).push (.node info kind children)
  return out[0]?.getD .missing

/-- Iterative left-to-right leaf collector ($O(|AST|)$ time, zero recursion). -/
def leavesIter (roots : Array Syntax) : Array Syntax := Id.run do
  let mut stack : Array Syntax := #[]
  let mut i := roots.size
  while i > 0 do
    i := i - 1
    stack := stack.push roots[i]!
  let mut out : Array Syntax := #[]
  while !stack.isEmpty do
    let s := stack.back!
    stack := stack.pop
    if s.isIdent || s matches .atom .. then
      out := out.push s
    else
      let args := s.getArgs
      let mut j := args.size
      while j > 0 do
        j := j - 1
        stack := stack.push args[j]!
  return out

/-- Iterative left-to-right identifier collector ($O(|AST|)$ time, zero recursion). -/
def identifiersIter (root : Syntax) : List Name := Id.run do
  let mut stack : Array Syntax := #[root]
  let mut out : Array Name := #[]
  while !stack.isEmpty do
    let s := stack.back!
    stack := stack.pop
    if s.isIdent then
      out := out.push s.getId
    else
      let args := s.getArgs
      let mut j := args.size
      while j > 0 do
        j := j - 1
        stack := stack.push args[j]!
  return out.toList

private def kindOf (d : Syntax) : Option UnitKind :=
  match d.getKind with
  | ``Command.inductive                      => some .inductiveDecl
  | ``Command.structure                      => some .structureDecl
  | ``Command.definition                     => some .defDecl
  | ``Command.abbrev                         => some .abbrevDecl
  | ``Command.theorem | ``Command.example    => some .theoremDecl
  | ``Command.axiom                          => some .axiomDecl
  | _                                        => none

private def binderNames (s : Syntax) : List Name :=
  if s.isIdent then [s.getId]
  else if [``Term.explicitBinder, ``Term.implicitBinder, ``Term.strictImplicitBinder,
           ``Term.instBinder].contains s.getKind then identifiersIter s[1]
  else []

/-- Iterative free-reference token collector ($O(|AST|)$ time, zero recursion). -/
def freeRefTokensIter (root : Syntax) : List Syntax := Id.run do
  let mut stack : Array (Syntax × List Name) := #[(root, [])]
  let mut out : Array Syntax := #[]
  while !stack.isEmpty do
    let (s, bound) := stack.back!
    stack := stack.pop
    if s.isIdent then
      if !bound.contains s.getId.getRoot then
        out := out.push s
    else if s.isOfKind ``Command.declId || s.isOfKind ``Term.letId then
      pure ()
    else
      let children := s.getArgs
      let pushSliceRev (cs : Array Syntax) (b : List Name) (stk : Array (Syntax × List Name)) :
          Array (Syntax × List Name) := Id.run do
        let mut r := stk
        let mut k := cs.size
        while k > 0 do
          k := k - 1
          r := r.push (cs[k]!, b)
        return r
      if s.isOfKind ``Term.basicFun || s.isOfKind ``Term.forall then
        let i := if s.isOfKind ``Term.basicFun then 0 else 1
        let binders := s[i].getArgs
        let declared := binders.toList.flatMap binderNames
        stack := pushSliceRev (children.extract (i + 1) children.size) (declared ++ bound) stack
        stack := pushSliceRev (binders.filter (!·.isIdent)) bound stack
      else if s.isOfKind ``Term.let then
        let decl := s[2][0]
        let names := if decl.isOfKind ``Term.letIdDecl then identifiersIter decl[0] else []
        stack := pushSliceRev (children.extract 3 children.size) (names ++ bound) stack
        stack := stack.push (decl, bound)
      else if s.isOfKind ``Term.explicitBinder || s.isOfKind ``Term.implicitBinder ||
              s.isOfKind ``Term.strictImplicitBinder then
        stack := pushSliceRev (children.extract 2 children.size) bound stack
      else if s.isOfKind ``Tactic.tacticSeq1Indented || s.isOfKind ``Tactic.tacticSeqBracketed then
        let seq := if s.isOfKind ``Tactic.tacticSeqBracketed then s[1] else s[0]
        let tacs := seq.getArgs
        let mut locals := bound
        let mut pairs : Array (Syntax × List Name) := #[]
        for tac in tacs do
          if tac.isOfKind ``Tactic.intro then
            locals := identifiersIter tac[1] ++ locals
          else
            pairs := pairs.push (tac, locals)
        let mut k := pairs.size
        while k > 0 do
          k := k - 1
          stack := stack.push pairs[k]!
      else if (kindOf s).isSome then
        let sig := if s.isOfKind ``Command.example then s[1] else s[2]
        let locals := sig[0].getArgs.toList.flatMap binderNames
        stack := pushSliceRev children (locals ++ bound) stack
      else if s.isOfKind ``Command.ctor then
        stack := stack.push (s[4], bound)
      else if s.isOfKind ``Command.structCtor then
        stack := stack.push (s[2], bound)
      else if s.isOfKind ``Command.structSimpleBinder then
        stack := pushSliceRev (children.extract 2 children.size) bound stack
      else if s.isOfKind ``Command.declSig || s.isOfKind ``Command.optDeclSig then
        stack := stack.push (s[1], bound)
        stack := pushSliceRev (s[0].getArgs.filter (!·.isIdent)) bound stack
      else
        stack := pushSliceRev children bound stack
  return out.toList

/-! ### Stage 1: Taboo Triage Rules (T1, T2, T3, T4, T6 + Surface Security) -/

private def metaTokens : List String := [
  "#eval", "#check", "#print", "#reduce", "#synth", "run_cmd",
  "elab", "elab_rules", "macro", "macro_rules", "syntax", "notation", "infix", "infixl",
  "infixr", "prefix", "postfix", "local", "attribute", "set_option", "run_tac", "by_elab",
  "eval%", "meta", "native_decide", "decreasing_by_elab"
]

private def nativeAttrs : List String := [
  "extern", "implemented_by", "csimp", "init", "builtin_init", "Pervasive", "export"
]

/-- Maximum allowed expression syntax nesting depth before Stage 1 shunting (T1). -/
def maxSyntaxExprDepth : Nat := 1024

/-- Maximum elements in a single `[...]` or `#[...]` literal expression (T1). -/
def maxContainerLitElems : Nat := 4096

/-- Maximum `|exponent|` on a scientific literal `m * 10^e` (T2, #16538 / #13987). -/
def maxScientificExponent : Nat := 308

/-- Maximum digit length of an integer literal token (T2). -/
def maxNumeralDigits : Nat := 256

/-- Maximum pattern rows in a single `match` / `fun` / equation block (T3, #3935 / #9322). -/
def maxMatchArms : Nat := 64

/-- Maximum constructors on an `inductive` deriving `DecidableEq` (T4, #11450). -/
def maxDecidableEqCtors : Nat := 64

/-- Flat sequence containers whose children are siblings rather than nested expressions. -/
private def isFlatSyntaxKind (k : SyntaxNodeKind) : Bool :=
  k == nullKind ||
  k == ``Command.mutual ||
  k == ``Command.declaration ||
  k == ``Term.matchAlts ||
  k == ``Term.doSeqIndent ||
  k == ``Term.doSeqBracketed ||
  k == ``Tactic.tacticSeq1Indented ||
  k == ``Tactic.tacticSeqBracketed

/-- Parse the decimal exponent magnitude `|e|` from a Lean scientific literal atom like `1.5e100000`. -/
private def parseScientificAbsExp? (raw : String) : Option Nat := Id.run do
  let cs := raw.toList.filter (· != '_')
  let rec dropToExp : List Char → Option (List Char)
    | [] => none
    | c :: rest => if c == 'e' || c == 'E' then some rest else dropToExp rest
  let some expChars := dropToExp cs | return none
  let digits := match expChars with
    | '+' :: d | '-' :: d => d
    | d => d
  return (String.ofList digits).toNat?

/-- Count total pattern rows in a `Term.matchAlts` node and check if any pattern contains `_`. -/
private def inspectMatchAlts (matchAltsStx : Syntax) : Nat × Bool := Id.run do
  let alts := matchAltsStx[0].getArgs
  let mut totalRows := 0
  let mut hasWildcard := false
  for alt in alts do
    let patGroups := alt[1].getArgs
    let rows := if patGroups.isEmpty then 1 else (patGroups.size + 1) / 2
    totalRows := totalRows + rows
    if !hasWildcard then
      let mut stk : Array Syntax := #[alt[1]]
      while !stk.isEmpty do
        let cur := stk.back!
        stk := stk.pop
        if cur.isOfKind ``Term.hole || (cur.isAtom && cur.getAtomVal == "_") then
          hasWildcard := true
          stk := #[]
        else
          for child in cur.getArgs do
            stk := stk.push child
  return (max alts.size totalRows, hasWildcard)

private def heavyDecideTypeNames : List String := [
  "String", "ByteArray", "Array", "Bytes", "SimWorld",
  "LojitaCtx.Terminal.Bytes", "LojitaCtx.World.SimWorld"
]

/-- Check if a command contains heavy types or large literals (> 64 bytes/elements) in its signature/statement,
    making `by decide` catastrophic in Lean 4's kernel (T6, #16268 / #5502). -/
private def commandHasHeavyDecideTarget (cmd : Syntax) : Bool := Id.run do
  -- Extract the declaration signature / statement portion (excluding the tactic proof body itself)
  -- or inspect literals across the statement.
  let members := if cmd.isOfKind ``Command.mutual then cmd[1].getArgs else #[cmd]
  for member in members do
    if member.isOfKind ``Command.declaration then
      let d := member[1]
      -- Inspect signature nodes (`d[1]`, `d[2]`) and also any large literals anywhere in `d`
      let sigPart := if d.isOfKind ``Command.example then #[d[1]] else #[d[1], d[2]]
      for leaf in leavesIter sigPart do
        if leaf.isIdent && heavyDecideTypeNames.contains leaf.getId.toString then
          return true
      let mut stk : Array Syntax := #[d]
      while !stk.isEmpty do
        let s := stk.back!
        stk := stk.pop
        if s.isOfKind strLitKind && s[0].getAtomVal.utf8ByteSize > 64 then
          return true
        if s.getArgs.size == 3 && (s[0].getAtomVal == "[" || s[0].getAtomVal == "#[") && s[2].getAtomVal == "]" then
          let elems := if s[1].getArgs.isEmpty then 0 else (s[1].getArgs.size + 1) / 2
          if elems > 64 then
            return true
          if s[0].getAtomVal == "#[" && elems > 0 then
            return true
        if s.isIdent && (s.getId == `ByteArray.mk || s.getId == `String.toUTF8 || s.getId == `List.toByteArray) then
          return true
        for ch in s.getArgs do
          stk := stk.push ch
  return false

/-- Check whether `decide` tactic syntax passes `+native` or `native := true` (synonym for `native_decide`!). -/
private def decideHasNativeConfig (decideTacStx : Syntax) : Bool := Id.run do
  for leaf in leavesIter #[decideTacStx] do
    let w := if leaf.isIdent then leaf.getId.toString else leaf.getAtomVal
    if w == "native" then return true
  return false

/-- Iterative single-pass Stage 1 AST scanner enforcing both security boundaries and Taboos T1, T2, T3, T4, T6. -/
def triageSyntax (root : Syntax) : Except SyntaxViolation Unit := do
  let mut stack : Array (Syntax × Nat × Bool) := #[(root, 0, false)]
  let mut sawDecideTactic : Option Syntax := none
  while !stack.isEmpty do
    let (stx, depth, inAttr) := stack.back!
    stack := stack.pop
    if depth > maxSyntaxExprDepth then
      throw (tabooViolation .syntaxDepth stx
        s!"expression syntax nesting depth exceeds {maxSyntaxExprDepth}")
    let inAttr := inAttr || stx.isOfKind ``Lean.Parser.Term.attributes
    let kind := stx.getKind

    -- Surface security check on identifiers and keyword atoms (never on string literals/comments)
    if stx.isIdent || (stx matches .atom .. && kind != strLitKind && kind != charLitKind &&
        kind != numLitKind && kind != scientificLitKind) then
      let word := if stx.isIdent then stx.getId.toString else stx.getAtomVal
      let code? :=
        if ["sorry", "admit"].contains word then some "hasSorrySyntax"
        else if word == "unsafe" then some "forbiddenUnsafe"
        else if word == "noncomputable" then some "forbiddenNoncomputable"
        else if ["partial", "partial_fixpoint"].contains word then some "forbiddenPartial"
        else if ["initialize", "builtin_initialize"].contains word || (inAttr && nativeAttrs.contains word) then
          some "forbiddenNativeOverride"
        else if metaTokens.contains word then some "forbiddenMetaprogramming"
        else none
      if let some code := code? then
        throw (violation code stx word)

    -- T1: Giant list `[...]` or array `#[...]` container literal
    let args := stx.getArgs
    if args.size == 3 && (args[0]!.getAtomVal == "[" || args[0]!.getAtomVal == "#[") &&
        args[2]!.getAtomVal == "]" then
      let rawItems := args[1]!.getArgs.size
      let elemCount := if rawItems == 0 then 0 else (rawItems + 1) / 2
      if elemCount > maxContainerLitElems then
        throw (tabooViolation .giantContainerLit stx
          s!"container literal has {elemCount} elements (limit: {maxContainerLitElems})")

    -- T2: Scientific literal exponent & giant integer literal (`isLit?` extracts `stx[0].getAtomVal`)
    if let some rawSci := Syntax.isLit? scientificLitKind stx then
      if let some exp := parseScientificAbsExp? rawSci then
        if exp > maxScientificExponent then
          throw (tabooViolation .scientificExponent stx
            s!"scientific literal exponent {exp} exceeds safe limit {maxScientificExponent}")
    if let some rawNum := Syntax.isLit? numLitKind stx then
      let cleanLen := rawNum.foldl (fun acc c => if c == '_' then acc else acc + 1) 0
      if cleanLen > maxNumeralDigits then
        throw (tabooViolation .giantNumeral stx
          s!"integer literal has {cleanLen} characters (limit: {maxNumeralDigits})")

    -- T3: Wide `match` / multi-discriminant overlapping `match`
    if kind == ``Term.match then
      let numDiscrs := (stx[3].getArgs.size + 1) / 2
      let (numRows, hasWild) := inspectMatchAlts stx[5]
      if numRows > maxMatchArms then
        throw (tabooViolation .wideMatch stx
          s!"`match` has {numRows} pattern rows (limit: {maxMatchArms})")
      if numDiscrs >= 4 && numRows > 32 && hasWild then
        throw (tabooViolation .overlappingMatch stx
          s!"`match` with {numDiscrs} scrutinees, {numRows} rows, and wildcard triggers splitter blowup")
    else if kind == ``Term.matchAlts then
      let (numRows, _) := inspectMatchAlts stx
      if numRows > maxMatchArms then
        throw (tabooViolation .wideMatch stx
          s!"pattern match block has {numRows} pattern rows (limit: {maxMatchArms})")

    -- T4: Wide `inductive` deriving `DecidableEq`
    if kind == ``Command.inductive then
      let numCtors := stx[4].getArgs.size
      if numCtors > maxDecidableEqCtors then
        let derivLeaves := leavesIter #[stx[6]]
        if derivLeaves.any (fun l => l.isIdent && l.getId == `DecidableEq) then
          throw (tabooViolation .wideDecidableEq stx
            s!"inductive has {numCtors} constructors with `deriving DecidableEq` (limit: {maxDecidableEqCtors})")

    -- T6 & Security: `decide` tactic (`decide +native` is forbidden; heavy `by decide` is shunted)
    if kind == ``Lean.Parser.Tactic.decide then
      if decideHasNativeConfig stx then
        throw (violation "forbiddenMetaprogramming" stx "decide +native")
      if sawDecideTactic.isNone then
        sawDecideTactic := some stx

    -- Push children in reverse order (skip inner literal/doc atoms); keep depth flat for sequence nodes
    let isLeafLitWrapper := kind == strLitKind || kind == charLitKind ||
      kind == numLitKind || kind == scientificLitKind || kind == ``Lean.Parser.Command.docComment
    if !isLeafLitWrapper then
      let nextDepth := if isFlatSyntaxKind kind ||
          (args.size == 3 && (args[0]!.getAtomVal == "[" || args[0]!.getAtomVal == "#[") && args[2]!.getAtomVal == "]")
        then depth else depth + 1
      let mut j := args.size
      while j > 0 do
        j := j - 1
        stack := stack.push (args[j]!, nextDepth, inAttr)

  if let some decStx := sawDecideTactic then
    if commandHasHeavyDecideTarget root then
      throw (tabooViolation .heavyDecide decStx
        "`by decide` used on String / ByteArray / Array / SimWorld or large literal (> 64 bytes/items)")

/-! ### Module Envelope Parsing, Rendering, Serialization & Surface Morphisms -/

/-- Pre-parser guard against unbalanced/20k-deep token chains before Pratt parsing if needed,
    combined with Lean's `parseHeader` + `parseCommand` + `triageSyntax`. -/
private def parseSource (src : String) :
    IO (Except SyntaxViolation (Environment × Syntax × Array Syntax)) := do
  let env ← grammar
  let input := mkInputContext src "<object>"
  let crlf := src.contains "\r\n"
  let original := if crlf then src.toFileMap else input.fileMap
  let restore := fun s => if crlf then restoreOriginalSpans input.fileMap original s else s
  let (header, initial, errors) ← parseHeader input
  if errors.hasErrors then return .error (← syntaxError original errors)
  let mut state := initial
  let mut cmds := #[]
  repeat
    let (cmd, next, log) := parseCommand input { env, options := {} } state {}
    let cmd := restore cmd
    if let .error v := triageSyntax cmd then return .error v
    if log.hasErrors then return .error (← syntaxError original log)
    if cmd.isOfKind ``Lean.Parser.Command.eoi then break
    cmds := cmds.push cmd
    state := next
  return .ok (env, restore header.raw, cmds)

/-- Parse and triage a Lean source string on a dedicated 64 MiB worker thread so even extreme
    Pratt-parser operator chains (e.g. 20,000 left-associative `+` tokens) never overflow a small caller stack. -/
private def sourceSyntax (src : String) : Except SyntaxViolation (Environment × Syntax × Array Syntax) :=
  let runParse : IO (Except SyntaxViolation (Environment × Syntax × Array Syntax)) := do
    initKernelLimits
    let t ← IO.asTask (prio := .dedicated) (parseSource src)
    match ← IO.wait t with
    | .ok res => return res
    | .error e => return .error ⟨"parserEnvironment", 0, toString e, none⟩
  match unsafe unsafeIO runParse with
  | .ok result => result
  | .error e   => .error ⟨"parserEnvironment", 0, toString e, none⟩

private def slice (src : String) (s : Syntax) : String :=
  let stop := s.getTailInfo.getTrailingTailPos? |>.getD (s.getTailPos?.getD 0)
  ((s.getPos?.getD 0).extract src stop).trimAsciiEnd.copy

private def fieldsOf (s : Syntax) : List Name := Id.run do
  let mut names := #[]
  for parent in s[3][0][1].getArgs do
    if parent.isOfKind ``Command.structParent then
      let id := parent[0][0]
      let ty := parent[1]
      let head := if ty.isOfKind ``Term.app then ty[0] else ty
      if id.isIdent then names := names.push id.getId
      else if head.isIdent then names := names.push (Name.mkSimple ("to" ++ head.getId.getString!))
  for field in s[4][2][0].getArgs do
    if field.isOfKind ``Command.structSimpleBinder then
      names := names.push field[1].getId
    else
      names := names ++ field[2].getArgs.map Syntax.getId
  return names.toList

private def namesOf (d : Syntax) : List Name := Id.run do
  if d.isOfKind ``Command.example then return []
  let n := d[1][0].getId
  let members :=
    if d.isOfKind ``Command.inductive then
      d[4].getArgs.toList.map (fun c => c[3].getId)
    else if d.isOfKind ``Command.structure then
      let ctor := d[4][1][0][1].getId
      (if ctor.isAnonymous then `mk else ctor) :: fieldsOf d
    else []
  return n :: members.map (n ++ ·)

private def headerTokens (cmd : Syntax) : List String := Id.run do
  let d := cmd[1]
  let head :=
    if d.isOfKind ``Command.example then d.getArgs.extract 0 2
    else d.getArgs.extract 0 (if d.isOfKind ``Command.structure then 4 else 3)
  return (leavesIter head).toList.map fun s =>
    if s.isIdent then s.getId.toString else s.getAtomVal

private def unitOf (src : String) (mod : Name) (idx : Nat) (cmd : Syntax) :
    Except SyntaxViolation SynUnit := do
  let mutualBlock := cmd.isOfKind ``Command.mutual
  let members := if mutualBlock then cmd[1].getArgs else #[cmd]
  let mut names := #[]
  let mut sigs := #[]
  let mut refs := #[]
  let mut kind := UnitKind.mutualDecl
  for member in members do
    let d := member[1]
    unless member.isOfKind ``Command.declaration do
      throw (violation "unsupportedCommand" member member.getKind.toString)
    let some k := kindOf d | throw (violation "unsupportedCommand" d d.getKind.toString)
    if !mutualBlock then kind := k
    let declared := namesOf d
    for n in declared do
      if n.isAnonymous || n.getRoot == `_root_ then
        throw (violation "namespaceBoundary" d s!"declaration {n}")
      names := names.push (QName.ofName (mod ++ n))
    sigs := sigs.push (String.intercalate " " (headerTokens member))
    for token in freeRefTokensIter d do
      refs := refs.push (QName.ofName token.getId)
  let name := names[0]?.getD (QName.ofName (mod ++ Name.mkSimple s!"_example{idx}"))
  return ⟨name, names.toList, kind, slice src cmd, String.intercalate "\n" sigs.toList,
    refs.toList.eraseDups⟩

private def isAlias (cmd : Syntax) : Bool :=
  let d := cmd[1]
  cmd.isOfKind ``Command.declaration && d.isOfKind ``Command.abbrev &&
    d[2].getPos?.isNone && d[3][1].isIdent

private def openedNames (s : Syntax) : List OpenDecl := Id.run do
  if s.isOfKind ``Command.openSimple then
    return (identifiersIter s[0]).map (.simple · [])
  let ns := s[0].getId
  if s.isOfKind ``Command.openOnly then
    return (identifiersIter s[2]).map fun n => .explicit n (ns ++ n)
  if s.isOfKind ``Command.openHiding then
    return [.simple ns (identifiersIter s[2])]
  if s.isOfKind ``Command.openRenaming then
    return (s[2].getArgs.filter (·.isOfKind ``Command.openRenamingItem)).toList.map fun pair =>
      .explicit pair[2].getId (ns ++ pair[0].getId)
  return []

private def qualifyRefs (env : Environment) (m : LeanMod) (opened : List OpenDecl)
    (aliases : List (Name × Name)) : LeanMod := Id.run do
  let locals := m.units.flatMap (·.definedNames) ++
    aliases.map (fun a => QName.ofName (m.modName.toLeanName ++ a.1))
  let imported := m.imports.flatMap fun i => i.assumes.flatMap (·.definedNames)
  let known := NameSet.ofList ((locals ++ imported).map QName.toLeanName)
  let scopes := m.modName.toLeanName.components.foldl
    (fun (ps : List Name) p => (ps.head! ++ p) :: ps) [.anonymous]
  let inScope := fun (n : Name) => (scopes.map (· ++ n)).find? known.contains
  let resolve (q : QName) : List QName := Id.run do
    let n := q.toLeanName
    if n.getRoot == `_root_ then return [QName.ofName (n.replacePrefix `_root_ .anonymous)]
    if let some localName := inScope n then return [QName.ofName localName]
    if let some aliasName := aliases.lookup n.getRoot then
      if n != n.getRoot then return [QName.ofName (n.replacePrefix n.getRoot aliasName)]
    let candidates := opened.filterMap fun
      | .simple ns hide => if hide.contains n.getRoot then none else some (ns ++ n)
      | .explicit id target => if id.isPrefixOf n then some (n.replacePrefix id target) else none
    let resolved := candidates.filterMap fun name =>
      inScope name <|> (if env.contains name then some name else none)
    if !resolved.isEmpty then return resolved.map QName.ofName
    if env.contains n || m.imports.any (fun i => i.imod.toLeanName.isPrefixOf n) then return [q]
    return q :: candidates.map QName.ofName
  return { m with units := m.units.map fun u =>
    { u with synRefs := (u.synRefs.flatMap resolve).eraseDups } }

private def parseEnvelope (src : String) (ifaces : List ImportSpec) (probe := false) :
    Except SyntaxViolation (LeanMod × Array Syntax) := do
  let (env, hdr, cmds) ← sourceSyntax src
  triageSyntax hdr
  unless hdr[0].getArgs.isEmpty && hdr[1].getArgs.isEmpty do
    throw (violation "unsupportedHeader" hdr "expected ordinary imports")
  let interfaces := Std.HashMap.ofList (ifaces.map fun i => (i.imod, i.assumes))
  let imports ← hdr[2].getArgs.toList.mapM fun imp => do
    let q := QName.ofName imp[4].getId
    unless allowedImport q || (probe && q.toLeanName == `Lojita.Session.SessionEnv) do
      throw (violation "forbiddenImport" imp s!"{q}")
    let assumes := if q.toLeanName.getRoot == `LojitaCtx then [] else interfaces[q]?.getD []
    return { imod := q, assumes : ImportSpec }
  let first := cmds[0]?.getD .missing
  let last := cmds.back?.getD .missing
  unless first.isOfKind ``Command.namespace && last.isOfKind ``Command.end do
    throw (violation "namespaceEnvelope" first "expected namespace M ... end M")
  let name := first[1].getId
  let q := QName.ofName name
  unless ordinaryPath q do
    throw (violation "forbiddenNamespace" first s!"{q}")
  unless last[1][0].getId == name do
    throw (violation "namespaceEnvelope" last "mismatched end")
  let mut units := #[]
  let mut opens := #[]
  let mut opened := []
  let mut aliases := []
  for cmd in cmds.extract 1 (cmds.size - 1) do
    if cmd.isOfKind ``Command.open || (units.isEmpty && isAlias cmd) then
      unless units.isEmpty do
        throw (violation "namespaceEnvelope" cmd "open after declaration")
      opens := opens.push (slice src cmd)
      if isAlias cmd then
        let a := cmd[1][1][0].getId
        if a.getRoot == `_root_ then throw (violation "namespaceBoundary" cmd s!"alias {a}")
        aliases := (a, cmd[1][3][1].getId) :: aliases
      else
        opened := openedNames cmd[1] ++ opened
    else
      units := units.push (← unitOf src name units.size cmd)
  return (qualifyRefs env ⟨q, imports, opens.toList, units.toList⟩ opened aliases, cmds)

def readEnvelope (src : String) : Except SyntaxViolation (LeanMod × Array Syntax) :=
  parseEnvelope src []

def readProbeEnvelope (src : String) : Except SyntaxViolation (LeanMod × Array Syntax) :=
  parseEnvelope src [] true

def parseLeanMod (src : String) : Except String LeanMod :=
  ((readEnvelope src).map Prod.fst).mapError toString

def renderLeanMod (m : LeanMod) : String :=
  String.intercalate "\n" ((m.imports.map fun i => s!"import {i.imod}") ++
    [s!"namespace {m.modName}"] ++ m.opens ++ m.units.map (·.rawSource) ++ [s!"end {m.modName}", ""])

def publicNames (m : LeanMod) : List QName := Id.run do
  let .ok (_, cmds) := readEnvelope (renderLeanMod m) | return []
  let mut out := #[]
  for cmd in cmds do
    let members := if cmd.isOfKind ``Command.mutual then cmd[1].getArgs else #[cmd]
    for c in members do
      if c.isOfKind ``Command.declaration && !c[0][2][0].isOfKind ``Command.«private» then
        for n in namesOf c[1] do
          out := out.push (QName.ofName (m.modName.toLeanName ++ n))
  return out.toList

private def qExpr (q : QName) : SExpr := .list (q.segments.map .str)

private def unitExpr (u : SynUnit) : SExpr := .list [
  qExpr u.uname,
  .list (u.definedNames.map qExpr),
  .num u.kind.ctorIdx,
  .str u.rawSource,
  .str u.sigSlice,
  .list (u.synRefs.map qExpr)
]

def encodeCanonical (m : LeanMod) : String := SExpr.canonical <| .list [
  .sym "lean-mod-v1", qExpr m.modName,
  .list (m.imports.map fun i => .list [qExpr i.imod, .list (i.assumes.map unitExpr)]),
  .list (m.opens.map .str),
  .list (m.units.map unitExpr)
]

private def listOf {α : Type} (f : SExpr → Option α) : SExpr → Option (List α)
  | .list xs => xs.mapM f
  | _ => none

private def asStr : SExpr → Option String
  | .str s => some s
  | _ => none

private def asQ (e : SExpr) : Option QName := QName.mk <$> listOf asStr e

private def asUnit : SExpr → Option SynUnit
  | .list [n, ns, .num k, .str raw, .str sig, refs] => do
    let kind ← [UnitKind.inductiveDecl, .structureDecl, .defDecl, .abbrevDecl,
      .theoremDecl, .mutualDecl, .axiomDecl][k]?
    return ⟨← asQ n, ← listOf asQ ns, kind, raw, sig, ← listOf asQ refs⟩
  | _ => none

def decodeCanonical (s : String) : Option LeanMod := do
  let .list [.sym "lean-mod-v1", n, imps, opens, units] ← SExpr.parseSExpr s | none
  let imports ← listOf (fun
    | .list [i, us] => return ⟨← asQ i, ← listOf asUnit us⟩
    | _ => none) imps
  return ⟨← asQ n, imports, ← listOf asStr opens, ← listOf asUnit units⟩

def encodeIface (units : List SynUnit) : SExpr := .list (.sym "iface" :: units.map unitExpr)

def decodeIface : SExpr → Option (List SynUnit)
  | .list (.sym "iface" :: units) => units.mapM asUnit
  | _ => none

private def renameSource (src : String) (stxs : Array Syntax) (before after : Name)
    (fixed : List Name := []) : String := Id.run do
  let mut out := ""
  let mut pos : String.Pos.Raw := 0
  for s in leavesIter stxs do
    if !s.isIdent then continue
    let n := s.getId
    if fixed.any (·.isPrefixOf (n.replacePrefix `_root_ .anonymous)) then continue
    let n' := (n.replacePrefix before after).replacePrefix (`_root_ ++ before) (`_root_ ++ after)
    if n == n' then continue
    let some span := s.getRange? | continue
    if span.start < pos then continue
    out := out ++ pos.extract src span.start ++ n'.toString
    pos := span.stop
  return out ++ pos.extract src src.rawEndPos

def withChildIfaces (m : LeanMod) (children : List LeanMod) : LeanMod := Id.run do
  let ifaces := Std.HashMap.ofList (children.map fun c => (c.modName, c))
  let imports := m.imports.map fun i =>
    match ifaces[i.imod]? with
    | some child => { i with assumes := child.units }
    | none => i
  return ((parseEnvelope (renderLeanMod m) imports).map Prod.fst).toOption.getD m

def renamedRef? (renames : Std.HashMap QName QName) (q : QName) : Option QName := Id.run do
  let n := q.toLeanName
  let mut owner := n
  while !owner.isAnonymous do
    if let some target := renames[QName.ofName owner]? then
      return some (QName.ofName (n.replacePrefix owner target.toLeanName))
    owner := owner.getPrefix
  return none

def opensAfterRemoval (m : LeanMod) (removed : List QName) : List String := Id.run do
  if removed.isEmpty || m.opens.isEmpty then return m.opens
  let removed := NameSet.ofList (removed.map QName.toLeanName)
  let gone := fun (name : Name) => Id.run do
    let absolute := name.getRoot == `_root_
    let mut scope := if absolute then .anonymous else m.modName.toLeanName
    repeat
      let mut n := scope ++ name.replacePrefix `_root_ .anonymous
      while !n.isAnonymous do
        if removed.contains n then return true
        n := n.getPrefix
      if scope.isAnonymous then break
      scope := scope.getPrefix
    return false
  let .ok (_, _, cmds) := sourceSyntax (renderLeanMod { m with units := [] }) | return m.opens
  let mut kept := #[]
  for raw in m.opens, cmd in cmds.extract 1 (cmds.size - 1) do
    let arg := cmd[1]
    if arg.isOfKind ``Command.openSimple then
      let names := identifiersIter arg[0]
      let left := names.filter (!gone ·)
      if left == names then kept := kept.push raw
      else if !left.isEmpty then kept := kept.push ("open " ++ String.intercalate " " (left.map toString))
    else if !(identifiersIter arg).any gone then
      kept := kept.push raw
  return kept.toList

def renameUnitRefs (m : LeanMod) (renames : Std.HashMap QName QName) : LeanMod := Id.run do
  if renames.isEmpty then return m
  let src := renderLeanMod m
  let .ok (_, cmds) := parseEnvelope src m.imports | return m
  let mut pos : String.Pos.Raw := 0
  let mut out := ""
  for u in m.units, cmd in cmds.extract (1 + m.opens.length) (cmds.size - 1) do
    let members := if cmd.isOfKind ``Command.mutual then cmd[1].getArgs else #[cmd]
    for member in members do
      for token in freeRefTokensIter member[1] do
        let n := token.getId.replacePrefix `_root_ .anonymous
        let candidates := u.synRefs.filter (fun q => n.components.isSuffixOf q.toLeanName.components)
        let [ref] := candidates | continue
        let some target := renamedRef? renames ref | continue
        if target == ref then continue
        let some span := token.getRange? | continue
        if span.start < pos then continue
        out := out ++ pos.extract src span.start ++ (`_root_ ++ target.toLeanName).toString
        pos := span.stop
  if pos == 0 then return m
  let rewritten := out ++ pos.extract src src.rawEndPos
  return ((parseEnvelope rewritten m.imports).map Prod.fst).toOption.getD m

def relocateInterface (m : LeanMod) (name : QName) : Except String LeanMod := do
  let src := renderLeanMod m
  let (_, _, cmds) ← (sourceSyntax src).mapError toString
  let old := m.modName.toLeanName
  let fixed := m.imports.map (·.imod.toLeanName) |>.filter old.isPrefixOf
  parseLeanMod (renameSource src cmds old name.toLeanName fixed)

def requalify (fromMod toMod : QName) (m : LeanMod) : LeanMod := Id.run do
  if fromMod == toMod then return m
  let src := renderLeanMod m
  let .ok (_, hdr, cmds) := sourceSyntax src | return m
  let rename := fun s trees => renameSource s trees fromMod.toLeanName toMod.toLeanName
  let .ok renamed := parseLeanMod (rename src (#[hdr] ++ cmds)) | return m
  let children := m.imports.filterMap fun i => Id.run do
    if i.assumes.isEmpty then return none
    let iface := renderLeanMod ⟨i.imod, [], [], i.assumes⟩
    let .ok (_, h, cs) := sourceSyntax iface | return none
    let .ok child := parseLeanMod (rename iface (#[h] ++ cs)) | return none
    let renameQ := fun (q : QName) =>
      QName.ofName (q.toLeanName.replacePrefix fromMod.toLeanName toMod.toLeanName)
    return some { child with units := child.units.zipWith (fun fresh old =>
      { fresh with synRefs := old.synRefs.map renameQ }) i.assumes }
  return if children.isEmpty then renamed else withChildIfaces renamed children

def stubOf (spec : LeanMod) : LeanMod := spec

def withTests (impl spec : LeanMod) : LeanMod := Id.run do
  let spec := requalify spec.modName impl.modName spec
  let names := Std.HashSet.ofList (impl.units.flatMap (·.definedNames))
  let sources := Std.HashSet.ofList (impl.units.map (·.rawSource))
  let tests := spec.units.filter fun u => u.kind == .theoremDecl &&
    (if u.definedNames.isEmpty then !sources.contains u.rawSource else !names.contains u.uname)
  let joined := { impl with units := impl.units ++ tests }
  return ((parseEnvelope (renderLeanMod joined) impl.imports).map Prod.fst).toOption.getD joined

end Lojita.Kernel
