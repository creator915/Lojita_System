import Lean
import Lojita.Kernel.Boundary
import Lojita.Store.SExpr

namespace Lojita.Kernel
open Lean Parser
open Lojita.Store (SExpr)

inductive Obj where
  | unit (q : QName) | ext (q : QName) | flags | bot
  deriving BEq, Hashable, Repr, Inhabited

inductive UnitKind where
  | inductiveDecl | structureDecl | defDecl | abbrevDecl | theoremDecl | mutualDecl | axiomDecl
  deriving BEq, Repr, Inhabited

structure SynUnit where
  uname : QName
  definedNames : List QName
  kind : UnitKind
  rawSource : String
  sigSlice : String
  synRefs : List QName
  deriving BEq, Repr, Inhabited

structure ImportSpec where
  imod : QName
  assumes : List SynUnit := []
  deriving BEq, Repr, Inhabited

structure LeanMod where
  modName : QName
  imports : List ImportSpec
  opens : List String
  units : List SynUnit
  deriving BEq, Repr, Inhabited

/-- The build toolchain's location is a fallback for standalone native clients.
    Parsing never shells out to discover Lean or to process source. -/
def toolchainRoot : System.FilePath := ⟨by_elab return toExpr (← getBuildDir).toString⟩

/-- Lean's initializer registry is process-global, including when the pure
    parser and a resident driver are first used on different threads. -/
private initialize importLock : Std.Mutex Unit ← Std.Mutex.new ()

def withImportLock {α : Type} (action : IO α) : IO α := importLock.atomically do action

private initialize grammarCache : Std.Mutex (Option Environment) ← Std.Mutex.new none

private def grammar : IO Environment := grammarCache.atomically do
  if let some env ← get then return env
  let env ← withImportLock do
    let original ← searchPathRef.get
    try
      searchPathRef.set (← getBuiltinSearchPath toolchainRoot)
      unsafe enableInitializersExecution
      importModules #[{module := `Init}] {} (loadExts := true)
    finally searchPathRef.set original
  set (some env)
  return env

private def syntaxError (original : FileMap) (log : MessageLog) : IO SyntaxViolation := do
  let msg := log.toList.head!
  return ⟨"parseError", (original.ofPosition msg.pos).byteIdx, ← msg.toString⟩

/-- Lean parses LF input. Put syntax spans back on the original UTF-8 bytes
    before extracting, editing or reporting a range in a CRLF file. -/
private partial def originalSpans (normalized original : FileMap) (s : Syntax) : Syntax :=
  let pos := fun p => original.ofPosition (normalized.toPosition p)
  let sub := fun (v : Substring.Raw) => {v with
    str := original.source, startPos := pos v.startPos, stopPos := pos v.stopPos}
  let info := fun
    | .original l p t e => SourceInfo.original (sub l) (pos p) (sub t) (pos e)
    | .synthetic p e c => .synthetic (pos p) (pos e) c
    | .none => .none
  match s with
  | .missing => .missing
  | .node i k args => .node (info i) k (args.map (originalSpans normalized original))
  | .ident i raw n pre => .ident (info i) (sub raw) n pre
  | .atom i a => .atom (info i) a

private def parseSource (src : String) : IO (Except SyntaxViolation (Environment × Syntax × Array Syntax)) := do
  let env ← grammar
  let input := mkInputContext src "<object>"
  let crlf := src.contains "\r\n"
  let original := if crlf then src.toFileMap else input.fileMap
  let restore := fun s => if crlf then originalSpans input.fileMap original s else s
  let (header, initial, errors) ← parseHeader input
  if errors.hasErrors then return .error (← syntaxError original errors)
  let mut state := initial
  let mut cmds := #[]
  repeat
    let (cmd, next, log) := parseCommand input {env, options := {}} state {}
    let cmd := restore cmd
    if let .error v := scanSurface cmd then return .error v
    if log.hasErrors then return .error (← syntaxError original log)
    if cmd.isOfKind ``Lean.Parser.Command.eoi then break
    cmds := cmds.push cmd
    state := next
  return .ok (env, restore header.raw, cmds)

/-- The IO in Lean's header parser constructs an empty environment. The command
    grammar above is fixed to the installed prelude, independent of object imports. -/
private def sourceSyntax (src : String) : Except SyntaxViolation (Environment × Syntax × Array Syntax) :=
  match unsafe unsafeIO (parseSource src) with
  | .ok result => result
  | .error e => .error ⟨"parserEnvironment", 0, toString e⟩

private def slice (src : String) (s : Syntax) : String :=
  let stop := s.getTailInfo.getTrailingTailPos? |>.getD (s.getTailPos?.getD 0)
  ((s.getPos?.getD 0).extract src stop).trimAsciiEnd.copy

private partial def leaves (s : Syntax) : Array Syntax :=
  if s.isIdent || s matches .atom .. then #[s] else s.getArgs.flatMap leaves

private def kindOf (d : Syntax) : Option UnitKind := do
  match d.getKind with
  | ``Command.inductive => return .inductiveDecl
  | ``Command.structure => return .structureDecl
  | ``Command.definition => return .defDecl
  | ``Command.abbrev => return .abbrevDecl
  | ``Command.theorem | ``Command.example => return .theoremDecl
  | ``Command.axiom => return .axiomDecl
  | _ => none

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
  let members := if d.isOfKind ``Command.inductive then
      d[4].getArgs.toList.map (fun c => c[3].getId)
    else if d.isOfKind ``Command.structure then
      let ctor := d[4][1][0][1].getId
      (if ctor.isAnonymous then `mk else ctor) :: fieldsOf d
    else []
  return n :: members.map (n ++ ·)

private def headerTokens (cmd : Syntax) : List String := Id.run do
  let d := cmd[1]
  let head := if d.isOfKind ``Command.example then d.getArgs.extract 0 2
    else d.getArgs.extract 0 (if d.isOfKind ``Command.structure then 4 else 3)
  return (head.flatMap leaves).toList.map fun s =>
    if s.isIdent then s.getId.toString else s.getAtomVal

private partial def identifiers (s : Syntax) : List Name :=
  if s.isIdent then [s.getId] else s.getArgs.toList.flatMap identifiers

private def binderNames (s : Syntax) : List Name :=
  if s.isIdent then [s.getId]
  else if [``Term.explicitBinder, ``Term.implicitBinder, ``Term.strictImplicitBinder,
           ``Term.instBinder].contains s.getKind then identifiers s[1]
  else []

/-- Walk lexical binders before looking up module names. Unresolved tactic or
    pattern identifiers are hints only. The semantic graph uses kernel terms. -/
private partial def freeRefTokens (s : Syntax) (bound : List Name := []) : List Syntax := Id.run do
  if s.isIdent then return if bound.contains s.getId.getRoot then [] else [s]
  if s.isOfKind ``Command.declId || s.isOfKind ``Term.letId then return []
  let children := s.getArgs
  let walk := fun (cs : Array Syntax) names => cs.toList.flatMap (freeRefTokens · names)
  if s.isOfKind ``Term.basicFun || s.isOfKind ``Term.forall then
    let i := if s.isOfKind ``Term.basicFun then 0 else 1
    let binders := s[i].getArgs
    let declared := binders.toList.flatMap binderNames
    return walk (binders.filter (!·.isIdent)) bound ++ walk (children.extract (i+1) children.size) (declared ++ bound)
  if s.isOfKind ``Term.let then
    let decl := s[2][0]
    let names := if decl.isOfKind ``Term.letIdDecl then identifiers decl[0] else []
    return freeRefTokens decl bound ++ walk (children.extract 3 children.size) (names ++ bound)
  if s.isOfKind ``Term.explicitBinder || s.isOfKind ``Term.implicitBinder ||
     s.isOfKind ``Term.strictImplicitBinder then return walk (children.extract 2 children.size) bound
  if s.isOfKind ``Tactic.tacticSeq1Indented || s.isOfKind ``Tactic.tacticSeqBracketed then
    let seq := if s.isOfKind ``Tactic.tacticSeqBracketed then s[1] else s[0]
    let mut locals := bound
    let mut refs := #[]
    for tac in seq.getArgs do
      if tac.isOfKind ``Tactic.intro then locals := identifiers tac[1] ++ locals
      else refs := refs ++ (freeRefTokens tac locals).toArray
    return refs.toList
  if (kindOf s).isSome then
    let sig := if s.isOfKind ``Command.example then s[1] else s[2]
    let locals := sig[0].getArgs.toList.flatMap binderNames
    return walk children (locals ++ bound)
  if s.isOfKind ``Command.ctor then return freeRefTokens s[4] bound
  if s.isOfKind ``Command.structCtor then return freeRefTokens s[2] bound
  if s.isOfKind ``Command.structSimpleBinder then return walk (children.extract 2 children.size) bound
  if s.isOfKind ``Command.declSig || s.isOfKind ``Command.optDeclSig then
    return walk (s[0].getArgs.filter (!·.isIdent)) bound ++ freeRefTokens s[1] bound
  return walk children bound

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
    for token in freeRefTokens d do refs := refs.push (QName.ofName token.getId)
  let name := names[0]?.getD (QName.ofName (mod ++ Name.mkSimple s!"_example{idx}"))
  return ⟨name, names.toList, kind, slice src cmd, String.intercalate "\n" sigs.toList,
    refs.toList.eraseDups⟩

private def isAlias (cmd : Syntax) : Bool :=
  let d := cmd[1]
  cmd.isOfKind ``Command.declaration && d.isOfKind ``Command.abbrev &&
    d[2].getPos?.isNone && d[3][1].isIdent

private def openedNames (s : Syntax) : List OpenDecl := Id.run do
  if s.isOfKind ``Command.openSimple then
    return (identifiers s[0]).map (.simple · [])
  let ns := s[0].getId
  if s.isOfKind ``Command.openOnly then
    return (identifiers s[2]).map fun n => .explicit n (ns ++ n)
  if s.isOfKind ``Command.openHiding then return [.simple ns (identifiers s[2])]
  if s.isOfKind ``Command.openRenaming then
    return (s[2].getArgs.filter (·.isOfKind ``Command.openRenamingItem)).toList.map fun pair =>
      .explicit pair[2].getId (ns ++ pair[0].getId)
  return [] -- `open scoped` activates notation, without opening names.

private def qualifyRefs (env : Environment) (m : LeanMod) (opened : List OpenDecl)
    (aliases : List (Name × Name)) : LeanMod := Id.run do
  let locals := m.units.flatMap (·.definedNames) ++ aliases.map (fun a => QName.ofName (m.modName.toLeanName ++ a.1))
  let imported := m.imports.flatMap fun i => i.assumes.flatMap (·.definedNames)
  let known := NameSet.ofList ((locals ++ imported).map QName.toLeanName)
  let scopes := m.modName.toLeanName.components.foldl (fun (ps : List Name) p => (ps.head! ++ p) :: ps) [.anonymous]
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
    let resolved := candidates.filterMap fun name => inScope name <|> (if env.contains name then some name else none)
    if !resolved.isEmpty then return resolved.map QName.ofName
    if env.contains n || m.imports.any (fun i => i.imod.toLeanName.isPrefixOf n) then return [q]
    return q :: candidates.map QName.ofName
  return {m with units := m.units.map fun u =>
    {u with synRefs := (u.synRefs.flatMap resolve).eraseDups}}

private def parseEnvelope (src : String) (ifaces : List ImportSpec) (probe := false) :
    Except SyntaxViolation (LeanMod × Array Syntax) := do
  let (env, hdr, cmds) ← sourceSyntax src
  scanSurface hdr
  unless hdr[0].getArgs.isEmpty && hdr[1].getArgs.isEmpty do
    throw (violation "unsupportedHeader" hdr "expected ordinary imports")
  let interfaces := Std.HashMap.ofList (ifaces.map fun i => (i.imod,i.assumes))
  let imports ← hdr[2].getArgs.toList.mapM fun imp => do
    let q := QName.ofName imp[4].getId
    unless allowedImport q || (probe && q.toLeanName == `Lojita.Session.SessionEnv) do throw (violation "forbiddenImport" imp s!"{q}")
    let assumes := if q.toLeanName.getRoot == `LojitaCtx then [] else
      interfaces[q]?.getD []
    return {imod := q, assumes : ImportSpec}
  let first := cmds[0]?.getD .missing
  let last := cmds.back?.getD .missing
  unless first.isOfKind ``Command.namespace && last.isOfKind ``Command.end do
    throw (violation "namespaceEnvelope" first "expected namespace M ... end M")
  let name := first[1].getId
  let q := QName.ofName name
  unless ordinaryPath q do throw (violation "forbiddenNamespace" first s!"{q}")
  unless last[1][0].getId == name do throw (violation "namespaceEnvelope" last "mismatched end")
  let mut units := #[]
  let mut opens := #[]
  let mut opened := []
  let mut aliases := []
  for cmd in cmds.extract 1 (cmds.size - 1) do
    if cmd.isOfKind ``Command.open || (units.isEmpty && isAlias cmd) then
      unless units.isEmpty do throw (violation "namespaceEnvelope" cmd "open after declaration")
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

/-- Inspect the exact syntax that will be handed to the command elaborator. -/
def readEnvelope (src : String) := parseEnvelope src []

/-- The probe checker uses its own prelude. Ordinary object parsing always uses readEnvelope. -/
def readProbeEnvelope (src : String) := parseEnvelope src [] true

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
        for n in namesOf c[1] do out := out.push (QName.ofName (m.modName.toLeanName ++ n))
  return out.toList

private def qExpr (q : QName) : SExpr := .list (q.segments.map .str)

private def unitExpr (u : SynUnit) : SExpr := .list [qExpr u.uname,
  .list (u.definedNames.map qExpr), .num u.kind.ctorIdx, .str u.rawSource, .str u.sigSlice,
  .list (u.synRefs.map qExpr)]

def encodeCanonical (m : LeanMod) : String := SExpr.canonical <| .list [
  .sym "lean-mod-v1", qExpr m.modName,
  .list (m.imports.map fun i => .list [qExpr i.imod, .list (i.assumes.map unitExpr)]),
  .list (m.opens.map .str), .list (m.units.map unitExpr)]

private def listOf {α : Type} (f : SExpr → Option α) : SExpr → Option (List α)
  | .list xs => xs.mapM f
  | _ => none

private def asStr : SExpr → Option String | .str s => some s | _ => none
private def asQ (e : SExpr) : Option QName := QName.mk <$> listOf asStr e

private def asUnit : SExpr → Option SynUnit
  | .list [n, ns, .num k, .str raw, .str sig, refs] => do
    let kind ← [UnitKind.inductiveDecl, .structureDecl, .defDecl, .abbrevDecl,
      .theoremDecl, .mutualDecl, .axiomDecl][k]?
    return ⟨← asQ n, ← listOf asQ ns, kind, raw, sig, ← listOf asQ refs⟩
  | _ => none

def decodeCanonical (s : String) : Option LeanMod := do
  let .list [.sym "lean-mod-v1", n, imps, opens, units] ← SExpr.parseSExpr s | none
  let imports ← listOf (fun | .list [i, us] => return ⟨← asQ i, ← listOf asUnit us⟩
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
  for s in stxs.flatMap leaves do
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
  let ifaces := Std.HashMap.ofList (children.map fun c => (c.modName,c))
  let imports := m.imports.map fun i =>
    match ifaces[i.imod]? with
    | some child => {i with assumes := child.units}
    | none => i
  return ((parseEnvelope (renderLeanMod m) imports).map Prod.fst).toOption.getD m

/-- A move on a module or inductive also relocates its qualified members. -/
def renamedRef? (renames : Std.HashMap QName QName) (q : QName) : Option QName := Id.run do
  let n := q.toLeanName
  let mut owner := n
  while !owner.isAnonymous do
    if let some target := renames[QName.ofName owner]? then
      return some (QName.ofName (n.replacePrefix owner target.toLeanName))
    owner := owner.getPrefix
  return none

/-- Drop opens into removed child imports. Preserve the other namespaces in
    a multi-namespace open, including short child names resolved in this scope. -/
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
  let .ok (_,_,cmds) := sourceSyntax (renderLeanMod {m with units := []}) | return m.opens
  let mut kept := #[]
  for raw in m.opens, cmd in cmds.extract 1 (cmds.size - 1) do
    let arg := cmd[1]
    if arg.isOfKind ``Command.openSimple then
      let names := identifiers arg[0]
      let left := names.filter (!gone ·)
      if left == names then kept := kept.push raw
      else if !left.isEmpty then kept := kept.push ("open " ++ String.intercalate " " (left.map toString))
    else if !(identifiers arg).any gone then kept := kept.push raw
  return kept.toList

/-- Move free identifiers in surviving declarations. Resolve short spellings
    against the original unit's scoped reference hints and edit only token
    spans, so binders, comments, literals and declaration names stay intact. -/
def renameUnitRefs (m : LeanMod) (renames : Std.HashMap QName QName) : LeanMod := Id.run do
  if renames.isEmpty then return m
  let src := renderLeanMod m
  let .ok (_, cmds) := parseEnvelope src m.imports | return m
  let mut pos : String.Pos.Raw := 0
  let mut out := ""
  for u in m.units, cmd in cmds.extract (1 + m.opens.length) (cmds.size - 1) do
    let members := if cmd.isOfKind ``Command.mutual then cmd[1].getArgs else #[cmd]
    for member in members do
      for token in freeRefTokens member[1] do
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

/-- Give an interface its own nominal scope in a joint comparison environment.
    Imported children can be descendants of the old module path. Their already
    sealed names must continue to denote the same dependency snapshots. -/
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
    let renameQ := fun (q : QName) => QName.ofName (q.toLeanName.replacePrefix fromMod.toLeanName toMod.toLeanName)
    -- The parent stores child units without the child's opens. Their resolved
    -- references already used those opens when the interface was attached.
    return some {child with units := child.units.zipWith (fun fresh old =>
      {fresh with synRefs := old.synRefs.map renameQ}) i.assumes}
  return if children.isEmpty then renamed else withChildIfaces renamed children

/-- Specifications already express open obligations as Lean axioms. Keeping
    concrete carriers and proven laws verbatim preserves their reductions. -/
def stubOf (spec : LeanMod) : LeanMod := spec

def withTests (impl spec : LeanMod) : LeanMod := Id.run do
  let spec := requalify spec.modName impl.modName spec
  let names := Std.HashSet.ofList (impl.units.flatMap (·.definedNames))
  let sources := Std.HashSet.ofList (impl.units.map (·.rawSource))
  let tests := spec.units.filter fun u => u.kind == .theoremDecl &&
    (if u.definedNames.isEmpty then !sources.contains u.rawSource else !names.contains u.uname)
  let joined := {impl with units := impl.units ++ tests}
  return ((parseEnvelope (renderLeanMod joined) impl.imports).map Prod.fst).toOption.getD joined

end Lojita.Kernel
