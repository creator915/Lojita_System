import Lean.Parser.Module
import LojitaCtx.CharClass

namespace Lojita.Kernel

structure QName where
  segments : List String
  deriving BEq, Hashable, Inhabited, Repr

def QName.toLeanName (q : QName) : Lean.Name := q.segments.foldl Lean.Name.str .anonymous

def QName.ofName (n : Lean.Name) : QName :=
  ⟨n.components.map fun | .str _ s => s | .num _ i => toString i | .anonymous => ""⟩

def QName.dotName (q : QName) : String := q.toLeanName.toString

instance : ToString QName := ⟨QName.dotName⟩

def reservedPrefixes := ["Lojita", "Lean", "Lake", "System", "Std", "IO", "Test",
  "Verification", "Main", "UI", "Unsafe", "TrustMe"]

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
  code : String
  offset : Nat
  detail : String
  deriving Repr, Inhabited

instance : ToString SyntaxViolation where
  toString v := s!"{v.code}: byte {v.offset}: {v.detail}"

private def metaTokens := ["#eval", "#check", "#print", "#reduce", "#synth", "run_cmd",
  "elab", "elab_rules", "macro", "macro_rules", "syntax", "notation", "infix", "infixl",
  "infixr", "prefix", "postfix", "local", "attribute", "set_option", "run_tac", "by_elab",
  "eval%", "meta", "native_decide", "decreasing_by_elab"]

private def nativeAttrs := ["extern", "implemented_by", "csimp", "init", "builtin_init",
  "Pervasive", "export"]

def violation (code : String) (stx : Lean.Syntax) (detail : String) : SyntaxViolation :=
  ⟨code, (stx.getPos?.getD 0).byteIdx, detail⟩

/-- Inspect tokens in syntax context. Literal contents, docstrings and comments
    are never interpreted as command words or attributes. -/
partial def scanSurface (stx : Lean.Syntax) (inAttr := false) : Except SyntaxViolation Unit := do
  let inAttr := inAttr || stx.isOfKind ``Lean.Parser.Term.attributes
  let word := if stx.isIdent then stx.getId.toString else stx.getAtomVal
  let code? :=
    if ["sorry", "admit"].contains word then some "hasSorrySyntax"
    else if word == "unsafe" then some "forbiddenUnsafe"
    else if word == "noncomputable" then some "forbiddenNoncomputable"
    else if ["partial", "partial_fixpoint"].contains word then some "forbiddenPartial"
    else if ["initialize", "builtin_initialize"].contains word || (inAttr && nativeAttrs.contains word)
      then some "forbiddenNativeOverride"
    else if metaTokens.contains word then some "forbiddenMetaprogramming"
    else none
  if let some code := code? then throw (violation code stx word)
  for child in stx.getArgs do scanSurface child inAttr

end Lojita.Kernel
