import LojitaCtx.CharClass

namespace Lojita.Store

inductive SExpr where
  | sym (value : String)
  | str (value : String)
  | num (value : Nat)
  | list (children : List SExpr)
  deriving Inhabited, BEq, Repr

namespace SExpr

inductive Token where
  | lp | rp | invalid
  | tsym (value : String) | tstr (value : String) | tnum (value : Nat)
  deriving Inhabited, BEq

private inductive LexState where
  | between | atom (s : String) | quoted (s : String) | escaped (s : String)

private def atomToken (s : String) : Token :=
  match s.toNat? with
  | some n => .tnum n
  | none => .tsym s

/-- Single-pass forward UTF-8 lexer with zero recursion. -/
def lex (s : String) : Array Token := Id.run do
  let mut state := LexState.between
  let mut tokens := #[]
  for c in s do
    match state with
    | .escaped text =>
      let ch? : Option Char :=
        match c with
        | 'n' => some '\n' | 'r' => some '\r' | 't' => some '\t'
        | '"' => some '"'  | '\\' => some '\\' | _ => none
      let some ch := ch? | return #[.invalid]
      state := .quoted (text.push ch)
    | .quoted text =>
      if c == '"' then
        tokens := tokens.push (.tstr text)
        state := .between
      else if c == '\\' then
        state := .escaped text
      else
        state := .quoted (text.push c)
    | .between | .atom _ =>
      if LojitaCtx.CharClass.space c || c == '(' || c == ')' || c == '"' then
        if let .atom text := state then tokens := tokens.push (atomToken text)
        state := if c == '"' then .quoted "" else .between
        if c == '(' then tokens := tokens.push .lp
        if c == ')' then tokens := tokens.push .rp
      else
        let text := match state with | .atom text => text | _ => ""
        state := .atom (text.push c)
  match state with
  | .between => return tokens
  | .atom text => return tokens.push (atomToken text)
  | _ => return #[.invalid]

/-- Explicit-stack iterative S-expression parser (safe for arbitrary nesting depth). -/
def parseSExpr (s : String) : Option SExpr := do
  let mut siblings : Array SExpr := #[]
  let mut parents : Array (Array SExpr) := #[]
  for tok in lex s do
    match tok with
    | .lp =>
      parents := parents.push siblings
      siblings := #[]
    | .rp =>
      if parents.isEmpty then none
      let parent := parents.back!
      parents := parents.pop
      siblings := parent.push (.list siblings.toList)
    | .tsym v => siblings := siblings.push (.sym v)
    | .tstr v => siblings := siblings.push (.str v)
    | .tnum v => siblings := siblings.push (.num v)
    | .invalid => none
  guard (parents.isEmpty && siblings.size == 1)
  return siblings[0]!

private def pushEscaped (out : String) (c : Char) : String :=
  match c with
  | '\n' => (out.push '\\').push 'n'
  | '\r' => (out.push '\\').push 'r'
  | '\t' => (out.push '\\').push 't'
  | '"' | '\\' => (out.push '\\').push c
  | _ => out.push c

def escape (s : String) : String := s.foldl pushEscaped ""

private inductive EmitFrame where
  | node (e : SExpr)
  | space
  | closeParen
  deriving Inhabited

/-- Explicit-stack iterative S-expression printer (zero call-stack recursion). -/
def showSExpr (root : SExpr) : String := Id.run do
  let mut out := ""
  let mut stack : Array EmitFrame := #[.node root]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .space => out := out.push ' '
    | .closeParen => out := out.push ')'
    | .node (.sym s) => out := out ++ s
    | .node (.num n) => out := out ++ toString n
    | .node (.str s) => out := (s.foldl pushEscaped (out.push '"')).push '"'
    | .node (.list xs) =>
      out := out.push '('
      stack := stack.push .closeParen
      let arr := xs.toArray
      let mut i := arr.size
      while i > 0 do
        i := i - 1
        stack := stack.push (.node arr[i]!)
        if i > 0 then
          stack := stack.push .space
  return out

abbrev canonical := showSExpr

end SExpr
end Lojita.Store
