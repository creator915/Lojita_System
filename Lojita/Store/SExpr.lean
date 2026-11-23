import LojitaCtx.CharClass

namespace Lojita.Store

inductive SExpr where
  | sym (value : String)
  | str (value : String)
  | num (value : Nat)
  | list (children : List SExpr)
  deriving Inhabited

namespace SExpr

inductive Token where
  | lp | rp | invalid
  | tsym (value : String) | tstr (value : String) | tnum (value : Nat)
  deriving Inhabited, BEq

private inductive LexState where
  | between | atom (s : String) | quoted (s : String) | escaped (s : String)

/-- Decimal natural numbers in the wire grammar. -/
abbrev toNum (s : String) : Option Nat := s.toNat?

private def atomToken (s : String) : Token :=
  match toNum s with
  | some n => .tnum n
  | none => .tsym s

/-- A single forward UTF-8 traversal. Only the current token owns the text buffer. -/
def lex (s : String) : Array Token := Id.run do
  let mut state := LexState.between
  let mut tokens := #[]
  for c in s do
    match state with
    | .escaped text =>
      let some ch := ([('n', '\n'), ('r', '\r'), ('t', '\t'), ('"', '"'), ('\\', '\\')].lookup c)
        | return #[.invalid]
      state := .quoted (text.push ch)
    | .quoted text =>
      if c == '"' then
        tokens := tokens.push (.tstr text)
        state := .between
      else if c == '\\' then state := .escaped text
      else state := .quoted (text.push c)
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

abbrev tokenize := lex

def parseSExpr (s : String) : Option SExpr := do
  let mut siblings := []
  let mut parents := []
  for tok in tokenize s do
    match tok with
    | .lp =>
      parents := siblings :: parents
      siblings := []
    | .rp =>
      let parent :: rest := parents | none
      siblings := .list siblings.reverse :: parent
      parents := rest
    | .tsym v => siblings := .sym v :: siblings
    | .tstr v => siblings := .str v :: siblings
    | .tnum v => siblings := .num v :: siblings
    | .invalid => none
  let [root] := siblings | none
  guard parents.isEmpty
  return root

private def pushEscaped (out : String) (c : Char) : String :=
  match c with
  | '\n' => (out.push '\\').push 'n'
  | '\r' => (out.push '\\').push 'r'
  | '\t' => (out.push '\\').push 't'
  | '"' | '\\' => (out.push '\\').push c
  | _ => out.push c

def escape (s : String) : String := s.foldl pushEscaped ""

/-- Suspend both descent and return. The interpreter tail-calls the next step,
    even for a chain of singleton lists deeper than the native thread stack. -/
private inductive PrintStep where
  | done (out : String)
  | more (next : Unit → PrintStep)

private def PrintStep.run : PrintStep → String
  | .done out => out
  | .more next => (next ()).run
termination_by structural step => step

private abbrev Continue := String → PrintStep

mutual
  private def printExpr (e : SExpr) (out : String) (k : Continue) : PrintStep :=
    match e with
    | .sym s => .more fun _ => k (s.foldl String.push out)
    | .num n => .more fun _ => k ((toString n).foldl String.push out)
    | .str s => .more fun _ => k ((s.foldl pushEscaped (out.push '"')).push '"')
    | .list xs => .more fun _ => printChildren xs (out.push '(') k
  termination_by structural e

  private def printChildren (xs : List SExpr) (out : String) (k : Continue) : PrintStep :=
    match xs with
    | [] => .more fun _ => k (out.push ')')
    | x :: rest => .more fun _ => printExpr x out fun buf =>
        .more fun _ => printChildren rest (if rest.isEmpty then buf else buf.push ' ') k
  termination_by structural xs
end

def showSExpr (e : SExpr) : String := (printExpr e "" .done).run

abbrev canonical := showSExpr

end SExpr
end Lojita.Store
