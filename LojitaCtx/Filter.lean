import LojitaCtx.Blueprint
namespace LojitaCtx.Filter
open Blueprint
inductive Mode : Type where
  | sensitive   : Mode
  | insensitive : Mode

inductive Kind : Type where
  | prefix  : Kind
  | suffix  : Kind
  | exclude : Kind

structure Signal : Type where
  signal ::
  kind   : Kind
  exactMatch : Thunk Bool
  foldedMatch : Thunk Bool

def Signal.exact (s : Signal) := s.exactMatch.get
def Signal.folded (s : Signal) := s.foldedMatch.get

structure Input : Type where
  input ::
  operation : Kind
  needle    : String
  text      : String

def starts : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, c :: cs => p == c && starts ps cs
termination_by structural ps _ => ps

def contains : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | ps, c :: cs => starts ps (c :: cs) || contains ps cs
termination_by structural _ cs => cs

def hit : Kind → List Char → List Char → Bool
  | .prefix,  p, s => starts p s
  | .suffix,  p, s => starts (List.reverse p) (List.reverse s)
  | .exclude, p, s => contains p s

def classify : Input → Signal
  | .input k p s =>
    .signal k (Thunk.mk fun _ => hit k p.toList s.toList)
      (Thunk.mk fun _ => hit k (p.toList.map Char.toLower) (s.toList.map Char.toLower))

def choose : Mode → Signal → Bool
  | .sensitive,   s => s.exact
  | .insensitive, s => s.folded

def combine : Kind → Bool → Bool
  | .prefix,  b => b
  | .suffix,  b => b
  | .exclude, b => Bool.not b

def expected0 (mode : Mode) (s : Signal) : Bool :=
  combine s.kind (choose mode s)

def expected1 (mode : Mode) (i : Input) : Bool :=
  expected0 mode (classify i)

def inputPort : PortLift Signal Input :=
  PortLift.mk classify

theorem classifyCommutes (mode : Mode) :
    Commutes₁ inputPort (keepPort Bool) (fun _ => True) Eq (expected0 mode) (expected1 mode) :=
  fun _ _ => rfl

end LojitaCtx.Filter
