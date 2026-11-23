import Lojita.Transport.Plan

namespace Lojita.Store
open Lojita.Kernel Lojita.Transport

abbrev Hash := String
def validHash (s : Hash) := s.utf8ByteSize == 64 && s.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

inductive Form where
  | quoted (s : String)
  | tagged (tag : String) (fields : List Form)

mutual
  def Form.toExpr (f : Form) : SExpr :=
    match f with
    | .quoted s => .str s
    | .tagged t fs => .list (.sym t :: fieldsExpr fs)
  termination_by structural f
  private def fieldsExpr (fs : List Form) : List SExpr :=
    match fs with | [] => [] | f :: xs => f.toExpr :: fieldsExpr xs
  termination_by structural fs
end

mutual
  def Form.ofExpr (e : SExpr) : Option Form :=
    match e with
    | .str s => some (.quoted s)
    | .list (.sym t :: fs) => .tagged t <$> readFields fs
    | _ => none
  termination_by structural e
  private def readFields (fs : List SExpr) : Option (List Form) :=
    match fs with | [] => some [] | f :: xs => return (← Form.ofExpr f) :: (← readFields xs)
  termination_by structural fs
end

structure HomeNodeObj where
  codeHash : Hash
  specHash : Hash
  memHash : Hash
  kids : List (String × Hash)
  /-- Pin a distinct specification header when its imports or opens differ from the implementation. -/
  specScope : Option Hash := none
  deriving BEq, Repr, Inhabited

structure Commit where
  parents : List Hash
  rootHome : Hash
  epoch : String
  why : String
  presentation : Option Hash := none
  deriving BEq, Repr, Inhabited

private def hashField : Form → Option Hash
  | .quoted h => if validHash h then some h else none
  | _ => none

def homeForm (h : HomeNodeObj) : Form :=
  let kids := h.kids.mergeSort (fun a b => decide (a.1 ≤ b.1))
  .tagged "home" ([.quoted h.codeHash, .quoted h.specHash, .quoted h.memHash] ++
    h.specScope.toList.map (fun k => .tagged "scope" [.quoted k]) ++
    kids.map fun (n,k) => .tagged "kid" [.quoted n, .quoted k])

def readHomeForm : Form → Option HomeNodeObj
  | .tagged "home" (c :: s :: m :: rest) => do
    let (scope, fields) ← match rest with
      | .tagged "scope" [k] :: ks => (hashField k).map (fun key => (some key, ks))
      | ks => some (none,ks)
    let mut kids := #[]
    let mut prev := none
    for f in fields do
      let .tagged "kid" [.quoted n, k] := f | none
      guard (!n.isEmpty && prev.all (· < n))
      prev := some n
      kids := kids.push (n, ← hashField k)
    return ⟨← hashField c, ← hashField s, ← hashField m, kids.toList, scope⟩
  | _ => none

def commitForm (c : Commit) : Form :=
  .tagged "commit" ([.tagged "parents" (c.parents.map .quoted), .quoted c.rootHome,
    .quoted c.epoch, .quoted c.why] ++ c.presentation.toList.map (fun h => .tagged "presentation" [.quoted h]))

def readCommitForm : Form → Option Commit
  | .tagged "commit" (.tagged "parents" ps :: root :: .quoted epoch :: .quoted why :: rest) => do
    let view ← match rest with | [] => some none | [.tagged "presentation" [h]] => some <$> hashField h | _ => none
    return ⟨← ps.mapM hashField, ← hashField root, epoch, why, view⟩
  | _ => none

inductive Kind where
  | code | iface | mem | home | commit
  deriving BEq, Repr, Inhabited

def Kind.dir : Kind → String | .code => "code" | .iface => "iface" | .mem => "mem" | .home => "home" | .commit => "commit"

abbrev Payload : Kind → Type | .code => LeanMod | .iface => List SynUnit | .mem => Memory | .home => HomeNodeObj | .commit => Commit

def encodeObject : (k : Kind) → Payload k → String
  | .code, m => encodeCanonical m
  | .iface, us => (encodeIface us).canonical
  | .mem, m => (encodeMemory m).canonical
  | .home, h => (homeForm h).toExpr.canonical
  | .commit, c => (commitForm c).toExpr.canonical

def decodeObject (k : Kind) (s : String) : Option (Payload k) := do
  let read : (k : Kind) → Option (Payload k)
    | .code => decodeCanonical s
    | .iface => SExpr.parseSExpr s >>= decodeIface
    | .mem => SExpr.parseSExpr s >>= decodeMemory
    | .home => SExpr.parseSExpr s >>= Form.ofExpr >>= readHomeForm
    | .commit => SExpr.parseSExpr s >>= Form.ofExpr >>= readCommitForm
  let a ← read k
  guard (encodeObject k a == s)
  return a

end Lojita.Store
