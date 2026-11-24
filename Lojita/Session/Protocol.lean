import Lojita.Harness.Submission
import Lojita.Kernel.Driver

namespace Lojita.Session
open Lojita.Store Lojita.Harness Lojita.Kernel

inductive SessionAction where
  | runScript (why source : String)
  | driveTree (treeName why specSrc : String) (baseTrees : List String)
      (maybeLiftSrc maybeTransportSrc : Option String) (replaces : List String := [])
  | buildExe (mode : ExeMode) (why entry : String)
  | finish (summary : String)
  deriving BEq, Repr

inductive RefTarget where
  | local (bin : String)
  | docker (image bin : String)
  deriving BEq, Repr

structure RefSpec where
  target : RefTarget
  arguments : List String := []
  timeoutMs : Nat := 30000
  deriving BEq, Repr

abbrev Fields := Std.HashMap String (List SExpr)

private def fieldsOf (fs : List SExpr) : Except String Fields := do
  let mut out := {}
  for f in fs do
    let .list (.sym k :: vs) := f | throw "expected a named field"
    if out.contains k then throw s!"duplicate field {k}"
    out := out.insert k vs
  return out

private def onlyFields (fs : Fields) (allowed : List String) : Except String Unit := do
  for (k,_) in fs do
    unless allowed.contains k do throw s!"unexpected field {k}. Expected {allowed}"

def stringList (vs : List SExpr) : Except String (List String) := vs.mapM fun
  | .str s => pure s
  | _ => throw "expected a list of quoted strings"

def sourceValue (drafts : DraftStore) : SExpr → Except String String
  | .str s => if s.startsWith "@" && !s.any Char.isWhitespace then
      .error s!"quoted draft reference {s}. Write bare {s} without quotes" else .ok s
  | .sym n => do
    unless n.startsWith "@" do throw "expected source text or @draft"
    let some src := drafts[(n.drop 1).toString]? | throw s!"unresolved {n}. Available drafts: {drafts.toList.map Prod.fst}"
    return src
  | _ => .error "expected source text or @draft"

def parseMode : String → Except String ExeMode
  | "cli" => .ok .cli
  | "reactive" => .ok .reactive
  | other => .error s!"unknown executable mode {other}"

def parseSessionAction (text : String) (drafts : DraftStore := {}) : Except String SessionAction := do
  let (env, sources) ← extractBlocks text drafts
  let some (.list (.sym "session-action" :: xs)) := SExpr.parseSExpr env |
    throw "expected one (session-action ...) envelope. Check matching fences and remove prose"
  let fs ← fieldsOf xs
  let field := fun k => match fs[k]? with
    | some [v] => sourceValue sources v
    | _ => .error s!"missing or malformed {k}"
  let optional := fun k => match fs[k]? with
    | none | some [.sym "nothing"] => pure none
    | some [.list [.sym "just", v]] => some <$> sourceValue sources v
    | _ => .error s!"{k} expects nothing or (just @name)"
  match fs["kind"]? with
  | some [.sym "run-script"] =>
    onlyFields fs ["kind","why","source"]
    return .runScript (← field "why") (← field "source")
  | some [.sym "drive-tree"] =>
    onlyFields fs ["kind","why","treeName","specSrc","baseTrees","maybeLiftSrc","maybeTransportSrc","replaces"]
    let some bases := fs["baseTrees"]? | throw "missing baseTrees"
    return .driveTree (← field "treeName") (← field "why") (← field "specSrc") (← stringList bases)
      (← optional "maybeLiftSrc") (← optional "maybeTransportSrc") (← stringList (fs["replaces"]?.getD []))
  | some [.sym "build-exe"] =>
    if fs.contains "source" then throw "build-exe accepts only a sealed entry. Remove the legacy (source ...) field"
    onlyFields fs ["kind","why","entry","mode"]
    let mode ← match fs["mode"]? with
      | none => pure .cli
      | some [.sym s] | some [.str s] => parseMode s
      | _ => throw "expected (mode cli) or (mode reactive)"
    return .buildExe mode (← field "why") (← field "entry")
  | some [.sym "finish"] =>
    onlyFields fs ["kind","summary"]
    return .finish (← field "summary")
  | _ => throw "expected kind run-script, drive-tree, build-exe or finish"

def explainSessionActionFailure (text : String) (drafts : DraftStore := {}) : String :=
  match parseSessionAction text drafts with
  | .ok _ => ""
  | .error e => s!"session-action: {e}"

def parseRefSpec (text : String) : Except String RefSpec := do
  let some (.list (.sym "ref-target" :: t :: xs)) := SExpr.parseSExpr text | throw "expected (ref-target ...)"
  let target ← match t with
    | .list [.sym "local", .str bin] => pure (.local bin)
    | .list [.sym "docker", .str img, .str bin] => pure (.docker img bin)
    | _ => throw "expected (local \"bin\") or (docker \"image\" \"bin\")"
  let fs ← fieldsOf xs
  onlyFields fs ["args","timeoutMs"]
  let timeoutMs ← match fs["timeoutMs"]? with
    | none => pure 30000
    | some [.num n] => pure n
    | _ => throw "timeoutMs expects a natural number"
  return ⟨target, ← stringList (fs["args"]?.getD []), timeoutMs⟩

def encodeRefSpec (r : RefSpec) : SExpr :=
  let target := match r.target with
    | .local b => SExpr.list [.sym "local", .str b]
    | .docker i b => .list [.sym "docker", .str i, .str b]
  .list [.sym "ref-target", target, .list (.sym "args" :: r.arguments.map .str), .list [.sym "timeoutMs", .num r.timeoutMs]]

def readReference (path : System.FilePath) : IO RefSpec := do
  let ref ← IO.ofExcept (parseRefSpec (← IO.FS.readFile path))
  if let .local bin := ref.target then
    let p ← IO.FS.realPath ((path.parent.getD ".") / bin)
    return {ref with target := .local p.toString}
  return ref

end Lojita.Session
