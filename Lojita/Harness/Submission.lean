import Lojita.Transport.Plan

namespace Lojita.Harness
open Lojita.Kernel Lojita.Transport Lojita.Store

inductive Submission where
  | plan (proposed : Plan) (subspecs : List LeanMod)
  | contradiction (refute : LeanMod)
  | refuteLift (why : String) (refute : LeanMod)
  | countermodel (why : String) (model refute : LeanMod)

abbrev DraftStore := Std.HashMap String String

def extractBlocks (text : String) (drafts : DraftStore) : Except String (String × DraftStore) := do
  let mut env := #[]
  let mut sources := drafts
  let mut fence : Option (Option String) := none
  let mut attached : Std.HashSet String := {}
  let mut lines := #[]
  for line in text.splitOn "\n" do
    let words := (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    if let some name := fence then
      if words == ["```"] then
        if let some n := name then sources := sources.insert n (String.intercalate "\n" lines.toList)
        else env := env ++ lines
        fence := none
        lines := #[]
      else lines := lines.push line
    else
      match words with
      | ["```sexp"] => fence := some none
      | [lang,n] =>
        if lang == "```lean" || lang == "```agda" || lang == "```sexp" then
          if attached.contains n then throw s!"DUPLICATE_BLOCK: {n}"
          attached := attached.insert n
          fence := some (some n)
        else env := env.push line
      | _ => env := env.push line
  if fence.isSome then throw "UNCLOSED_FENCE"
  return (String.intercalate "\n" env.toList, sources)

def invalidSubmission : String :=
  "INVALID_SUBMISSION: expected one bare (submission ...) S-expression (or @draft holding one) with no surrounding prose"

/-- Look up `@name` (or a draft literally named `@name`). -/
def draftRef? (sources : DraftStore) (n : String) : Option String :=
  if n.startsWith "@" then sources[(n.drop 1).toString]? <|> sources[n]? else none

/-- The envelope of a reply that is either a bare S-expression or a single
    `@draft` holding one. Blocks fenced inside the draft are attached too. -/
def submissionEnvelope (text : String) (drafts : DraftStore) : Except String (SExpr × DraftStore) := do
  let (envelope, sources) ← extractBlocks text drafts
  let some e := SExpr.parseSExpr envelope | throw invalidSubmission
  let .sym n := e | return (e, sources)
  unless n.startsWith "@" do return (e, sources)
  let some content := draftRef? sources n | throw s!"UNRESOLVED_BLOCK: {n}"
  let (inner, sources) ← extractBlocks content sources
  let some e := SExpr.parseSExpr inner | throw invalidSubmission
  return (e, sources)

def parseSubmission (text : String) (drafts : DraftStore := {}) : Except String Submission := do
  let (envelope, sources) ← submissionEnvelope text drafts
  let .list (.sym "submission" :: fs) := envelope | throw invalidSubmission
  let mut fields : Std.HashMap String (List SExpr) := {}
  for f in fs do
    let .list (.sym k :: vs) := f | throw "INVALID_FIELD"
    if fields.contains k then throw s!"DUPLICATE_FIELD: {k}"
    fields := fields.insert k vs
  let value := fun (e : SExpr) => match e with
    | .str s => Except.ok s
    | .sym n => if n.startsWith "@" then
        match draftRef? sources n with
        | some s => .ok s
        | none => .error s!"UNRESOLVED_BLOCK: {n}"
      else .error "INVALID_SOURCE"
    | _ => .error "INVALID_SOURCE"
  let field := fun k => match fields[k]? with
    | some [e] => value e
    | _ => .error s!"INVALID_FIELD: {k}"
  let allowed := fun (names : List String) =>
    unless fields.toList.all (fun e => e.1 == "kind" || names.contains e.1) do throw "UNKNOWN_FIELD"
  let some [.sym kind] := fields["kind"]? | throw "INVALID_KIND"
  match kind with
  | "plan" =>
    allowed ["why", "main", "subspecs", "moves"]
    let why ← field "why"
    let m ← parseLeanMod (← field "main")
    let some moves := fields["moves"]? >>= (·.mapM decMove) | throw "INVALID_MOVES"
    let subs ← (fields["subspecs"]?.getD []).mapM fun e => do
      let .list [.str slot, src] := e | throw "INVALID_SUBSPEC"
      let sub ← parseLeanMod (← value src)
      unless slot == toString sub.modName || some slot == sub.modName.segments.getLast? do
        throw s!"SUBSPEC_SLOT_MISMATCH: {slot}"
      return sub
    return .plan ⟨why, some m.modName, some m, moves⟩ subs
  | "contradiction" =>
    allowed ["refute", "why"]
    return .contradiction (← parseLeanMod (← field "refute"))
  | "refute-lift" | "countermodel" =>
    allowed (["why", "refute", "witness"] ++ (if kind == "countermodel" then ["model"] else []))
    if fields.contains "refute" == fields.contains "witness" then throw "INVALID_WITNESS"
    let why ← if fields.contains "why" then field "why" else pure ""
    let r ← parseLeanMod (← field (if fields.contains "refute" then "refute" else "witness"))
    if kind == "refute-lift" then return .refuteLift why r
    return .countermodel why (← parseLeanMod (← field "model")) r
  | _ => throw s!"INVALID_KIND: {kind}"

end Lojita.Harness
