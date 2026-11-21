import Prism.TranscodeChk

/-! Execution views of guarded records. Each copattern has its own match under
the field's thunk, so observing one field never inspects another field's inputs. -/
namespace Prism.ExecRecords

open Lean (TSyntax Term mkIdent)
open Lean.Parser.Term
open Lean.Parser.Command (declId)
open Chk

def projections (ctx : EmitCtx) (u : ModUnit) : PrismOutcome (Array Cmd) := do
  let .recUnit n params _ _ rd fs := u.kind | return #[]
  unless rd.coind do return #[]
  let scope := ctx.modPrefix ++ [n]
  if hasDependentRecordFields scope fs then
    .bot s!"dependent coinductive projection in {n}"
  let binders ← telescope ctx [] (params.map fun (.bind _ xs ty) => .bind .hidden xs ty)
  let record ← reference ctx (mkQ scope)
  let args := (params.flatMap fun (.bind _ xs _) => xs.map (fun x => (varId x : Term))).toArray
  let target ← `(@$record $args*)
  fs.toArray.mapM fun (field, ty) => do
    let proj ← declName ctx (leanMangleIdent n ++ "." ++ leanMangleIdent field)
    let raw := mkIdent ((leanModNamespace ctx.modPrefix).toName.str (leanMangleIdent n) |>.str ("_thunk_" ++ leanMangleIdent field))
    let result ← expr ctx [] ty
    `(def $proj:declId $binders:bracketedBinder* (self : $target) : $result := agda_exec_val% ($raw self))

private structure ProjectionClause where
  field : String
  hidden : List (Arg Pat)
  visible : List (Arg Pat)
  body : Expr

def copatternBody (ctx : EmitCtx) (lvls slots : List String) (ty : Expr) (cs : List Clause) :
    PrismOutcome Term := do
  let some record := resultHeadCanon ty >>= fun r => ctx.recMeta.find? (·.recCanon == r)
    | .bot "copattern result must be a known record"
  let fieldNames := record.fields.map Prod.fst
  let clauses ← cs.mapM fun c => do
    let .clause (.proj q (.head _ ps) []) (.rhs body) [] := c
      | .bot "unsupported nested copattern"
    let field := q.full.getLastD ""
    unless q.full.dropLast == record.recCanon && fieldNames.contains field do
      .bot s!"unexpected copattern projection {fullDot q}"
    let (hp,vp) := ps.span (·.hid != .visible)
    if vp.any (·.hid != .visible) then .bot "interleaved hidden copattern argument"
    return ({field, hidden := hp, visible := vp, body} : ProjectionClause)
  let some first := clauses.head? | .bot "missing copattern clauses"
  let arity := first.visible.length
  unless clauses.all (·.visible.length == arity) do .bot "inconsistent copattern arity"
  let vars := (List.range arity).toArray.map (fun i => ident s!"prismCopatternArg{i}")
  let discrs ← vars.mapM fun v => `(matchDiscr| $v:ident)
  let vals ← fieldNames.mapM fun f => do
    let alternatives := clauses.filter (·.field == f)
    let some firstAlt := alternatives.head? | .bot s!"missing copattern for field {f}"
    let body (c : ProjectionClause) := do aliasLets slots c.hidden (← expr ctx lvls c.body)
    if vars.isEmpty then
      unless alternatives.length == 1 do .bot s!"overlapping nullary copatterns for {f}"
      return (f, ← body firstAlt)
    let arms ← alternatives.toArray.mapM fun alt => do
      let used := collectVarsExpr alt.body
      let pats ← alt.visible.toArray.mapM fun p => pattern ctx (wildcardUnusedPat used p.thing)
      `(matchAltExpr| | $pats:term,* => $(← body alt))
    return (f, ← `(match $discrs:matchDiscr,* with $arms:matchAlt*))
  let fs ← fields ctx vals
  let result ← `({ $fs:structInstField,* })
  if vars.isEmpty then return result
  `(fun $vars:ident* => $result)

end Prism.ExecRecords
