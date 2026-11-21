import Lean.Elab.Command
import Lean.Util.CollectAxioms
import AgdaMirror.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Zero-Axiom Kernel Gate (`#agda_prism_guard_axioms`)

Ensures translated Lean 4 modules stay strictly inside pure constructive
Martin-Löf Type Theory: zero `Classical.choice`, zero `propext`, zero
`Quot.sound`, zero `sorryAx`, and zero user `axiom` declarations.
-/

namespace AgdaMirror.AxiomGuard

open Lean Elab Command

/-- When the endpoints are known, a transparent auxiliary definition asks the
    kernel to check conversion once. Its exact type is available to subsequent
    elaboration, including when the surrounding program discards the proof. -/
elab "agda_refl%" : term <= expected => do
  let ty ← Lean.instantiateMVars expected
  let fallback := Term.elabTerm (mkIdent ``AgdaMirror.AgdaId.refl) (some expected)
  if ty.hasMVar then fallback else
    let_expr AgdaMirror.AgdaId α lhs rhs := ty | fallback
    let ctor := mkConst ``AgdaMirror.AgdaId.refl ty.getAppFn.constLevels!
    let proof := mkApp2 ctor α lhs
    if lhs == rhs then return proof
    Meta.mkAuxDefinition (← Term.mkAuxName `checkedRefl) ty proof

/-- The official frontend already decoded the Unicode scalars. Emit the literal
    list as a closed kernel expression without elaborating one list notation per byte. -/
elab "agda_chars%" s:str : term => return toExpr s.getString.toList

/-- Scoped naturals keep their Agda type even in a field whose expected type
    admits additional Lean numeric notation. -/
elab "agda_nat%" n:num : term => return mkNatLit n.getNat

/-- This internal term contains an ordinary syntax tree of closed constructor
    applications. Parameters and polymorphic constructors use normal elaboration.
    For monomorphic trees the kernel checks every application in one traversal. -/
private partial def groundExpr (env : Environment) (t : Syntax) : Option Expr := do
  if let `(agda_nat% $n:num) := t then return mkNatLit n.getNat
  let (head, args) := if t.isOfKind ``Lean.Parser.Term.app then (t[0],t[1].getArgs) else (t,#[])
  guard head.isIdent
  let n := head.getId
  let some (.ctorInfo info) := env.find? n | none
  guard (info.numParams == 0 && info.levelParams.isEmpty && info.numFields == args.size)
  return mkAppN (mkConst n) (← args.mapM (groundExpr env))

elab "agda_ground%" t:term : term <= expected => do
  let env ← getEnv
  if let some e := groundExpr env t.raw then
    match Kernel.check env {} e with
    | .ok _ => return e
    | .error ex => throwError "{ex.toMessageData (← getOptions)}"
  Term.elabTerm t (some expected)

elab "#agda_prism_guard_axioms" ids:ident* : command => do
  let env ← getEnv
  for idStx in ids do
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo idStx
    if !env.contains declName then
      throwErrorAt idStx s!"axiom-guard: declaration '{declName}' not found in environment"
    let axs ← liftCoreM <| Lean.collectAxioms declName
    if !axs.isEmpty then
      let axList := String.intercalate ", " (axs.toList.map toString)
      throwErrorAt idStx s!"axiom-guard: non-constructive or unsound axiom(s) [{axList}] detected in '{declName}'"

-- The authoritative refutation stub contributes named assumptions. Everything
-- else in the witness's type and body must have a kernel-checked definition.
elab "#agda_prism_guard_witness" witness:ident "assuming" "[" allowed:ident,* "]" : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo witness
  let env ← getEnv
  unless (env.find? declName).any (fun | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true | _ => false) do
    throwErrorAt witness "INDEPENDENCE_AXIOM_ERROR: {declName} requires a checked proof body"
  let assumptions ← allowed.getElems.mapM fun id => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    unless (env.find? name).any (fun | .axiomInfo _ => true | _ => false) do
      throwErrorAt id "INDEPENDENCE_AXIOM_ERROR: {name} is not a specification assumption"
    return name
  let deps ← Lean.collectAxioms declName
  let forbidden := #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  let dirty := deps.filter fun dep => forbidden.contains dep || !assumptions.contains dep
  unless dirty.isEmpty do
    throwErrorAt witness "INDEPENDENCE_AXIOM_ERROR: proof {declName} depends on disallowed axioms {dirty}. Use a constructive proof whose only assumptions are the staged SPECIFICATION postulates."

end AgdaMirror.AxiomGuard
