import Lean
import Prism.ExecGhost

/-! Type-directed adapters for the execution projection. Only `Thunk.mk`,
    `Thunk.get` and ordinary lambdas remain after elaboration. -/

namespace Prism.ExecPorts
open Lean Meta Elab Term

private def thunkDomain? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnf ty
  return if ty.isAppOfArity ``Thunk 1 then some ty.appArg! else none

private def delay (e : Expr) : MetaM Expr := do
  if e.isAppOfArity ``Thunk.get 2 then return e.appArg!
  let ty ← inferType e
  let u ← getDecLevel ty
  if e.isFVar || e.isLit || e.isConst then return mkApp2 (mkConst ``Thunk.pure [u]) ty e
  let fn := mkLambda `_ .default (mkConst ``Unit) (e.liftLooseBVars 0 1)
  return mkApp2 (mkConst ``Thunk.mk [u]) ty fn

/-- Higher-order calls to the mirror can demand a strict callback. Adapt
    remaining arrows after partial application, preserving each input's value. -/
private partial def adapt (e actual expected : Expr) : MetaM Expr := do
  if let some ty ← thunkDomain? actual then
    if (← thunkDomain? expected).isNone then
      return ← adapt (← mkAppM ``Thunk.get #[e]) ty expected
  if ← isDefEq actual expected then return e
  if let some ty ← thunkDomain? expected then
    return ← delay (← adapt e actual ty)
  let src ← whnf actual
  let dst ← whnf expected
  if src.isAppOfArity ``AgdaMirror.AgdaPair 2 && dst.isAppOfArity ``AgdaMirror.AgdaPair 2 then
    return ← withLetDecl `pair actual e fun pair => do
      let first ← mkAppM ``AgdaMirror.AgdaPair.proj₁ #[pair]
      let second ← mkAppM ``AgdaMirror.AgdaPair.proj₂ #[pair]
      let left ← adapt first src.getAppArgs[0]! dst.getAppArgs[0]!
      let right ← adapt second src.getAppArgs[1]! dst.getAppArgs[1]!
      mkLetFVars #[pair] (← mkAppM ``AgdaMirror.AgdaPair.mk #[left,right])
  let .forallE _ domain rest _ ← whnf actual | return e
  let .forallE name to_ target info ← whnf expected | return e
  withLocalDecl name info to_ fun x => do
    let arg ← adapt x to_ domain
    let body ← adapt (mkApp e arg) (rest.instantiate1 arg) (target.instantiate1 x)
    mkLambdaFVars #[x] body

syntax (name := execValue) "agda_exec_val% " term : term
syntax (name := execArgument) "agda_exec_arg% " term : term
syntax (name := execField) "agda_exec_field% " term : term
syntax (name := execBindingType) "agda_exec_binding_type% " term : term
syntax (name := execBinding) "agda_exec_binding% " term : term
syntax (name := execCallee) "agda_exec_head% " term : term
syntax (name := execTypedLambda) "agda_exec_fun% " "(" term ")" "(" term ")" : term

private partial def strictDomain (ty : Expr) : MetaM Expr := do
  if let some t ← thunkDomain? ty then return ← strictDomain t
  let t ← whnf ty
  if t.isAppOfArity ``AgdaMirror.AgdaPair 2 then
    let args ← t.getAppArgs.mapM strictDomain
    if args != t.getAppArgs then return mkAppN t.getAppFn args
  return ty

private partial def strictArrow (ty : Expr) (result := false) : MetaM Expr := do
  let .forallE n dom cod info ← whnf ty | do
    if result then return (← thunkDomain? ty).getD ty else return ty
  let outer ← strictDomain dom
  withLocalDecl n info outer fun x => do
    let arg ← if outer == dom then pure x else adapt x outer dom
    let rest ← strictArrow (cod.instantiate1 arg) true
    mkForallFVars #[x] rest

private partial def delayedArrow (ty : Expr) : MetaM Bool := do
  let .forallE n dom cod info ← whnf ty | return false
  if (← thunkDomain? dom).isSome then return true
  withLocalDecl n info dom fun x => delayedArrow (cod.instantiate1 x)

@[builtin_term_elab execCallee] def elabCallee : TermElab := fun stx _ => do
  let e ← elabTerm stx[1] none
  if (← thunkDomain? (← inferType e)).isSome then mkAppM ``Thunk.get #[e] else return e

@[builtin_term_elab execTypedLambda] def elabTypedLambda : TermElab := fun stx expected? => do
  if let some expected := expected? then
    if let .forallE _ dom .. ← whnf expected then
      if (← thunkDomain? dom).isSome then return ← elabTerm stx[5] expected?
  elabTerm stx[2] expected?

@[builtin_term_elab execValue] def elabValue : TermElab := fun stx expected? => do
  -- A polymorphic consumer (e.g. List.map) may not yet know its input
  -- type. Inferring that type from the worker's internal arrow would leak
  -- Thunk into the source-level signature.
  let hint? ← expected?.filterM fun ty => do
    let ty ← whnf ty
    return !ty.isForall && !ty.isMVar
  let input ← elabTerm stx[1] hint?
  let inputType ← inferType input
  let (e,ty) ← if let some ty ← thunkDomain? inputType then
    pure (← mkAppM ``Thunk.get #[input],ty)
  else pure (input,inputType)
  if let some expected := expected? then
    if ← delayedArrow expected then
      -- The same type parameter may occur in a delayed callback and in
      -- another argument, such as eqList's List A. Infer A from the source
      -- payload before adapting the worker's actual representation.
      if expected.hasExprMVar then
        let src ← strictArrow ty
        let dst ← strictArrow expected
        discard <| isDefEq src dst
      return ← adapt e ty expected
  let strict ← strictArrow ty
  let e ← if strict == ty then pure e else adapt e ty strict
  if let some expected := expected? then adapt e strict expected
  else return e

@[builtin_term_elab execArgument] def elabArgument : TermElab := fun stx expected? => do
  if let some expected := expected? then
    if let some dom ← thunkDomain? expected then
      let e ← elabTermEnsuringType stx[1] (some dom)
      return ← delay (← ExecGhost.eraseProof e)
  ExecGhost.eraseProof (← elabTerm stx[1] expected?)

/-- A pair literal can lack a type annotation. Infer its original payload,
    agreeing with the projection of the field's type even for erased proofs. -/
@[builtin_term_elab execField] def elabField : TermElab := fun stx expected? => do
  let hint ← expected?.mapM fun expected => do return (← thunkDomain? expected).getD expected
  let e ← elabTerm stx[1] hint
  if ← ExecGhost.erasedType (← inferType e) then ExecGhost.eraseProof e else delay e

/-- Nullary computations are shared across their demand sites. Function and IO
    values already have a runtime closure, and type and proof bindings retain
    their erased representation. This decision also works on inferred aliases. -/
private def shareBinding (ty : Expr) : MetaM Bool := do
  return !(← whnf ty).isForall && !(← ExecGhost.erasedType ty)

@[builtin_term_elab execBindingType] def elabBindingType : TermElab := fun stx _ => do
  let t ← elabType stx[1]
  if ← shareBinding t then return mkApp (mkConst ``Thunk [← getDecLevel t]) t else return t

@[builtin_term_elab execBinding] def elabBinding : TermElab := fun stx expected? => do
  let hint ← expected?.bindM fun ty => do
    if (← whnf ty).isMVar then return none
    return some ((← thunkDomain? ty).getD ty)
  let e ← elabTerm stx[1] hint
  if ← shareBinding (← inferType e) then delay e else ExecGhost.eraseProof e

end Prism.ExecPorts
