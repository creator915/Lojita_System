import Lean
import AgdaMirror.Core

/-! The checked mirror models intensional equality in Type. In an execution
image a proof can travel through Lean's proof-irrelevant Eq before returning to
the same indexed type. The C compiler drops the whole argument to agdaIdToEq
and agdaEqToId produces the scalar representation of the unique constructor. -/
namespace Prism.ExecGhost

open Lean Meta Elab Term

def erasedType (ty : Expr) : MetaM Bool := do
  let t ← whnf ty
  return t.isSort || t.isAppOfArity ``AgdaMirror.AgdaId 3 || (← isProp t)

/-- A user-defined Agda proposition is known after name resolution. Preserve
    its proof-irrelevant sort even in a field or argument marked non-strict. -/
syntax (name := deferredType) "agda_exec_defer% " term : term

@[builtin_term_elab deferredType] def elabDeferredType : TermElab := fun stx _ => do
  let t ← elabType stx[1]
  if ← erasedType t then return t
  elabType (← `(Thunk $(← exprToSyntax t)))

def eraseProof (e : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType e)
  unless ty.isAppOfArity ``AgdaMirror.AgdaId 3 do return e
  mkAppM ``AgdaMirror.agdaEqToId #[← mkAppM ``AgdaMirror.agdaIdToEq #[e]]

/-- Erase the implementation of a proof at every arity, including functions
whose proof would otherwise inspect a recursive or partial computation. -/
syntax (name := execProof) "agda_exec_proof% " term : term

@[builtin_term_elab execProof] def elabProof : TermElab := fun stx expected? => do
  let some expected := expected? | throwError "expected a proof signature"
  let value ← elabTermEnsuringType stx[1] expected
  forallTelescopeReducing expected fun args _ => do
    mkLambdaFVars args (← eraseProof (mkAppN value args))

end Prism.ExecGhost
