import Lojita.Kernel.KernelLimits
import Lean.Environment

namespace Lojita.Kernel
open Lean

/-- Resource bounds passed directly to `Lean.Kernel.Environment.addDeclCore` (`lean_add_decl`),
    which activates C++ `scope_max_heartbeat`, `scope_max_rec_depth`, `scope_cancel_tk`,
    and periodic `/proc/self/statm` `check_memory` checks.
    Direct calls to `Lean.Kernel.isDefEq`, `Lean.Kernel.whnf`, and `Lean.Kernel.check` are
    strictly banned across Lojita because their FFI wrappers leave those TLS guards at `0` (∞). -/
structure KernelLimitsConfig where
  maxHeartbeats : USize := 400000
  maxRecDepth   : USize := 2048
  cancelTk?     : Option IO.CancelToken := none
  deriving Inhabited

/-- Classify a C++ `Kernel.Exception` into a structured `TabooError` if it is a resource/taboo fault. -/
def classifyKernelException (ex : Kernel.Exception) (context : String) : Option TabooError :=
  match ex with
  | .deterministicTimeout =>
    some { code := .kernelTimeout, detail := s!"{context}: kernel exceeded deterministic maxHeartbeats" }
  | .deepRecursion =>
    some { code := .deepRecursion, detail := s!"{context}: kernel exceeded maxRecDepth" }
  | .excessiveMemory =>
    some { code := .excessiveMemory, detail := s!"{context}: kernel exceeded maxMemory RSS limit" }
  | .interrupted =>
    some { code := .kernelTimeout, detail := s!"{context}: kernel check cancelled/interrupted" }
  | _ => none

/-- Add a kernel declaration under all four C++ resource guards with a fresh zero-drift
    `check_system` heartbeat budget (`lean::reset_heartbeat()` + `scope_max_heartbeat`). -/
@[noinline] def addDeclGuarded (env : Kernel.Environment) (decl : Declaration)
    (cfg : KernelLimitsConfig := {}) : Except Kernel.Exception Kernel.Environment :=
  addDeclCoreFreshHb env cfg.maxHeartbeats cfg.maxRecDepth decl cfg.cancelTk?

/-- Verify that `ty` is a well-typed universe/type in `env` with only `levelParams` free. -/
def checkTypeWellFormed (env : Kernel.Environment) (levelParams : List Name) (ty : Expr)
    (cfg : KernelLimitsConfig := {}) : Except Kernel.Exception Unit := do
  if ty.hasMVar then
    throw (.other "expression contains metavariables")
  if ty.hasLevelParam && !(collectLevelParams {} ty).params.all levelParams.contains then
    throw (.other "expression contains undeclared universe level parameters")
  let decl : Declaration := .axiomDecl {
    name        := `_lojita_internal_wf_ty_chk
    levelParams := levelParams
    type        := ty
    isUnsafe    := false
  }
  discard <| addDeclGuarded env decl cfg

/-- Guarded check that both `actualType` and `expectedType` are well-formed types in `env`
    and `actualType ≡ expectedType` definitionally in the C++ kernel.
    Constructs `def _lojita_internal_ty_chk.{us} (x : actualType) : expectedType := x`
    and discards the resulting `Kernel.Environment`. -/
def checkTypesDefEq (env : Kernel.Environment) (levelParams : List Name)
    (actualType expectedType : Expr) (cfg : KernelLimitsConfig := {}) :
    Except Kernel.Exception Unit := do
  if actualType.hasMVar || expectedType.hasMVar then
    throw (.other "type contains metavariables")
  if (expectedType.hasLevelParam && !(collectLevelParams {} expectedType).params.all levelParams.contains) ||
     (actualType.hasLevelParam && !(collectLevelParams {} actualType).params.all levelParams.contains) then
    throw (.other "type contains undeclared universe level parameters")
  let decl : Declaration := .defnDecl {
    name        := `_lojita_internal_ty_chk
    levelParams := levelParams
    type        := .forallE `x actualType expectedType .default
    value       := .lam `x actualType (.bvar 0) .default
    hints       := .opaque
    safety      := .safe
  }
  discard <| addDeclGuarded env decl cfg

/-- Guarded check that `expectedVal` and `actualVal` both have type `ty : Sort u` in `env`
    and `expectedVal ≡ actualVal` definitionally in the C++ kernel.
    Constructs `theorem _lojita_internal_val_chk.{us} : @Eq.{u} ty expectedVal actualVal := @Eq.refl.{u} ty expectedVal`
    and discards the resulting `Kernel.Environment`.
    Note: C++ `check_theorem` verifies both `type` (`expectedVal : ty` and `actualVal : ty`) and
    `value` (`@Eq.refl.{u} ty expectedVal : @Eq.{u} ty expectedVal actualVal`, forcing `is_def_eq expectedVal actualVal`). -/
def checkValuesDefEq (env : Kernel.Environment) (levelParams : List Name)
    (u : Level) (ty expectedVal actualVal : Expr) (cfg : KernelLimitsConfig := {}) :
    Except Kernel.Exception Unit := do
  if ty.hasMVar || expectedVal.hasMVar || actualVal.hasMVar then
    throw (.other "value contains metavariables")
  for e in [ty, expectedVal, actualVal] do
    if e.hasLevelParam && !(collectLevelParams {} e).params.all levelParams.contains then
      throw (.other "value contains undeclared universe level parameters")
  let eqTy := mkApp3 (.const ``Eq [u]) ty expectedVal actualVal
  let refl := mkApp2 (.const ``Eq.refl [u]) ty expectedVal
  let decl : Declaration := .thmDecl {
    name        := `_lojita_internal_val_chk
    levelParams := levelParams
    type        := eqTy
    value       := refl
  }
  discard <| addDeclGuarded env decl cfg

/-- Run an IO/interpreter computation on a dedicated worker thread (`lthread` with 64 MiB stack
    from `initKernelLimits`) with a C++ thread-local heartbeat limit (`setRuntimeMaxHeartbeats`).
    Defends against non-tail-recursive bytecode interpreter blowups (Historical Repro H2). -/
def runBoundedTask {α : Type} (maxHeartbeats : USize := 200000) (act : IO α) : IO (Except TabooError α) := do
  initKernelLimits
  let task ← IO.asTask (prio := .dedicated) do
    resetRuntimeHeartbeats
    setRuntimeMaxHeartbeats maxHeartbeats
    try
      act
    finally
      setRuntimeMaxHeartbeats 0
  match ← IO.wait task with
  | .ok val => return .ok val
  | .error err =>
    let msg := toString err
    if msg.contains "deterministic timeout" || msg.contains "heartbeats" ||
       msg.contains "excessive memory" || msg.contains "deep recursion" ||
       msg.contains "stack space" then
      return .error { code := .interpreterLimit, detail := msg }
    else
      return .error { code := .interpreterLimit, detail := s!"bounded evaluation failed: {msg}" }

end Lojita.Kernel
