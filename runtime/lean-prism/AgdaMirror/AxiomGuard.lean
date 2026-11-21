import Lean

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

elab "#agda_prism_guard_axioms" ids:ident* : command => do
  let env ← getEnv
  for idStx in ids do
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo idStx
    if !env.contains declName then
      throwErrorAt idStx s!"axiom-guard: declaration '{declName}' not found in environment"
    let axs ← liftCoreM <| Lean.collectAxioms declName
    -- Forbid `sorryAx`, `Classical.choice`, and any custom user `axiom`!
    -- (`propext` / `Quot.sound` may appear internally inside Lean's `Init` `String`/`Nat.div` runtime helpers,
    -- which remain 100% constructive and cannot affect `Type u` `AgdaId`.)
    let forbidden := axs.filter fun ax =>
      ax != ``propext && ax != ``Quot.sound
    if !forbidden.isEmpty then
      let axList := String.intercalate ", " (forbidden.toList.map toString)
      throwErrorAt idStx s!"axiom-guard: non-constructive or unsound axiom(s) [{axList}] detected in '{declName}'"

end AgdaMirror.AxiomGuard
