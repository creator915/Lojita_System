module
public import Lean.Environment
import Lean.Compiler.Old
import all Lean.Util.CollectAxioms

namespace Prism

/-- Compute one complete root's footprint. The caller only caches results of
    entire traversals in this environment. A back edge into an inductive or
    mutual declaration can leave intermediate entries of Lean's DFS incomplete,
    so each new root gets a fresh traversal state. -/
public def collectRootAxioms (env : Lean.Environment) (complete : Lean.NameMap (Array Lean.Name))
    (root : Lean.Name) (base? : Option Lean.Environment := none) : Array Lean.Name :=
  -- A serialized snapshot's own exported table can also contain partial results
  -- for a cycle. Only reuse library entries from the immutable mirror imports.
  let library : Lean.Name → Option (Array Lean.Name) := match base? with
    | some base => (Lean.exportedAxiomsExt.getState (asyncMode := .mainOnly) base).find? base
    | none => fun _ => none
  -- A partial function's public constant can have an empty axiom footprint.
  -- Its implementation is recorded separately. Inspect intermediate constants
  -- as well as the root so a total alias cannot hide the partial definition.
  let lookup _ name := complete.find? name <|> library name <|>
    if (env.find? (Lean.Compiler.mkUnsafeRecName name)).any Lean.ConstantInfo.isPartial
    then some #[`unsafePrimAx] else none
  Lean.CollectAxioms.runM (env.setExporting false) <| Lean.CollectAxioms.collectAndGet lookup root

end Prism
