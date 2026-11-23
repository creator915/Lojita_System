module
import all Lean.Environment
public import Lean.Environment

namespace Lojita.Kernel
open Lean

/-- Feed heap-resident module images to the same importer that loads oleans.
    Lean 4.36 pairs every import part with a region. For a heap image borrow
    the resident prelude's lifetime and retain only the original region table
    in the resulting environment. No heap image owns a mapped region. -/
public def importResidentImages (s : ImportState) (images : Array (Name × ModuleData))
    (imports : Array Import) (opts : Options) : IO Environment := do
  let modules := s.moduleNames.filterMap (s.moduleNameMap[·]?)
  let regions := modules.flatMap (·.parts.map (·.2)) ++ modules.flatMap (·.irParts.map (·.2))
  let some lifetime := regions[0]? | throw (IO.userError "missing resident prelude")
  let mut state := s
  for (n,data) in images do
    if state.moduleNameMap.contains n then throw (IO.userError s!"DUPLICATE_MODULE: {n}")
    let m : ImportedModule := {
      module := n, hasData := true, importAll := true, isExported := false, irPhases := .all
      parts := #[(data, lifetime)], irParts := #[], needsIRTrans := false }
    state := ⟨state.moduleNameMap.insert n m, state.moduleNames.push n⟩
  let env ← finalizeImport state imports opts (trustLevel := 0) (leakEnv := false) (loadExts := true)
  let k := env.toKernelEnv
  return env.setCheckedSync {k with header := {k.header with regions}}

end Lojita.Kernel
