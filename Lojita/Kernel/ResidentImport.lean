module
import all Lean.Environment
import all Lean.Shell
public import Lean.Environment

namespace Lojita.Kernel
open Lean

/-- Configure default stack size (in bytes) for newly spawned Lean worker threads (`lthread`). -/
public def setRuntimeThreadStackBytes (sz : USize) : IO Unit :=
  Lean.Internal.setThreadStackSize sz

/-- Configure C++ soft RSS cap (in bytes); checked every 200 `check_system` calls via `/proc/self/statm`. -/
public def setRuntimeMaxMemoryBytes (max : USize) : IO Unit :=
  Lean.Internal.setMaxMemory max

/-- Configure thread-local C++ runtime heartbeat cap (used e.g. by the bytecode interpreter). -/
public def setRuntimeMaxHeartbeats (max : USize) : IO Unit :=
  Lean.Internal.setMaxHeartbeat max

/-- Reset thread-local `check_system` heartbeat counter (`thread.cpp:g_heartbeat`) without
    disturbing `CoreM`'s allocator heartbeat counter (`object.cpp`). -/
@[extern "lojita_reset_runtime_heartbeat"]
public opaque resetRuntimeHeartbeats : IO Unit

/-- Wrapper around `lean_add_decl` (`Kernel.Environment.addDeclCore`) that resets `thread.cpp:g_heartbeat`
    immediately before entering `scope_max_heartbeat`, preventing cumulative thread heartbeat drift. -/
@[extern "lojita_add_decl_guarded"]
public opaque addDeclCoreFreshHb (env : Kernel.Environment) (maxHeartbeats : USize) (maxRecDepth : USize)
    (decl : @& Declaration) (cancelTk? : @& Option IO.CancelToken) :
    Except Kernel.Exception Kernel.Environment

/-- Exception-safe wrapper around `lean_eval_const` catching `lean::throwable` (`stack_space_exception` / `memory_exception`). -/
@[extern "lojita_eval_const_guarded"]
public unsafe opaque evalConstCoreGuarded (α : Type) (env : @& Environment) (opts : @& Options)
    (constName : @& Name) : Except String α

/-- Feed heap-resident module images into Lean 4.36's native importer.
    Heap images borrow the resident prelude's lifetime without owning an mmap region. -/
public def importResidentImages (s : ImportState) (images : Array (Name × ModuleData))
    (imports : Array Import) (opts : Options) : IO Environment := do
  let modules := s.moduleNames.filterMap (s.moduleNameMap[·]?)
  let regions := modules.flatMap (·.parts.map (·.2)) ++ modules.flatMap (·.irParts.map (·.2))
  let some lifetime := regions[0]? | throw (IO.userError "missing resident prelude")
  let mut state := s
  for (n, data) in images do
    if state.moduleNameMap.contains n then
      throw (IO.userError s!"DUPLICATE_MODULE: {n}")
    let m : ImportedModule := {
      module := n, hasData := true, importAll := true, isExported := false, irPhases := .all
      parts := #[(data, lifetime)], irParts := #[], needsIRTrans := false
    }
    state := ⟨state.moduleNameMap.insert n m, state.moduleNames.push n⟩
  let env ← finalizeImport state imports opts (trustLevel := 0) (leakEnv := false) (loadExts := true)
  let k := env.toKernelEnv
  return env.setCheckedSync { k with header := { k.header with regions } }

end Lojita.Kernel
