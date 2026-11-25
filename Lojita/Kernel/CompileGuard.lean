import Lean
import Lean.Compiler.LCNF.EmitC
import Lojita.Kernel.SafeCompare
import Lojita.Kernel.ElabGuard

namespace Lojita.Kernel
open Lean

inductive ExeMode where
  | cli | reactive
  deriving BEq, Repr

/-- Verify that `entry` is a public monomorphic constant in `snap` with exact `CliApp` or `ReactiveApp` type. -/
def checkEntryType (snap : Snapshot) (entry : Name) (mode : ExeMode) : MetaM Unit := do
  let info ← getConstInfo entry
  let caps ← Meta.mkFreshExprMVar (mkApp (mkConst ``List [.zero]) (mkConst `LojitaCtx.World.Cap))
  let wanted ← match mode with
    | .cli => pure <| mkApp (mkConst `LojitaCtx.World.CliApp) caps
    | .reactive => do
      let state ← Meta.mkFreshExprMVar (mkSort (.succ .zero))
      pure <| mkApp2 (mkConst `LojitaCtx.World.ReactiveApp) caps state
  unless snap.constants.contains entry && !isPrivateName entry && info.levelParams.isEmpty &&
      (← Meta.isDefEq info.type wanted) && !(← instantiateMVars wanted).hasMVar do
    throwError "ENTRY_TYPE_MISMATCH: {entry} has type {info.type}, expected {wanted}"

/-- Measure maximum single-function line span in an emitted `.c` file so oversized functions
    degrade automatically from `-O2` to `-O1 -fno-var-tracking-assignments` (T10). -/
def measureMaxCFunctionLines (cSrc : String) : Nat := Id.run do
  let mut inFunc := false
  let mut curLines := 0
  let mut maxLines := 0
  for line in cSrc.splitOn "\n" do
    if !inFunc then
      if line == "{" || line.endsWith ") {" then
        inFunc := true
        curLines := 1
    else
      curLines := curLines + 1
      if line == "}" then
        if curLines > maxLines then maxLines := curLines
        inFunc := false
        curLines := 0
  if curLines > maxLines then maxLines := curLines
  return maxLines

/-- Select safe C optimization flags based on `.c` byte size and single-function line count (T10).
    - `< 128 KiB` and max function `< 3000` lines → `-O2`
    - `≥ 128 KiB` or max function `≥ 3000` lines → `-O1 -fno-var-tracking-assignments` -/
def selectCcOptFlags (cSrc : String) : String × Array String :=
  let bytes := cSrc.utf8ByteSize
  let maxFn := measureMaxCFunctionLines cSrc
  if bytes < 131072 && maxFn < 3000 then
    ("-O2", #["-O2"])
  else
    ("-O1", #["-O1", "-fno-var-tracking-assignments"])

/-- Execute `cc` wrapped in `timeout -k 2 <timeoutSec>` so pathological C optimizer blowup
    can never hang the host process (T10). -/
def runCcBounded (args : Array String) (timeoutSec : Nat := 30) : IO Unit := do
  let fullArgs := #["-k", "2", toString timeoutSec, "cc"] ++ args
  let result ← IO.Process.output { cmd := "timeout", args := fullArgs }
  if result.exitCode == 124 || result.exitCode == 137 then
    let te : TabooError := {
      code   := .ccBlowup
      detail := s!"cc exceeded {timeoutSec}s wall-clock limit"
    }
    throw (IO.userError (toString te))
  unless result.exitCode == 0 do
    throw (IO.userError s!"NATIVE_BUILD_ERROR: cc ({result.exitCode})\n{result.stderr}{result.stdout}")

/-- Materialize deferred LCNF + IR declarations on an environment elaborated with `postponeCompile := true`,
    running inside a dedicated 64 MiB worker thread with bounded `codeGenOptions`, then emit C source. -/
def materializeAndEmitC (env : Environment) (outPath : System.FilePath) :
    IO (Environment × String × Nat) := do
  initKernelLimits
  let task ← IO.asTask (prio := .dedicated) do
    let ctx : Core.Context := {
      fileName := env.mainModule.toString
      fileMap  := default
      options  := codeGenOptions
      maxHeartbeats := Core.getMaxHeartbeats codeGenOptions
      maxRecDepth   := 4096
    }
    let groups := deferredCompileGroupsExt.getState env
    let action : CoreM String := do
      for grp in groups do
        Core.withCurrHeartbeats do
          runFullCompileDecls grp
      Core.withCurrHeartbeats do
        Compiler.LCNF.emitC (← getEnv).mainModule
    try
      let (cSrc, st) ← action.toIO ctx { env }
      IO.FS.writeFile outPath cSrc
      let (optTag, _) := selectCcOptFlags cSrc
      return (st.env, optTag, cSrc.utf8ByteSize)
    catch e =>
      let msg := toString e
      if msg.contains "deterministic timeout" || msg.contains "heartbeats" ||
         msg.contains "deep recursion" || msg.contains "maximum recursion depth" ||
         msg.contains "excessive memory" then
        let te : TabooError := { code := .lcnfCompileBlowup, detail := msg }
        throw (IO.userError (toString te))
      throw e
  IO.ofExcept (← IO.wait task)

/-- Compile `.c` files in bounded parallel batches using adaptive per-file optimization flags (`-O2` vs `-O1`). -/
def buildObjectsAdaptive (sources : Array System.FilePath) (timeoutSec : Nat := 30) :
    IO (Array (String × String)) := do
  let baseFlags := #[
    "-I", (toolchainRoot / "include").toString,
    "-ffp-contract=off",
    "-ffunction-sections",
    "-fdata-sections"
  ]
  let mut objects : Array (String × String) := #[]
  for first in [0:sources.size:4] do
    let mut jobs := #[]
    let batch := sources.extract first (min (first + 4) sources.size)
    for src in batch do
      let cText ← IO.FS.readFile src
      let (optTag, optFlags) := selectCcOptFlags cText
      let obj := (src.withExtension "o").toString
      let job ← IO.asTask (prio := .dedicated) do
        runCcBounded (optFlags ++ baseFlags ++ #["-c", src.toString, "-o", obj]) timeoutSec
      jobs := jobs.push (obj, optTag, job)
    for (obj, optTag, job) in jobs do
      IO.ofExcept (← IO.wait job)
      objects := objects.push (obj, optTag)
  return objects

/-- Safely compile and evaluate a closed pure `Nat` constant in-memory on a dedicated worker thread
    guarded by `setThreadStackSize(64MB)`, `setMaxMemory`, and `setRuntimeMaxHeartbeats` (Historical Repro H2). -/
def evalPureNatConstBounded (env : Environment) (declName : Name)
    (maxHeartbeatsK : Nat := 1000) : IO (Except TabooError Nat) := do
  let some info := env.checked.get.find? declName
    | return .error { code := .interpreterLimit, detail := s!"constant `{declName}` not found" }
  unless info.levelParams.isEmpty && info.type.isConstOf ``Nat do
    return .error { code := .interpreterLimit, detail := s!"constant `{declName}` does not have closed type `Nat`" }
  initKernelLimits
  -- Step 1: Compile IR on a dedicated worker thread with codeGenOptions
  let compileTask ← IO.asTask (prio := .dedicated) do
    let ctx : Core.Context := {
      fileName := env.mainModule.toString
      fileMap  := default
      options  := codeGenOptions
      maxHeartbeats := Core.getMaxHeartbeats codeGenOptions
      maxRecDepth   := 4096
    }
    let groups := deferredCompileGroupsExt.getState env
    let (_, st) ← (do
      for grp in groups do
        Core.withCurrHeartbeats (runFullCompileDecls grp)
      if groups.isEmpty then
        Core.withCurrHeartbeats (runFullCompileDecls #[declName])
    : CoreM Unit).toIO ctx { env }
    return st.env
  let compiledEnv ← match ← IO.wait compileTask with
    | .ok e => pure e
    | .error err =>
      return .error { code := .lcnfCompileBlowup, detail := toString err }
  -- Step 2: Run `evalConstCoreGuarded` on a dedicated 64 MiB worker thread so C++ `lean::throwable`
  -- (`stack_space_exception` / `memory_exception`) is caught and converted into `TabooError` cleanly!
  let evalOpts := codeGenOptions.set `maxHeartbeats maxHeartbeatsK
  runBoundedTask (maxHeartbeatsK * 1000).toUSize do
    let res := unsafe evalConstCoreGuarded Nat compiledEnv evalOpts declName
    match res with
    | .ok v    => return v
    | .error e => throw (IO.userError e)

end Lojita.Kernel
