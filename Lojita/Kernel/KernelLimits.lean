import Lojita.Kernel.ResidentImport
import Lean.Compiler.Options
import Lean.Compiler.LCNF.Main
import Lean.Compiler.LCNF.ToDecl

namespace Lojita.Kernel
open Lean

/-- Structured taboo error codes covering the 10 Lean 4 community & historical crash classes. -/
inductive TabooCode where
  | syntaxDepth
  | giantContainerLit
  | scientificExponent
  | giantNumeral
  | wideMatch
  | overlappingMatch
  | wideDecidableEq
  | heavyDecide
  | decideTimeout
  | rflReductionBlowup
  | wfKernelUnfold
  | deepRecursion
  | excessiveMemory
  | kernelTimeout
  | hugePowShift
  | largeGroundMismatchSyntax
  | interpreterLimit
  | lcnfCompileBlowup
  | ccBlowup
  deriving BEq, Repr, Inhabited

def TabooCode.tag : TabooCode → String
  | .syntaxDepth               => "TABOO_SYNTAX_DEPTH"
  | .giantContainerLit         => "TABOO_GIANT_CONTAINER_LIT"
  | .scientificExponent        => "TABOO_SCIENTIFIC_EXPONENT"
  | .giantNumeral              => "TABOO_GIANT_NUMERAL"
  | .wideMatch                 => "TABOO_WIDE_MATCH"
  | .overlappingMatch          => "TABOO_OVERLAPPING_MATCH"
  | .wideDecidableEq           => "TABOO_WIDE_DECIDABLE_EQ"
  | .heavyDecide               => "TABOO_HEAVY_DECIDE"
  | .decideTimeout             => "TABOO_DECIDE_TIMEOUT"
  | .rflReductionBlowup        => "TABOO_RFL_REDUCTION_BLOWUP"
  | .wfKernelUnfold            => "TABOO_WF_KERNEL_UNFOLD"
  | .deepRecursion             => "TABOO_DEEP_RECURSION"
  | .excessiveMemory           => "TABOO_EXCESSIVE_MEMORY"
  | .kernelTimeout             => "TABOO_KERNEL_TIMEOUT"
  | .hugePowShift              => "TABOO_HUGE_POW_SHIFT"
  | .largeGroundMismatchSyntax => "TABOO_LARGE_GROUND_MISMATCH_SYNTAX"
  | .interpreterLimit          => "TABOO_INTERPRETER_LIMIT"
  | .lcnfCompileBlowup         => "TABOO_LCNF_BLOWUP"
  | .ccBlowup                  => "TABOO_CC_BLOWUP"

def TabooCode.detour : TabooCode → String
  | .syntaxDepth =>
    "[DETOUR] Split deeply nested expressions or giant left-associative chains into smaller named definitions or compact folds."
  | .giantContainerLit =>
    "[DETOUR] Avoid single list/array syntax literals over 4,096 elements; encode compact range tables `(lo, hi)` or compute tables iteratively."
  | .scientificExponent =>
    "[DETOUR] Lean eagerly expands scientific literals `m * 10^e`; represent large IEEE-754 scales symbolically or via explicit rational arithmetic."
  | .giantNumeral =>
    "[DETOUR] Avoid raw integer literals over 256 digits; construct big constants via compact expressions."
  | .wideMatch =>
    "[DETOUR] `match` with > 64 arms causes quadratic splitter/eq_def blowup in Lean 4; partition into sub-matches, interval checks (`lo ≤ x && x ≤ hi`), or binary search on sorted range tables."
  | .overlappingMatch =>
    "[DETOUR] Multi-discriminant `match` with ≥ 4 scrutinees, > 32 arms, and wildcards causes exponential splitter blowup; cascade nested matches instead."
  | .wideDecidableEq =>
    "[DETOUR] `deriving DecidableEq` on inductives with > 64 constructors causes quadratic `noConfusion` blowup; map constructors to an explicit `Nat` tag and prove injectivity."
  | .heavyDecide =>
    "[DETOUR] Never run `by decide` over `String`, `ByteArray`, `Array`, or `Posix.Machine` (Lean 4's kernel unfolds UTF-8 `ByteArray`/`BitVec` term-by-term); use `simp`, structural lemmas, or `rfl` on small ground steps."
  | .decideTimeout =>
    "[DETOUR] `decide` exceeded deterministic heartbeat/memory budget; replace kernel brute-force decision with `simp` or algebraic lemmas."
  | .rflReductionBlowup =>
    "[DETOUR] Definitional reduction (`rfl`) exceeded deterministic budget; rewrite step-by-step using `simp` or equational lemmas instead of forcing kernel WHNF."
  | .wfKernelUnfold =>
    "[DETOUR] Kernel definitional equality cannot use `[irreducible]` on `WellFounded.fix` and explodes unfolding `Acc.rec`; rewrite with `[simp]` equational lemmas (`rw [foo]`) or use `termination_by structural`."
  | .deepRecursion =>
    "[DETOUR] Elaboration or kernel WHNF hit the safe recursion depth cap (`maxRecDepth = 2048`); make auxiliary loops tail-recursive or reduce structural fuel in kernel reductions."
  | .excessiveMemory =>
    "[DETOUR] Compilation/checking exceeded the C++ runtime memory ceiling (`setMaxMemory`); eliminate giant unfolded tables or non-tail-recursive evaluations."
  | .kernelTimeout =>
    "[DETOUR] Guarded C++ kernel check (`addDeclCore`) exceeded deterministic `maxHeartbeats`; factor out shared lemmas or avoid unfolding large definitions."
  | .hugePowShift =>
    "[DETOUR] Closed `a ^ b` or `a <<< b` with exponent > 65,536 triggers multi-megabyte single-step GMP allocation in the kernel; keep exponents symbolic or bounded."
  | .largeGroundMismatchSyntax =>
    "[DETOUR] Large ground container (> 512 elements) uses distinct term representations across spec and impl; share the same named table definition."
  | .interpreterLimit =>
    "[DETOUR] Bytecode evaluation hit heartbeat, stack, or memory limits (check for non-tail-recursive functions over long inputs)."
  | .lcnfCompileBlowup =>
    "[DETOUR] LCNF code generation exceeded resource bounds; split oversized functions or giant match tables."
  | .ccBlowup =>
    "[DETOUR] Native C compilation timed out or failed; split large generated modules into smaller units."

structure TabooError where
  code   : TabooCode
  offset : Nat := 0
  detail : String
  deriving Repr, Inhabited

def TabooError.format (e : TabooError) : String :=
  let loc := if e.offset > 0 then s!" (byte {e.offset})" else ""
  s!"{e.code.tag}:{loc} {e.detail}\n{e.code.detour}"

instance : ToString TabooError := ⟨TabooError.format⟩

/-- Safe default elaboration options:
    - `Elab.async := false` keeps errors deterministic on the current worker thread;
    - `compiler.postponeCompile := true` skips heavy LCNF passes during checking (T10);
    - `maxRecDepth := 2048` (32,768 C++ frames ≈ 8 MiB) trips cleanly well inside a 64 MiB stack (T5);
    - `maxHeartbeats := 400000` bounds per-command elaboration. -/
def safeElabOptions : Options := ({} : Options)
  |>.setBool `Elab.async false
  |>.setBool `autoImplicit true
  |>.setBool `linter.all false
  |>.setBool `compiler.postponeCompile true
  |>.setBool `pp.deepTerms false
  |>.set `pp.deepTerms.threshold (32 : Nat)
  |>.set `pp.maxSteps (512 : Nat)
  |>.setBool `pp.proofs false
  |>.set `maxRecDepth (1024 : Nat)
  |>.set `maxHeartbeats (12000 : Nat)

/-- Options used exclusively during final `CompileGuard` code generation. -/
def codeGenOptions : Options :=
  safeElabOptions
    |>.setBool `compiler.postponeCompile false
    |>.set `maxRecDepth (4096 : Nat)
    |>.set `maxHeartbeats (200000 : Nat)

/-- Persistent environment extension recording declaration groups whose LCNF codegen was deferred
    while `compiler.postponeCompile = true` (even on non-`module` environments). -/
initialize deferredCompileGroupsExt :
    SimplePersistentEnvExtension (Array Name) (Array (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => #[]
    addEntryFn    := fun acc grp => acc.push grp
  }

private initialize origCompileRef : IO.Ref (Option (Array Name → Options → CoreM Unit)) ←
  IO.mkRef none

private initialize limitsInitLock : Std.Mutex Bool ← Std.Mutex.new false

/-- Lightweight computability input check mirroring lines 161–171 of `Lean.Compiler.LCNF.Main`:
    catches illegal `Classical.choice` / `noncomputable` usage in computable `def`s without running
    any heavy LCNF passes (`basePasses`, `monoPasses`, `splitScc`, `impurePasses`, `ResetReuse`, `IR`). -/
private def checkComputableInputsOnly (declNames : Array Name) : CoreM Unit := do
  Core.withCurrHeartbeats do
    let declNames ← declNames.filterM Compiler.LCNF.shouldGenerateCode
    if declNames.isEmpty then return
    Compiler.LCNF.CompilerM.run do
      for declName in declNames do
        discard <| Compiler.LCNF.toDecl declName

/-- Run the original full LCNF + IR compiler on `declNames`. -/
def runFullCompileDecls (declNames : Array Name) (baseOpts : Options := {}) : CoreM Unit := do
  let some orig ← origCompileRef.get
    | (← Lean.compileDeclsRef.get) declNames baseOpts
  withOptions (Compiler.compiler.postponeCompile.set · false) do
    orig declNames baseOpts

/-- One-time idempotent process initialization of Lean 4 C++ runtime limits & LCNF deferral hook. -/
def initKernelLimits (stackMB : Nat := 64) (maxMemMB : Nat := 2048) : IO Unit :=
  limitsInitLock.atomically do
    setRuntimeThreadStackBytes ((stackMB * 1024 * 1024).toUSize)
    setRuntimeMaxMemoryBytes ((maxMemMB * 1024 * 1024).toUSize)
    if ← get then return
    let orig ← Lean.compileDeclsRef.get
    origCompileRef.set (some orig)
    Lean.compileDeclsRef.set fun declNames baseOpts => do
      let opts ← getOptions
      if Compiler.compiler.postponeCompile.get opts then
        let env ← getEnv
        let isInd := declNames.any fun n => (env.find? n).any (· matches .inductInfo _)
        if isInd || declNames.any (isMarkedMeta env) then
          orig declNames baseOpts
        else
          -- Perform lightweight computability verification so `isNoncomputable` stays exact,
          -- while deferring all expensive LCNF optimization/monomorphization/IR passes.
          checkComputableInputsOnly declNames
          modifyEnv (deferredCompileGroupsExt.addEntry · declNames)
      else
        orig declNames baseOpts
    set true

/-- Read current process resident set size (RSS) in KiB from `/proc/self/statm` on Linux. -/
def readProcessRssKB : IO Nat := do
  try
    let text ← IO.FS.readFile "/proc/self/statm"
    let fields := (text.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    let some rssPagesStr := fields[1]? | return 0
    let some pages := rssPagesStr.toNat? | return 0
    return pages * 4
  catch _ =>
    return 0

end Lojita.Kernel
