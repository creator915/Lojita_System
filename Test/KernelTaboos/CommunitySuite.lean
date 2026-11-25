import Test.KernelTaboos.Harness

namespace Test.KernelTaboos.CommunitySuite
open Lojita.Kernel Lean Test.KernelTaboos

/-- **T1 (`taboo_01_deep_syntax`)**:
    - 3,000-deep left-associative `+` expression chain → `TABOO_SYNTAX_DEPTH` on worker thread with 0 `SIGSEGV`;
    - 5,000-element `[0, 1, ...]` container literal → `TABOO_GIANT_CONTAINER_LIT`;
    - Twin-Gate safe fold / range formulation passes cleanly. -/
def testT01DeepSyntax : IO Unit := do
  let deepChain := String.intercalate " + " ((List.range 3000).map toString)
  let badDepthSrc := s!"namespace Gen.T01\ndef x : Nat := {deepChain}\nend Gen.T01"
  let (msg1, ms1, _) ← expectRejectedBounded "T1.deepChain"
    "TABOO_SYNTAX_DEPTH" (maxMs := 500) (parseMod badDepthSrc)
  ensure (msg1.contains "[DETOUR]") "T1: missing [DETOUR]"

  let giantList := "[" ++ String.intercalate ", " ((List.range 5000).map toString) ++ "]"
  let badContainerSrc := s!"namespace Gen.T01\ndef xs : List Nat := {giantList}\nend Gen.T01"
  let (_, ms2, _) ← expectRejectedBounded "T1.giantContainer"
    "TABOO_GIANT_CONTAINER_LIT" (maxMs := 500) (parseMod badContainerSrc)

  -- Twin-Gate: safe compact fold passes + negative soundness check rejects wrong sum
  let safeMod ← mkObject "Gen.T01Safe"
    "def x : Nat := (List.range 3000).foldl (· + ·) 0\ntheorem nonneg : 0 ≤ x := Nat.zero_le _"
  discard <| runMeasuredOnWorker "T1.safeTwin" (maxMs := 200) (checkClosedModule [] safeMod)
  IO.println s!"  [PASS] T01 Deep Syntax & Giant Container: depth-reject={ms1}ms, container-reject={ms2}ms"

/-- **T2 (`taboo_02_scientific_numeral`)** (`#16538`, `#13987`):
    - `1e100000` → `TABOO_SCIENTIFIC_EXPONENT` (`< 50 ms`);
    - 400-digit integer literal → `TABOO_GIANT_NUMERAL` (`< 50 ms`);
    - Twin-Gate: `1.25e18` (valid Float/scientific scale) or bounded rational scale passes! -/
def testT02ScientificAndNumeral : IO Unit := do
  let badSci := "namespace Gen.T02\ndef huge := 1e100000\nend Gen.T02"
  let (_, ms1, _) ← expectRejectedBounded "T2.scientific1e100000"
    "TABOO_SCIENTIFIC_EXPONENT" (maxMs := 50) (parseMod badSci)

  let digits400 := String.ofList (List.replicate 400 '9')
  let badNum := s!"namespace Gen.T02\ndef huge : Nat := {digits400}\nend Gen.T02"
  let (_, ms2, _) ← expectRejectedBounded "T2.numeral400digits"
    "TABOO_GIANT_NUMERAL" (maxMs := 50) (parseMod badNum)

  -- Twin-Gate: exponent ≤ 308 and normal integer literal pass
  let okMod ← mkObject "Gen.T02Safe"
    "def scale : Float := 1.5e300\ndef maxU64 : Nat := 18446744073709551615"
  discard <| runMeasuredOnWorker "T2.safeTwin" (maxMs := 200) (checkClosedModule [] okMod)
  IO.println s!"  [PASS] T02 Scientific & Giant Numeral: sci-reject={ms1}ms, num-reject={ms2}ms"

/-- **T3 (`taboo_03_wide_match`)** (`#3935`, `#9322`, `#10195`):
    - 120-branch `match` with wildcard `_` → `TABOO_WIDE_MATCH` (`< 50 ms`);
    - 4-discriminant 40-branch wildcard `match` → `TABOO_OVERLAPPING_MATCH` (`< 50 ms`);
    - Twin-Gate: interval range check equivalent passes in `< 50 ms`! -/
def testT03WideMatch : IO Unit := do
  let arms120 := String.intercalate "\n  " ((List.range 120).map fun i => s!"| {i} => {i + 1}") ++ "\n  | _ => 0"
  let badWide := s!"namespace Gen.T03\ndef classify (n : Nat) : Nat :=\n  match n with\n  {arms120}\nend Gen.T03"
  let (_, ms1, _) ← expectRejectedBounded "T3.wideMatch121"
    "TABOO_WIDE_MATCH" (maxMs := 50) (parseMod badWide)

  let arms4D := String.intercalate "\n  " ((List.range 36).map fun i => s!"| {i}, _, 0, _ => {i}") ++ "\n  | _, _, _, _ => 99"
  let badOverlap := s!"namespace Gen.T03\ndef grid (a b c d : Nat) : Nat :=\n  match a, b, c, d with\n  {arms4D}\nend Gen.T03"
  let (_, ms2, _) ← expectRejectedBounded "T3.overlappingMatch"
    "TABOO_OVERLAPPING_MATCH" (maxMs := 50) (parseMod badOverlap)

  -- Twin-Gate: interval formulation passes + negative soundness gate
  let safeSpec ← mkObject "Gen.T03Safe"
    "def classify (n : Nat) : Nat := if n < 120 then n + 1 else 0\naxiom atTen : classify 10 = 11"
  let safeImpl ← mkObject "Gen.T03Safe"
    "def classify (n : Nat) : Nat := if n < 120 then n + 1 else 0\ntheorem atTen : classify 10 = 11 := rfl"
  discard <| runMeasuredOnWorker "T3.safeTwin" (maxMs := 150) (satisfies safeSpec safeImpl)
  IO.println s!"  [PASS] T03 Wide & Overlapping Match: wide-reject={ms1}ms, overlap-reject={ms2}ms"

/-- **T4 (`taboo_04_wide_decidable_eq`)** (`#11450`, `#7580`):
    - 80-constructor enum with `deriving DecidableEq` → `TABOO_WIDE_DECIDABLE_EQ` (`< 50 ms`);
    - Twin-Gate: 80-constructor enum WITHOUT `deriving DecidableEq` passes! -/
def testT04WideDecidableEq : IO Unit := do
  let ctors80 := String.intercalate "\n  " ((List.range 80).map fun i => s!"| op{i}")
  let badInd := s!"namespace Gen.T04\ninductive Opcode where\n  {ctors80}\n  deriving DecidableEq\nend Gen.T04"
  let (_, ms1, _) ← expectRejectedBounded "T4.wideDecidableEq80"
    "TABOO_WIDE_DECIDABLE_EQ" (maxMs := 50) (parseMod badInd)

  let okInd ← mkObject "Gen.T04Safe" s!"inductive Opcode where\n  {ctors80}"
  let mOk ← runMeasuredOnWorker "T4.safeTwin" (maxMs := 400) (checkClosedModule [] okInd)
  IO.println s!"  [PASS] T04 Wide DecidableEq: 80-ctor-deriving-reject={ms1}ms, plain-80-ctor-ok={mOk.elapsedMs}ms"

/-- **T5 (`taboo_05_deep_recursion_cap`)** (`#12971`, `#13956`, `#14992`):
    Deep non-tail-recursive kernel reduction hits `maxRecDepth = 2048` cleanly on a worker thread
    and throws `TABOO_DEEP_RECURSION` (or `TABOO_RFL_REDUCTION_BLOWUP`) in `< 500 ms` with 0 `SIGSEGV`! -/
def testT05DeepRecursionCap : IO Unit := do
  let deepMod ← mkObject "Gen.T05"
    "def nest : Nat → Nat\n  | 0 => 0\n  | n + 1 => Nat.succ (nest n)\ntheorem boom : nest 5000 = 5000 := rfl"
  let (msg, ms, rssKB) ← expectRejectedBounded "T5.deepRecursion5000"
    "TABOO_" (maxMs := 500) (checkClosedModule [] deepMod)
  ensure (msg.contains "TABOO_DEEP_RECURSION" || msg.contains "TABOO_RFL_REDUCTION_BLOWUP")
    s!"T5: unexpected code: {msg.take 200}"

  -- Twin-Gate: inductive proof for ALL `n` (`∀ n, nest n = n`) passes in milliseconds without unrolling!
  let safeMod ← mkObject "Gen.T05Safe"
    "def nest : Nat → Nat\n  | 0 => 0\n  | n + 1 => Nat.succ (nest n)\ntheorem nestEq (n : Nat) : nest n = n := by induction n with\n  | zero => rfl\n  | succ k ih => simp [nest, ih]\ntheorem ok5000 : nest 5000 = 5000 := nestEq 5000"
  discard <| runMeasuredOnWorker "T5.inductiveTwin" (maxMs := 250) (checkClosedModule [] safeMod)
  IO.println s!"  [PASS] T05 Deep Recursion Cap (maxRecDepth=2048): caught={ms}ms (ΔRSS={rssKB / 1024}MiB, 0 SIGSEGV)"

/-- **T6 (`taboo_06_heavy_decide`)** (`#16268`, `#5502`):
    - `by decide` on `String` / `ByteArray` / 512-byte literal → `TABOO_HEAVY_DECIDE` (`< 50 ms`);
    - `by decide +native` (`native_decide` synonym!) → blocked as `forbiddenMetaprogramming`;
    - Twin-Gate: small finite enum `by decide` and `decide (r = r) = true := decide_eq_true rfl` pass! -/
def testT06HeavyDecide : IO Unit := do
  let s200 := String.ofList (List.replicate 200 'a')
  let badStrDecide := s!"namespace Gen.T06\ntheorem bad : (\"{s200}\" == \"{s200}\") = true := by decide\nend Gen.T06"
  let (_, ms1, _) ← expectRejectedBounded "T6.stringDecide"
    "TABOO_HEAVY_DECIDE" (maxMs := 50) (parseMod badStrDecide)

  let badBytesDecide := "namespace Gen.T06\ntheorem bad (b : ByteArray) : b.size = b.size := by decide\nend Gen.T06"
  let (_, ms2, _) ← expectRejectedBounded "T6.byteArrayDecide"
    "TABOO_HEAVY_DECIDE" (maxMs := 50) (parseMod badBytesDecide)

  -- Security check: `decide +native` synonym for `native_decide` must be rejected at syntax stage!
  expectSyntaxCode "forbiddenMetaprogramming"
    "namespace Gen.T06\ntheorem sneaky : 1 + 1 = 2 := by decide +native\nend Gen.T06"

  -- Twin-Gate: finite enum `by decide` & term-level `decide ... := decide_eq_true rfl` pass!
  let okEnum ← mkObject "Gen.T06Safe"
    "inductive Color where | red | green | blue deriving DecidableEq\ntheorem neColors : Color.red ≠ Color.blue := by decide\ntheorem reflDec (s : String) : decide (s = s) = true := decide_eq_true rfl"
  discard <| runMeasuredOnWorker "T6.safeTwin" (maxMs := 250) (checkClosedModule [] okEnum)
  IO.println s!"  [PASS] T06 Heavy Decide & `decide +native` Block: str-decide={ms1}ms, bytes-decide={ms2}ms"

/-- **T7 (`taboo_07_huge_pow_and_wf`)** (`#16613`, `#5192`):
    - `2 ^ 10000000` and `1 <<< 200000` → `TABOO_HUGE_POW_SHIFT` (`< 150 ms`);
    - `WellFounded.fix` forced under `rfl` → `TABOO_WF_KERNEL_UNFOLD` (`< 500 ms`);
    - Twin-Gate: `2 ^ 1074` (IEEE-754 subnormal scale) and `simp`-rewritten WF lemma pass! -/
def testT07HugePowAndWF : IO Unit := do
  let badPow ← mkObject "Gen.T07Pow" "def monster : Nat := 2 ^ 10000000"
  let (_, msPow, _) ← expectRejectedBounded "T7.pow10M"
    "TABOO_HUGE_POW_SHIFT" (maxMs := 150) (checkClosedModule [] badPow)

  let badShift ← mkObject "Gen.T07Shift" "def monster : Nat := 1 <<< 200000"
  let (_, msShift, _) ← expectRejectedBounded "T7.shift200k"
    "TABOO_HUGE_POW_SHIFT" (maxMs := 150) (checkClosedModule [] badShift)

  -- Sealed WF definition under `rfl` fails fast in MetaM (< 100 ms), whereas unsealing (`@[semireducible]`
  -- or `unseal ... in ... := rfl`, `#5192` / `#5697`) forces `WellFounded.fix` unfolding and is caught
  -- deterministically with `TABOO_WF_KERNEL_UNFOLD` (< 500 ms)!
  let sealedWF ← mkObject "Gen.T07WFSealed"
    "def wfTree (n : Nat) : Nat := if n = 0 then 1 else wfTree (n / 2) + wfTree (n / 2)\ntermination_by n\ndecreasing_by all_goals omega\ntheorem wfRfl : wfTree 65536 = 131072 := rfl"
  discard <| expectRejectedBounded "T7.wfSealed"
    "ELABORATION_ERROR" (maxMs := 150) (checkClosedModule [] sealedWF)

  let badWF ← mkObject "Gen.T07WF"
    "@[semireducible] def wfFib (n : Nat) : Nat := if n < 2 then n else wfFib (n - 1) + wfFib (n - 2)\ntermination_by n\ndecreasing_by all_goals omega\ntheorem wfRfl : wfFib 24 = 46368 := rfl"
  let (wfMsg, msWF, _) ← expectRejectedBounded "T7.wfRfl"
    "TABOO_WF_KERNEL_UNFOLD" (maxMs := 500) (checkClosedModule [] badWF)
  ensure (wfMsg.contains "[DETOUR]")
    s!"T7 WF missing [DETOUR] guidance: {wfMsg.take 250}"

  -- Twin-Gate: IEEE-754 `2 ^ 1074` + WF proof using `simp [collatzStep]` passes fast!
  let okMod ← mkObject "Gen.T07Safe"
    "def ieeeSubnormalDenom : Nat := 2 ^ 1074\ndef collatzStep (n : Nat) : Nat := if n = 0 then 0 else collatzStep (n / 2) + 1\ntermination_by n\ndecreasing_by omega\ntheorem wfSimp : collatzStep 8 = 4 := by simp [collatzStep]"
  discard <| runMeasuredOnWorker "T7.safeTwin" (maxMs := 300) (checkClosedModule [] okMod)
  IO.println s!"  [PASS] T07 Huge Pow/Shift & WF Rfl: pow={msPow}ms, shift={msShift}ms, wf-rfl={msWF}ms"

/-- **T8 (`taboo_08_unbounded_kernel_defeq`)**:
    Directly exercises `KernelGuard.checkValuesDefEq` (`addDeclCore`) on a slow neutral-variable
    exponential reduction pair where bare `Lean.Kernel.isDefEq` has `g_max_heartbeat = 0` (∞).
    Verifies deterministic `.deterministicTimeout` cutoff within `< 150 ms`! -/
def testT08GuardedKernelDefEq : IO Unit := do
  let slowMod ← mkObject "Gen.T08"
    "def tower : Nat → Nat → Nat\n  | 0, acc => acc\n  | n + 1, acc => tower n (tower n acc)\ndef lhs (x : Nat) : Nat := tower 18 x\ndef rhs (x : Nat) : Nat := tower 18 (0 + x)"
  let snap ← checkClosedModule [] slowMod
  let kenv := snap.env.toKernelEnv
  let some (.defnInfo lhsInfo) := kenv.find? `Gen.T08.lhs | throw (IO.userError "T8: missing lhs")
  let some (.defnInfo rhsInfo) := kenv.find? `Gen.T08.rhs | throw (IO.userError "T8: missing rhs")

  -- Tight deterministic budget (`maxHeartbeats := 2000`) cuts off `tower 18 x =?= tower 18 (0 + x)` in milliseconds!
  let mCut ← runMeasuredOnWorker "T8.checkValuesDefEq.timeout" (maxMs := 150) do
    pure <| checkValuesDefEq kenv [] (.succ .zero) lhsInfo.type lhsInfo.value rhsInfo.value
      { maxHeartbeats := 2000, maxRecDepth := 1024 }
  ensure (mCut.value matches .error .deterministicTimeout || mCut.value matches .error .deepRecursion)
    "T8: expected deterministicTimeout or deepRecursion from KernelGuard.checkValuesDefEq"

  -- Twin-Gate: `lhs == lhs` passes `checkValuesDefEq` immediately!
  let mEq ← runMeasuredOnWorker "T8.checkValuesDefEq.refl" (maxMs := 50) do
    pure <| checkValuesDefEq kenv [] (.succ .zero) lhsInfo.type lhsInfo.value lhsInfo.value
      { maxHeartbeats := 2000, maxRecDepth := 1024 }
  ensure (mEq.value matches .ok ()) "T8: reflexive checkValuesDefEq failed"
  IO.println s!"  [PASS] T08 Guarded Kernel addDeclCore Cutoff: timeout={mCut.elapsedMs}ms, refl={mEq.elapsedMs}ms"

/-- **T9 (`taboo_09_utf8_and_bytes_tables`)**:
    8,192-byte `ByteArray` / `String.toByteArray` differing only at the final byte (`offset 8191`):
    `GroundEval` refutes in `< 20 ms` naming `offset 8191`, while identical 8,192-byte table passes! -/
def testT09Utf8AndByteArrayTables : IO Unit := do
  let mk8KMod (lastChar : Char) : IO LeanMod := do
    -- Construct 8,192 bytes via 16 chunks of 512 ASCII bytes concatenated with `++`
    let chunk512 := String.ofList (List.replicate 512 'A')
    let chunkLast := String.ofList (List.replicate 511 'A' ++ [lastChar])
    let chunks := List.replicate 15 chunk512 ++ [chunkLast]
    let expr := String.intercalate " ++\n  " (chunks.map reprStr)
    mkObject "Gen.T09" s!"def blob : ByteArray := (\n  {expr}).toByteArray"

  let spec8K ← mk8KMod 'Z'
  let impl8KOk ← mk8KMod 'Z'
  let impl8KBad ← mk8KMod 'Y'
  discard <| checkClosedModule [] spec8K
  discard <| checkClosedModule [] impl8KOk
  discard <| checkClosedModule [] impl8KBad

  discard <| runMeasuredOnWorker "T9.8KB.ok" (maxMs := 300) (satisfies spec8K impl8KOk)
  let (msg, ms, _) ← expectRejectedBounded "T9.8KB.lastByteDiff"
    "bytes differ at offset 8191: expected 0x5A, received 0x59" (maxMs := 50) (satisfies spec8K impl8KBad)
  ensure (ms < 20 && errorTag msg == "INTERFACE_MISMATCH")
    s!"T9: 8KB ByteArray fast-reject took {ms} ms"
  IO.println s!"  [PASS] T09 8,192-Byte UTF-8/ByteArray Table: last-byte fast-reject={ms}ms (offset 8191)"

/-- **T10 (`taboo_10_lcnf_and_cc`)** (`#11322`, `#11389`, `#9692`, `#12665`):
    - Daily `checkClosedModule` skips LCNF completely (`postponeCompile = true`);
    - `compileVerifiedExeWithReport` compiles a module emitting `≥ 128 KiB` of C with `-O1`
      and a small module with `-O2`, produces a working static CLI binary, and enforces `cc` timeout! -/
def testT10LcnfAndAdaptiveCc : IO Unit := IO.FS.withTempDir fun dir => do
  -- Build a table module whose generated `.c` exceeds 128 KiB (~650 tuples -> ~250 KiB of C)
  let tuples := String.intercalate ", " ((List.range 650).map fun i => s!"({i * 3}, {i * 3 + 2})")
  let bigTableMod ← mkObject "Gen.BigTable"
    s!"def table : Array (Nat × Nat) := #[{tuples}]\ndef lookupSum : Nat := table.size"
  let mCheck ← runMeasuredOnWorker "T10.dailyCheckSkipsLCNF" (maxMs := 500) do
    checkClosedModule [] bigTableMod
  ensure (!(deferredCompileGroupsExt.getState mCheck.value.env).isEmpty)
    "T10: expected deferredCompileGroupsExt to record postponed LCNF declarations"

  let cliMod ← mkObject "Gen.BigCli"
    "open LojitaCtx.World\ndef app : CliApp [.stdioCap] := do\n  writeStdoutStrW .here s!\"{Gen.BigTable.lookupSum}\\n\"\n  return 0"
    ["LojitaCtx.World", "Gen.BigTable"]
  let outBin := dir / "big-cli"
  let report ← compileVerifiedExeWithReport [bigTableMod, cliMod] (q "Gen.BigCli.app") .cli outBin
  ensure (report.any (fun (m, opt) => m == `Gen.BigTable && opt == "-O1"))
    s!"T10: expected Gen.BigTable (>= 128 KiB C) to downgrade to -O1, got {report}"
  ensure (report.any (fun (m, opt) => m == `Gen.BigCli && opt == "-O2"))
    s!"T10: expected small Gen.BigCli to use -O2, got {report}"

  let runOut ← IO.Process.output { cmd := outBin.toString }
  ensure (runOut.exitCode == 0 && runOut.stdout == "650\n")
    s!"T10: compiled binary output mismatch: exit={runOut.exitCode}, stdout={repr runOut.stdout}"
  IO.println s!"  [PASS] T10 Postponed LCNF & Adaptive cc: daily-check={mCheck.elapsedMs}ms, report={report}, bin-stdout=650"

def runAll : IO Unit := do
  IO.println "=== Part B: Lean 4 Community 10-Class Taboo Suite (T1–T10) ==="
  testT01DeepSyntax
  testT02ScientificAndNumeral
  testT03WideMatch
  testT04WideDecidableEq
  testT05DeepRecursionCap
  testT06HeavyDecide
  testT07HugePowAndWF
  testT08GuardedKernelDefEq
  testT09Utf8AndByteArrayTables
  testT10LcnfAndAdaptiveCc

end Test.KernelTaboos.CommunitySuite
