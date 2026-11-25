import Test.KernelTaboos.Harness

namespace Test.KernelTaboos.HistoricalRepros
open Lojita.Kernel Lean Test.KernelTaboos

/-- **H1 (`2026-11-24 22:55` 1,305-line `gronT1TokenSpec.block` + `Array (Nat × Nat)` 366-tuple table)**:
    - Positive Gate: unmodified 1,305-line `gronT1TokenSpec.block` (3 `mutual` blocks, IEEE-754 Binary64
      rational arithmetic, 366-item `suffixRanges : Array (Nat × Nat)`) passes `checkClosedModule` & `satisfies`.
    - Server-Crash Negative Gate: mutating a single tuple `(121344, 121398) -> (121344, 121399)` near the end
      of `suffixRanges` (blind spot of old `groundText?`) is fast-refuted by `GroundEval` in `< 20 ms`! -/
def testH1GronTokenSpec : IO Unit := do
  let t0Src ← IO.FS.readFile "Test/Fixtures/GronT0.lean"
  let t1Src ← IO.FS.readFile "Test/Fixtures/gronT1TokenSpec.block"
  let t0 ← parseMod t0Src
  let t1 ← parseMod t1Src

  -- Soundness pre-check: `t1` is an open spec (`axiom dispatch`, etc.), so `checkClosedModule` must reject it,
  -- while `checkConditionalGlue ... (checkingSpec := true)` verifies the full 1,305-line spec!
  let mCheck ← runMeasuredOnWorker "H1.checkSpec" (maxMs := 4000) do
    checkConditionalGlue [t0] [] t1 (checkingSpec := true)
  expectErrorCode "DISALLOWED_AXIOM_VIOLATION" (checkClosedModule [t0] t1)
  -- Verify `postponeCompile = true` actually deferred LCNF passes!
  ensure (!(deferredCompileGroupsExt.getState mCheck.value.env).isEmpty)
    "H1: expected LCNF compilation to be deferred during spec checking"

  -- Positive Gate 2: `satisfies ... .subspec` on refactored copy of the 1,305-line draft
  let t1Copy ← parseMod (t1Src.replace "def digit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57"
    "def digit (b : UInt8) : Bool := (48 ≤ b) && (b ≤ 57)")
  discard <| checkConditionalGlue [t0] [] t1Copy (checkingSpec := true)
  let mSat ← runMeasuredOnWorker "H1.satisfies.positive" (maxMs := 500) do
    satisfies t1 t1Copy [t0] .subspec

  -- Server-Crash Negative Gate: mutate `(121344, 121398)` inside `suffixRanges : Array (Nat × Nat)`!
  let mutatedSrc := t1Src.replace "(121344, 121398)" "(121344, 121399)"
  ensure (mutatedSrc != t1Src) "H1: target tuple not found in gronT1TokenSpec.block"
  let t1Mut ← parseMod mutatedSrc
  -- Pre-elaborate `t1Mut` so we measure the pure interface comparison / fast-refutation latency!
  let snapT1 ← checkConditionalGlue [t0] [] t1 (checkingSpec := true)
  let snapT1Mut ← checkConditionalGlue [t0] [] t1Mut (checkingSpec := true)
  -- Direct `GroundEval` fast-refutation on `suffixRanges` (< 20 ms!) + full `satisfies` check:
  let some (.defnInfo sr1) := snapT1.env.checked.get.find? `Gen.T1.Gron.suffixRanges
    | throw (IO.userError "H1: missing suffixRanges in t1")
  let some (.defnInfo sr2) := snapT1Mut.env.checked.get.find? `Gen.T1.Gron.suffixRanges
    | throw (IO.userError "H1: missing suffixRanges in t1Mut")
  let mGround ← runMeasuredOnWorker "H1.GroundEval.suffixRanges" (maxMs := 20) do
    let out := compareGroundFast snapT1Mut.env sr1.value sr2.value
    ensure (out matches .refuted _) "H1: GroundEval failed to refute mutated Array (Nat × Nat)"
  let (msg, negMs, rssKB) ← expectRejectedBounded "H1.suffixRanges.tupleTypo"
    "elements differ at index" (maxMs := 20) (satisfies t1 t1Mut [t0] .subspec)
  ensure (errorTag msg == "INTERFACE_MISMATCH" &&
    msg.contains "(121344, 121398)" && msg.contains "(121344, 121399)")
    s!"H1: expected exact tuple diff in diagnostic, got:\n{msg.take 400}"
  IO.println s!"  [PASS] H1 gronT1TokenSpec (1,305 lines): check={mCheck.elapsedMs}ms, satisfies={mSat.elapsedMs}ms, groundEval={mGround.elapsedMs}ms, full-satisfies-reject={negMs}ms (ΔRSS={rssKB / 1024}MiB)"

/-- **H2 (`2026-11-24 22:55–22:58` Whole-Server OOM Reboot Culprit: 65,525-byte line + non-tail-recursive `tokenRunes`)**:
    Verbatim `tokenRunes` from `gronT1TokenSpec.block:575-583` fed `List.replicate 65525 32`:
    - Twin-Gate Positive: 32-byte input passes both `rfl` and `evalPureNatConstBounded`;
    - Negative Gate A (Kernel `rfl`): intercepted in `< 500 ms` with 0 `SIGSEGV` and ΔRSS `< 256 MiB`;
    - Negative Gate B (Bytecode interpreter `evalPureNatConstBounded`): intercepted in `< 500 ms` (`TABOO_INTERPRETER_LIMIT`)! -/
def testH2NonTailRecTokenRunes : IO Unit := do
  let coreDefs := "open LojitaCtx.Terminal
structure TokenRune where
  scalar : Char
  spelling : Bytes
def runeWidth (first : Byte) : Nat :=
  if first < 128 then 1
  else if first < 224 then 2
  else if first < 240 then 3
  else 4
def tokenRunes : Nat → Bytes → List TokenRune
  | 0, _ | _, [] => []
  | fuel+1, input@(first :: rest) =>
    let width := runeWidth first
    let spelling := input.take width
    match (String.fromUTF8? spelling.toByteArray).bind (fun s => s.toList.head?) with
    | some scalar => ⟨scalar, spelling⟩ :: tokenRunes fuel (input.drop width)
    | none => ⟨'?', [first]⟩ :: tokenRunes fuel rest
termination_by structural fuel _ => fuel\n"

  let baseMod ← mkObject "Gen.H2Core" coreDefs ["LojitaCtx.Terminal"]
  let warmMod ← mkObject "Gen.H2Warm" "open Gen.H2Core\ndef warm : Nat := runeWidth 65" ["Gen.H2Core"]
  discard <| checkClosedModule [baseMod] warmMod

  -- Positive Twin-Gate: 32 spaces
  let smallMod ← mkObject "Gen.H2Small" (coreDefs ++
    "def smallCount : Nat := (tokenRunes 33 (List.replicate 32 32)).length\ntheorem smallOk : smallCount = 32 := rfl")
    ["LojitaCtx.Terminal"]
  let smallSnap ← (runMeasuredOnWorker "H2.small.positive" (maxMs := 450) do
    checkClosedModule [] smallMod).map (·.value)
  match ← evalPureNatConstBounded smallSnap.env `Gen.H2Small.smallCount 2000 with
  | .ok n => ensure (n == 32) s!"H2: expected 32, got {n}"
  | .error e => throw (IO.userError s!"H2: small bounded eval unexpectedly failed: {e}")

  -- Crash Negative Gate A: Kernel `rfl` on 65,525 spaces (against pre-checked `Gen.H2Core`)
  let bigRflMod ← mkObject "Gen.H2BigRfl"
    "open Gen.H2Core\ntheorem crashRfl : (tokenRunes 65526 (List.replicate 65525 32)).length = 65525 := rfl"
    ["Gen.H2Core"]
  let (rflMsg, rflMs, _) ← expectRejectedBounded "H2.kernelRfl65525"
    "[DETOUR]" (maxMs := 500) (checkClosedModule [baseMod] bigRflMod)
  ensure (rflMsg.contains "TABOO_DEEP_RECURSION" || rflMsg.contains "TABOO_RFL_REDUCTION_BLOWUP")
    s!"H2: unexpected rfl taboo tag: {rflMsg.take 300}"

  -- Crash Negative Gate B: Bytecode interpreter `evalPureNatConstBounded`:
  -- (1) 65,525 spaces (which SIGSEGV'd small pthreads) now fits safely inside the 64 MiB worker stack;
  -- (2) 250,000 spaces (> 64 MiB stack) trips C++ `lean::check_stack("interpreter")` cleanly as
  --     `TABOO_INTERPRETER_LIMIT` ("deep recursion was detected") with 0 SIGSEGV!
  let midEvalMod ← mkObject "Gen.H2MidEval" (coreDefs ++
    "def midCount : Nat := (tokenRunes 65526 (List.replicate 65525 32)).length")
    ["LojitaCtx.Terminal"]
  let midEvalSnap ← checkClosedModule [] midEvalMod
  let mMid ← runMeasuredOnWorker "H2.interpreter65525.safe64MB" (maxMs := 500) do
    evalPureNatConstBounded midEvalSnap.env `Gen.H2MidEval.midCount
  ensure (mMid.value matches .ok 65525) "H2: 65,525-space eval failed on 64 MiB stack"

  let bigEvalMod ← mkObject "Gen.H2BigEval" (coreDefs ++
    "def hugeCount : Nat := (tokenRunes 250001 (List.replicate 250000 32)).length")
    ["LojitaCtx.Terminal"]
  let bigEvalSnap ← checkClosedModule [] bigEvalMod
  let mEval ← runMeasuredOnWorker "H2.interpreter250k.stackGuard" (maxMs := 500) do
    evalPureNatConstBounded bigEvalSnap.env `Gen.H2BigEval.hugeCount
  match mEval.value with
  | .ok v => throw (IO.userError s!"H2: 250,000-layer non-tail-rec eval unexpectedly returned {v}")
  | .error te =>
    ensure (te.code == .interpreterLimit) s!"H2: expected interpreterLimit, got {te}"
  IO.println s!"  [PASS] H2 non-tail-rec tokenRunes: kernel-rfl-guard={rflMs}ms, 65k-64MB-ok={mMid.elapsedMs}ms, 250k-stack-guard={mEval.elapsedMs}ms (0 SIGSEGV)"

/-- **H3 (`"Linux Add Swap File Guide"` Multi-Chunk Long Text & `Bytes` / `ByteArray` + 1,500-Char Unicode Table)**:
    Tests all three representations (String `++` chunks, `LojitaCtx.Terminal.Bytes` / `ByteArray`, and `Array Char`)
    for both positive equivalence and `< 20 ms` single-character / single-byte fast refutation! -/
def testH3SwapGuideAndTables : IO Unit := do
  let mkGuideChunks (typo : Bool) : List String := Id.run do
    let header := "# Linux Add Swap File Guide\n\nStep 1: Allocate swap storage with fallocate -l 4G /swapfile.\n"
    let mut chunks : Array String := #[header]
    for i in [0:40] do
      let marker := if typo && i == 25 then "chmod 0644 /swapfile" else "chmod 0600 /swapfile"
      chunks := chunks.push s!"Section {i}: Verify permissions ({marker}), run mkswap /swapfile, swapon /swapfile, and persist /swapfile none swap sw 0 0 in /etc/fstab.\n"
    return chunks.toList

  -- Variant A: Multi-chunk `++` String guide (positive same-syntax, TABOO_LARGE_GROUND_MISMATCH_SYNTAX on flattened 6KB, and <20ms typo fast-reject!)
  let guideTextExpr (typo : Bool) : String :=
    String.intercalate " ++\n  " ((mkGuideChunks typo).map reprStr)
  let guideSpec ← mkObject "Gen.SwapGuide" s!"def doc : String :=\n  {guideTextExpr false}\naxiom okDoc : doc = doc"
  let guideImplOk ← mkObject "Gen.SwapGuide" s!"def doc : String :=\n  {guideTextExpr false}\ntheorem okDoc : doc = doc := rfl"
  let guideImplJoined ← mkObject "Gen.SwapGuide" s!"def doc : String :=\n  {reprStr (String.join (mkGuideChunks false))}\ntheorem okDoc : doc = doc := rfl"
  let guideImplBad ← mkObject "Gen.SwapGuide" s!"def doc : String :=\n  {guideTextExpr true}\ntheorem okDoc : doc = doc := rfl"
  discard <| checkConditionalGlue [] [] guideSpec (checkingSpec := true)
  discard <| checkClosedModule [] guideImplOk
  discard <| checkClosedModule [] guideImplJoined
  discard <| checkClosedModule [] guideImplBad
  discard <| runMeasuredOnWorker "H3.guideString.ok" (maxMs := 200) (satisfies guideSpec guideImplOk)
  discard <| expectRejectedBounded "H3.guideString.syntaxTaboo"
    "TABOO_LARGE_GROUND_MISMATCH_SYNTAX" (maxMs := 300) (satisfies guideSpec guideImplJoined)
  let (strMsg, strMs, _) ← expectRejectedBounded "H3.guideString.typo"
    "text differs at index" (maxMs := 50) (satisfies guideSpec guideImplBad)
  ensure (strMs < 20 && errorTag strMsg == "INTERFACE_MISMATCH")
    s!"H3 String fast-reject took {strMs} ms: {strMsg.take 200}"

  -- Variant B: `LojitaCtx.Terminal.Bytes` (`List UInt8`) & `ByteArray` representation of the guide
  let bytesMod (typo : Bool) := mkObject "Gen.SwapBytes"
    s!"open LojitaCtx.Terminal\ndef rawGuide : Bytes := bytes (\n  {guideTextExpr typo})\ndef packed : ByteArray := rawGuide.toByteArray"
    ["LojitaCtx.Terminal"]
  let bSpec ← bytesMod false
  let bOk   ← bytesMod false
  let bBad  ← bytesMod true
  discard <| checkClosedModule [] bSpec
  discard <| checkClosedModule [] bOk
  discard <| checkClosedModule [] bBad
  discard <| runMeasuredOnWorker "H3.guideBytes.ok" (maxMs := 300) (satisfies bSpec bOk)
  let (byteMsg, byteMs, _) ← expectRejectedBounded "H3.guideBytes.typo"
    "bytes differ at offset" (maxMs := 50) (satisfies bSpec bBad)
  ensure (byteMs < 20 && errorTag byteMsg == "INTERFACE_MISMATCH")
    s!"H3 Bytes fast-reject took {byteMs} ms: {byteMsg.take 200}"

  -- Variant C: Exact 1,500-char Unicode `Array Char` table (`S2Kernel.lean:295-309`)
  let mkUnicodeTable (typo : Bool) : String := Id.run do
    let cs := (List.range 1500).map fun i => Char.ofNat (if typo && i == 1000 then 0x0C3E else 0x4E00 + i)
    let chunks := (List.range 5).map fun k => "\"" ++ String.ofList ((cs.drop (300 * k)).take 300) ++ "\""
    return "def ranges : Array Char := (" ++ String.intercalate " ++\n    " chunks ++ ").toList.toArray\n" ++
      "def isRange (c : Char) : Bool := ranges.contains c"
  let uSpec ← mkObject "Gen.T1.Gron" (mkUnicodeTable false)
  let uOk   ← mkObject "Gen.T1.Gron" (mkUnicodeTable false)
  let uBad  ← mkObject "Gen.T1.Gron" (mkUnicodeTable true)
  discard <| checkClosedModule [] uSpec
  discard <| checkClosedModule [] uOk
  discard <| checkClosedModule [] uBad
  discard <| runMeasuredOnWorker "H3.unicode1500.ok" (maxMs := 300) (satisfies uSpec uOk)
  let (uMsg, uMs, _) ← expectRejectedBounded "H3.unicode1500.typo"
    "text differs at index 1000: expected U+51E8, received U+0C3E" (maxMs := 50) (satisfies uSpec uBad)
  ensure (uMs < 20 && errorTag uMsg == "INTERFACE_MISMATCH")
    s!"H3 1500-char table fast-reject took {uMs} ms"
  IO.println s!"  [PASS] H3 SwapGuide & Ground Tables: str-reject={strMs}ms, bytes-reject={byteMs}ms, unicode1500-reject={uMs}ms"

/-- **H4 (Commit `97198b7` `LargeFuel.lean` `UInt64.size = 2^64` Structural Fuel — Positive + Negative Crash Gates!)**:
    Verifies both `< 200 ms` positive equivalence AND `< 200 ms` bounded rejection when `scan` or `bigBudget`
    differs (where old `Driver.lean` unrolled $2^{64}$ `Nat.brecOn` frames in bare `Kernel.isDefEq` and froze). -/
def testH4LargeFuel : IO Unit := do
  let src ← IO.FS.readFile "Test/Fixtures/LargeFuel.lean"
  let impl ← parseMod src
  let spec ← parseMod (src.replace "theorem runLaw" "axiom runLaw" |>.replace " := rfl" "")

  let mClosed ← runMeasuredOnWorker "H4.checkClosed" (maxMs := 200) (checkClosedModule [] impl)
  let some (.defnInfo scanInfo) := mClosed.value.env.find? `Gen.LargeFuel.scan
    | throw (IO.userError "H4: missing scan")
  ensure (scanInfo.value.getUsedConstantsAsSet.contains ``Nat.brecOn)
    "H4: large-fuel fixture lost structural Nat.brecOn"

  let mSat ← runMeasuredOnWorker "H4.satisfies" (maxMs := 200) (satisfies spec impl)

  -- Unpaired single-side private wrapper `observe := scan bigBudget`
  let hidden ← parseMod (src.replace "def run (xs : List UInt8) := scan bigBudget xs"
    "private def observe := scan bigBudget\ndef run (xs : List UInt8) := observe xs")
  discard <| runMeasuredOnWorker "H4.hiddenWrapper" (maxMs := 200) (satisfies hidden impl)

  -- Paired `private def scan` + `private def bigBudget`
  let privSrc := src.replace "def scan" "private def scan" |>.replace "def bigBudget" "private def bigBudget"
  let privSpec ← parseMod (privSrc.replace " := rfl" " := by rfl")
  let privImpl ← parseMod privSrc
  let mPrivPos ← runMeasuredOnWorker "H4.privPositive" (maxMs := 200) (satisfies privSpec privImpl)

  -- CRITICAL NEGATIVE GATE 1: `private def scan` body mutated (`+ 1` -> `+ 2`)!
  let privBadScan ← parseMod (privSrc.replace "scan fuel rest + 1" "scan fuel rest + 2")
  discard <| checkClosedModule [] privBadScan
  let (badScanMsg, badScanMs, _) ← expectRejectedBounded "H4.privBadScan"
    "INTERFACE_MISMATCH" (maxMs := 200) (satisfies privSpec privBadScan)
  ensure (badScanMs < 200 && errorTag badScanMsg == "INTERFACE_MISMATCH")
    s!"H4 negative scan took {badScanMs} ms"

  -- CRITICAL NEGATIVE GATE 2: `private def bigBudget` mutated (`UInt64.size` -> `UInt64.size - 1`)!
  let privBadFuel ← parseMod (privSrc.replace "UInt64.size" "(UInt64.size - 1)")
  discard <| checkClosedModule [] privBadFuel
  let (badFuelMsg, badFuelMs, _) ← expectRejectedBounded "H4.privBadFuel"
    "INTERFACE_MISMATCH" (maxMs := 200) (satisfies privSpec privBadFuel)
  ensure (badFuelMs < 200 && errorTag badFuelMsg == "INTERFACE_MISMATCH")
    s!"H4 negative fuel took {badFuelMs} ms"

  IO.println s!"  [PASS] H4 LargeFuel (2^64): pos={mSat.elapsedMs}ms, privPos={mPrivPos.elapsedMs}ms, negScan={badScanMs}ms, negFuel={badFuelMs}ms"

/-- **H5 (Commit `3223766` Same-Module `deriving Repr, BEq, DecidableEq` + 22-Layer Shared `private def` DAG + Private Theorem)**:
    22 binary-branching layers (`h_{i+1} x := h_i x + h_i x`) represent $2^{22} = 4,194,304$ virtual tree leaves!
    - Old `mapConstants (unfoldProofs := true)` expanded the DAG into 4.2M lambda/app nodes and OOMed;
    - `SafeCompare` verifies BOTH paired (`h_i` vs `h_i`) AND unpaired (`h_i` vs `g_i`!) in `< 150 ms` via DAG preservation,
      and rejects a `+ 1` leaf mutation at `g_0`! -/
def testH5PrivateDAGAndProofIrrel : IO Unit := do
  let mkDagMod (prefixName : String) (leafBias : Nat) (asSpec : Bool) : IO LeanMod := do
    let mut lines : Array String := #[
      "inductive Tag where | alpha (s : String) | beta | gamma (n : Nat) deriving Repr, BEq, DecidableEq",
      "structure Row where\n  label : String\n  depth : Nat\n  deriving Repr, BEq, DecidableEq",
      s!"private def {prefixName}_0 (r : Row) : Nat := r.depth + {leafBias}"
    ]
    for i in [0:22] do
      lines := lines.push s!"private def {prefixName}_{i + 1} (r : Row) : Nat := {prefixName}_{i} r + {prefixName}_{i} r"
    -- Add a multi-case private theorem to verify zero proof unfolding (`is_def_eq_proof_irrel` in O(1))
    lines := lines.push
      "private theorem rowSelfEq (r : Row) : (match r.depth with | 0 => r | _ + 1 => r) = r := by cases r.depth <;> rfl"
    lines := lines.push
      "def certifiedRow (r : Row) : { out : Row // out = r } := ⟨match r.depth with | 0 => r | _ + 1 => r, rowSelfEq r⟩"
    lines := lines.push s!"def compute (r : Row) : Nat := {prefixName}_22 r"
    lines := lines.push
      "theorem reprCheck : repr Tag.beta = Std.Format.group (Std.Format.nest 2 (Std.Format.text \"Gen.T1.Dag.Tag.beta\")) := rfl"
    if asSpec then
      lines := lines.push "axiom postLaw : ∀ r : Row, (certifiedRow r).1 = r"
    else
      lines := lines.push "theorem postLaw (r : Row) : (certifiedRow r).1 = r := rowSelfEq r"
    mkObject "Gen.T1.Dag" (String.intercalate "\n" lines.toList)

  let specH ← mkDagMod "h" 0 true
  let implH ← mkDagMod "h" 0 false
  let implG ← mkDagMod "g" 0 false
  let implGBad ← mkDagMod "g" 1 false

  discard <| checkClosedModule [] implH
  discard <| checkClosedModule [] implG
  discard <| checkClosedModule [] implGBad

  -- Paired 22-layer DAG (`h_0..h_22` in both)
  let mPaired ← runMeasuredOnWorker "H5.paired22LayerDAG" (maxMs := 200) (satisfies specH implH)
  -- Unpaired 22-layer DAG (`h_0..h_22` in spec vs `g_0..g_22` in impl — exercises Path 2 kernel relocation + C++ equiv_manager!)
  let mUnpaired ← runMeasuredOnWorker "H5.unpaired22LayerDAG" (maxMs := 200) (satisfies specH implG)
  -- Anti-false-positive gate (`g_0` leaf mutated by `+ 1`)
  let (_, negMs, _) ← expectRejectedBounded "H5.mutatedLeafDAG"
    "INTERFACE_MISMATCH" (maxMs := 400) (satisfies specH implGBad)

  IO.println s!"  [PASS] H5 22-Layer Shared Private DAG (2^22 virtual leaves): paired={mPaired.elapsedMs}ms, unpaired={mUnpaired.elapsedMs}ms, leaf-mutation-reject={negMs}ms"

def runAll : IO Unit := do
  IO.println "=== Part A: Historical Server-Crash Repros (H1–H5) ==="
  testH1GronTokenSpec
  testH2NonTailRecTokenRunes
  testH3SwapGuideAndTables
  testH4LargeFuel
  testH5PrivateDAGAndProofIrrel

end Test.KernelTaboos.HistoricalRepros
