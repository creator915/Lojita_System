import Test.KernelTaboos.Harness

namespace Test.KernelTaboos.SoundnessGates
open Lojita.Store Lojita.Kernel Lean Test.KernelTaboos

namespace AxiomGuardKernelFixture

private unsafe def uncheckedFn (n : Nat) := n
private def helperCode (n : Nat) := n
@[implemented_by helperCode] private def overriddenOp (n : Nat) := n
private def callsOverridden : Nat := overriddenOp 1
@[export lojita_sneaky_c_symbol] def exportedOp (n : Nat) : Nat := n + 1

-- Directly exercise kernel-level `AxiomGuard` (including the new `@[export]` check!)
run_meta
  for (n, code) in [
    (``uncheckedFn, "UNSAFE_VIOLATION"),
    (``getObjTagNat, "UNSAFE_VIOLATION"),
    (``callsOverridden, "NATIVE_OVERRIDE_VIOLATION"),
    (``exportedOp, "NATIVE_OVERRIDE_VIOLATION")
  ] do
    match collectRootAxioms (← getEnv) #[n] with
    | .ok _ => throwError "AxiomGuard accepted forbidden constant {n}"
    | .error e =>
      unless (e.splitOn ":").head! == code do
        throwError "expected {code} on {n}, got {e}"

end AxiomGuardKernelFixture

def testCodecAndIterativeSpans : IO Unit := do
  -- 20,000-deep S-expression roundtrip via iterative parser & iterative printer (< 200 ms, 0 stack overflow!)
  let deep := (List.range 20000).foldl (fun v _ => SExpr.list [v]) (.str "雪\n\"\\")
  let mCodec ← runMeasuredOnWorker "Soundness.SExpr20k" (maxMs := 250) do
    let encoded := SExpr.canonical deep
    let some decoded := SExpr.parseSExpr encoded | throw (IO.userError "deep SExpr parse failed")
    ensure (SExpr.canonical decoded == encoded) "deep SExpr canonical mismatch"
  let crlf ← parseMod "namespace CRLF\r\ndef n := 42 -- 尾\r\ntheorem t : n = 42 := by\r\n  rfl\r\nend CRLF"
  ensure (crlf.units.head!.rawSource == "def n := 42 -- 尾" &&
    crlf.units[1]!.rawSource.contains "by\r\n  rfl") "CRLF iterative span restoration failed"
  IO.println s!"  [PASS] S1 Iterative S-Expr 20k-Depth Codec & CRLF Spans ({mCodec.elapsedMs}ms)"

def testGluingQuotientAndSecurity : IO Unit := do
  -- Conditional gluing & diamond dependency
  let spec ← mkObject "Gen.T1.Root.Child"
    "structure Box where\n  value : Nat\ndef zero : Box := ⟨0⟩\naxiom measure : Box → Nat\naxiom atZero : measure zero = 0"
  let child ← mkObject "Gen.T1.Root.Child"
    "structure Box where\n  value : Nat\ndef zero : Box := ⟨0⟩\ndef measure (x : Box) := x.value\ntheorem atZero : measure zero = 0 := rfl"
  let root ← mkObject "Gen.T1.Root"
    "open Gen.T1.Root.Child\ndef computed := measure zero\ntheorem answer : computed = 0 := atZero"
    ["Gen.T1.Root.Child"]
  let annotated := withChildIfaces root [spec]
  let stage ← checkConditionalGlue [] [stubOf spec] annotated
  ensure (stage.axioms.contains `Gen.T1.Root.Child.atZero) "missing staged axiom"
  satisfies spec child
  let finalSnap ← checkClosedModule [child] root
  ensure (finalSnap.axioms.all trustedBaseAxioms.contains) "sealed module retained staged axiom"
  expectErrorCode "DISALLOWED_AXIOM_VIOLATION" (checkClosedModule [spec] root)

  -- Option.casesOn vs match_1 + Certified proof irrelevance + private inductive nominal check
  let optSpec ← mkObject "Gen.Opt"
    "def port (s : Option Nat) : Nat := match s with | some n => n | none => 80"
  let optCases ← mkObject "Gen.Opt"
    "def port (s : Option Nat) : Nat := Option.casesOn (motive := fun _ => Nat) s 80 (fun n => n)"
  satisfies optSpec optCases

  let certNamed ← mkObject "Certified"
    "structure Box where\n  n : Nat\nprivate theorem certifies (x : Box) : x = x := rfl\ndef tag (x : Box) : { y : Box // y = x } := ⟨x, certifies x⟩"
  let certInline ← mkObject "Certified"
    "structure Box where\n  n : Nat\ndef tag (x : Box) : { y : Box // y = x } := ⟨x, rfl⟩"
  eqIface certNamed certInline

  let hiddenNat ← mkObject "DataSpec"
    "private inductive Hidden where | make (x : Nat)\ndef Carrier := Hidden\ndef head : Carrier := Hidden.make 7"
  let hiddenCopy := requalify hiddenNat.modName (q "DataImpl") hiddenNat
  satisfies hiddenNat hiddenCopy
  let hiddenBool ← mkObject "DataImpl"
    "private inductive Hidden where | make (x : Bool)\ndef Carrier := Hidden\ndef head : Carrier := Hidden.make true"
  expectErrorCode "INTERFACE_MISMATCH" (satisfies hiddenNat hiddenBool)

  -- Structure vs Inductive nominal distinction
  let asStruct ← mkObject "Gen.PairMod" "structure Pair where\n  fst : Nat\n  snd : Nat"
  let asInduct ← mkObject "Gen.PairMod" "inductive Pair where\n  | mk (fst : Nat) (snd : Nat)"
  expectErrorCode "INTERFACE_MISMATCH" (satisfies asStruct asInduct)
  expectErrorCode "INTERFACE_MISMATCH" (satisfies asInduct asStruct)

  -- Universe polymorphism arities & ordering
  let uFirst ← mkObject "Universes" "axiom carrier.{u,v} : Type u → Type v → Type u"
  let uSecond ← mkObject "Universes" "def carrier.{a,b} (_ : Type a) (β : Type b) : Type b := β"
  expectErrorCode "INTERFACE_MISMATCH" (satisfies uFirst uSecond)

  -- Boundary & Security checks (including reserved prelude root namespaces Nat / String / ByteArray!)
  for badNs in ["Lojita.Evil", "Gen.Unsafe.Foo", "LojitaCtx.Fake", "Nat.Spoof", "String.Spoof", "ByteArray.Spoof"] do
    expectSyntaxCode "forbiddenNamespace" s!"namespace {badNs}\nend {badNs}"
  for (code, body) in [
    ("hasSorrySyntax", "theorem t : True := by sorry"),
    ("forbiddenUnsafe", "unsafe def f := 1"),
    ("forbiddenNoncomputable", "noncomputable def f : Nat := Classical.choice inferInstance"),
    ("forbiddenPartial", "partial def f (n : Nat) : Nat := f n"),
    ("forbiddenNativeOverride", "@[extern \"c_fn\"] def f := 1"),
    ("forbiddenNativeOverride", "@[implemented_by f] def g := 1"),
    ("forbiddenNativeOverride", "@[export sneaky_sym] def f := 1"),
    ("forbiddenMetaprogramming", "#eval 1"),
    ("forbiddenMetaprogramming", "theorem t : 1 = 1 := by native_decide"),
    ("namespaceBoundary", "def _root_.escape := 1")
  ] do
    expectSyntaxCode code s!"namespace Gen.Bad\n{body}\nend Gen.Bad"

  let sorryTerm ← mkObject "HiddenSorry" "def proof : False := sorryAx False false"
  expectErrorCode "SORRY_AXIOM_VIOLATION" (checkClosedModule [] sorryTerm)

  let classicalData ← mkObject "ClassicalData"
    "axiom assumption : True\ndef chosen : Nat := Classical.choice inferInstance"
  expectErrorCode "NONCOMPUTABLE_VIOLATION" (checkConditionalGlue [] [] classicalData true)

  -- Refutation check
  let badSpec ← mkObject "OpenSpec" "axiom impossible : 1 = 2"
  let witness ← mkObject "RefuteMod" "theorem boom : False := by have h := OpenSpec.impossible; cases h" ["OpenSpec"]
  let refSnap ← checkRefutation [] badSpec witness
  ensure (refSnap.axioms.contains `OpenSpec.impossible) "refutation lost target axiom footprint"

  IO.println "  [PASS] S2 Soundness, AxiomGuard (@[export]), Gluing, Polymorphism & Boundary Gates"

def testNativeCliAndReactiveBinaries : IO Unit := IO.FS.withTempDir fun dir => do
  let support ← mkObject "Gen.App.Shared" "def code : Nat := 23"
  let cli ← mkObject "Gen.App.Cli" r#"open LojitaCtx.Posix
def app : PosixMachine CoreCaps Unit UInt32 where
  init := ()
  step _ :=
    .step .clockGettime (by decide) fun _ =>
    .step .getArgs (by decide) fun
      | .ok args =>
        let msg := (String.intercalate "|" (args.map (fun arg => LojitaCtx.Utf8.decodeLossy arg))).toUTF8
        .step (.write 1 (msg ++ "\n".toUTF8)) (show Cap.fdIoCap ∈ CoreCaps from by decide) fun _ =>
        .step (.write 2 "cli stderr\n".toUTF8) (by decide) fun _ =>
        .step (.openat none "payload".toUTF8.data.toList {access := .writeOnly, create := true, trunc := true} 0o600) (by decide) fun
          | .ok fd => .step (.write fd msg) (show Cap.fdIoCap ∈ CoreCaps from by decide) fun _ =>
              .step (.close fd) (show Cap.fdIoCap ∈ CoreCaps from by decide) fun _ => .pure (.inr Gen.App.Shared.code.toUInt32)
          | _ => .pure (.inr 99)
      | _ => .pure (.inr 98)"#
    ["LojitaCtx.Posix.Program", "LojitaCtx.Utf8", "Gen.App.Shared"]
  let react ← mkObject "Gen.App.Reactive" r#"open LojitaCtx.Posix
def app : PosixMachine CoreCaps UInt32 UInt32 where
  init := 30
  step n := .pure (if n < 31 then .inl (n + 1) else .inr n)
def wrongCaps : PosixMachine [] Unit UInt32 := ⟨(), fun _ => .pure (.inr 0)⟩"# ["LojitaCtx.Posix.Program"]
  let cliBin := dir / "cli"
  let reactBin := dir / "reactive"
  expectErrorCode "ENTRY_TYPE_MISMATCH" (compileVerifiedExe [react] (q "Gen.App.Reactive.wrongCaps") cliBin)
  compileVerifiedExe [cli, support] (q "Gen.App.Cli.app") cliBin
  compileVerifiedExe [react] (q "Gen.App.Reactive.app") reactBin

  let runDir := dir / "cli-run"
  IO.FS.createDir runDir
  let r1 ← IO.Process.output { cmd := cliBin.toString, args := #["雪", "two words"], cwd := runDir }
  ensure (r1.exitCode == 23 && r1.stdout == "雪|two words\n" && r1.stderr == "cli stderr\n")
    s!"CLI execution failed: exit={r1.exitCode}, out={repr r1.stdout}"
  ensure ((← IO.FS.readFile (runDir / "payload")) == "雪|two words") "CLI payload mismatch"

  let reactDir := dir / "reactive-run"
  IO.FS.createDir reactDir
  let r2 ← IO.Process.output { cmd := reactBin.toString, cwd := reactDir }
  ensure (r2.exitCode == 31 && r2.stdout == "" && r2.stderr == "")
    s!"Reactive execution failed: exit={r2.exitCode}"
  IO.println "  [PASS] S3 End-to-End Native CLI & Reactive Binaries"

def runAll : IO Unit := do
  IO.println "=== Part C: Soundness, Boundary, Codec & Native Linker Gates ==="
  testCodecAndIterativeSpans
  testGluingQuotientAndSecurity
  testNativeCliAndReactiveBinaries

end Test.KernelTaboos.SoundnessGates
