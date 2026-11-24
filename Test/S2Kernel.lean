import Lojita.Kernel.Driver

namespace Test.S2Kernel
open Lojita.Store Lojita.Kernel Lean

namespace GuardFixture

private unsafe def unchecked (n : Nat) := n
private def machineCode (n : Nat) := n
@[implemented_by machineCode] private def operation (n : Nat) := n
private def usesOperation : Nat := operation 1

-- Exercise the kernel inspector independently of the surface scanner.
run_meta
  for (n, code) in [(``unchecked, "UNSAFE_VIOLATION"), (``getObjTagNat, "UNSAFE_VIOLATION"),
      (``usesOperation, "NATIVE_OVERRIDE_VIOLATION")] do
    match collectRootAxioms (← getEnv) #[n] with
    | .ok _ => throwError "guard accepted {n}"
    | .error e => unless (e.splitOn ":").head! == code do throwError "expected {code}, got {e}"

end GuardFixture

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def parse (s : String) : IO LeanMod := IO.ofExcept (parseLeanMod s)

private def object (n body : String) (imports : List String := []) : IO LeanMod :=
  parse (String.intercalate "\n" ((imports.map ("import " ++ ·)) ++
    ["namespace " ++ n, body, "end " ++ n]))

private def q (s : String) : QName := ⟨s.splitOn "."⟩

private def tag (message : String) := (message.splitOn ":").head!

private def expectCode {α : Type} (expected : String) (act : IO α) : IO Unit := do
  let failure ← try
    discard act
    pure none
  catch e => pure (some (toString e))
  let some message := failure | throw (IO.userError s!"accepted input requiring {expected}")
  ensure (tag message == expected) s!"expected {expected}, received {message}"

private def syntaxCode (expected src : String) : IO Unit := do
  match readEnvelope src with
  | .ok _ => throw (IO.userError s!"accepted input requiring {expected}: {src}")
  | .error e => ensure (e.code == expected) s!"expected {expected}, received {e}\n{src}"

private def codec : IO Unit := do
  let deep := (List.range 20000).foldl (fun v _ => SExpr.list [v]) (.str "雪\n\"\\")
  let begin ← IO.monoNanosNow
  let encoded := SExpr.canonical deep
  let some decoded := SExpr.parseSExpr encoded | throw (IO.userError "deep parse")
  let mut leaf := decoded
  for _ in [0:20000] do
    let .list [next] := leaf | throw (IO.userError "nested list depth")
    leaf := next
  ensure ((leaf matches .str "雪\n\"\\") && SExpr.canonical decoded == encoded) "deep roundtrip"
  let ms := ((← IO.monoNanosNow) - begin) / 1000000
  ensure (ms < 200) s!"20,000 nested lists took {ms} ms"
  let large := SExpr.str (String.ofList (List.replicate 524288 'λ'))
  let some (.str text) := SExpr.parseSExpr (SExpr.canonical large) | throw (IO.userError "1 MiB parse")
  ensure (text.utf8ByteSize == 1048576) "truncated 1 MiB atom"
  for bad in ["", "(a", "a b", ")", "\"\\q\""] do
    ensure (SExpr.parseSExpr bad).isNone s!"malformed S-expression {bad}"

  let draft ← object "DraftMod" "open LojitaCtx.World
abbrev Number := Nat
def foo : Number := 42
def DraftModule := \"DraftMod.foo\"
def double := DraftMod.foo + DraftMod.foo
structure Box where
  pack ::
  count : Nat
inductive Kind where
  | small | large
mutual
  def left (n : Nat) := n
  def right := DraftMod.foo
end
theorem preserved : DraftMod.foo = 42 := by
  -- DraftMod.foo stays in this comment
  rfl" ["LojitaCtx.World"]
  let m := requalify draft.modName (q "Gen.T1.App") draft
  let src := renderLeanMod m
  ensure (src.contains "Gen.T1.App.foo + Gen.T1.App.foo" && src.contains "\"DraftMod.foo\"" &&
    src.contains "-- DraftMod.foo stays" && src.contains "def DraftModule") "token requalification"
  ensure ((← parse src) == m && decodeCanonical (encodeCanonical m) == some m) "module roundtrip"
  let names := m.units.flatMap (·.definedNames)
  for n in ["Box.pack", "Box.count", "Kind.small", "Kind.large", "left", "right"] do
    ensure (names.contains (q ("Gen.T1.App." ++ n))) s!"missing declaration {n}"
  ensure ((m.units.find? (·.uname == q "Gen.T1.App.double")).any
    (·.synRefs.contains (q "Gen.T1.App.foo"))) "missing pre-elaboration edge"
  let crlf ← parse "namespace CRLF\r\ndef n := 42 -- 尾\r\ntheorem t : n = 42 := by\r\n  rfl\r\nend CRLF"
  ensure (crlf.units.head!.rawSource == "def n := 42 -- 尾" &&
    crlf.units[1]!.rawSource.contains "by\r\n  rfl") "CRLF byte spans and trailing comment"
  IO.println s!"1  Codec and surface morphisms ({ms} ms for 20,000 nested lists)"

private def gluing : IO Unit := do
  let spec ← object "Gen.T1.Root.Child" "structure Box where
  value : Nat
def zero : Box := ⟨0⟩
axiom measure : Box → Nat
axiom atZero : measure zero = 0"
  let child ← object "Gen.T1.Root.Child" "structure Box where
  value : Nat
def zero : Box := ⟨0⟩
def measure (x : Box) := x.value
theorem atZero : measure zero = 0 := rfl"
  let root ← object "Gen.T1.Root" "open Gen.T1.Root.Child
def computed := measure zero
theorem answer : computed = 0 := atZero" ["Gen.T1.Root.Child"]
  let annotated := withChildIfaces root [spec]
  ensure (annotated.imports.head!.assumes == spec.units &&
    decodeCanonical (encodeCanonical annotated) == some annotated) "child interfaces"
  ensure (annotated.units.head!.synRefs.contains (q "Gen.T1.Root.Child.measure")) "opened child edge"
  let stage ← checkConditionalGlue [] [stubOf spec] annotated
  ensure (stage.axioms.contains `Gen.T1.Root.Child.atZero) "staged footprint"
  ensure (stage.graph.semArrows.contains (.unit (q "Gen.T1.Root.computed"), .ext (q "Gen.T1.Root.Child.measure")))
    "kernel dependency edge"
  ensure (stage.graph.sorts.contains (q "Gen.T1.Root.answer", .law) &&
    stage.graph.sorts.contains (q "Gen.T1.Root.computed", .carrier)) "intrinsic sorts"
  let cs ← checkClosedModule [] child
  satisfies spec child
  let finalSnap ← checkClosedModule [child] root
  ensure (finalSnap.id != stage.id && finalSnap.axioms.all trustedBaseAxioms.contains) "open/closed cache collision"
  ensure ((← checkClosedModule [child] root).id == finalSnap.id &&
    (← checkClosedModule [] child).id == cs.id) "DAG cache missed an unchanged dependency"
  expectCode "DISALLOWED_AXIOM_VIOLATION" (checkClosedModule [spec] root)
  let t0 ← object "Gen.T0.Foo" "def answer := 40"
  let t1 ← object "Gen.T1.Foo" "def answer := Gen.T0.Foo.answer + 2" ["Gen.T0.Foo"]
  let side ← object "Gen.Side" "def answer := Gen.T0.Foo.answer + 1" ["Gen.T0.Foo"]
  let joinMod ← object "Gen.Join" "theorem both : Gen.T1.Foo.answer + Gen.Side.answer = 83 := rfl"
    ["Gen.Side", "Gen.T1.Foo"]
  let diamond ← checkClosedModule [t1, t0, side] joinMod
  ensure ((diamond.env.find? `Gen.T0.Foo.answer).isSome && (diamond.env.find? `Gen.T1.Foo.answer).isSome)
    "ancestor namespace collision"
  let t0' ← object "Gen.T0.Foo" "def answer := 41"
  expectCode "ELABORATION_ERROR" (checkClosedModule [t1, side, t0'] joinMod)
  ensure ((← checkClosedModule [t0, side, t1] joinMod).id == diamond.id) "lost original diamond version"
  IO.println "2  Conditional child, closed implementation and sealed link"

private def concreteInterfaces : IO Unit := do
  let fetch := fun (port decoder : String) => object "Gen.Fetch" ("structure UserInfo where
  portText : Option String
  name : List UInt8
  password : Option (List UInt8)
def thePort (info : UserInfo) : Nat :=
  " ++ port ++ "
def base64 : List UInt8 → List Nat
  | [] => []
  | [a] => [a.toNat]
  | [a, b] => [a.toNat, b.toNat]
  | a :: b :: c :: rest => [a.toNat, b.toNat, c.toNat] ++ base64 rest
termination_by structural raw => raw
def basic (info : UserInfo) := base64 (info.name ++ [58] ++ info.password.getD [])
def quotedRune (c : Char) : Nat :=
  match c.toNat with
  | 7 => 0 | 8 => 1 | 9 => 2 | 34 => 3 | 92 => 4 | n => n
def quoted (s : String) := s.toList.map quotedRune
def prepare (target : Option (String × UserInfo)) : List Nat :=
  match target with
  | none => []
  | some (s, info) => thePort info :: (quoted s ++ basic info)
" ++ decoder ++ "
def urlPiece (raw : List UInt8) : Except String (List Nat) := do
  let decoded ← unescape raw
  return base64 decoded
def idPoly.{u} {α : Type u} (x : α) : α := match some x with | some y => y | none => x")
  let port := "match info.portText.bind String.toNat? with | some n => n | none => 80"
  let decoder := "private def unescapeInto : List UInt8 → List UInt8 → Except String (List UInt8)
  | [], acc => .ok acc.reverse
  | b :: rest, acc => unescapeInto rest (b :: acc)
def unescape (raw : List UInt8) := unescapeInto raw []"
  let spec ← fetch port "axiom unescape : List UInt8 → Except String (List UInt8)"
  let impl ← fetch port decoder
  satisfies spec impl
  let cases ← fetch "Option.casesOn (motive := fun _ => Nat)
    (info.portText.bind String.toNat?) 80 (fun n => n)" decoder
  satisfies spec cases
  let client ← object "Gen.Client" "def leak := Gen.Fetch.unescapeInto [] []" ["Gen.Fetch"]
  expectCode "ELABORATION_ERROR" (checkClosedModule [impl] client)
  expectCode "ELABORATION_ERROR" (checkConditionalGlue [impl] [] client)
  let cert := fun (helper proof : String) => object "Certified" ("structure Box where
  n : Nat
" ++ helper ++ "
def tag (x : Box) : { y : Box // y = x } := ⟨x, " ++ proof ++ "⟩")
  let named ← cert "private theorem certifies (x : Box) : x = x := rfl" "certifies x"
  let inlined ← cert "" "rfl"
  eqIface named inlined
  let helpers ← object "Helpers" "def helper := 1\ndef answer := helper"
  let inlineAnswer ← object "Helpers" "def helper := 1\ndef answer := 1"
  satisfies helpers inlineAnswer

private def largeFuel : IO Unit := do
  let src ← IO.FS.readFile "Test/S2/LargeFuel.lean"
  let impl ← parse src
  let spec ← parse (src.replace "theorem runLaw" "axiom runLaw" |>.replace " := rfl" "")
  let start ← IO.monoNanosNow
  let snap ← checkClosedModule [] impl
  let closed := ((← IO.monoNanosNow) - start) / 1000000
  ensure (closed < 200) s!"checkClosedModule on large fuel took {closed} ms"
  let some (.defnInfo scan) := snap.env.find? `Gen.LargeFuel.scan | throw (IO.userError "missing scan")
  ensure (scan.value.getUsedConstantsAsSet.contains ``Nat.brecOn) "large-fuel fixture lost structural recursion"
  let start ← IO.monoNanosNow
  satisfies spec impl
  let sat := ((← IO.monoNanosNow) - start) / 1000000
  ensure (sat < 200) s!"satisfies on large fuel took {sat} ms"
  let hidden ← parse (src.replace "def run (xs : List UInt8) := scan bigBudget xs"
    "private def observe := scan bigBudget\ndef run (xs : List UInt8) := observe xs")
  satisfies hidden impl
  let privateScan := src.replace "def scan" "private def scan" |>.replace "def bigBudget" "private def bigBudget"
  let start ← IO.monoNanosNow
  satisfies (← parse (privateScan.replace " := rfl" " := by rfl")) (← parse privateScan)
  let hiddenMs := ((← IO.monoNanosNow) - start) / 1000000
  ensure (hiddenMs < 200) s!"satisfies on private structural fuel took {hiddenMs} ms"
  IO.println s!"   Large structural fuel took {closed} ms for checkClosedModule, {sat} ms for satisfies, {hiddenMs} ms with a private scan"

private def constructorIndices : IO Unit := do
  let base ← object "Gen.Base" "inductive Command where
  | start | stop | read (n : Nat) | write (n : Nat) | help"
  let upper ← object "Gen.Upper" "open Gen.Base
def count (cmd : Command) : Nat := by
  cases cmd with
  | start | stop | help => exact 0
  | read n | write n => exact n
theorem distinct (h : Command.read x = .write y) : False := by contradiction
theorem injective (h : Command.read x = .read y) : x = y := by injection h" ["Gen.Base"]
  let snap ← checkClosedModule [base] upper
  ensure (snap.owners.find? `Gen.Base.Command.ctorIdx == some (q "Gen.Base.Command"))
    "generated constructor index lost its inductive owner"
  satisfies base (requalify base.modName (q "Gen.BaseCopy") base)
  discard <| checkClosedModule [] (← object "Gen.Empty" "inductive Command : Type where")

/-- Same-module comparisons relocate the checked spec image at the kernel level.
    Re-elaborating it under a temporary name would let `deriving Repr` embed
    that name in its constructor labels. -/
private def sameModuleDerived : IO Unit := do
  let body := fun (extra : String) => "inductive Literal where
  | atom (s : String) | array | nested (xs : List Nat)
  deriving Repr, BEq, DecidableEq
structure Row where
  key : String
  depth : Nat
  deriving Repr, BEq, DecidableEq
private inductive Mark where
  | open_ | close_
  deriving Repr, BEq, DecidableEq
private def markCount (m : Mark) : Nat := match m with | .open_ => 1 | .close_ => 2
def total (r : Row) : Nat := r.depth + markCount .open_ + r.key.length
def render (l : Literal) : String := reprStr l
theorem reprLaw : repr Literal.array =
    Std.Format.group (Std.Format.nest 2 (Std.Format.text \"Gen.T1.Gron.Literal.array\")) := rfl
theorem rowLaw (r : Row) : decide (r = r) = true := decide_eq_true rfl
" ++ extra
  let spec ← object "Gen.T1.Gron" (body "axiom tail : Row → Nat\naxiom tailLaw : ∀ r, tail r = r.depth")
  let impl ← object "Gen.T1.Gron" (body "def tail (r : Row) : Nat := r.depth\ntheorem tailLaw : ∀ r, tail r = r.depth := fun _ => rfl")
  let start ← IO.monoNanosNow
  satisfies spec impl
  let ms := ((← IO.monoNanosNow) - start) / 1000000
  -- Repeated calls see the same relocation; no moving-target interface name.
  satisfies spec impl
  satisfies spec impl [] .subspec
  eqIface (← object "Gen.T1.Gron" (body "")) (← object "Gen.T1.Gron" (body ""))
  -- A child stub imported below the parent's prefix keeps its own names.
  let childSpec ← object "Gen.T1.Gron.Lines" "structure Line where
  text : String
  deriving Repr, BEq, DecidableEq
axiom nextLine : String → Option Line"
  let withChild := fun (extra : String) => do
    let m ← object "Gen.T1.Gron" ("open Gen.T1.Gron.Lines
inductive Literal where
  | atom (s : String) | array
  deriving Repr, BEq, DecidableEq
def first (s : String) : Option Line := nextLine s
theorem reprLaw : repr Literal.array =
    Std.Format.group (Std.Format.nest 2 (Std.Format.text \"Gen.T1.Gron.Literal.array\")) := rfl
" ++ extra) ["Gen.T1.Gron.Lines"]
    return withChildIfaces m [childSpec]
  satisfies (← withChild "axiom count : Nat") (← withChild "def count : Nat := 3") [] .closedImplOK [stubOf childSpec]
  -- Structure flags still compare faithfully after relocation.
  let asStruct ← object "Gen.T1.Gron" "structure Pair where\n  fst : Nat\n  snd : Nat\n  deriving Repr, BEq, DecidableEq"
  let asInduct ← object "Gen.T1.Gron" "inductive Pair where\n  | mk (fst : Nat) (snd : Nat)\n  deriving Repr, BEq, DecidableEq"
  expectCode "INTERFACE_MISMATCH" (satisfies asStruct asInduct)
  expectCode "INTERFACE_MISMATCH" (satisfies asInduct asStruct)
  -- String literals are still compared exactly.
  let manual := fun (label : String) => object "Gen.T1.Gron" ("inductive Literal where
  | atom (s : String) | array
def manualRepr : Repr Literal :=
  ⟨fun l _ => match l with | .atom _ => \"atom\" | .array => \"" ++ label ++ "\"⟩")
  satisfies (← manual "array") (← manual "array")
  expectCode "INTERFACE_MISMATCH" (satisfies (← manual "array") (← manual "Array"))
  -- A one-codepoint typo in a long literal table is refuted structurally, not
  -- by kernel unfolding, and the diagnostic names the codepoints.
  let table := fun (typo : Bool) => Id.run do
    let cs := (List.range 1500).map fun i => Char.ofNat (if typo && i == 1000 then 0x0C3E else 0x4E00 + i)
    let chunks := (List.range 5).map fun k => "\"" ++ String.ofList ((cs.drop (300 * k)).take 300) ++ "\""
    return "def ranges : Array Char := (" ++ String.intercalate " ++\n    " chunks ++ ").toList.toArray\n" ++
      "def isRange (c : Char) : Bool := ranges.contains c"
  let tStart ← IO.monoNanosNow
  satisfies (← object "Gen.T1.Gron" (table false)) (← object "Gen.T1.Gron" (table false))
  let failure ← try
      satisfies (← object "Gen.T1.Gron" (table false)) (← object "Gen.T1.Gron" (table true))
      pure none
    catch e => pure (some (toString e))
  let tableMs := ((← IO.monoNanosNow) - tStart) / 1000000
  let some msg := failure | throw (IO.userError "accepted a one-codepoint table typo")
  ensure (tag msg == "INTERFACE_MISMATCH" &&
    msg.contains "text differs at index 1000: expected U+51E8, received U+0C3E") s!"table diagnostic {msg.take 400}"
  IO.println s!"   Same-module derived Repr/BEq/DecidableEq interface relocated at the kernel level ({ms} ms); 1500-char table typo refuted in {tableMs} ms"

private def quotient : IO Unit := do
  let spec ← object "Specification" "axiom rev_involutive : ∀ {α : Type} (xs : List α), List.reverse (List.reverse xs) = xs
axiom add_comm_law : ∀ (a b : Nat), a + b = b + a"
  let impl ← object "Gen.Laws" "theorem rev_involutive {β : Type} (xs : List β) : xs.reverse.reverse = xs := by simp
theorem add_comm_law (x y : Nat) : x + y = y + x := by omega"
  satisfies spec impl
  let poly ← object "Polymorphic" "axiom rev_involutive.{u} : ∀ {α : Type u} (xs : List α), xs.reverse.reverse = xs"
  let bare ← object "DraftLaws" "theorem rev_involutive (xs : List β) : xs.reverse.reverse = xs := by simp"
  satisfies poly bare
  let mono ← object "Monomorphic" "axiom rev_involutive : ∀ {α : Type} (xs : List α), xs.reverse.reverse = xs"
  expectCode "INTERFACE_MISMATCH" (satisfies mono bare)
  let first ← object "Universes" "axiom carrier.{u,v} : Type u → Type v → Type u"
  let second ← object "Universes" "def carrier.{a,b} (_ : Type a) (β : Type b) : Type b := β"
  expectCode "INTERFACE_MISMATCH" (satisfies first second)
  let untyped ← object "NoBinderType" "axiom add_comm_law : ∀ a b, a + b = b + a"
  expectCode "ELABORATION_ERROR" (checkConditionalGlue [] [] untyped true)
  expectCode "INTERFACE_MISMATCH" (satisfies poly impl)
  let narrowed ← object "Narrowed" "axiom rev_involutive : ∀ {α : Type} (xs : List α), xs.reverse.reverse = xs
axiom add_comm_law : ∀ (x y : Nat), Nat.succ x + y = y + x"
  expectCode "INTERFACE_MISMATCH" (satisfies spec narrowed [] .subspec)
  let helper ← object "Helper" "private def amount := 1
def answer := amount
axiom law : answer = 1"
  let changed ← object "Helper" "private def amount := 2
def answer := amount
axiom law : answer = 1"
  expectCode "INTERFACE_MISMATCH" (satisfies helper changed [] .subspec)
  let equiv ← object "Specs2" "def answer := Nat.succ 0
axiom law : answer = 1"
  eqIface helper equiv
  let tree ← object "DataSpec" "inductive T (α : Type) where | node (x : α)"
  let other ← object "DataImpl" "inductive T (β : Type) where | node (x : Nat)"
  expectCode "INTERFACE_MISMATCH" (satisfies tree other)
  let missing ← object "EmptyImpl" ""
  expectCode "INTERFACE_MISSING" (satisfies tree missing)
  let hiddenCarrier ← object "DataSpec" "private inductive Hidden where | make (x : Nat)
def Carrier := Hidden
def head : Carrier := Hidden.make 7"
  let copiedCarrier := requalify hiddenCarrier.modName (q "DataImpl") hiddenCarrier
  satisfies hiddenCarrier copiedCarrier
  let changedCarrier ← object "DataImpl" "private inductive Hidden where | make (x : Bool)
def Carrier := Hidden
def head : Carrier := Hidden.make true"
  expectCode "INTERFACE_MISMATCH" (satisfies hiddenCarrier changedCarrier)
  let tests ← object "WithLaws" "theorem two : 1 + 1 = 2 := rfl
example : True := by trivial"
  let blank ← object "WithoutLaws" ""
  let extended := withTests blank tests
  ensure ((withTests extended tests).units == extended.units && extended.units.length == 2) "withTests"
  discard <| checkClosedModule [] extended
  concreteInterfaces
  largeFuel
  constructorIndices
  sameModuleDerived
  IO.println "3  Kernel quotient, polymorphism, helper bodies and specification tests"

private def security : IO Unit := do
  let negatives := [
    ("hasSorrySyntax", "theorem t : True := by sorry"),
    ("hasSorrySyntax", "def n : Nat := sorry"),
    ("hasSorrySyntax", "theorem t : True := by admit"),
    ("forbiddenUnsafe", "unsafe def f := 1"),
    ("forbiddenNoncomputable", "noncomputable def f : Nat := Classical.choice inferInstance"),
    ("forbiddenPartial", "partial def f (n : Nat) : Nat := f n"),
    ("forbiddenNativeOverride", "@[extern \"x\"] def f := 1"),
    ("forbiddenNativeOverride", "@[implemented_by f] def g := 1"),
    ("forbiddenNativeOverride", "@[csimp] theorem t : True := True.intro"),
    ("forbiddenNativeOverride", "@[init f] def x := 0"),
    ("forbiddenNativeOverride", "@[Pervasive] def f := 1"),
    ("forbiddenNativeOverride", "initialize pure ()"),
    ("forbiddenNativeOverride", "builtin_initialize pure ()"),
    ("forbiddenMetaprogramming", "#eval 1"),
    ("forbiddenMetaprogramming", "#check Nat"),
    ("forbiddenMetaprogramming", "#print Nat"),
    ("forbiddenMetaprogramming", "#reduce 1"),
    ("forbiddenMetaprogramming", "#synth Inhabited Nat"),
    ("forbiddenMetaprogramming", "run_cmd pure ()"),
    ("forbiddenMetaprogramming", "elab \"objTerm\" : term => pure default"),
    ("forbiddenMetaprogramming", "macro \"objTerm\" : term => `(1)"),
    ("forbiddenMetaprogramming", "syntax \"objTerm\" : term"),
    ("forbiddenMetaprogramming", "elab_rules : term | `(true) => pure default"),
    ("forbiddenMetaprogramming", "macro_rules | `(true) => `(false)"),
    ("forbiddenMetaprogramming", "notation \"objTerm\" => 1"),
    ("forbiddenMetaprogramming", "infix:60 \" +++ \" => Nat.add"),
    ("forbiddenMetaprogramming", "infixl:60 \" +++ \" => Nat.add"),
    ("forbiddenMetaprogramming", "infixr:60 \" +++ \" => Nat.add"),
    ("forbiddenMetaprogramming", "prefix:70 \"Obj!\" => Nat.succ"),
    ("forbiddenMetaprogramming", "postfix:70 \"!Obj\" => Nat.succ"),
    ("forbiddenMetaprogramming", "local notation \"objTerm\" => 1"),
    ("forbiddenMetaprogramming", "attribute [simp] Nat.add_zero"),
    ("forbiddenMetaprogramming", "set_option autoImplicit false"),
    ("namespaceBoundary", "def _root_.outside := 1")]
  for (code, body) in negatives do syntaxCode code ("namespace Gen.Bad\n" ++ body ++ "\nend Gen.Bad")
  for name in ["Lean", "Lojita.WorldRunner", "Lojita.Kernel.Driver", "Init", "Gen.TrustMe.X"] do
    syntaxCode "forbiddenImport" ("import " ++ name ++ "\nnamespace Gen.Bad\nend Gen.Bad")
  for name in ["Lojita.Evil", "Gen.Unsafe.Foo", "LojitaCtx.Counterfeit"] do
    syntaxCode "forbiddenNamespace" ("namespace " ++ name ++ "\nend " ++ name)
  syntaxCode "namespaceEnvelope" "namespace Foo\nend Bar"
  let ax ← object "Open" "axiom postulate : False"
  expectCode "DISALLOWED_AXIOM_VIOLATION" (checkClosedModule [] ax)
  let hidden ← object "Hidden" "def proof : False := sorryAx False false"
  expectCode "SORRY_AXIOM_VIOLATION" (checkClosedModule [] hidden)
  let cast ← object "ClassicalData" "axiom assumption : True
def chosen : Nat := Classical.choice inferInstance"
  expectCode "NONCOMPUTABLE_VIOLATION" (checkConditionalGlue [] [] cast true)
  let anon ← object "Anonymous" "example : False := Open.postulate" ["Open"]
  let staged ← checkConditionalGlue [] [ax] anon
  ensure (staged.axioms.contains `Open.postulate) "anonymous example escaped the footprint audit"
  let claim ← object "Refute" "theorem wrong : True := by trivial"
  expectCode "REFUTATION_TARGET_MISMATCH" (checkRefutation [] ax claim)
  let vacuous ← object "Refute" "theorem wrong (h : False) : False := h"
  expectCode "REFUTATION_TARGET_MISMATCH" (checkRefutation [] ax vacuous)
  let missing ← object "Unlinked" "def n := 0" ["Gen.Missing"]
  expectCode "UNKNOWN_IMPORT" (checkClosedModule [] missing)
  let circular ← object "Cycle" "def n := 0" ["Cycle"]
  expectCode "IMPORT_CYCLE" (checkClosedModule [] circular)
  let noImport ← object "NoContext" "def c := LojitaCtx.World.Cap.clockCap"
  expectCode "UNDECLARED_IMPORT" (checkClosedModule [] noImport)
  IO.println "4  Surface, dependency, axiom and refutation boundary codes"

private def refutation : IO Unit := do
  let t0 ← object "Gen.T0.Gron" "def width := 1"
  let t1 ← object "Gen.T1.Gron" "def width := Gen.T0.Gron.width" ["Gen.T0.Gron"]
  let parser ← object "Gen.T2.Gron.Prefix" "mutual
  def parseWithin (cs : List Char) : Nat :=
    match cs with
    | [] => 0
    | c :: rest => if c == '[' then Gen.T1.Gron.width + parseGroup rest else parseWithin rest
  termination_by cs.length
  def parseGroup (cs : List Char) : Nat :=
    match cs with
    | [] => 0
    | c :: rest => if c == ']' then parseWithin rest else parseGroup rest
  termination_by cs.length
end" ["Gen.T1.Gron"]
  let spec ← object "Gen.T3.Gron" "axiom nonempty : Gen.T2.Gron.Prefix.parseWithin [] ≠ 0" ["Gen.T2.Gron.Prefix"]
  let witness ← object "GronRefutation" "theorem contradiction : False :=
  Gen.T3.Gron.nonempty (by simp [Gen.T2.Gron.Prefix.parseWithin])" ["Gen.T3.Gron"]
  let base ← checkClosedModule [t0, t1] parser
  ensure ((base.env.find? `Gen.T2.Gron.Prefix.parseWithin).any (· matches .defnInfo _)) "abstracted upstream parser"
  let start ← IO.monoNanosNow
  let snap ← checkRefutation [parser, t0, t1] (stubOf spec) witness
  let ms := ((← IO.monoNanosNow) - start) / 1000000
  ensure (ms < 200 && snap.axioms.contains `Gen.T3.Gron.nonempty &&
    snap.axioms.all (fun n => n == `Gen.T3.Gron.nonempty || trustedBaseAxioms.contains n))
    s!"first refutation took {ms} ms, footprint {snap.axioms.toList}"
  let strings ← object "NativeString" "theorem roundtrip (cs : List Char) : String.toList (String.ofList cs) = cs := by simp"
  discard <| checkClosedModule [] strings
  let target ← object "CountermodelCheck" "inductive VerifiedClaim : Prop where | verified"
  let claim ← object "Countermodel" "theorem witness : CountermodelCheck.VerifiedClaim := .verified" ["CountermodelCheck"]
  discard <| checkRefutation [target, parser, t1, t0] spec claim [`CountermodelCheck.VerifiedClaim]
  IO.println s!"5  Sealed T2 parser, first T3 refutation ({ms} ms) and native String law"

private def binaries : IO Unit := IO.FS.withTempDir fun dir => do
  let support ← object "Gen.App.Shared" "def code : Nat := 23"
  let cli ← object "Gen.App.Cli" "open LojitaCtx.World
def app : CliApp [.clockCap, .envCap, .stdioCap, .fsCap] := do
  let _ ← nowMonoW .here
  let args ← getArgsW (.there .here)
  let msg := String.intercalate \"|\" args
  writeStdoutStrW (.there (.there .here)) (msg ++ \"\\n\")
  writeStderrStrW (.there (.there .here)) \"cli stderr\\n\"
  let .inr () ← writeFileW (.there (.there (.there .here))) \"payload\" (LojitaCtx.Terminal.bytes msg) | return 99
  return Gen.App.Shared.code" ["LojitaCtx.World", "Gen.App.Shared"]
  let react ← object "Gen.App.Reactive" "open LojitaCtx.World
def app : ReactiveApp [.clockCap] Nat where
  init := pure 30
  onStep _ n := pure (if n < 31 then .inl (n + 1) else .inr n)" ["LojitaCtx.World"]
  let cliBin := dir / "cli"
  let reactiveBin := dir / "reactive"
  expectCode "ENTRY_TYPE_MISMATCH" (compileVerifiedExe [cli, support] (q "Gen.App.Cli.app") .reactive cliBin)
  compileVerifiedExe [cli, support] (q "Gen.App.Cli.app") .cli cliBin
  compileVerifiedExe [react] (q "Gen.App.Reactive.app") .reactive reactiveBin
  let runDir := dir / "cli-run"
  IO.FS.createDir runDir
  let r ← IO.Process.output {cmd := cliBin.toString, args := #["雪", "two words"], cwd := runDir}
  ensure (r.exitCode == 23 && r.stdout == "雪|two words\n" && r.stderr == "cli stderr\n")
    s!"CLI process: {r.exitCode} {repr r.stdout} {repr r.stderr}"
  ensure ((← IO.FS.readFile (runDir / "payload")) == "雪|two words" &&
    (← runDir.readDir).size == 1) "CLI file output"
  let reactDir := dir / "reactive-run"
  IO.FS.createDir reactDir
  let r ← IO.Process.output {cmd := reactiveBin.toString, cwd := reactDir}
  ensure (r.exitCode == 31 && r.stdout == "" && r.stderr == "" && (← reactDir.readDir).isEmpty)
    s!"reactive process: {r.exitCode} {repr r.stdout} {repr r.stderr}"
  IO.println "6  Native CLI and reactive programs, exit status, both streams and files"

def run : IO Unit := do
  codec
  preload
  try
    gluing
    quotient
    security
    refutation
    binaries
  finally close

end Test.S2Kernel

def main : IO Unit := Test.S2Kernel.run
