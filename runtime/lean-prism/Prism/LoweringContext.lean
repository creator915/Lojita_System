import Prism.LensSlice

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Shared scope, constructor and projection metadata for lowering scoped Agda commands. -/
namespace Prism

inductive EmitMode : Type where
  | pureFast
  | hybridCheck
  | erasedExec
  deriving Repr, BEq

structure RecMetaEntry : Type where
  recCanon : List String
  isCoind  : Bool
  constr   : Option String
  fields   : List (String × Expr)

abbrev DeferredFields := Std.HashMap (List String) (List Nat)

structure EmitCtx : Type where
  modPrefix    : List String
  mode         : EmitMode := .pureFast
  deferredFields : DeferredFields := {}
  instanceSlots : Std.HashMap (List String) (List (String × Bool)) := {}
  usesDepSigma : Bool := true
  symByCanon   : List (List String × SymInfo)
  sigImplicits    : List (List String × List String)  -- canonPath -> ordered implicit binder names
  recMeta         : List RecMetaEntry
  factoredEquations : List (List String) := []
  factoredWalks : List (List String) := []
  symIndex : Std.HashMap (List String) SymInfo := Std.HashMap.ofList symByCanon.reverse
  implicitIndex : Std.HashMap (List String) (List String) := Std.HashMap.ofList sigImplicits.reverse

def EmitCtx.withLocal (ctx : EmitCtx) (s : SymInfo) : EmitCtx :=
  { ctx with symByCanon := (s.canonPath,s) :: ctx.symByCanon, symIndex := ctx.symIndex.insert s.canonPath s }

private def allStdModules : List (List SymInfo) :=
  [ builtinNatExports, dataNatExports, dataNatPropsExports, dataNatShowExports, dataNatDivModExports
  , builtinIntExports, dataIntExports, dataIntPropsExports
  , builtinBoolExports, dataBoolExports, dataBoolPropsExports, builtinListExports, dataListExports
  , dataListPropsExports, dataListAnyExports, dataListAllExports
  , dataPermutationExports "Data.List.Relation.Binary.Permutation.Propositional"
  , dataPermutationExports "Data.List.Relation.Binary.Permutation.Propositional.Core"
  , dataMaybeExports, dataProductExports, dataSumExports, dataFinExports
  , dataCharExports, builtinCharPropsExports, dataCharPropsExports, builtinStringExports, dataStringExports, builtinStringPropsExports, dataStringPropsExports
  , dataUnitExports, dataPolyUnitExports
  , dataEmptyExports, relNullaryExports, decidableCoreExports, propEqExports, functionExports
  , blueprintExports, polyTransportExports, terminalExports, filterExports, tabooExports
  , clockExports, clockLawsExports, termLawsExports, fuzzGenExports
  , fsSandboxExports, fsLawsExports, netSandboxExports, netLawsExports
  , gitSandboxExports, gitLawsExports, webOperadExports
  , worldExports, worldLawsExports, protocolExports
  , ioExports, primIOExports, primFiniteIOExports, sysEnvExports, primSysEnvExports, ffiSafeExports, worldRunnerExports ]

/-- Select instance arguments in declaration order, including explicitly named
    arguments after an omitted instance. A true slot has no executable binder. -/
def projectInstances {α : Type} (slots : List (String × Bool)) (args : List (Arg α)) : List (Arg α) := Id.run do
  if slots.isEmpty then return args
  let mut i := 0
  let mut result := #[]
  for a in args do
    if a.hid == .inst then
      let j := (a.label >>= fun n => slots.findIdx? (fun s => s.1 == n)).getD i
      if let some (name, erased) := slots[j]? then
        i := j + 1
        unless erased do result := result.push {a with hid := .hidden, label := some name}
        continue
    result := result.push a
  return result.toList

private def stdImplicitNames : List (List String × List String) :=
  [ (["Agda", "Builtin", "Equality", "_≡_"], ["A"])
  , (["Relation", "Binary", "PropositionalEquality", "Core", "_≢_"], ["A"])
  , (["Agda", "Builtin", "Equality", "_≡_", "refl"], ["A", "x"])
  , (["Data", "List", "Properties", "_", "++-assoc"], ["A"])
  , (["Data", "List", "Properties", "_", "++-identityˡ"], ["A"])
  , (["Data", "List", "Properties", "_", "++-identityʳ"], ["A"])
  , (["Data", "Nat", "Base", "_≤_", "z≤n"], ["n"])
  , (["Data", "Nat", "Base", "_≤_", "s≤s"], ["m", "n"])
  , (["Data", "Nat", "Properties", "≤-trans"], ["i", "j", "k"])
  , (["Data", "Nat", "Properties", "<-irrefl"], ["i", "j"])
  , (["Relation", "Binary", "PropositionalEquality", "Core", "sym"], ["A", "x", "y"])
  , (["Relation", "Binary", "PropositionalEquality", "Core", "trans"], ["A", "x", "y", "z"])
  , (["Relation", "Binary", "PropositionalEquality", "Core", "cong"], ["A", "B"])
  , (["Relation", "Binary", "PropositionalEquality", "Core", "cong₂"], ["A", "B", "C"])
  , (["Relation", "Binary", "PropositionalEquality", "Core", "subst"], ["A"])
  , (["Relation", "Nullary", "Dec", "does"], ["P"])
  , (["Relation", "Nullary", "Decidable", "Core", "isYes"], ["P"])
  , (["Relation", "Nullary", "Decidable", "Core", "⌊_⌋"], ["P"])
  , (["Relation", "Nullary", "Decidable", "Core", "isYes≗does"], ["P"])
  , (["Relation", "Nullary", "Decidable", "Core", "map′"], ["P", "Q"])
  , (["Relation", "Nullary", "Decidable", "Core", "dec-true"], ["P"])
  , (["Relation", "Nullary", "Decidable", "Core", "dec-false"], ["P"])
  , (["Relation", "Nullary", "Decidable", "Core", "True"], ["P"])
  , (["Relation", "Nullary", "Decidable", "Core", "False"], ["P"])
  , (["Relation", "Nullary", "Decidable", "Core", "toWitness"], ["P", "Q"])
  , (["Relation", "Nullary", "Decidable", "Core", "toWitnessFalse"], ["P", "Q"])
  , (["Data", "Bool", "Base", "if_then_else_"], ["A"])
  , (["Data", "Product", "∃"], ["A"])
  , (["Data", "Empty", "⊥-elim"], ["A"])
  , (["Agda", "Builtin", "List", "List", "[]"], ["α"])
  , (["Agda", "Builtin", "List", "List", "_∷_"], ["α"])
  , (["Data", "List", "Base", "[_]"], ["A"])
  , (["Data", "List", "Base", "_++_"], ["A"])
  , (["Data", "List", "Base", "map"], ["A", "B"])
  , (["Data", "List", "Base", "mapMaybe"], ["A", "B"])
  , (["Data", "List", "Base", "concatMap"], ["A", "B"])
  , (["Data", "List", "Base", "foldr"], ["A", "B"])
  , (["Data", "List", "Base", "foldl"], ["A", "B"])
  , (["Data", "List", "Base", "length"], ["A"])
  , (["Data", "List", "Base", "reverse"], ["A"])
  , (["Data", "List", "Base", "replicate"], ["A"])
  , (["Data", "List", "Base", "all"], ["A"])
  , (["Data", "List", "Base", "any"], ["A"])
  , (["Data", "List", "Base", "take"], ["A"])
  , (["Data", "List", "Base", "drop"], ["A"])
  , (["Data", "List", "Base", "applyUpTo"], ["A"])
  , (["Data", "List", "Base", "zip"], ["A", "B"])
  , (["Data", "List", "Base", "tails"], ["A"])
  , (["Data", "List", "Base", "lookup"], ["A"])
  , (["Data", "List", "Base", "linesBy"], ["A", "P"])
  , (["Data", "List", "Base", "wordsBy"], ["A", "P"])
  , (["Data", "List", "Relation", "Unary", "Any", "Any"], ["A"])
  , (["Data", "List", "Relation", "Unary", "Any", "Any", "here"], ["A", "P", "x", "xs"])
  , (["Data", "List", "Relation", "Unary", "Any", "Any", "there"], ["A", "P", "x", "xs"])
  , (["Data", "List", "Relation", "Unary", "All", "All"], ["A"])
  , (["Data", "List", "Relation", "Unary", "All", "All", "[]"], ["A", "P"])
  , (["Data", "List", "Relation", "Unary", "All", "All", "_∷_"], ["A", "P", "x", "xs"])
  , (["Agda", "Builtin", "Maybe", "Maybe", "just"], ["A"])
  , (["Agda", "Builtin", "Maybe", "Maybe", "nothing"], ["A"])
  , (["Data", "Maybe", "Base", "map"], ["A", "B"])
  , (["Data", "Maybe", "Base", "_>>=_"], ["A", "B"])
  , (["Data", "Maybe", "Base", "maybe′"], ["A", "B"])
  , (["Data", "Maybe", "Base", "fromMaybe"], ["A"])
  , (["Data", "Maybe", "Base", "when"], ["A"])
  , (["Data", "Maybe", "Base", "is-just"], ["A"])
  , (["Data", "Maybe", "Base", "is-nothing"], ["A"])
  , (["Data", "Maybe", "Base", "zipWith"], ["A", "B", "C"])
  , (["Agda", "Builtin", "Sigma", "_,_"], ["A", "B"])
  , (["Agda", "Builtin", "Sigma", "Σ", "fst"], ["A", "B"])
  , (["Agda", "Builtin", "Sigma", "Σ", "snd"], ["A", "B"])
  , (["Data", "Product", "map₁"], ["A", "B", "C"])
  , (["Data", "Product", "map₂"], ["A", "B", "C"])
  , (["Data", "Sum", "Base", "_⊎_", "inj₁"], ["A", "B"])
  , (["Data", "Sum", "Base", "_⊎_", "inj₂"], ["A", "B"])
  , (["Data", "Sum", "Base", "map"], ["A", "B", "C", "D"])
  , (["Data", "Sum", "Base", "map₁"], ["A", "B", "C"])
  , (["Data", "Sum", "Base", "map₂"], ["A", "B", "D"])
  , (["Data", "Fin", "Base", "Fin", "zero"], ["n"])
  , (["Data", "Fin", "Base", "Fin", "suc"], ["n"])
  , (["Data", "Fin", "Base", "toℕ"], ["n"])
  , (["Data", "String", "wordsBy"], ["P"])
  , (["Data", "String", "linesBy"], ["P"])
  , (["Function", "Base", "id"], ["A"])
  , (["Function", "Base", "const"], ["A", "B"])
  , (["Function", "Base", "_∘_"], ["A", "B", "C"])
  , (["Function", "Base", "_$_"], ["A", "B"])
  , (["Function", "Base", "case_of_"], ["A", "B"])
  , (["IO", "Base", "pure"], ["A"])
  , (["IO", "Base", "_", "_>>=_"], ["A", "B"])
  , (["IO", "Base", "_", "_>>_"], ["A", "B"])
  , (["IO", "Primitive", "return"], ["A"])
  , (["IO", "Primitive", "_>>=_"], ["A", "B"])
  , (["Context", "Blueprint", "fromEl"], ["Base"])
  , (["Context", "Blueprint", "FiberOf"], ["B", "U"])
  , (["Context", "Blueprint", "composeLift"], ["A", "B", "C"])
  , (["Context", "Blueprint", "Commutes₁"], ["A", "B", "U", "V"])
  , (["Context", "Blueprint", "Commutes₂"], ["A", "B", "C", "U", "V", "W"])
  , (["Context", "Blueprint", "Commutes₃"], ["A", "B", "C", "D", "U", "V", "W", "X"])
  , (["Context", "PolyTransport", "equivPort"], ["A"])
  , (["Context", "PolyTransport", "graphPort"], ["A", "B"])
  , (["Context", "PolyTransport", "cographPort"], ["A", "B"])
  , (["Context", "PolyTransport", "tensorPort"], ["A₁", "B₁", "A₂", "B₂"])
  , (["Context", "PolyTransport", "splitPort"], ["A", "B₁", "B₂"])
  , (["Context", "PolyTransport", "mergePort"], ["A₁", "A₂", "B"])
  , (["Context", "PolyTransport", "compPort"], ["A", "B", "C"])
  , (["Context", "PolyTransport", "cut₁"], ["A", "B", "C", "D"])
  , (["Context", "PolyTransport", "cutRel"], ["A", "B", "C", "D"])
  , (["Context", "PolyTransport", "TransportsPoly"], ["Aᵢ", "Aₒ", "Bᵢ", "Bₒ"])
  , (["Context", "PolyTransport", "Transports₁"], ["A", "B", "C", "D"])
  , (["Context", "PolyTransport", "Transports₂"], ["A₁", "B₁", "A₂", "B₂", "C", "D"])
  , (["Context", "Terminal", "TimerEdit", "arm"], ["E"])
  , (["Context", "Terminal", "TimerEdit", "cancel"], ["E"])
  , (["Context", "Terminal", "timer"], ["E"])
  , (["Context", "Terminal", "Timer", "slot"], ["E"])
  , (["Context", "Terminal", "Timer", "deadline"], ["E"])
  , (["Context", "Terminal", "Timer", "payload"], ["E"])
  , (["Context", "Terminal", "Event", "input"], ["E"])
  , (["Context", "Terminal", "Event", "timeout"], ["E"])
  , (["Context", "Terminal", "effect"], ["S", "E"])
  , (["Context", "Terminal", "Effect", "nextState"], ["S", "E"])
  , (["Context", "Terminal", "Effect", "output"], ["S", "E"])
  , (["Context", "Terminal", "Effect", "edits"], ["S", "E"])
  , (["Context", "Terminal", "timed"], ["S", "E"])
  , (["Context", "Terminal", "TimedMachine", "now"], ["S", "E"])
  , (["Context", "Terminal", "TimedMachine", "state"], ["S", "E"])
  , (["Context", "Terminal", "TimedMachine", "timers"], ["S", "E"])
  , (["Context", "Terminal", "TimedMachine", "pending"], ["S", "E"])
  , (["Context", "Terminal", "removeTimer"], ["E"])
  , (["Context", "Terminal", "insertTimer"], ["E"])
  , (["Context", "Terminal", "editTimers"], ["E"])
  , (["Context", "Terminal", "applyEffect"], ["S", "E"])
  , (["Context", "Terminal", "fireDue"], ["S", "E"])
  , (["Context", "Terminal", "advance"], ["S", "E"])
  , (["Context", "Terminal", "perform"], ["S", "E"])
  , (["Context", "Terminal", "observe"], ["S", "E"])
  , (["Context", "Terminal", "stepTimed"], ["S", "E"])
  , (["Context", "Terminal", "traceTimed"], ["S", "E"])
  , (["Context", "Terminal", "putAt"], ["A"])
  , (["Context", "Terminal", "getAt"], ["A"])
  , (["Context", "Terminal", "mapIndexed"], ["A", "B"])
  , (["Data", "Nat", "Base", "_≤_", "z≤n"], ["n"])
  , (["Data", "Nat", "Base", "_≤_", "s≤s"], ["m", "n"])
  , (["Data", "Integer", "Base", "_≤_", "-≤-"], ["m", "n"])
  , (["Data", "Integer", "Base", "_≤_", "-≤+"], ["m", "n"])
  , (["Data", "Integer", "Base", "_≤_", "+≤+"], ["m", "n"])
  , (["Context", "Tools", "Clock", "withTimeoutClock"], ["A"])
  , (["Context", "Tools", "TermLaws", "foldl-++"], ["A", "B"])
  , (["Context", "Tools", "TermLaws", "advance-zero"], ["S", "E"])
  , (["Context", "Tools", "TermLaws", "advance-+"], ["S", "E"])
  , (["Context", "Tools", "FuzzGen", "runGen"], ["A"])
  , (["Context", "Tools", "FuzzGen", "genPure"], ["A"])
  , (["Context", "Tools", "FuzzGen", "genMap"], ["A", "B"])
  , (["Context", "Tools", "FuzzGen", "genBind"], ["A", "B"])
  , (["Context", "Tools", "FuzzGen", "genPair"], ["A", "B"])
  , (["Context", "Tools", "FuzzGen", "genList"], ["A"])
  , (["Context", "Tools", "FuzzGen", "chooseAt"], ["A"])
  , (["Context", "Tools", "FuzzGen", "genChoose"], ["A"])
  , (["Context", "Tools", "FuzzGen", "sampleMany"], ["A"])
  , (["Context", "Tools", "FuzzGen", "shrinkList"], ["A"])
  , (["Context", "Tools", "FuzzGen", "firstFailure"], ["A"])
  , (["Context", "Tools", "FuzzGen", "minimize"], ["A"])
  , (["Context", "Tools", "FuzzGen", "fuzzCheck"], ["A"])
  , (["Context", "Tools", "FsSandbox", "all"], ["A"])
  , (["Context", "Tools", "FsSandbox", "bindMaybe"], ["A", "B"])
  , (["Context", "Tools", "GitSandbox", "lookupName"], ["A"])
  , (["Context", "Tools", "GitSandbox", "putName"], ["A"])
  , (["Context", "Tools", "GitSandbox", "removeName"], ["A"])
  , (["Context", "Tools", "GitSandbox", "present"], ["A"])
  , (["Context", "Tools", "GitLaws", "lookupName-putName-same"], ["A"])
  , (["Context", "Tools", "GitLaws", "lookupName-putName-other"], ["A"])
  , (["Context", "Tools", "WebOperad", "Scene", "empty"], ["A"])
  , (["Context", "Tools", "WebOperad", "Scene", "decorRect"], ["A"])
  , (["Context", "Tools", "WebOperad", "Scene", "occludeRect"], ["A"])
  , (["Context", "Tools", "WebOperad", "Scene", "hitRect"], ["A"])
  , (["Context", "Tools", "WebOperad", "Scene", "decorLine"], ["A"])
  , (["Context", "Tools", "WebOperad", "Scene", "transform"], ["A"])
  , (["Context", "Tools", "WebOperad", "Scene", "clip"], ["A"])
  , (["Context", "Tools", "WebOperad", "Scene", "over"], ["A"])
  , (["Context", "Tools", "WebOperad", "mapScene"], ["A", "B"])
  , (["Context", "Tools", "WebOperad", "paint"], ["A", "V"])
  , (["Context", "Tools", "WebOperad", "ownerInk"], ["A"])
  , (["Context", "Tools", "WebOperad", "colourInk"], ["A"])
  , (["Context", "Tools", "WebOperad", "paintOwner"], ["A"])
  , (["Context", "Tools", "WebOperad", "paintSurfaceColour"], ["A"])
  , (["Context", "Tools", "WebOperad", "HitResult", "miss"], ["A"])
  , (["Context", "Tools", "WebOperad", "HitResult", "blocked"], ["A"])
  , (["Context", "Tools", "WebOperad", "HitResult", "hit"], ["A"])
  , (["Context", "Tools", "WebOperad", "route"], ["A"])
  , (["Context", "Tools", "WebOperad", "resolve"], ["A"])
  , (["Context", "Tools", "WebOperad", "hitTest"], ["A"])
  , (["Context", "Tools", "WebOperad", "visual-hit-consistent"], ["A"])
  , (["Context", "Tools", "WebOperad", "emit"], ["A"])
  , (["Context", "Tools", "WebOperad", "compileDraw"], ["A"])
  , (["Context", "Tools", "WebOperad", "compileSurfaceDraw"], ["A"])
  , (["Context", "Tools", "WebOperad", "draw-machine-sound"], ["A"])
  , (["Context", "World", "_∈_", "here"], ["c", "cs"])
  , (["Context", "World", "_∈_", "there"], ["c", "d", "cs"])
  , (["Context", "World", "⊆-refl"], ["Δ"])
  , (["Context", "World", "⊆-trans"], ["Δ₁", "Δ₂", "Δ₃"])
  , (["Context", "World", "⊆-nil"], ["Δ"])
  , (["Context", "World", "⊆-step"], ["d", "Δ₁", "Δ₂"])
  , (["Context", "World", "⊆-cons"], ["c", "Δ₁", "Δ₂"])
  , (["Context", "World", "Ret"], ["c"])
  , (["Context", "World", "WorldProg", "pure"], ["Δ", "A"])
  , (["Context", "World", "WorldProg", "step"], ["Δ", "A", "c"])
  , (["Context", "World", "_>>=w_"], ["Δ", "A", "B"])
  , (["Context", "World", "_>>w_"], ["Δ", "A", "B"])
  , (["Context", "World", "mapWorld"], ["Δ", "A", "B"])
  , (["Context", "World", "liftWorld"], ["Δ₁", "Δ₂", "A"])
  , (["Context", "World", "nowMonoW"], ["Δ"])
  , (["Context", "World", "nowWallW"], ["Δ"])
  , (["Context", "World", "sleepW"], ["Δ"])
  , (["Context", "World", "getProgNameW"], ["Δ"])
  , (["Context", "World", "getArgsW"], ["Δ"])
  , (["Context", "World", "lookupEnvW"], ["Δ"])
  , (["Context", "World", "readStdinAllW"], ["Δ"])
  , (["Context", "World", "readStdinLineW"], ["Δ"])
  , (["Context", "World", "isTTYStdinW"], ["Δ"])
  , (["Context", "World", "isTTYStdoutW"], ["Δ"])
  , (["Context", "World", "isTTYStderrW"], ["Δ"])
  , (["Context", "World", "termSizeW"], ["Δ"])
  , (["Context", "World", "writeStdoutW"], ["Δ"])
  , (["Context", "World", "writeStdoutStrW"], ["Δ"])
  , (["Context", "World", "writeStderrW"], ["Δ"])
  , (["Context", "World", "writeStderrStrW"], ["Δ"])
  , (["Context", "World", "readTTYByteW"], ["Δ"])
  , (["Context", "World", "readFileW"], ["Δ"])
  , (["Context", "World", "writeFileW"], ["Δ"])
  , (["Context", "World", "mkdirW"], ["Δ"])
  , (["Context", "World", "symlinkW"], ["Δ"])
  , (["Context", "World", "unlinkW"], ["Δ"])
  , (["Context", "World", "statW"], ["Δ"])
  , (["Context", "World", "tcpExchangeW"], ["Δ"])
  , (["Context", "World", "tlsExchangeW"], ["Δ"])
  , (["Context", "World", "gitStepW"], ["Δ"])
  , (["Context", "World", "gitSummaryW"], ["Δ"])
  , (["Context", "World", "webViewportW"], ["Δ"])
  , (["Context", "World", "webSetTitleW"], ["Δ"])
  , (["Context", "World", "webDrawSceneW"], ["Δ"])
  , (["Context", "World", "webHitTestW"], ["Δ"])
  , (["Context", "World", "webPollInputW"], ["Δ"])
  , (["Context", "World", "mkEvent"], ["Δ", "evCap"])
  , (["Context", "World", "Event", "evHasCap"], ["Δ"])
  , (["Context", "World", "Event", "evPayload"], ["Δ"])
  , (["Context", "World", "liftEvent"], ["Δ₁", "Δ₂"])
  , (["Context", "World", "reactiveApp"], ["Δ", "S"])
  , (["Context", "World", "ReactiveApp", "init"], ["Δ", "S"])
  , (["Context", "World", "ReactiveApp", "onStep"], ["Δ", "S"])
  , (["Context", "World", "stepWorldPure"], ["c"])
  , (["Context", "World", "runWorldPure"], ["Δ", "A"])
  , (["Context", "World", "runCliPure"], ["Δ"])
  , (["Context", "World", "runReactiveSteps"], ["Δ", "S"])
  , (["Context", "World", "runReactivePure"], ["Δ", "S"])
  , (["Context", "WorldLaws", "bind-pure-left"], ["Δ", "A", "B"])
  , (["Context", "WorldLaws", "bind-pure-left-run"], ["Δ", "A", "B"])
  , (["Context", "WorldLaws", "bind-pure-right-run"], ["Δ", "A"])
  , (["Context", "WorldLaws", "runWorldPure-bind"], ["Δ", "A", "B"])
  , (["Context", "WorldLaws", "bind-assoc-run"], ["Δ", "A", "B", "C"])
  , (["Context", "WorldLaws", "mapWorld-pure"], ["Δ", "A", "B"])
  , (["Context", "WorldLaws", "mapWorld-run"], ["Δ", "A", "B"])
  , (["Context", "WorldLaws", "liftWorld-pure"], ["Δ₁", "Δ₂", "A"])
  , (["Context", "WorldLaws", "liftWorld-preserves-run"], ["Δ₁", "Δ₂", "A"])
  , (["Context", "WorldLaws", "liftWorld-bind-run"], ["Δ₁", "Δ₂", "A", "B"])
  , (["Context", "WorldLaws", "notHasCap⇒∉"], ["c", "Δ"])
  , (["Context", "WorldLaws", "step-preserves-clock"], ["c"])
  , (["Context", "WorldLaws", "step-preserves-fs"], ["c"])
  , (["Context", "WorldLaws", "step-preserves-net"], ["c"])
  , (["Context", "WorldLaws", "step-preserves-tty"], ["c"])
  , (["Context", "WorldLaws", "prog-preserves-clock"], ["Δ", "A"])
  , (["Context", "Protocol", "Proto", "pEnd"], ["Tag"])
  , (["Context", "Protocol", "Proto", "pSend"], ["Tag"])
  , (["Context", "Protocol", "Proto", "pRecv"], ["Tag"])
  , (["Context", "Protocol", "Proto", "pSelect"], ["Tag"])
  , (["Context", "Protocol", "Proto", "pOffer"], ["Tag"])
  , (["Context", "Protocol", "dual"], ["Tag"])
  , (["Context", "Protocol", "dual-involutive"], ["Tag"])
  , (["Context", "Protocol", "EndpointCore"], ["Tag"])
  , (["Context", "Protocol", "Endpoint"], ["Tag"])
  , (["Context", "Protocol", "EndpointCore", "epDone"], ["Tag", "Δ", "Payload", "A"])
  , (["Context", "Protocol", "EndpointCore", "epStep"], ["Tag", "Δ", "Payload", "A", "P", "c"])
  , (["Context", "Protocol", "EndpointCore", "epSend"], ["Tag", "Δ", "Payload", "A", "t", "P"])
  , (["Context", "Protocol", "EndpointCore", "epRecv"], ["Tag", "Δ", "Payload", "A", "t", "P"])
  , (["Context", "Protocol", "EndpointCore", "epSelectL"], ["Tag", "Δ", "Payload", "A", "P", "Q"])
  , (["Context", "Protocol", "EndpointCore", "epSelectR"], ["Tag", "Δ", "Payload", "A", "P", "Q"])
  , (["Context", "Protocol", "EndpointCore", "epOffer"], ["Tag", "Δ", "Payload", "A", "P", "Q"])
  , (["Context", "Protocol", "mapEndpoint"], ["Tag", "Δ", "Payload", "P", "A", "B"])
  , (["Context", "Protocol", "liftProgToEndpoint"], ["Tag", "Δ", "Payload", "P", "A", "B"])
  , (["Context", "Protocol", "liftEndpoint"], ["Tag", "Δ₁", "Δ₂", "Payload", "P", "A"])
  , (["Context", "Protocol", "coupleEndpoints"], ["Tag", "Δ", "Payload", "P", "A", "B"])
  , (["Context", "Protocol", "composeReactive"], ["Δ₁", "Δ₂", "Δ", "S₁", "S₂"])
  , (["Context", "Protocol", "coupleReactiveTurn"], ["Tag", "Δ₁", "Δ₂", "Δ", "Payload", "P", "S₁", "S₂"])
  , (["Context", "Protocol", "coupleReactive"], ["Tag", "Δ₁", "Δ₂", "Δ", "Payload", "P", "S₁", "S₂"])
  , (["Context", "Protocol", "couple-done"], ["Tag", "Δ", "Payload", "A", "B"])
  , (["Context", "Protocol", "couple-send-recv"], ["Tag", "Δ", "Payload", "t", "P", "A", "B"])
  , (["Context", "Protocol", "couple-recv-send"], ["Tag", "Δ", "Payload", "t", "P", "A", "B"])
  , (["Context", "Protocol", "couple-selectL-offer"], ["Tag", "Δ", "Payload", "P", "Q", "A", "B"])
  , (["Context", "Protocol", "couple-selectR-offer"], ["Tag", "Δ", "Payload", "P", "Q", "A", "B"])
  , (["Context", "Protocol", "couple-offer-selectL"], ["Tag", "Δ", "Payload", "P", "Q", "A", "B"])
  , (["Context", "Protocol", "couple-offer-selectR"], ["Tag", "Δ", "Payload", "P", "Q", "A", "B"])
  , (["Context", "Protocol", "couple-step-left"], ["Tag", "Δ", "Payload", "P", "A", "B", "c"])
  , (["Context", "Protocol", "couple-preserves-clock"], ["Tag", "Δ", "Payload", "P", "A", "B"])
  , (["Context", "Protocol", "couple-preserves-fs"], ["Tag", "Δ", "Payload", "P", "A", "B"])
  , (["Context", "Protocol", "couple-preserves-net"], ["Tag", "Δ", "Payload", "P", "A", "B"])
  , (["Context", "Protocol", "couple-preserves-tty"], ["Tag", "Δ", "Payload", "P", "A", "B"])
  , (["Context", "WorldLaws", "prog-preserves-fs"], ["Δ", "A"])
  , (["Context", "WorldLaws", "prog-preserves-net"], ["Δ", "A"])
  , (["Context", "WorldLaws", "prog-preserves-tty"], ["Δ", "A"])
  , (["Context", "WorldLaws", "continueReactiveAfter"], ["Δ", "S"])
  , (["Context", "WorldLaws", "runReactiveSteps-++"], ["Δ", "S"])
  , (["OwnershipIO", "WorldRunner", "runWorldIO"], ["Δ", "A"])
  , (["OwnershipIO", "WorldRunner", "runCliIO"], ["Δ"])
  , (["OwnershipIO", "WorldRunner", "runReactiveIO"], ["Δ", "S"])
  ]

private partial def extractLeadingImplicits : Expr → List String
  | .pi (.bind .hidden xs _) rest => xs.map leanMangleIdent ++ extractLeadingImplicits rest
  | .fun_ { hid := .hidden, .. } rest => "_" :: extractLeadingImplicits rest
  | _ => []

def collectLevelVarsInType : Expr → List String :=
  let rec go : Expr → List String
    | .pi (.bind _ xs (.def_ q)) rest =>
        if q.full == ["Agda", "Primitive", "Level"] then
          xs ++ go rest
        else go rest
    | .app (.set 0) { thing := .var u, .. } => [u]
    | .pi (.bind _ _ t) rest => go t ++ go rest
    | .fun_ a rest => go a.thing ++ go rest
    | .app f a => go f ++ go a.thing
    | _ => []
  fun e => (go e).eraseDups

def resolveLeanQName (ctx : EmitCtx) (q : QName) : PrismOutcome String :=
  match ctx.symIndex[q.full]? with
  | some info =>
      if info.leanName.isEmpty then .bot s!"'{fullDot q}' requires native Agda checking"
      else .translated info.leanName
  | none =>
      if q.full.take ctx.modPrefix.length == ctx.modPrefix then
        let rest := q.full.drop ctx.modPrefix.length
        match rest with
        | [nm] => .translated (leanModNamespace ctx.modPrefix ++ "." ++ leanMangleIdent nm)
        | [tyNm, subNm] =>
            .translated (leanModNamespace ctx.modPrefix ++ "." ++ leanMangleIdent tyNm ++ "." ++ leanMangleIdent subNm)
        | _ => .bot s!"unsupported nested path '{fullDot q}'"
      else
        .bot s!"unresolved canonical symbol '{fullDot q}'"

-- Resolve record field identifier: user/dependency records use `leanMangleIdent`,
-- whereas precompiled `StdScope` (`AgdaMirror`) records use their native Lean field name!
def resolveRecFieldIdent (ctx : EmitCtx) (fNames : List String) (fn : String) : String :=
  let matchesUserRec :=
    !fNames.isEmpty &&
    ctx.recMeta.any fun rm =>
      let rFieldNames := rm.fields.map Prod.fst
      fNames.all (rFieldNames.contains ·)
  if matchesUserRec then
    leanMangleIdent fn
  else
    let stdCand := ctx.symByCanon.find? fun (c, info) =>
      match info.kind with
      | .projSym _ =>
          c.getLastD "" == fn &&
          let recCanon := c.dropLast
          let modStr := String.intercalate "." (recCanon.dropLast)
          (lookupStdModule modStr).isSome &&
          fNames.all (fun f => ctx.symByCanon.any (fun (c2, i2) =>
            match i2.kind with
            | .projSym _ => c2 == recCanon ++ [f]
            | _          => false))
      | _ => false
    match stdCand with
    | some (_, info) => (info.leanName.splitOn ".").getLastD (leanMangleIdent fn)
    | none           => leanMangleIdent fn

-- Replace pattern variables not referenced in the clause RHS / `where` block with `_`
-- so Lean 4's dependent pattern matcher freely unifies forced index positions (e.g. `y`
-- in `square x y d refl = ...` on `TransportsPoly (graphPort ...)`).
mutual
  partial def collectVarsExpr : Expr → List String
    | .var x => [x]
    | .def_ _ | .con _ | .lit _ | .set _ | .hole | .meta_ | .absurdLam _ => []
    | .dot e => collectVarsExpr e
    | .lamCase cs => cs.flatMap fun (.clause _ r ws) => collectVarsRhs r ++ ws.flatMap collectVarsDecl
    | .app f a => collectVarsExpr f ++ collectVarsExpr a.thing
    | .lam _ body => collectVarsExpr body
    | .lamT (.bind _ _ ty) body => collectVarsExpr ty ++ collectVarsExpr body
    | .pi (.bind _ _ ty) body => collectVarsExpr ty ++ collectVarsExpr body
    | .fun_ a body => collectVarsExpr a.thing ++ collectVarsExpr body
    | .let_ bs body => bs.flatMap collectVarsLetBind ++ collectVarsExpr body
    | .rec_ fs => fs.flatMap (fun (_, fv) => collectVarsExpr fv)
    | .recUpd base fs => collectVarsExpr base ++ fs.flatMap (fun (_, fv) => collectVarsExpr fv)

  partial def collectVarsLetBind : LetBind → List String
    | .letBind _ ty rhs => collectVarsExpr ty ++ collectVarsExpr rhs
    | .letPat _ rhs     => collectVarsExpr rhs

  partial def collectVarsRhs : RHS → List String
    | .rhs body => collectVarsExpr body
    | .withRHS es scs =>
        es.flatMap collectVarsExpr ++
        scs.flatMap (fun (.clause _ sr sws) => collectVarsRhs sr ++ sws.flatMap collectVarsDecl)
    | .rewriteRHS es inner => es.flatMap collectVarsExpr ++ collectVarsRhs inner
    | .absurdRHS => []

  partial def collectVarsDecl : Decl → List String
    | .sig _ _ ty => collectVarsExpr ty
    | .fun_ _ _ cs => cs.flatMap (fun (.clause _ r ws) => collectVarsRhs r ++ ws.flatMap collectVarsDecl)
    | .dataSig _ _ ps s => ps.flatMap (fun (.bind _ _ t) => collectVarsExpr t) ++ collectVarsExpr s
    | .dataDef _ _ _ cons => cons.flatMap (fun (_, t) => collectVarsExpr t)
    | .recSig _ _ ps s => ps.flatMap (fun (.bind _ _ t) => collectVarsExpr t) ++ collectVarsExpr s
    | .recDef _ _ _ _ flds => flds.flatMap (fun (_, t) => collectVarsExpr t)
    | .patSyn _ _ _ e => collectVarsExpr e
    | _ => []
end

partial def wildcardUnusedPat (usedVars : List String) : Pat → Pat
  | .varP x   => if usedVars.contains x then .varP x else .wildP
  | .asP x p  =>
      let p' := wildcardUnusedPat usedVars p
      if usedVars.contains x then .asP x p' else p'
  | .conP q ps => .conP q (ps.map (fun a => { a with thing := wildcardUnusedPat usedVars a.thing }))
  | .recP fs   => .recP (fs.map (fun (fn, fp) => (fn, wildcardUnusedPat usedVars fp)))
  | p          => p

partial def hasInterleavedImplicitBeforeK : Nat → Expr → Bool
  | 0, _ => false
  | k, .pi (.bind .visible xs _) rest =>
      if xs.length >= k then false
      else hasInterleavedImplicitBeforeK (k - xs.length) rest
  | k, .fun_ { hid := .visible, .. } rest =>
      hasInterleavedImplicitBeforeK (k - 1) rest
  | _, .pi (.bind .hidden _ _) _ => true
  | _, .fun_ { hid := .hidden, .. } _ => true
  | _, .pi (.bind .inst _ _) _ => true
  | _, .fun_ { hid := .inst, .. } _ => true
  | _, _ => false

partial def codomainIsSet : Expr → Bool
  | .set _               => true
  | .app (.set 0) _      => true
  | .pi _ rest           => codomainIsSet rest
  | .fun_ _ rest         => codomainIsSet rest
  | _                    => false

partial def looksLikeTypeRhs : Expr → Bool
  | .set _          => true
  | .pi _ _         => true
  | .fun_ _ _       => true
  | .def_ q         =>
      q.full == ["Agda", "Builtin", "String", "String"] ||
      q.full == ["Agda", "Builtin", "Nat", "Nat"] ||
      q.full == ["Agda", "Builtin", "Bool", "Bool"] ||
      q.full == ["Agda", "Builtin", "Char", "Char"]
  | .app (.def_ q) _ =>
      q.full == ["Agda", "Builtin", "List", "List"] ||
      q.full == ["Agda", "Builtin", "Maybe", "Maybe"] ||
      q.full == ["Data", "Fin", "Base", "Fin"]
  | .app (.app (.def_ q) _) _ =>
      q.full == ["Data", "Product", "_×_"] ||
      q.full == ["Data", "Sum", "Base", "_⊎_"]
  | _ => false

partial def replaceFirstAbsurdPat : Pat → Option Pat
  | .absurdP   => some (.varP "_abs_bot")
  | .asP x p   => (replaceFirstAbsurdPat p).map (.asP x)
  | .conP q ps =>
      let rec go : List (Arg Pat) → Option (List (Arg Pat))
        | [] => none
        | a :: as =>
            if a.hid != .visible then
              (go as).map (a :: ·)
            else
              match replaceFirstAbsurdPat a.thing with
              | some p' => some ({ a with thing := p' } :: as)
              | none    => (go as).map (a :: ·)
      (go ps).map (.conP q)
  | .recP fs =>
      let rec goF : List (String × Pat) → Option (List (String × Pat))
        | [] => none
        | (fn, fp) :: rest =>
            match replaceFirstAbsurdPat fp with
            | some p' => some ((fn, p') :: rest)
            | none    => (goF rest).map ((fn, fp) :: ·)
      (goF fs).map (.recP)
  | _ => none

partial def mentionsDepSigmaWithTarget (targets : List (List String)) : Expr → Bool
  | .app (.app (.def_ q) a1) a2 =>
      if q.full == ["Data", "Product", "_×_"] || q.full == ["Agda", "Builtin", "Sigma", "Σ"] then
        if targets.any (fun t => mentionsQName t a1.thing || mentionsQName t a2.thing) then true
        else mentionsDepSigmaWithTarget targets a1.thing || mentionsDepSigmaWithTarget targets a2.thing
      else
        mentionsDepSigmaWithTarget targets (.app (.def_ q) a1) || mentionsDepSigmaWithTarget targets a2.thing
  | .app f a     => mentionsDepSigmaWithTarget targets f || mentionsDepSigmaWithTarget targets a.thing
  | .pi (.bind _ _ t) b => mentionsDepSigmaWithTarget targets t || mentionsDepSigmaWithTarget targets b
  | .fun_ a b    => mentionsDepSigmaWithTarget targets a.thing || mentionsDepSigmaWithTarget targets b
  | .lam _ e     => mentionsDepSigmaWithTarget targets e
  | .lamT (.bind _ _ t) e => mentionsDepSigmaWithTarget targets t || mentionsDepSigmaWithTarget targets e
  | _ => false

partial def substSelfRecFields (recCanon : List String) (seenFields : List String) : Expr → Expr
  | .def_ q =>
      match seenFields.find? (fun f => q.full == recCanon ++ [f]) with
      | some f => .var f
      | none   => .def_ q
  | .app f a =>
      .app (substSelfRecFields recCanon seenFields f)
           { a with thing := substSelfRecFields recCanon seenFields a.thing }
  | .lam a b => .lam a (substSelfRecFields recCanon (seenFields.filter (· != a.thing)) b)
  | .lamT (.bind h xs ty) b =>
      let seen' := seenFields.filter (fun f => !xs.contains f)
      .lamT (.bind h xs (substSelfRecFields recCanon seenFields ty))
            (substSelfRecFields recCanon seen' b)
  | .pi (.bind h xs ty) b =>
      let seen' := seenFields.filter (fun f => !xs.contains f)
      .pi (.bind h xs (substSelfRecFields recCanon seenFields ty))
          (substSelfRecFields recCanon seen' b)
  | .fun_ a b =>
      .fun_ { a with thing := substSelfRecFields recCanon seenFields a.thing }
            (substSelfRecFields recCanon seenFields b)
  | .let_ lbs b =>
      .let_ lbs (substSelfRecFields recCanon seenFields b)
  | .rec_ fs =>
      .rec_ (fs.map fun (fn, fe) => (fn, substSelfRecFields recCanon seenFields fe))
  | .recUpd r fs =>
      .recUpd (substSelfRecFields recCanon seenFields r)
              (fs.map fun (fn, fe) => (fn, substSelfRecFields recCanon seenFields fe))
  | .dot e => .dot (substSelfRecFields recCanon seenFields e)
  | e => e

def hasDependentRecordFields (scope : List String) (flds : List (String × Expr)) : Bool :=
  let rec check (seen : List String) : List (String × Expr) → Bool
    | [] => false
    | (fn, fTy) :: rest =>
        let rec mentionsLocalVar (available : List String) : Expr → Bool
          | .var x       => available.contains x
          | .app f a     => mentionsLocalVar available f || mentionsLocalVar available a.thing
          | .lam a e     => mentionsLocalVar (available.erase a.thing) e
          | .lamT (.bind _ xs t) e => mentionsLocalVar available t || mentionsLocalVar (available.filter (!xs.contains ·)) e
          | .pi (.bind _ xs t) e   => mentionsLocalVar available t || mentionsLocalVar (available.filter (!xs.contains ·)) e
          | .fun_ a e    => mentionsLocalVar available a.thing || mentionsLocalVar available e
          | _            => false
        (collectExprQNames fTy).any (fun q => q.dropLast == scope && seen.contains (q.getLastD "")) ||
          mentionsLocalVar seen fTy || check (fn :: seen) rest
  check [] flds

private def depSigmaTriggerCanons : List (List String) :=
  [ ["Agda", "Builtin", "Sigma", "Σ"]
  , ["Data", "Product", "∃"]
  , ["Context", "Blueprint", "fromEl"]
  , ["Context", "Blueprint", "FiberOf"]
  , ["Context", "PolyTransport", "tensorPort"]
  , ["Context", "PolyTransport", "splitPort"]
  , ["Context", "PolyTransport", "mergePort"]
  , ["Context", "PolyTransport", "compPort"]
  , ["Context", "PolyTransport", "cut₁"]
  , ["Context", "PolyTransport", "cutRel"]
  , ["Context", "PolyTransport", "composeTransportsCut"] ]

def buildBaseEmitCtx (depMods : List (CodeMod × ExportedModule))
    (curMod : CodeMod) (curExp : ExportedModule) (mode : EmitMode) : EmitCtx :=
  let allMods := depMods.map Prod.fst ++ [curMod]
  let allRefCanons := allMods.flatMap (fun cm => cm.decls.flatMap collectDeclQNames)
  let isSigmaContextMod := allMods.any fun cm =>
    cm.modName.full == ["Context", "Blueprint"] || cm.modName.full == ["Context", "PolyTransport"]
  let usesDepSigma :=
    isSigmaContextMod || allRefCanons.any (depSigmaTriggerCanons.contains ·)

  let remapPairSym (s : SymInfo) : SymInfo :=
    if usesDepSigma then
      if s.canonPath == ["Context", "Terminal", "observe"] then { s with leanName := "AgdaMirror.Context.observeSigma" }
      else if s.canonPath == ["Context", "Terminal", "stepTimed"] then { s with leanName := "AgdaMirror.Context.stepTimedSigma" }
      else if s.canonPath == ["Context", "Tools", "Clock", "readMonoMs"] then { s with leanName := "AgdaMirror.Clock.readMonoMsSigma" }
      else if s.canonPath == ["Context", "Tools", "Clock", "readWallMs"] then { s with leanName := "AgdaMirror.Clock.readWallMsSigma" }
      else if s.canonPath == ["Context", "World", "writeVirtualFile"] then { s with leanName := "AgdaMirror.World.writeVirtualFileSigma" }
      else if s.canonPath == ["Context", "World", "stepWorldPure"] then { s with leanName := "AgdaMirror.World.stepWorldPureSigma" }
      else if s.canonPath == ["Context", "World", "runWorldPure"] then { s with leanName := "AgdaMirror.World.runWorldPureSigma" }
      else if s.canonPath == ["Context", "World", "runCliPure"] then { s with leanName := "AgdaMirror.World.runCliPureSigma" }
      else if s.canonPath == ["Context", "World", "runReactiveSteps"] then { s with leanName := "AgdaMirror.World.runReactiveStepsSigma" }
      else if s.canonPath == ["Context", "World", "runReactivePure"] then { s with leanName := "AgdaMirror.World.runReactivePureSigma" }
      else if s.canonPath == ["Context", "Protocol", "coupleEndpoints"] then { s with leanName := "AgdaMirror.Protocol.coupleEndpointsSigma" }
      else if s.canonPath == ["Context", "Protocol", "composeReactive"] then { s with leanName := "AgdaMirror.Protocol.composeReactiveSigma" }
      else if s.canonPath == ["Context", "Protocol", "coupleReactiveTurn"] then { s with leanName := "AgdaMirror.Protocol.coupleReactiveTurnSigma" }
      else if s.canonPath == ["Context", "Protocol", "coupleReactive"] then { s with leanName := "AgdaMirror.Protocol.coupleReactiveSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-done"] then { s with leanName := "AgdaMirror.Protocol.coupleDoneSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-send-recv"] then { s with leanName := "AgdaMirror.Protocol.coupleSendRecvSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-recv-send"] then { s with leanName := "AgdaMirror.Protocol.coupleRecvSendSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-selectL-offer"] then { s with leanName := "AgdaMirror.Protocol.coupleSelectLOfferSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-selectR-offer"] then { s with leanName := "AgdaMirror.Protocol.coupleSelectROfferSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-offer-selectL"] then { s with leanName := "AgdaMirror.Protocol.coupleOfferSelectLSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-offer-selectR"] then { s with leanName := "AgdaMirror.Protocol.coupleOfferSelectRSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-step-left"] then { s with leanName := "AgdaMirror.Protocol.coupleStepLeftSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-preserves-clock"] then { s with leanName := "AgdaMirror.Protocol.couplePreservesClockSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-preserves-fs"] then { s with leanName := "AgdaMirror.Protocol.couplePreservesFsSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-preserves-net"] then { s with leanName := "AgdaMirror.Protocol.couplePreservesNetSigma" }
      else if s.canonPath == ["Context", "Protocol", "couple-preserves-tty"] then { s with leanName := "AgdaMirror.Protocol.couplePreservesTtySigma" }
      else s
    else if s.canonPath == ["Data", "Product", "_×_"] then { s with leanName := "AgdaMirror.AgdaPair" }
    else if s.canonPath == ["Agda", "Builtin", "Sigma", "_,_"] then { s with leanName := "AgdaMirror.AgdaPair.mk" }
    else if s.canonPath == ["Agda", "Builtin", "Sigma", "Σ", "fst"] then { s with leanName := "AgdaMirror.AgdaPair.proj₁" }
    else if s.canonPath == ["Agda", "Builtin", "Sigma", "Σ", "snd"] then { s with leanName := "AgdaMirror.AgdaPair.proj₂" }
    else if s.canonPath == ["Data", "Product", "map₁"] then { s with leanName := "AgdaMirror.pairMap1" }
    else if s.canonPath == ["Data", "Product", "map₂"] then { s with leanName := "AgdaMirror.pairMap2" }
    else if s.canonPath == ["Data", "List", "Base", "zip"] then { s with leanName := "AgdaMirror.agdaZipPair" }
    else s

  let stdSyms : List (List String × SymInfo) :=
    allStdModules.flatMap (fun ms => ms.map (fun s => (s.canonPath, remapPairSym s)))
  let depSyms : List (List String × SymInfo) :=
    depMods.flatMap (fun (_, em) => em.symbols.map (fun s => (s.canonPath, remapPairSym s)))
  let ownSyms : List (List String × SymInfo) :=
    curExp.symbols.map (fun s => (s.canonPath, remapPairSym s))

  let collectModImplicits (cm : CodeMod) : List (List String × List String) :=
    let pfx := cm.modName.full
    cm.decls.flatMap fun
      | .sig _ nm ty => [(pfx ++ [nm], extractLeadingImplicits ty)]
      | .dataSig _ nm params _ | .recSig _ nm params _ =>
          let all := params.flatMap fun (.bind _ xs _) => xs.map leanMangleIdent
          let hidden := params.flatMap fun
            | .bind .hidden xs _ => xs.map leanMangleIdent
            | _ => []
          [(pfx ++ [nm], hidden), (pfx ++ [nm, "__params"], all)]
      | _ => []

  let expandConImplicits (cm : CodeMod) (baseImps : List (List String × List String)) :
      List (List String × List String) :=
    let pfx := cm.modName.full
    cm.decls.flatMap fun
      | .dataDef _ dNm _ cons =>
          let dParams := (baseImps.find? (fun (k, _) => k == pfx ++ [dNm, "__params"])).map Prod.snd |>.getD []
          cons.map fun (cNm, cTy) =>
            (pfx ++ [dNm, cNm], dParams ++ extractLeadingImplicits cTy)
      | .recDef _ rNm _ rd flds =>
          let rParams := (baseImps.find? (fun (k, _) => k == pfx ++ [rNm, "__params"])).map Prod.snd |>.getD []
          let cEntry := match rd.constr with
            | some cNm => [(pfx ++ [cNm], rParams)]
            | none     => []
          let fEntries := flds.map fun (fNm, _) => (pfx ++ [rNm, fNm], rParams)
          cEntry ++ fEntries
      | _ => []

  let collectRecMeta (cm : CodeMod) : List RecMetaEntry :=
    let pfx := cm.modName.full
    cm.decls.filterMap fun
      | .recDef _ rNm _ rd flds =>
          some { recCanon := pfx ++ [rNm], isCoind := rd.coind, constr := rd.constr, fields := flds }
      | _ => none

  let rawImps := allMods.flatMap collectModImplicits
  let conImps := allMods.flatMap (fun cm => expandConImplicits cm rawImps)
  let rMeta   := allMods.flatMap collectRecMeta

  let symbols := ownSyms ++ depSyms ++ stdSyms
  let implicits := conImps ++ rawImps ++ stdImplicitNames
  { modPrefix    := curMod.modName.full
  , mode         := mode
  , usesDepSigma := usesDepSigma
  , symByCanon   := symbols
  , sigImplicits := implicits
  , recMeta      := rMeta }

/-- Both backends use the same dependency and conversion closure. Capability probes
    are supplied by the backend that will actually consume the declarations. -/
def planUnitSlices
    (probeGroup : EmitCtx → List ModUnit → PrismOutcome Unit)
    (probeBoundary : EmitCtx → ModUnit → PrismOutcome Unit)
    (depMods : List (CodeMod × ExportedModule))
    (curMod : CodeMod) (curExp : ExportedModule) :
    PrismOutcome (SlicePlan × ExportedModule) := do
  let (headers, units) ← extractModUnits curMod
  let graph := unitGraph units
  let sccs := graph.sccs
  let deps (u : ModUnit) := graph.dependencies[u.uid]?.getD []
  let probeCtx := buildBaseEmitCtx depMods curMod curExp .pureFast

  let depExps := depMods.map Prod.snd
  let allCoindRecs := (curExp.coindRecords ++ depExps.flatMap (·.coindRecords)).eraseDups
  let coindConCanons : List (List String) :=
    probeCtx.recMeta.filterMap fun rm =>
      if rm.isCoind then
        rm.constr.map (fun cNm => rm.recCanon.dropLast ++ [cNm])
      else none

  let unitConstructsOrLoopsCoind (u : ModUnit) : Bool :=
    match u.kind with
    | .recUnit _ _ _ _ rd _ => rd.coind
    | .funUnit _ fNm sigTy cs =>
        let retCoind := match resultHeadCanon sigTy with
          | some rc => allCoindRecs.contains rc
          | none    => false
        let selfCanon := curMod.modName.full ++ [fNm]
        let isRec := cs.any (mentionsClause selfCanon)
        let usesCoindCon := u.bodyQNames.any (coindConCanons.contains ·)
        let hasRecLit := cs.any clauseHasRecLit
        usesCoindCon || (retCoind && isRec) || (!allCoindRecs.isEmpty && hasRecLit)
    | .anonUnit _ _ cs =>
        !allCoindRecs.isEmpty && cs.any clauseHasRecLit
    | _ => false

  let mut slowIds : List Nat := []
  let mut fastIds : List Nat := []
  let importedOpaque := (depExps.flatMap (·.slowExports)).eraseDups
  let mut slowValCanons := importedOpaque
  let mut unboundarySlowIds : List Nat := []

  for scc in sccs do
    let sccUnits := scc.filterMap (fun uid => units.find? (·.uid == uid))
    let mut sccSlow ← match probeGroup probeCtx sccUnits with
      | .syntaxErr e => PrismOutcome.syntaxErr e
      | .bot _ => pure true
      | .translated () => pure false
    for u in sccUnits do
      if unitConstructsOrLoopsCoind u then
        sccSlow := true
      -- Boundary taint 1: function/proof signature mentions a slow value/projection (needs unfolding in Agda!).
      -- Pure `dataUnit` declarations only check constructor type well-formedness (`Type`) and strict positivity
      -- without unfolding slow value bodies, so keeping `dataUnit` in `FastFocus` preserves full Lean `inductive`!
      let isPureData := match u.kind with | .dataUnit _ _ _ _ _ => true | _ => false
      if !isPureData && u.sigQNames.any (slowValCanons.contains ·) then
        sccSlow := true
      -- Boundary taint 2: references a slow unit that cannot even be exposed as a Lean `axiom` stub
      let allLocalDeps := deps u
      if allLocalDeps.any (unboundarySlowIds.contains ·) then
        sccSlow := true

    if sccSlow then
      slowIds := slowIds ++ scc
      for u in sccUnits do
        slowValCanons := (slowValCanons ++ u.valueCanons).eraseDups
        match probeBoundary probeCtx u with
        | .translated _ => pure ()
        | _ => unboundarySlowIds := u.uid :: unboundarySlowIds
    else
      fastIds := fastIds ++ scc

  -- Definitional-reduction fixed-point closure over `sccs`:
  -- (a) If a non-data unit `u` mentions in its type signature (`unitLocalSigDeps`) any `funUnit`
  --     that transitively reaches `slowIds`, `u` may rely on unfolding that call and must join `slowIds`.
  -- (b) If any unit already in `slowIds` depends on a `funUnit` SCC that itself transitively reaches
  --     `slowIds` (or `unboundarySlowIds`), that intermediate `funUnit` SCC cannot remain an abstract
  --     `_SlowResidual` parameter and must also join `slowIds`.
  let isFunSCC (scc : List Nat) : Bool :=
    scc.any fun uid =>
      match units.find? (·.uid == uid) with
      | some u => match u.kind with | .funUnit _ _ _ _ | .anonUnit _ _ _ => true | _ => false
      | none   => false
  let mut conversionDeps := slowIds
  let mut changed := !slowIds.isEmpty || !importedOpaque.isEmpty
  while changed do
    changed := false
    let curSlowValCanons : List (List String) :=
      (importedOpaque ++ (units.filter (fun u => slowIds.contains u.uid)).flatMap (·.valueCanons)).eraseDups
    let mut reachesAnySlow : List Nat := slowIds
    let mut reachesSlowFun : List Nat :=
      slowIds.filter (fun uid => isFunSCC [uid])
    for scc in sccs do
      if isFunSCC scc then
        let sccUnits := scc.filterMap (fun uid => units.find? (·.uid == uid))
        if scc.any (slowIds.contains ·) ||
           sccUnits.any (fun u => (deps u).any (reachesAnySlow.contains ·)) then
          reachesAnySlow := (reachesAnySlow ++ scc).eraseDups
        let touchesSlowVal := sccUnits.any fun u =>
          let allQs := u.sigQNames ++ u.bodyQNames
          allQs.any (curSlowValCanons.contains ·) ||
          (deps u).any (reachesSlowFun.contains ·)
        if scc.any (reachesSlowFun.contains ·) || touchesSlowVal then
          reachesSlowFun := (reachesSlowFun ++ scc).eraseDups
    conversionDeps := reachesSlowFun
    let slowUsedDeps : List Nat :=
      (units.filter (fun u => slowIds.contains u.uid)).flatMap (deps) |>.eraseDups
    for scc in sccs do
      if !scc.any (slowIds.contains ·) then
        let sccUnits := scc.filterMap (fun uid => units.find? (·.uid == uid))
        let pullBySig := sccUnits.any fun u =>
          let isPureData := match u.kind with | .dataUnit _ _ _ _ _ => true | _ => false
          !isPureData &&
          (u.sigQNames.any (curSlowValCanons.contains ·) ||
           (graph.signatures[u.uid]?.getD []).any (reachesSlowFun.contains ·))
        let pullIntermediate :=
          isFunSCC scc && scc.any (reachesAnySlow.contains ·) && scc.any (slowUsedDeps.contains ·)
        let pullUnboundary :=
          sccUnits.any fun u => (deps u).any (unboundarySlowIds.contains ·)
        if pullBySig || pullIntermediate || pullUnboundary then
          slowIds := (slowIds ++ scc).eraseDups
          fastIds := fastIds.filter (fun id => !scc.contains id)
          for u in sccUnits do
            match probeBoundary probeCtx u with
            | .translated _ => pure ()
            | _ => unboundarySlowIds := (u.uid :: unboundarySlowIds).eraseDups
          changed := true

  let ownSlowExports :=
    (units.filter (fun u => slowIds.contains u.uid)).flatMap (·.valueCanons) |>.eraseDups
  -- An otherwise fast helper can return an expression blocked on an opaque call.
  -- Its clients may compute through that helper when checking their signatures.
  let exportedOpaque := (units.filter (fun u => conversionDeps.contains u.uid)).flatMap (·.valueCanons)
  let updatedExp : ExportedModule :=
    { curExp with slowExports := (ownSlowExports ++ exportedOpaque).eraseDups }
  let plan : SlicePlan :=
    { headers          := headers
    , units            := units
    , sccs             := sccs
    , slowUnitIds      := slowIds
    , fastUnitIds      := fastIds
    , slowExportCanons := ownSlowExports
    , coindRecCanons   := allCoindRecs }
  .translated (plan, updatedExp)

end Prism
