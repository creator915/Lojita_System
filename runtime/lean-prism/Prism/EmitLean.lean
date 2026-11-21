import Prism.LensSlice

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.EmitLean`: Three-Mode Lean 4 Emitter & Unit-SCC Lens Classifier

Supports three unified emission modes over `CodeMod`:
1. `EmitMode.pureFast`: Zero-overhead pure Lean 4 emission when `SlowUnits = ∅`
   across the module and its imports (identical to v1 fast path).
2. `EmitMode.hybridCheck` (`Lens.put` Layer 1 — Fast-Lane Verification):
   Emits `F₁` and `F₂` as full kernel-checked Lean `inductive`/`structure`/`def`
   (`termination_by structural`), while exposing `S` (`SlowUnits`) as typed,
   reduction-free boundary declarations `∂_S` inside `noncomputable section`
   (simultaneously verified by Agda on parameterized `SlowSlice_<Mod>.agda`).
3. `EmitMode.erasedExec` (`Lens.put` Layer 2 — Unified Native C Codegen):
   Executed ONLY AFTER both `hybridCheck` and `SlowSlice` pass! Lowers `S` directly
   into the same Lean 4 C build (`coinductive` records → memoized `Thunk` structures
   + `.get` projections; copatterns → universal product `Thunk.mk` `partial def`;
   multi-arg/mutual Foetus & `with`-clauses → `partial def` + `match`), linking
   `F₁ + S_lowered + F₂ + Main` into a single ~5 MB `leanc -O3` native binary.
-/

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

structure EmitCtx : Type where
  modPrefix    : List String
  mode         : EmitMode := .pureFast
  usesDepSigma : Bool := true
  symByCanon   : List (List String × SymInfo)
  sigImplicits : List (List String × List String)  -- canonPath -> ordered implicit binder names
  recMeta      : List RecMetaEntry

private def allStdModules : List (List SymInfo) :=
  [ builtinNatExports, dataNatExports, dataNatPropsExports, dataNatShowExports, dataNatDivModExports
  , builtinIntExports, dataIntExports, dataIntPropsExports
  , builtinBoolExports, dataBoolExports, dataBoolPropsExports, builtinListExports, dataListExports
  , dataListAnyExports, dataListAllExports
  , dataMaybeExports, dataProductExports, dataSumExports, dataFinExports
  , dataCharExports, dataCharPropsExports, dataStringExports, dataStringPropsExports
  , dataUnitExports, dataPolyUnitExports
  , dataEmptyExports, relNullaryExports, propEqExports, functionExports
  , blueprintExports, polyTransportExports, terminalExports, filterExports
  , clockExports, clockLawsExports, termLawsExports, fuzzGenExports
  , fsSandboxExports, fsLawsExports, netSandboxExports, netLawsExports
  , gitSandboxExports, gitLawsExports, webOperadExports
  , worldExports, worldLawsExports, protocolExports
  , ioExports, primIOExports, primFiniteIOExports, sysEnvExports, ffiSafeExports, worldRunnerExports ]

private def stdImplicitNames : List (List String × List String) :=
  [ (["Agda", "Builtin", "Equality", "_≡_"], ["A"])
  , (["Agda", "Builtin", "Equality", "_≡_", "refl"], ["A", "x"])
  , (["Relation", "Binary", "PropositionalEquality", "Core", "sym"], ["A", "x", "y"])
  , (["Relation", "Binary", "PropositionalEquality", "Core", "trans"], ["A", "x", "y", "z"])
  , (["Relation", "Binary", "PropositionalEquality", "Core", "cong"], ["A", "B"])
  , (["Relation", "Binary", "PropositionalEquality", "cong₂"], ["A", "B", "C"])
  , (["Relation", "Binary", "PropositionalEquality", "Core", "subst"], ["A"])
  , (["Relation", "Nullary", "Decidable", "Core", "does"], ["P"])
  , (["Data", "Bool", "Base", "if_then_else_"], ["A"])
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
  , (["IO", "Base", "_>>=_"], ["A", "B"])
  , (["IO", "Base", "_>>_"], ["A", "B"])
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

private def collectLevelVarsInType : Expr → List String :=
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

private def leanEscapeStr (s : String) : String :=
  let hexDigit (n : Nat) : Char :=
    if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))
  let rec go : List Char → List Char
    | [] => []
    | '"' :: cs  => '\\' :: '"' :: go cs
    | '\\' :: cs => '\\' :: '\\' :: go cs
    | '\n' :: cs => '\\' :: 'n' :: go cs
    | '\r' :: cs => '\\' :: 'r' :: go cs
    | '\t' :: cs => '\\' :: 't' :: go cs
    | c :: cs    =>
        if c.toNat < 32 || c.toNat == 127 then
          let v := c.toNat
          '\\' :: 'x' :: hexDigit (v / 16) :: hexDigit (v % 16) :: go cs
        else
          c :: go cs
  "\"" ++ String.ofList (go s.toList) ++ "\""

private def leanEscapeChar (c : Char) : String :=
  if c == '\'' then "'\\''"
  else if c == '\\' then "'\\\\'"
  else if c == '\n' then "'\\n'"
  else if c == '\r' then "'\\r'"
  else if c == '\t' then "'\\t'"
  else if c.toNat >= 32 && c.toNat < 127 then "'" ++ String.singleton c ++ "'"
  else
    let hexDigit (n : Nat) : Char :=
      if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))
    let v := c.toNat
    if v < 256 then
      s!"'\\x{String.ofList [hexDigit (v / 16), hexDigit (v % 16)]}'"
    else
      "'" ++ String.singleton c ++ "'"

private def natSucPatStr : Nat → String
  | 0     => "Nat.zero"
  | n + 1 => s!"(Nat.succ {natSucPatStr n})"

private def emitLit : Lit → String
  | .natL 0  => "Nat.zero"
  | .natL n  => s!"(OfNat.ofNat {n} : Nat)"
  | .strL s  => s!"({leanEscapeStr s} : String)"
  | .charL c => s!"(Char.ofNat {c.toNat} : Char)"

private def resolveLeanQName (ctx : EmitCtx) (q : QName) : PrismOutcome String :=
  match ctx.symByCanon.find? (fun (c, _) => c == q.full) with
  | some (_, info) => .translated info.leanName
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

-- Detect if a field list in `record { f₁ = e₁ ; ... }` belongs to a known coinductive record
private def isCoindFieldSet (ctx : EmitCtx) (fNames : List String) : Bool :=
  !fNames.isEmpty &&
  ctx.recMeta.any fun rm =>
    rm.isCoind &&
    let rFieldNames := rm.fields.map Prod.fst
    fNames.all (rFieldNames.contains ·)

-- Resolve record field identifier: user/dependency records use `leanMangleIdent`,
-- whereas precompiled `StdScope` (`AgdaMirror`) records use their native Lean field name!
private def resolveRecFieldIdent (ctx : EmitCtx) (fNames : List String) (fn : String) : String :=
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
  private partial def collectVarsExpr : Expr → List String
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

  private partial def collectVarsLetBind : LetBind → List String
    | .letBind _ ty rhs => collectVarsExpr ty ++ collectVarsExpr rhs
    | .letPat _ rhs     => collectVarsExpr rhs

  private partial def collectVarsRhs : RHS → List String
    | .rhs body => collectVarsExpr body
    | .withRHS es scs =>
        es.flatMap collectVarsExpr ++
        scs.flatMap (fun (.clause _ sr sws) => collectVarsRhs sr ++ sws.flatMap collectVarsDecl)
    | .rewriteRHS es inner => es.flatMap collectVarsExpr ++ collectVarsRhs inner
    | .absurdRHS => []

  private partial def collectVarsDecl : Decl → List String
    | .sig _ _ ty => collectVarsExpr ty
    | .fun_ _ _ cs => cs.flatMap (fun (.clause _ r ws) => collectVarsRhs r ++ ws.flatMap collectVarsDecl)
    | .dataSig _ _ ps s => ps.flatMap (fun (.bind _ _ t) => collectVarsExpr t) ++ collectVarsExpr s
    | .dataDef _ _ _ cons => cons.flatMap (fun (_, t) => collectVarsExpr t)
    | .recSig _ _ ps s => ps.flatMap (fun (.bind _ _ t) => collectVarsExpr t) ++ collectVarsExpr s
    | .recDef _ _ _ _ flds => flds.flatMap (fun (_, t) => collectVarsExpr t)
    | .patSyn _ _ _ e => collectVarsExpr e
    | _ => []
end

private partial def wildcardUnusedPat (usedVars : List String) : Pat → Pat
  | .varP x   => if usedVars.contains x then .varP x else .wildP
  | .asP x p  =>
      let p' := wildcardUnusedPat usedVars p
      if usedVars.contains x then .asP x p' else p'
  | .conP q ps => .conP q (ps.map (fun a => { a with thing := wildcardUnusedPat usedVars a.thing }))
  | .recP fs   => .recP (fs.map (fun (fn, fp) => (fn, wildcardUnusedPat usedVars fp)))
  | p          => p

mutual
  partial def emitExpr (ctx : EmitCtx) (lvlVars : List String) : Expr → PrismOutcome String
    | .var x =>
        if x == "_" then .translated "_"
        else .translated (leanMangleIdent x)
    | .def_ q => resolveLeanQName ctx q
    | .con q  => resolveLeanQName ctx q
    | .lit l  => .translated (emitLit l)
    | .set n  => .translated (if n == 0 then "Type" else s!"Type {n}")
    | .hole   => .syntaxErr "unsolved interaction hole '?'/'{!!}' is forbidden"
    | .meta_  => .translated "_"
    | .dot e  => emitExpr ctx lvlVars e
    | .absurdLam .visible => .translated "(fun _abs => nomatch _abs)"
    | .absurdLam .hidden  => .translated "(fun {_abs} => nomatch _abs)"
    | .absurdLam .inst    => .bot "instance absurd lambda routed to Agda"
    | .lamCase cs => do
        if ctx.mode != .erasedExec then
          .bot "extended lambda ('λ where') routed to Agda"
        else do
          let liveCs := cs.filter fun | .clause _ .absurdRHS _ => false | _ => true
          if liveCs.isEmpty then
            .translated "(fun _abs => nomatch _abs)"
          else do
            let arms ← liveCs.mapM fun
              | .clause (.head _ ps) (.rhs body) [] => do
                  let visPs := ps.filter (fun a => a.hid == .visible)
                  if visPs.isEmpty then
                    PrismOutcome.bot "0-arg lamCase routed to Agda"
                  let used := collectVarsExpr body
                  let pStrs ← visPs.mapM (fun a => emitPat ctx (wildcardUnusedPat used a.thing))
                  let bStr ← emitExpr ctx lvlVars body
                  .translated ("| " ++ String.intercalate ", " pStrs ++ " => " ++ bStr)
              | _ => .bot "complex lamCase clause routed to MAlonzo"
            .translated ("(fun " ++ String.intercalate " " arms ++ ")")
    | e@(.app _ _) =>
        match e with
        | .app (.set 0) { hid := .visible, thing := .var u, .. } =>
            if lvlVars.contains u then
              .translated s!"Type u_{u}"
            else
              emitAppSpine ctx lvlVars e
        | _ => emitAppSpine ctx lvlVars e
    | .lam a body => do
        let bStr ← emitExpr ctx lvlVars body
        let v := if a.thing == "_" then "_" else leanMangleIdent a.thing
        match a.hid with
        | .visible => .translated s!"(fun {v} => {bStr})"
        | .hidden  => .translated ("(fun {" ++ v ++ "} => " ++ bStr ++ ")")
        | .inst    => .bot "instance lambda routed to Agda"
    | .lamT (.bind h xs .meta_) body => do
        if h == .inst then
          .bot "instance lambda routed to Agda"
        else do
          let bStr ← emitExpr ctx lvlVars body
          let vs := String.intercalate " " (xs.map fun x => if x == "_" then "_" else leanMangleIdent x)
          let binder := match h with
            | .visible => vs
            | .hidden  => "{" ++ vs ++ "}"
            | .inst    => ""
          .translated s!"(fun {binder} => {bStr})"
    | .lamT (.bind h xs ty) body => do
        if h == .inst then
          .bot "instance lambda routed to Agda"
        else do
          let tyStr ← emitExpr ctx lvlVars ty
          let bStr ← emitExpr ctx lvlVars body
          let vs := String.intercalate " " (xs.map fun x => if x == "_" then "_" else leanMangleIdent x)
          let binder := match h with
            | .visible => "(" ++ vs ++ " : " ++ tyStr ++ ")"
            | .hidden  => "{" ++ vs ++ " : " ++ tyStr ++ "}"
            | .inst    => ""
          .translated s!"(fun {binder} => {bStr})"
    | .pi (.bind h xs (.def_ q)) body =>
        if q.full == ["Agda", "Primitive", "Level"] then
          emitExpr ctx (lvlVars ++ xs) body
        else
          emitPiBind ctx lvlVars h xs (.def_ q) body
    | .pi (.bind h xs .meta_) body => do
        if h == .inst then .bot "instance binder routed to Agda"
        let bStr ← emitExpr ctx lvlVars body
        let vs := String.intercalate " " (xs.map fun x => if x == "_" then "_" else leanMangleIdent x)
        let binder := if h == .hidden then "{" ++ vs ++ " : _}" else "(" ++ vs ++ " : _)"
        .translated s!"({binder} → {bStr})"
    | .pi (.bind h xs ty) body =>
        emitPiBind ctx lvlVars h xs ty body
    | .fun_ a body => do
        if a.hid == .inst then .bot "instance arrow routed to Agda"
        let domStr ← emitExpr ctx lvlVars a.thing
        let codStr ← emitExpr ctx lvlVars body
        match a.hid with
        | .visible => .translated s!"({domStr} → {codStr})"
        | .hidden  => .translated ("({_ : " ++ domStr ++ "} → " ++ codStr ++ ")")
        | .inst    => .bot "instance arrow routed to Agda"
    | .let_ bs body => do
        let bStr ← emitExpr ctx lvlVars body
        let rec wrapLets : List LetBind → PrismOutcome String
          | [] => .translated bStr
          | .letBind x .meta_ rhs :: rest => do
              if ctx.mode != .erasedExec && mentionsQName ["Agda", "Builtin", "Sigma", "_,_"] rhs then
                PrismOutcome.bot "untyped dependent pair in 'let' routed to Agda meta-unifier"
              let rStr ← emitExpr ctx lvlVars rhs
              let inner ← wrapLets rest
              .translated s!"(let {leanMangleIdent x} := {rStr}; {inner})"
          | .letBind x ty rhs :: rest => do
              let tStr ← emitExpr ctx lvlVars ty
              let rStr ← emitExpr ctx lvlVars rhs
              let inner ← wrapLets rest
              .translated s!"(let {leanMangleIdent x} : {tStr} := {rStr}; {inner})"
          | .letPat pat rhs :: rest => do
              let used := rest.flatMap collectVarsLetBind ++ collectVarsExpr body
              let pStr ← emitPat ctx (wildcardUnusedPat used pat)
              let rStr ← emitExpr ctx lvlVars rhs
              let inner ← wrapLets rest
              .translated s!"(match {rStr} with | {pStr} => {inner})"
        wrapLets bs
    | .rec_ fs => do
        let fNames := fs.map Prod.fst
        let isCoind := ctx.mode == .erasedExec && isCoindFieldSet ctx fNames
        let assignStrs ← fs.mapM fun (fn, fv) => do
          let vStr ← emitExpr ctx lvlVars fv
          if isCoind then
            .translated s!"_thunk_{leanMangleIdent fn} := Thunk.mk (fun _ => {vStr})"
          else
            .translated s!"{resolveRecFieldIdent ctx fNames fn} := {vStr}"
        .translated ("{ " ++ String.intercalate ", " assignStrs ++ " }")
    | .recUpd base fs => do
        let fNames := fs.map Prod.fst
        let isCoind := ctx.mode == .erasedExec && isCoindFieldSet ctx fNames
        let baseStr ← emitExpr ctx lvlVars base
        let assignStrs ← fs.mapM fun (fn, fv) => do
          let vStr ← emitExpr ctx lvlVars fv
          if isCoind then
            .translated s!"_thunk_{leanMangleIdent fn} := Thunk.mk (fun _ => {vStr})"
          else
            .translated s!"{resolveRecFieldIdent ctx fNames fn} := {vStr}"
        .translated ("{ " ++ baseStr ++ " with " ++ String.intercalate ", " assignStrs ++ " }")

  partial def emitPiBind (ctx : EmitCtx) (lvlVars : List String) (h : Hiding)
      (xs : List String) (ty body : Expr) : PrismOutcome String := do
    if h == .inst then .bot "instance Pi binder routed to Agda"
    let tStr ← emitExpr ctx lvlVars ty
    let bStr ← emitExpr ctx lvlVars body
    let vs := String.intercalate " " (xs.map fun x => if x == "_" then "_" else leanMangleIdent x)
    let binder := if h == .hidden then "{" ++ vs ++ " : " ++ tStr ++ "}" else "(" ++ vs ++ " : " ++ tStr ++ ")"
    .translated s!"({binder} → {bStr})"

  partial def emitAppSpine (ctx : EmitCtx) (lvlVars : List String) (e : Expr) : PrismOutcome String := do
    let (hd, args) := unrollApps e
    if args.any (fun a => a.hid == .inst) then
      .bot "instance argument application routed to Agda"
    -- In `erasedExec`, emit short-circuiting `match` for `if_then_else_`, `_∧_`, `_∨_`
    -- so strict call-by-value C codegen never eagerly evaluates untaken recursive branches!
    if ctx.mode == .erasedExec then
      let visOnly := args.filter (fun a => a.hid == .visible)
      if args.all (fun a => a.hid == .visible || a.hid == .hidden) then
        match hd, visOnly with
        | .def_ q, [cArg, tArg, fArg] =>
            if q.full == ["Data", "Bool", "Base", "if_then_else_"] then do
              let cStr ← emitExpr ctx lvlVars cArg.thing
              let tStr ← emitExpr ctx lvlVars tArg.thing
              let fStr ← emitExpr ctx lvlVars fArg.thing
              return s!"(match {cStr} with | Bool.true => {tStr} | Bool.false => {fStr})"
        | .def_ q, [aArg, bArg] =>
            if q.full == ["Data", "Bool", "Base", "_∧_"] then do
              let aStr ← emitExpr ctx lvlVars aArg.thing
              let bStr ← emitExpr ctx lvlVars bArg.thing
              return s!"(match {aStr} with | Bool.true => {bStr} | Bool.false => Bool.false)"
            else if q.full == ["Data", "Bool", "Base", "_∨_"] then do
              let aStr ← emitExpr ctx lvlVars aArg.thing
              let bStr ← emitExpr ctx lvlVars bArg.thing
              return s!"(match {aStr} with | Bool.true => Bool.true | Bool.false => {bStr})"
        | _, _ => pure ()
    let hdStr ← emitExpr ctx lvlVars hd
    let headCanon : Option (List String) :=
      match hd with
      | .def_ q => some q.full
      | .con q  => some q.full
      | _       => none
    let knownImps : List String :=
      match headCanon.bind (fun c => ctx.sigImplicits.find? (fun (k, _) => k == c)) with
      | some (_, ns) => ns
      | none         => []
    let mut parts : List String := [hdStr]
    let mut impIdx : Nat := 0
    for a in args do
      match a.hid with
      | .visible =>
          let aStr ← emitExpr ctx lvlVars a.thing
          parts := parts ++ [aStr]
      | .hidden =>
          let aStr ← emitExpr ctx lvlVars a.thing
          match a.label with
          | some lbl =>
              let targetLbl :=
                if headCanon.any (fun c => !(c.take ctx.modPrefix.length == ctx.modPrefix) &&
                    (lookupStdModule (String.intercalate "." (c.dropLast))).isSome) then
                  lbl
                else
                  leanMangleIdent lbl
              parts := parts ++ [s!"({targetLbl} := {aStr})"]
              impIdx := impIdx + 1
          | none =>
              match knownImps[impIdx]? with
              | some paramNm =>
                  if paramNm == "_" then
                    PrismOutcome.bot "positional application of unnamed implicit parameter routed to Agda"
                  else
                    parts := parts ++ [s!"({paramNm} := {aStr})"]
                    impIdx := impIdx + 1
              | none =>
                  PrismOutcome.bot "positional implicit application without known parameter name routed to Agda"
      | .inst => PrismOutcome.bot "instance application routed to Agda"
    .translated ("(" ++ String.intercalate " " parts ++ ")")

  partial def emitPat (ctx : EmitCtx) : Pat → PrismOutcome String
    | .varP x => .translated (leanMangleIdent x)
    | .wildP  => .translated "_"
    | .litP (.natL 0) => .translated "Nat.zero"
    | .litP (.natL n) =>
        if ctx.mode != .erasedExec && n <= 16 then
          .translated (natSucPatStr n)
        else
          .translated (toString n)
    | .litP (.strL s) => .translated (leanEscapeStr s)
    | .litP (.charL c) => .translated (leanEscapeChar c)
    | .dotP _   =>
        if ctx.mode == .erasedExec then .translated "_"
        else .bot "dot pattern routed to Agda"
    | .projP _  => .bot "copattern projection routed to Agda"
    | .absurdP  => .bot "absurd pattern handled at clause level"
    | .asP x p  => do
        let pStr ← emitPat ctx p
        .translated s!"({leanMangleIdent x}@({pStr}))"
    | .conP q ps => do
        if ctx.mode != .erasedExec && ps.any (fun a => a.hid != .visible) then
          .bot "implicit constructor pattern argument routed to Agda"
        let visPs := ps.filter (fun a => a.hid == .visible)
        let cStr ← resolveLeanQName ctx q
        if visPs.isEmpty then
          .translated cStr
        else do
          let argStrs ← visPs.mapM (fun a => emitPat ctx a.thing)
          .translated ("(" ++ cStr ++ " " ++ String.intercalate " " argStrs ++ ")")
    | .recP fs => do
        let fNames := fs.map Prod.fst
        let fStrs ← fs.mapM fun (fn, fp) => do
          let pStr ← emitPat ctx fp
          .translated s!"{resolveRecFieldIdent ctx fNames fn} := {pStr}"
        .translated ("{ " ++ String.intercalate ", " fStrs ++ " }")
end

-- §2 Fast-Lane Unit Emitter (`F₁` & `F₂`)

private def emitTeleBinders (ctx : EmitCtx) (lvlVars : List String) (bs : List Bind) :
    PrismOutcome String := do
  let strs ← bs.mapM fun (.bind h xs ty) => do
    if h == .inst then PrismOutcome.bot "instance parameter routed to Agda"
    let tStr ← emitExpr ctx lvlVars ty
    let vs := String.intercalate " " (xs.map leanMangleIdent)
    match h with
    | .visible => .translated ("(" ++ vs ++ " : " ++ tStr ++ ")")
    | .hidden  => .translated ("{" ++ vs ++ " : " ++ tStr ++ "}")
    | .inst    => .bot "instance parameter"
  .translated (String.intercalate " " strs)

private def emitImplicitTeleBinders (ctx : EmitCtx) (lvlVars : List String) (bs : List Bind) :
    PrismOutcome String := do
  let strs ← bs.mapM fun (.bind h xs ty) => do
    if h == .inst then PrismOutcome.bot "instance parameter routed to Agda"
    let tStr ← emitExpr ctx lvlVars ty
    let vs := String.intercalate " " (xs.map leanMangleIdent)
    .translated ("{" ++ vs ++ " : " ++ tStr ++ "}")
  .translated (String.intercalate " " strs)

private partial def splitLeadingHiddenBinds (ctx : EmitCtx) (lvlVars : List String) (ty : Expr) :
    PrismOutcome (List (String × String) × List String × Expr) := do
  match ty with
  | .pi (.bind .hidden xs (.def_ q)) rest =>
      if q.full == ["Agda", "Primitive", "Level"] then
        splitLeadingHiddenBinds ctx (lvlVars ++ xs) rest
      else do
        let tStr ← emitExpr ctx lvlVars (.def_ q)
        let cur := xs.map fun x => (x, "{" ++ (if x == "_" then "_" else leanMangleIdent x) ++ " : " ++ tStr ++ "}")
        let (morePairs, moreStrs, remTy) ← splitLeadingHiddenBinds ctx lvlVars rest
        .translated (cur ++ morePairs, cur.map Prod.snd ++ moreStrs, remTy)
  | .pi (.bind .hidden xs .meta_) rest => do
      let cur := xs.map fun x => (x, "{" ++ (if x == "_" then "_" else leanMangleIdent x) ++ " : _}")
      let (morePairs, moreStrs, remTy) ← splitLeadingHiddenBinds ctx lvlVars rest
      .translated (cur ++ morePairs, cur.map Prod.snd ++ moreStrs, remTy)
  | .pi (.bind .hidden xs dom) rest => do
      let tStr ← emitExpr ctx lvlVars dom
      let cur := xs.map fun x => (x, "{" ++ (if x == "_" then "_" else leanMangleIdent x) ++ " : " ++ tStr ++ "}")
      let (morePairs, moreStrs, remTy) ← splitLeadingHiddenBinds ctx lvlVars rest
      .translated (cur ++ morePairs, cur.map Prod.snd ++ moreStrs, remTy)
  | _ => .translated ([], [], ty)

private def resolveImplicitAliasLets (slots : List String) (hidPats : List (Arg Pat)) :
    Option (List String) :=
  if hidPats.any (fun a => a.hid != .hidden) then none
  else if hidPats.any (fun a => match a.thing with | .varP _ | .wildP => false | _ => true) then none
  else
    let rec go (idx : Nat) (rem : List (Arg Pat)) (lets : List String) : Option (List String) :=
      match rem with
      | [] => some lets.reverse
      | a :: rest =>
          match a.label with
          | none =>
              match slots[idx]? with
              | none => none
              | some formal =>
                  let addLet := match a.thing with
                    | .varP v =>
                        if v == formal || formal == "_" then []
                        else [s!"let {leanMangleIdent v} := {leanMangleIdent formal}"]
                    | _ => []
                  go (idx + 1) rest (addLet ++ lets)
          | some lbl =>
              match slots.findIdx? (· == lbl) with
              | none => none
              | some foundIdx =>
                  let addLet := match a.thing with
                    | .varP v =>
                        if v == lbl then []
                        else [s!"let {leanMangleIdent v} := {leanMangleIdent lbl}"]
                    | _ => []
                  go (foundIdx + 1) rest (addLet ++ lets)
    go 0 hidPats []

private partial def hasInterleavedImplicitBeforeK : Nat → Expr → Bool
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

private def emitPatSynAbbrev (ctx : EmitCtx) (synNm : String) (args : List String) (rExpr : Expr) :
    PrismOutcome String := do
  let leanSyn := leanMangleIdent synNm
  let argBinds :=
    if args.isEmpty then ""
    else " " ++ String.intercalate " " (args.map (fun a => s!"({leanMangleIdent a} : _)"))
  let rhsStr ← emitExpr ctx [] rExpr
  .translated s!"@[match_pattern] abbrev {leanSyn}{argBinds} :=\n  {rhsStr}"

private partial def codomainIsSet : Expr → Bool
  | .set _               => true
  | .app (.set 0) _      => true
  | .pi _ rest           => codomainIsSet rest
  | .fun_ _ rest         => codomainIsSet rest
  | _                    => false

private partial def looksLikeTypeRhs : Expr → Bool
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

private partial def replaceFirstAbsurdPat : Pat → Option Pat
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

private def emitFunctionDef (ctx : EmitCtx) (fnName : String) (sigTy : Expr)
    (clauses : List Clause) (anonIdx : Option Nat) : PrismOutcome (String × String) := do
  let leanFn := match anonIdx with
    | some idx => s!"_ag_anon_test_{idx}"
    | none     => leanMangleIdent fnName
  let recInfo ← analyzeFunctionRecursion ctx.modPrefix fnName clauses
  let lvlVars := collectLevelVarsInType sigTy
  let uDecl :=
    if lvlVars.isEmpty then ""
    else "." ++ "{" ++ String.intercalate " " (lvlVars.map (s!"u_{·}")) ++ "}"
  let (impPairs, impBindStrs, coreSigTy) ← splitLeadingHiddenBinds ctx lvlVars sigTy
  let impParamHeader := if impBindStrs.isEmpty then "" else " " ++ String.intercalate " " impBindStrs
  let tyAnnot ←
    if isMetaExpr coreSigTy then .translated ""
    else do
      let tyStr ← emitExpr ctx lvlVars coreSigTy
      .translated s!" : {tyStr}"
  let isTypeAbbrev :=
    anonIdx.isNone &&
    (match recInfo with | .nonRecursive => true | _ => false) &&
    match clauses with
    | [.clause (.head _ ps) (.rhs body) []] =>
        ps.all (fun a => match a.thing with | .varP _ | .wildP => true | _ => false) &&
        (codomainIsSet coreSigTy || (isMetaExpr coreSigTy && ps.isEmpty && looksLikeTypeRhs body))
    | _ => false
  let kw := if isTypeAbbrev then "abbrev" else "def"
  let fullHeader := s!"{kw} {leanFn}{uDecl}{impParamHeader}{tyAnnot}"
  let impSlotNames := impPairs.map Prod.fst

  if clauses.any (fun (.clause _ _ ws) => !ws.isEmpty) then
    emitWithWhere ctx leanFn fullHeader impSlotNames lvlVars coreSigTy clauses recInfo
  else
    emitPlainClauses ctx leanFn fullHeader impSlotNames lvlVars coreSigTy clauses recInfo
  where
    emitPlainClauses (ctx : EmitCtx) (leanFn fullHeader : String) (impSlots lvlVars : List String)
        (coreSigTy : Expr) (clauses : List Clause) (recInfo : RecAnalysis) :
        PrismOutcome (String × String) := do
      match clauses with
      | [.clause (.head _ []) (.rhs body) []] => do
          let bStr ← emitExpr ctx lvlVars body
          .translated (leanFn, s!"{fullHeader} :=\n  {bStr}")
      | _ => do
          let liveClauses : List Clause := clauses.filter fun c =>
            match c with
            | Clause.clause _ RHS.absurdRHS _ => false
            | _ => true
          match liveClauses with
          | [] =>
            match clauses with
            | [.clause (.head _ ps) .absurdRHS []] =>
                let (hidPfx, visRest) := ps.span (fun a => a.hid != Hiding.visible)
                if visRest.isEmpty || visRest.any (fun a => a.hid != Hiding.visible) then
                  .bot "implicit absurd clause routed to Agda"
                else if hasInterleavedImplicitBeforeK visRest.length coreSigTy then
                  .bot "interleaved implicit Pi binder in absurd function routed to Agda"
                else
                  match resolveImplicitAliasLets impSlots hidPfx with
                  | none => .bot "implicit constructor pattern in absurd clause routed to Agda"
                  | some aliasLets =>
                      let rec findAndReplace : List (Arg Pat) → Option (List Pat)
                        | [] => none
                        | a :: as =>
                            match replaceFirstAbsurdPat a.thing with
                            | some p' => some (p' :: as.map (·.thing))
                            | none    => (findAndReplace as).map (a.thing :: ·)
                      match findAndReplace visRest with
                      | none => .bot "absurd clause missing '()' pattern routed to Agda"
                      | some replacedPats => do
                          let pStrs ← replacedPats.mapM fun p =>
                            emitPat ctx (wildcardUnusedPat ["_abs_bot"] p)
                          let rhsFull := String.intercalate "; " (aliasLets ++ [s!"nomatch {leanMangleIdent "_abs_bot"}"])
                          .translated (leanFn, s!"{fullHeader}\n  | {String.intercalate ", " pStrs} => {rhsFull}")
            | _ => .bot "multi-clause absurd-only function routed to Agda"
          | _ :: _ => do
            let splitClause (c : Clause) : Option (List String × List (Arg Pat) × Expr) :=
              match c with
              | Clause.clause (LHS.head _ ps) (RHS.rhs body) _ =>
                  let (hidPfx, visRest) := ps.span (fun a => a.hid != Hiding.visible)
                  if visRest.any (fun a => a.hid != Hiding.visible) then none
                  else
                    match resolveImplicitAliasLets impSlots hidPfx with
                    | some aliasLets => some (aliasLets, visRest, body)
                    | none           => none
              | _ => none
            let splitOpt := liveClauses.mapM splitClause
            match splitOpt with
            | none => .bot s!"function '{fnName}' uses copattern/with/implicit-con LHS; routed to slow slice"
            | some unpacked =>
                match unpacked with
                | [] => .bot "empty clause list"
                | [(aliasLets, [], body)] => do
                    let bStr ← emitExpr ctx lvlVars body
                    let rhsFull := String.intercalate "; " (aliasLets ++ [bStr])
                    .translated (leanFn, s!"{fullHeader} :=\n  {rhsFull}")
                | (_, firstVis, _) :: _ => do
                    let k := firstVis.length
                    if k == 0 || unpacked.any (fun (_, vp, _) => vp.length != k) then
                      .bot s!"varying clause arities in '{fnName}'; routed to slow slice"
                    if hasInterleavedImplicitBeforeK k coreSigTy then
                      .bot s!"interleaved implicit Pi binder in '{fnName}'; routed to slow slice"
                    let armLines ← unpacked.mapM fun (aliasLets, vp, body) => do
                      let used := collectVarsExpr body
                      let pStrs ← vp.mapM (fun a => emitPat ctx (wildcardUnusedPat used a.thing))
                      let bStr ← emitExpr ctx lvlVars body
                      let rhsFull := String.intercalate "; " (aliasLets ++ [bStr])
                      .translated ("  | " ++ String.intercalate ", " pStrs ++ " => " ++ rhsFull)
                    let termLine := match recInfo with
                      | .nonRecursive => ""
                      | .structuralArg idx =>
                          let vars := (List.range k).map (fun i => s!"_s{i}")
                          "\ntermination_by structural " ++ String.intercalate " " vars ++ s!" => _s{idx}"
                    let code :=
                      s!"{fullHeader}\n" ++
                      String.intercalate "\n" armLines ++ termLine
                    .translated (leanFn, code)

    emitWithWhere (ctx : EmitCtx) (leanFn fullHeader : String) (impSlots lvlVars : List String)
        (coreSigTy : Expr) (clauses : List Clause) (recInfo : RecAnalysis) :
        PrismOutcome (String × String) := do
      match clauses, recInfo with
      | [.clause (.head _ ps) (.rhs body) ws], .nonRecursive =>
          let (hidPfx, visRest) := ps.span (fun a => a.hid != Hiding.visible)
          if visRest.any (fun a => a.hid != Hiding.visible) then
            .bot "interleaved implicit pattern with 'where' routed to Agda"
          else if hasInterleavedImplicitBeforeK visRest.length coreSigTy then
            .bot "interleaved implicit Pi binder with 'where' routed to slow slice"
          else
            match resolveImplicitAliasLets impSlots hidPfx with
            | none => .bot "implicit constructor pattern with 'where' routed to Agda"
            | some aliasLets => do
                let subPrefix := ctx.modPrefix ++ ["_"]
                let rec buildWhereLets (rem : List Decl) (curCtx : EmitCtx) (lets : List String) :
                    PrismOutcome (List String × EmitCtx) :=
                  match rem with
                  | [] => .translated (lets.reverse, curCtx)
                  | .import_ _ _ _ _ :: rest | .open_ _ _ :: rest | .fixity _ _ _ :: rest =>
                      buildWhereLets rest curCtx lets
                  | .sig _ hNm hTy :: .fun_ _ hNm2 [.clause (.head _ hPs) (.rhs hBody) []] :: rest =>
                      if hNm != hNm2 || hPs.any (fun a => a.hid != .visible) then
                        .bot "complex 'where' helper routed to Agda"
                      else do
                        let hCanon := subPrefix ++ [hNm]
                        let isSelfRec := mentionsQName hCanon hBody
                        if isSelfRec then
                          .bot "recursive 'where' helper routed to Agda"
                        else if !hPs.all (fun a => match a.thing with | .varP _ => true | _ => false) then
                          .bot "pattern-matching 'where' helper routed to Agda"
                        else do
                          let hLean := leanMangleIdent ("where_" ++ hNm)
                          let hInfo : SymInfo :=
                            { localName := hNm, canonPath := hCanon, kind := .defSym, leanName := hLean }
                          let nextCtx := { curCtx with symByCanon := (hCanon, hInfo) :: curCtx.symByCanon }
                          let hBodyStr ← emitExpr curCtx lvlVars hBody
                          let lamArgs := hPs.map fun a =>
                            match a.thing with | .varP v => leanMangleIdent v | _ => "_"
                          let rhsVal :=
                            if lamArgs.isEmpty then hBodyStr
                            else s!"(fun {String.intercalate " " lamArgs} => {hBodyStr})"
                          let letLine ←
                            if isMetaExpr hTy then
                              .translated s!"let {hLean} := {rhsVal}"
                            else do
                              let hTyStr ← emitExpr curCtx lvlVars hTy
                              .translated s!"let {hLean} : {hTyStr} := {rhsVal}"
                          buildWhereLets rest nextCtx (letLine :: lets)
                  | _ => .bot "complex 'where' block routed to Agda"
                let (letLines, bodyCtx) ← buildWhereLets ws ctx []
                let used := ws.flatMap collectVarsDecl ++ collectVarsExpr body
                let pStrs ← visRest.mapM (fun a => emitPat ctx (wildcardUnusedPat used a.thing))
                let bStr ← emitExpr bodyCtx lvlVars body
                let fullRhs := String.intercalate "; " (aliasLets ++ letLines ++ [bStr])
                if pStrs.isEmpty then
                  .translated (leanFn, s!"{fullHeader} :=\n  {fullRhs}")
                else
                  .translated (leanFn, s!"{fullHeader}\n  | {String.intercalate ", " pStrs} => {fullRhs}")
      | _, _ => .bot s!"multi-clause or recursive function '{fnName}' with 'where' block routed to Agda"

private partial def mentionsDepSigmaWithTarget (targets : List (List String)) : Expr → Bool
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

private partial def isTriviallyInhabitedTy : Expr → Bool
  | .def_ q =>
      q.full == ["Agda", "Builtin", "String", "String"] ||
      q.full == ["Code", "Name"] ||
      q.full == ["Code", "QName"] ||
      q.full == ["Agda", "Builtin", "Nat", "Nat"] ||
      q.full == ["Agda", "Builtin", "Bool", "Bool"] ||
      q.full == ["Agda", "Builtin", "Char", "Char"] ||
      q.full == ["Agda", "Builtin", "Unit", "⊤"] ||
      q.full == ["Data", "Unit", "Polymorphic", "Base", "⊤"]
  | .app (.def_ q) _ =>
      q.full == ["Agda", "Builtin", "List", "List"] ||
      q.full == ["Agda", "Builtin", "Maybe", "Maybe"]
  | .app (.app (.def_ q) a1) a2 =>
      q.full == ["Data", "Product", "_×_"] &&
      isTriviallyInhabitedTy a1.thing && isTriviallyInhabitedTy a2.thing
  | _ => false

private partial def isInhabitedConTy (targetCanon : List String) : Expr → Bool
  | .def_ q => q.full == targetCanon
  | .fun_ a rest => a.hid == .visible && isTriviallyInhabitedTy a.thing && isInhabitedConTy targetCanon rest
  | _ => false

private def emitDataBlock (ctx : EmitCtx) (mutualCanons : List (List String))
    (dNm : String) (params : List Bind) (sortE : Expr) (cons : List (String × Expr)) :
    PrismOutcome String := do
  if ctx.usesDepSigma && cons.any (fun (_, cTy) => mentionsDepSigmaWithTarget mutualCanons cTy) then
    .bot s!"inductive '{dNm}' nests mutual/self type inside dependent AgdaSigma; routed to Agda"
  let pStr ← emitTeleBinders ctx [] params
  let sStr ← emitExpr ctx [] sortE
  let leanD := leanMangleIdent dNm
  let pPart := if pStr.isEmpty then "" else " " ++ pStr
  let conLines ← cons.mapM fun (cNm, cTy) => do
    let cTyStr ← emitExpr ctx [] cTy
    .translated s!"  | {leanMangleIdent cNm} : {cTyStr}"
  let deriveSuffix :=
    if ctx.mode == .erasedExec && mutualCanons.length == 1 && params.isEmpty &&
       cons.any (fun (_, cTy) => isInhabitedConTy (ctx.modPrefix ++ [dNm]) cTy) then
      "\n  deriving Inhabited"
    else ""
  .translated (s!"inductive {leanD}{pPart} : {sStr} where\n" ++ String.intercalate "\n" conLines ++ deriveSuffix)

private def emitMutualDataSCC (ctx : EmitCtx) (ns : String) (sccUnits : List ModUnit) :
    PrismOutcome (String × List String) := do
  let mutCanons := sccUnits.filterMap fun u =>
    match u.kind with
    | .dataUnit dNm _ _ _ _ => some (ctx.modPrefix ++ [dNm])
    | _ => none
  let mut indBlocks : List String := []
  let mut gNames : List String := []
  for u in sccUnits do
    match u.kind with
    | .dataUnit dNm params sortE _ cons => do
        let blk ← emitDataBlock ctx mutCanons dNm params sortE cons
        let indented := "  " ++ String.intercalate "\n  " (blk.splitOn "\n")
        indBlocks := indBlocks ++ [indented]
        gNames := gNames ++ [s!"{ns}.{leanMangleIdent dNm}"]
    | _ => PrismOutcome.bot "non-data unit in mutual data SCC"
  .translated ("mutual\n" ++ String.intercalate "\n\n" indBlocks ++ "\nend", gNames)

private def emitFastUnit (ctx : EmitCtx) (ns : String) (u : ModUnit) :
    PrismOutcome (String × Option String) := do
  match u.kind with
  | .dataUnit dNm params sortE _ cons => do
      let block ← emitDataBlock ctx [ctx.modPrefix ++ [dNm]] dNm params sortE cons
      let leanD := leanMangleIdent dNm
      .translated (block, some s!"{ns}.{leanD}")
  | .recUnit rNm params sortE _ rd flds => do
      if rd.coind then .bot s!"coinductive record '{rNm}'"
      let pStr ← emitTeleBinders ctx [] params
      let sStr ← emitExpr ctx [] sortE
      let leanR := leanMangleIdent rNm
      let pPart := if pStr.isEmpty then "" else " " ++ pStr
      let cLine := match rd.constr with
        | some cn => s!"  {leanMangleIdent cn} ::\n"
        | none    => "  mk ::\n"
      let fLines ← flds.mapM fun (fNm, fTy) => do
        let fTyStr ← emitExpr ctx [] fTy
        .translated s!"  {leanMangleIdent fNm} : {fTyStr}"
      let deriveSuffix :=
        if ctx.mode == .erasedExec && params.isEmpty && !flds.isEmpty &&
           flds.all (fun (_, fTy) => isTriviallyInhabitedTy fTy) then
          "\n  deriving Inhabited"
        else ""
      let block :=
        s!"structure {leanR}{pPart} : {sStr} where\n" ++ cLine ++
        String.intercalate "\n" fLines ++ deriveSuffix
      .translated (block, some s!"{ns}.{leanR}")
  | .patSynUnit synNm args _ rExpr => do
      let code ← emitPatSynAbbrev ctx synNm args rExpr
      .translated (code, none)
  | .postulateUnit _ fNm sigTy => do
      if ctx.mode == .erasedExec then
        .bot s!"cannot compile executable from postulated symbol '{fNm}'"
      let leanFn := leanMangleIdent fNm
      let lvlVars := collectLevelVarsInType sigTy
      let uDecl :=
        if lvlVars.isEmpty then ""
        else "." ++ "{" ++ String.intercalate " " (lvlVars.map (s!"u_{·}")) ++ "}"
      let (_, impBindStrs, coreSigTy) ← splitLeadingHiddenBinds ctx lvlVars sigTy
      let impParamHeader := if impBindStrs.isEmpty then "" else " " ++ String.intercalate " " impBindStrs
      let tyStr ← emitExpr ctx lvlVars coreSigTy
      .translated (s!"axiom {leanFn}{uDecl}{impParamHeader} : {tyStr}", none)
  | .funUnit m fNm sigTy cs => do
      if m.termCheck != .check then
        .bot s!"pragma {repr m.termCheck} on '{fNm}' routed to slow slice"
      let (leanFn, code) ← emitFunctionDef ctx fNm sigTy cs none
      .translated (code, some s!"{ns}.{leanFn}")
  | .anonUnit idx ty cs => do
      let (leanFn, code) ← emitFunctionDef ctx "_" ty cs (some idx)
      .translated (code, some s!"{ns}.{leanFn}")

-- §3 Boundary Stub Emitter (`∂_S` in `EmitMode.hybridCheck`) & Erased Native Lowerer (`EmitMode.erasedExec`)

private def hasDependentRecordFields (flds : List (String × Expr)) : Bool :=
  let rec check (seen : List String) : List (String × Expr) → Bool
    | [] => false
    | (fn, fTy) :: rest =>
        let rec mentionsLocalVar : Expr → Bool
          | .var x       => seen.contains x
          | .app f a     => mentionsLocalVar f || mentionsLocalVar a.thing
          | .lam a e     => (a.thing != "" && seen.contains a.thing && false) || mentionsLocalVar e
          | .lamT (.bind _ xs t) e => mentionsLocalVar t || (!xs.any (seen.contains ·) && mentionsLocalVar e)
          | .pi (.bind _ xs t) e   => mentionsLocalVar t || (!xs.any (seen.contains ·) && mentionsLocalVar e)
          | .fun_ a e    => mentionsLocalVar a.thing || mentionsLocalVar e
          | _            => false
        mentionsLocalVar fTy || check (fn :: seen) rest
  check [] flds

private def emitSlowBoundaryStub (ctx : EmitCtx) (u : ModUnit) : PrismOutcome String := do
  match u.kind with
  | .anonUnit _ _ _ =>
      -- Anonymous proof `_ : T` exports nothing to `F₂`; checked in `SlowSlice.agda`!
      .translated ""
  | .dataUnit dNm _ _ _ _ =>
      .bot s!"inductive-recursive data '{dNm}' cannot be abstracted as opaque"
  | .recUnit rNm params sortE _ rd flds => do
      if hasDependentRecordFields flds then
        .bot s!"dependent coinductive record '{rNm}' fields cannot be flattened to simple projections"
      let pVisStr ← emitTeleBinders ctx [] params
      let pImpStr ← emitImplicitTeleBinders ctx [] params
      let sStr ← emitExpr ctx [] sortE
      let leanR := leanMangleIdent rNm
      let pVisPart := if pVisStr.isEmpty then "" else " " ++ pVisStr
      let pImpPart := if pImpStr.isEmpty then "" else " " ++ pImpStr
      let paramNames := params.flatMap fun (.bind _ xs _) => xs.map leanMangleIdent
      let appliedR :=
        if paramNames.isEmpty then leanR
        else "(" ++ String.intercalate " " (leanR :: paramNames) ++ ")"
      let typeStub := s!"axiom {leanR}{pVisPart} : {sStr}"
      let projStubs ← flds.mapM fun (fNm, fTy) => do
        let fTyStr ← emitExpr ctx [] fTy
        .translated s!"axiom {leanR}.{leanMangleIdent fNm}{pImpPart} : {appliedR} → {fTyStr}"
      let conStub ← match rd.constr with
        | none => .translated []
        | some cNm => do
            let fTyStrs ← flds.mapM (fun (_, fTy) => emitExpr ctx [] fTy)
            let fullConTy := fTyStrs.foldr (fun d acc => s!"({d} → {acc})") appliedR
            .translated [s!"axiom {leanR}.{leanMangleIdent cNm}{pImpPart} : {fullConTy}"]
      .translated (String.intercalate "\n" (typeStub :: (conStub ++ projStubs)))
  | .funUnit _ fNm sigTy _ => do
      let leanFn := leanMangleIdent fNm
      let lvlVars := collectLevelVarsInType sigTy
      let uDecl :=
        if lvlVars.isEmpty then ""
        else "." ++ "{" ++ String.intercalate " " (lvlVars.map (s!"u_{·}")) ++ "}"
      let (_, impBindStrs, coreSigTy) ← splitLeadingHiddenBinds ctx lvlVars sigTy
      let impParamHeader := if impBindStrs.isEmpty then "" else " " ++ String.intercalate " " impBindStrs
      if isMetaExpr coreSigTy then
        .bot s!"unannotated slow function '{fNm}' cannot be emitted as opaque axiom stub"
      else do
        let tyStr ← emitExpr ctx lvlVars coreSigTy
        .translated s!"axiom {leanFn}{uDecl}{impParamHeader} : {tyStr}"
  | .patSynUnit synNm args _ rExpr =>
      emitPatSynAbbrev ctx synNm args rExpr
  | .postulateUnit _ fNm sigTy => do
      let leanFn := leanMangleIdent fNm
      let lvlVars := collectLevelVarsInType sigTy
      let uDecl :=
        if lvlVars.isEmpty then ""
        else "." ++ "{" ++ String.intercalate " " (lvlVars.map (s!"u_{·}")) ++ "}"
      let (_, impBindStrs, coreSigTy) ← splitLeadingHiddenBinds ctx lvlVars sigTy
      let impParamHeader := if impBindStrs.isEmpty then "" else " " ++ String.intercalate " " impBindStrs
      let tyStr ← emitExpr ctx lvlVars coreSigTy
      .translated s!"axiom {leanFn}{uDecl}{impParamHeader} : {tyStr}"

private def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

private partial def collectClauseLevelVars : Clause → List String
  | .clause _ r ws =>
      let fromR := match r with
        | .withRHS _ scs => scs.flatMap collectClauseLevelVars
        | _ => []
      let fromW := ws.flatMap fun
        | .sig _ _ ty => collectLevelVarsInType ty
        | .fun_ _ _ cs => cs.flatMap collectClauseLevelVars
        | _ => []
      fromR ++ fromW

private partial def lhsHeadCanon : LHS → Option (List String)
  | .head q _     => some q.full
  | .proj _ l _   => lhsHeadCanon l
  | .with_ l _ _  => lhsHeadCanon l

private partial def lhsBaseVisPats : LHS → Option (List (Arg Pat))
  | .head _ ps => some (ps.filter (fun a => a.hid == .visible))
  | .with_ inner _ _ => lhsBaseVisPats inner
  | _ => none

-- Lower verified `Slow` units (including nested `where` blocks, mutual `let rec`,
-- multi-stage `with`, and `rewrite`) to native Lean 4!
mutual
  private partial def emitWhereDeclsErased (ctx : EmitCtx) (lvlVars : List String)
      (ind : Nat) (ws : List Decl) : PrismOutcome (List String × EmitCtx) := do
    if ws.isEmpty then
      .translated ([], ctx)
    else
      let subPfx := ctx.modPrefix ++ ["_"]
      let (_, wUnits) ← extractModUnits { modName := mkQ subPfx, params := [], decls := ws }
      if wUnits.isEmpty then
        .translated ([], ctx)
      else
        let wSCCs := computeUnitSCCs wUnits
        -- Pre-register all `where` helper symbols & implicit parameter names in `wCtx`
        let mut wCtx := ctx
        for wu in wUnits do
          match wu.kind with
          | .funUnit _ hNm hTy hCs =>
              let realCanon :=
                match hCs.head? >>= (fun (.clause l _ _) => lhsHeadCanon l) with
                | some c => c
                | none   => subPfx ++ [hNm]
              let depthTag := toString realCanon.length
              let hLean := leanMangleIdent s!"wh{depthTag}_{hNm}"
              let hInfo : SymInfo :=
                { localName := hNm, canonPath := realCanon, kind := .defSym, leanName := hLean }
              let hImps := extractLeadingImplicits hTy
              wCtx :=
                { wCtx with
                  symByCanon   := (realCanon, hInfo) :: wCtx.symByCanon
                  sigImplicits := (realCanon, hImps) :: wCtx.sigImplicits }
          | _ => PrismOutcome.bot "local data/record inside 'where' block routed to MAlonzo"

        let mut stmtBlocks : List String := []
        for scc in wSCCs do
          let sccUnits := scc.filterMap (fun uid => wUnits.find? (·.uid == uid))
          let liveUnits := sccUnits.filter fun u => match u.kind with | .anonUnit _ _ _ => false | _ => true
          if !liveUnits.isEmpty then
            let plainLetOpt : Option (PrismOutcome String) :=
              match liveUnits with
              | [u] =>
                  match u.kind with
                  | .funUnit _ hNm hTy [.clause (.head headQ []) (.rhs hBody) []] =>
                      let realCanon := headQ.full
                      if mentionsQName realCanon hBody || !(collectLevelVarsInType hTy).isEmpty then
                        none
                      else
                        some do
                          let (_, impBindStrs, coreHTy) ← splitLeadingHiddenBinds wCtx lvlVars hTy
                          if !impBindStrs.isEmpty then
                            PrismOutcome.bot "unreachable"
                          else do
                            let depthTag := toString realCanon.length
                            let hLean := leanMangleIdent s!"wh{depthTag}_{hNm}"
                            let tyAnnot ←
                              if isMetaExpr coreHTy then .translated ""
                              else do
                                let tStr ← emitExpr wCtx lvlVars coreHTy
                                .translated s!" : {tStr}"
                            let bStr ← emitExpr wCtx lvlVars hBody
                            .translated s!"{spaces ind}let {hLean}{tyAnnot} :=\n{spaces (ind + 2)}{bStr}"
                  | _ => none
              | _ => none
            let block ←
              match plainLetOpt with
              | some res => res
              | none => do
                  let items ← liveUnits.mapM fun u =>
                    match u.kind with
                    | .funUnit _ hNm hTy hCs => do
                        let realCanon :=
                          match hCs.head? >>= (fun (.clause l _ _) => lhsHeadCanon l) with
                          | some c => c
                          | none   => subPfx ++ [hNm]
                        let depthTag := toString realCanon.length
                        let hLean := leanMangleIdent s!"wh{depthTag}_{hNm}"
                        emitErasedFunCore wCtx lvlVars (ind + 2) "" hLean hNm hTy hCs false
                    | _ => .bot "unsupported unit in 'where' SCC"
                  .translated (s!"{spaces ind}let rec\n" ++ String.intercalate ",\n" items)
            stmtBlocks := stmtBlocks ++ [block]
        .translated (stmtBlocks, wCtx)

  private partial def emitErasedClauseRhs (ctx : EmitCtx) (lvlVars : List String)
      (ind : Nat) (fNm : String) (baseVisPats : List (Arg Pat))
      (aliasLets : List String) (ws : List Decl) (r : RHS) : PrismOutcome String := do
    let (whereBlocks, rhsCtx) ← emitWhereDeclsErased ctx lvlVars ind ws
    let aLines := aliasLets.map (fun s => spaces ind ++ s)
    let coreExpr ←
      match r with
      | .rhs body => do
          let bStr ← emitExpr rhsCtx lvlVars body
          .translated (spaces ind ++ bStr)
      | .rewriteRHS _ innerR =>
          -- In `EmitMode.erasedExec` (after Agda `SlowSlice` verified the rewrite equation!),
          -- runtime value computation evaluates `innerR` directly.
          emitErasedClauseRhs rhsCtx lvlVars ind fNm baseVisPats [] [] innerR
      | .withRHS withExprs subClauses => do
          let weStrs ← withExprs.mapM (emitExpr rhsCtx lvlVars)
          let liveSubs := subClauses.filter fun
            | .clause _ .absurdRHS _ => false
            | _ => true
          if liveSubs.isEmpty then
            match weStrs, subClauses with
            | [we0], [.clause (.with_ _ [wArg] []) .absurdRHS []] =>
                if match wArg.thing with | .absurdP => true | _ => false then
                  return s!"{spaces ind}(nomatch {we0})"
                else
                  PrismOutcome.bot s!"absurd-only 'with' block in '{fNm}' routed to MAlonzo"
            | _, _ => PrismOutcome.bot s!"absurd-only 'with' block in '{fNm}' routed to MAlonzo"
          let subArms ← liveSubs.mapM fun sc =>
            match sc with
            | .clause (.with_ innerLhs wArgs extraPs) subRhs subWs => do
                match lhsBaseVisPats innerLhs with
                | none => PrismOutcome.bot s!"copattern inside 'with' in '{fNm}' routed to MAlonzo"
                | some subVis => do
                    if subVis.map encArgPat != baseVisPats.map encArgPat then
                      PrismOutcome.bot s!"dependent pattern-refining 'with' in '{fNm}' routed to MAlonzo"
                    let subUsed := subWs.flatMap collectVarsDecl ++ collectVarsRhs subRhs
                    let wStrs ← wArgs.mapM (fun a => emitPat rhsCtx (wildcardUnusedPat subUsed a.thing))
                    let visExtra := extraPs.filter (fun a => a.hid == .visible)
                    if visExtra.isEmpty then do
                      let sbStr ← emitErasedClauseRhs rhsCtx lvlVars (ind + 2) fNm baseVisPats [] subWs subRhs
                      .translated (s!"{spaces ind}| " ++ String.intercalate ", " wStrs ++ " =>\n" ++ sbStr)
                    else do
                      let epStrs ← visExtra.mapM (fun a => emitPat rhsCtx (wildcardUnusedPat subUsed a.thing))
                      let sbStr ← emitErasedClauseRhs rhsCtx lvlVars (ind + 4) fNm baseVisPats [] subWs subRhs
                      let lamLine := s!"{spaces (ind + 2)}(fun | " ++ String.intercalate ", " epStrs ++ " =>\n" ++ sbStr ++ ")"
                      .translated (s!"{spaces ind}| " ++ String.intercalate ", " wStrs ++ " =>\n" ++ lamLine)
            | _ => .bot s!"malformed 'with' sub-clause in '{fNm}' routed to MAlonzo"
          .translated (s!"{spaces ind}(match " ++ String.intercalate ", " weStrs ++ " with\n" ++
                       String.intercalate "\n" subArms ++ ")")
      | .absurdRHS => .bot s!"unexpected absurdRHS in '{fNm}'"
    .translated (String.intercalate "\n" (aLines ++ whereBlocks ++ [coreExpr]))

  private partial def emitErasedFunCore (ctx : EmitCtx) (outerLvls : List String)
      (ind : Nat) (kwPrefix leanFn fNm : String) (sigTy : Expr)
      (clauses : List Clause) (allowUnivDecl : Bool) : PrismOutcome String := do
    let ownLvls :=
      (collectLevelVarsInType sigTy ++ clauses.flatMap collectClauseLevelVars).eraseDups
    let lvlVars := (outerLvls ++ ownLvls).eraseDups
    let uDecl :=
      if !allowUnivDecl || lvlVars.isEmpty then ""
      else "." ++ "{" ++ String.intercalate " " (lvlVars.map (s!"u_{·}")) ++ "}"
    let (impPairs, impBindStrs, coreSigTy) ← splitLeadingHiddenBinds ctx lvlVars sigTy
    let impParamHeader := if impBindStrs.isEmpty then "" else " " ++ String.intercalate " " impBindStrs
    let tyAnnot ←
      if isMetaExpr coreSigTy then .translated ""
      else do
        let tyStr ← emitExpr ctx lvlVars coreSigTy
        .translated s!" : {tyStr}"
    let pfx := if kwPrefix.isEmpty then "" else kwPrefix ++ " "
    let fullHeader := s!"{spaces ind}{pfx}{leanFn}{uDecl}{impParamHeader}{tyAnnot}"
    let impSlots := impPairs.map Prod.fst

    -- Case A: Copattern definition (`hd (from n) = ...`, `from n .hd = ...`)
    let isCopat := clauses.any fun
      | .clause (.proj _ _ _) _ _ => true
      | _ => false

    if isCopat then
      if clauses.any (fun (.clause _ _ ws) => !ws.isEmpty) then
        .bot s!"copattern function '{fNm}' with 'where' block routed to MAlonzo"
      else
        match resultHeadCanon coreSigTy >>= (fun rc => ctx.recMeta.find? (fun m => m.recCanon == rc)) with
        | none => .bot s!"copattern function '{fNm}' target record metadata not found"
        | some rm => do
            let unpackProj (c : Clause) : Option (List String × List String × List (Arg Pat) × Expr) :=
              match c with
              | .clause (.proj projQ (.head _ ps) []) (.rhs body) [] =>
                  let (hidPfx, visRest) := ps.span (fun a => a.hid != Hiding.visible)
                  if visRest.any (fun a => a.hid != Hiding.visible) then none
                  else
                    match resolveImplicitAliasLets impSlots hidPfx with
                    | some aliasLets => some (projQ.full, aliasLets, visRest, body)
                    | none           => none
              | _ => none
            match clauses.mapM unpackProj with
            | none => .bot s!"nested or trailing-argument copattern in '{fNm}' routed to MAlonzo"
            | some unpacked => do
                match unpacked with
                | [] => .bot "empty copattern clause list"
                | (_, _, firstVis, _) :: _ => do
                    let k := firstVis.length
                    if unpacked.any (fun (_, _, vp, _) => vp.length != k) then
                      .bot s!"varying arity in copattern '{fNm}'"
                    let outerVars := (List.range k).map (fun i => s!"_cp{i}")
                    let fldAssigns ← rm.fields.mapM fun (fldNm, _) => do
                      let targetProjCanon := rm.recCanon ++ [fldNm]
                      let fldClauses := unpacked.filter (fun (pc, _, _, _) => pc == targetProjCanon)
                      if fldClauses.isEmpty then
                        PrismOutcome.bot s!"missing copattern projection '{fldNm}' in '{fNm}'"
                      let fldValStr ←
                        if k == 0 then
                          match fldClauses with
                          | [(_, aliasLets, [], body)] => do
                              let bStr ← emitExpr ctx lvlVars body
                              .translated (String.intercalate "; " (aliasLets ++ [bStr]))
                          | _ => .bot s!"ambiguous 0-arg copattern field '{fldNm}' in '{fNm}'"
                        else do
                          let arms ← fldClauses.mapM fun (_, aliasLets, vp, body) => do
                            let used := collectVarsExpr body
                            let pStrs ← vp.mapM (fun a => emitPat ctx (wildcardUnusedPat used a.thing))
                            let bStr ← emitExpr ctx lvlVars body
                            let rhsFull := String.intercalate "; " (aliasLets ++ [bStr])
                            .translated ("| " ++ String.intercalate ", " pStrs ++ " => " ++ rhsFull)
                          let scrut := String.intercalate ", " outerVars
                          .translated ("(match " ++ scrut ++ " with " ++ String.intercalate " " arms ++ ")")
                      if rm.isCoind then
                        .translated s!"_thunk_{leanMangleIdent fldNm} := Thunk.mk (fun _ => {fldValStr})"
                      else
                        .translated s!"{leanMangleIdent fldNm} := {fldValStr}"
                    let recBody := "{ " ++ String.intercalate ", " fldAssigns ++ " }"
                    if k == 0 then
                      .translated s!"{fullHeader} :=\n{spaces (ind + 2)}{recBody}"
                    else
                      .translated s!"{fullHeader} :=\n{spaces (ind + 2)}fun {String.intercalate " " outerVars} =>\n{spaces (ind + 4)}{recBody}"
    else
      -- Case B: Multi-arg Foetus / Mutual / `with`-abstraction / `where` function!
      let liveClauses := clauses.filter fun
        | .clause _ .absurdRHS _ => false
        | _ => true
      if liveClauses.isEmpty then
        .bot s!"absurd-only slow function '{fNm}' routed to MAlonzo"
      else
        let unpackHead (c : Clause) : Option (List String × List (Arg Pat) × RHS × List Decl) :=
          match c with
          | .clause (.head _ ps) rhs ws =>
              let (hidPfx, visRest) := ps.span (fun a => a.hid != Hiding.visible)
              if visRest.any (fun a => a.hid != Hiding.visible) then none
              else
                let aliasOpt :=
                  match resolveImplicitAliasLets impSlots hidPfx with
                  | some a => some a
                  | none   => some []   -- erased implicit constructor patterns in `erasedExec`
                aliasOpt.map (fun aliasLets => (aliasLets, visRest, rhs, ws))
          | _ => none

        match liveClauses.mapM unpackHead with
        | none => .bot s!"interleaved implicit pattern in slow function '{fNm}' routed to MAlonzo"
        | some unpacked =>
            match unpacked with
            | [] => .bot "empty clause list"
            | [(aliasLets, [], rhs, ws)] => do
                let rStr ← emitErasedClauseRhs ctx lvlVars (ind + 2) fNm [] aliasLets ws rhs
                .translated s!"{fullHeader} :=\n{rStr}"
            | (_, firstVis, _, _) :: _ => do
                let k := firstVis.length
                if k == 0 || unpacked.any (fun (_, vp, _, _) => vp.length != k) then
                  .bot s!"varying clause arities in '{fNm}'"
                if hasInterleavedImplicitBeforeK k coreSigTy then
                  .bot s!"interleaved implicit Pi binder in '{fNm}' routed to MAlonzo"
                let armLines ← unpacked.mapM fun (aliasLets, vp, rhs, ws) => do
                  let used := ws.flatMap collectVarsDecl ++ collectVarsRhs rhs
                  let pStrs ← vp.mapM (fun a => emitPat ctx (wildcardUnusedPat used a.thing))
                  let rStr ← emitErasedClauseRhs ctx lvlVars (ind + 4) fNm vp aliasLets ws rhs
                  .translated (s!"{spaces (ind + 2)}| " ++ String.intercalate ", " pStrs ++ " =>\n" ++ rStr)
                .translated (s!"{fullHeader}\n" ++ String.intercalate "\n" armLines)
end

private def emitSlowErasedFun (ctx : EmitCtx) (fNm : String) (sigTy : Expr)
    (clauses : List Clause) (forcePartial : Bool := false) : PrismOutcome String :=
  let isTrulyNonRec :=
    !forcePartial &&
    clauses.all (fun (.clause _ _ ws) => ws.isEmpty) &&
    match analyzeFunctionRecursion ctx.modPrefix fNm clauses with
    | .translated .nonRecursive => true
    | _ => false
  let kw := if isTrulyNonRec then "def" else "partial def"
  emitErasedFunCore ctx [] 0 kw (leanMangleIdent fNm) fNm sigTy clauses true

private def emitSlowSCCErased (ctx : EmitCtx) (sccUnits : List ModUnit) :
    PrismOutcome (List String) := do
  match sccUnits with
  | [u] =>
    match u.kind with
    | .anonUnit _ _ _ => .translated []
    | .postulateUnit _ fNm _ => .bot s!"cannot compile executable from postulated symbol '{fNm}'"
    | .recUnit rNm params sortE _ rd flds => do
        if !rd.coind then
          -- Inductive record that landed in Slow -> emit regular structure
          let pStr ← emitTeleBinders ctx [] params
          let sStr ← emitExpr ctx [] sortE
          let leanR := leanMangleIdent rNm
          let pPart := if pStr.isEmpty then "" else " " ++ pStr
          let cLine := match rd.constr with
            | some cn => s!"  {leanMangleIdent cn} ::\n"
            | none    => "  mk ::\n"
          let fLines ← flds.mapM fun (fNm, fTy) => do
            let fTyStr ← emitExpr ctx [] fTy
            .translated s!"  {leanMangleIdent fNm} : {fTyStr}"
          let deriveSuffix :=
            if params.isEmpty && !flds.isEmpty &&
               flds.all (fun (_, fTy) => isTriviallyInhabitedTy fTy) then
              "\n  deriving Inhabited"
            else ""
          .translated [s!"structure {leanR}{pPart} : {sStr} where\n" ++ cLine ++ String.intercalate "\n" fLines ++ deriveSuffix]
        else do
          if hasDependentRecordFields flds then
            PrismOutcome.bot s!"dependent coinductive record '{rNm}' routed to MAlonzo"
          let pVisStr ← emitTeleBinders ctx [] params
          let pImpStr ← emitImplicitTeleBinders ctx [] params
          let sStr ← emitExpr ctx [] sortE
          let leanR := leanMangleIdent rNm
          let pVisPart := if pVisStr.isEmpty then "" else " " ++ pVisStr
          let pImpPart := if pImpStr.isEmpty then "" else " " ++ pImpStr
          let paramNames := params.flatMap fun (.bind _ xs _) => xs.map leanMangleIdent
          let appliedR :=
            if paramNames.isEmpty then leanR
            else "(" ++ String.intercalate " " (leanR :: paramNames) ++ ")"
          let fThunkLines ← flds.mapM fun (fNm, fTy) => do
            let fTyStr ← emitExpr ctx [] fTy
            .translated s!"  _thunk_{leanMangleIdent fNm} : Thunk ({fTyStr})"
          let structBlock :=
            s!"structure {leanR}{pVisPart} : {sStr} where\n  mk ::\n" ++
            String.intercalate "\n" fThunkLines
          let projDefs ← flds.mapM fun (fNm, fTy) => do
            let fTyStr ← emitExpr ctx [] fTy
            .translated s!"def {leanR}.{leanMangleIdent fNm}{pImpPart} (_self : {appliedR}) : {fTyStr} := _self._thunk_{leanMangleIdent fNm}.get"
          let conDefs ← match rd.constr with
            | none => .translated []
            | some cNm => do
                let idxFlds := List.zip (List.range flds.length) flds
                let argBinds ← idxFlds.mapM fun (i, (_, fTy)) => do
                  let fTyStr ← emitExpr ctx [] fTy
                  .translated s!"(_cf{i} : {fTyStr})"
                let thunks := idxFlds.map fun (i, (fNm, _)) =>
                  s!"_thunk_{leanMangleIdent fNm} := Thunk.mk (fun _ => _cf{i})"
                let bindPart := if argBinds.isEmpty then "" else " " ++ String.intercalate " " argBinds
                .translated [s!"def {leanR}.{leanMangleIdent cNm}{pImpPart}{bindPart} : {appliedR} := " ++ "{ " ++ String.intercalate ", " thunks ++ " }"]
          .translated ([structBlock] ++ conDefs ++ projDefs)
    | .funUnit _ fNm sigTy cs => do
        let code ← emitSlowErasedFun ctx fNm sigTy cs
        .translated [code]
    | .patSynUnit synNm args _ rExpr => do
        let code ← emitPatSynAbbrev ctx synNm args rExpr
        .translated [code]
    | .dataUnit dNm params sortE _ cons => do
        let blk ← emitDataBlock ctx [ctx.modPrefix ++ [dNm]] dNm params sortE cons
        .translated [blk]
  | _ =>
    -- Multi-unit mutual `SlowSCC`: support mutual `funUnit`s AND mutual `dataUnit`s!
    let liveUnits := sccUnits.filter fun u => match u.kind with | .anonUnit _ _ _ => false | _ => true
    if liveUnits.all (fun u => match u.kind with | .funUnit _ _ _ _ => true | _ => false) then do
      let fnBlocks ← liveUnits.mapM fun u =>
        match u.kind with
        | .funUnit _ fNm sigTy cs => do
            let b ← emitSlowErasedFun ctx fNm sigTy cs true
            .translated ("  " ++ String.intercalate "\n  " (b.splitOn "\n"))
        | _ => .bot "unreachable"
      .translated ["mutual\n" ++ String.intercalate "\n\n" fnBlocks ++ "\nend"]
    else if liveUnits.all (fun u => match u.kind with | .dataUnit _ _ _ _ _ => true | _ => false) then do
      let (blk, _) ← emitMutualDataSCC ctx (leanModNamespace ctx.modPrefix) liveUnits
      .translated [blk]
    else
      .bot "inductive-recursive or mixed-type mutual cycle routed to MAlonzo"

-- §4 Build `EmitCtx` & Compute `SlicePlan` (`Lens.get`)

private def depSigmaTriggerCanons : List (List String) :=
  [ ["Agda", "Builtin", "Sigma", "Σ"]
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
    cm.decls.filterMap fun
      | .sig _ nm ty => some (pfx ++ [nm], extractLeadingImplicits ty)
      | .dataSig _ dNm params _ =>
          let pImps := params.flatMap fun (.bind _ xs _) => xs.map leanMangleIdent
          some (pfx ++ [dNm, "__params"], pImps)
      | .recSig _ rNm params _ =>
          let pImps := params.flatMap fun (.bind _ xs _) => xs.map leanMangleIdent
          some (pfx ++ [rNm, "__params"], pImps)
      | _ => none

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

  { modPrefix    := curMod.modName.full
  , mode         := mode
  , usesDepSigma := usesDepSigma
  , symByCanon   := ownSyms ++ depSyms ++ stdSyms
  , sigImplicits := conImps ++ rawImps ++ stdImplicitNames
  , recMeta      := rMeta }

def computeSlicePlan (depMods : List (CodeMod × ExportedModule))
    (curMod : CodeMod) (curExp : ExportedModule) :
    PrismOutcome (SlicePlan × ExportedModule) := do
  let (headers, units) ← extractModUnits curMod
  let sccs := computeUnitSCCs units
  let probeCtx := buildBaseEmitCtx depMods curMod curExp .pureFast
  let ns := leanModNamespace curMod.modName.full

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
  let mut slowValCanons : List (List String) := (depExps.flatMap (·.slowExports)).eraseDups
  let mut unboundarySlowIds : List Nat := []

  for scc in sccs do
    let sccUnits := scc.filterMap (fun uid => units.find? (·.uid == uid))
    let isMultiDataSCC :=
      !(sccUnits.drop 1).isEmpty &&
      sccUnits.all (fun u => match u.kind with | .dataUnit _ _ _ _ _ => true | _ => false)
    let mut sccSlow : Bool := !(sccUnits.drop 1).isEmpty && !isMultiDataSCC
    if isMultiDataSCC then
      match emitMutualDataSCC probeCtx ns sccUnits with
      | .syntaxErr e  => PrismOutcome.syntaxErr e
      | .bot _        => sccSlow := true
      | .translated _ => pure ()
    for u in sccUnits do
      if !isMultiDataSCC then
        match emitFastUnit probeCtx ns u with
        | .syntaxErr e => PrismOutcome.syntaxErr e
        | .bot _       => sccSlow := true
        | .translated _ => pure ()
      if unitConstructsOrLoopsCoind u then
        sccSlow := true
      -- Boundary taint 1: function/proof signature mentions a slow value/projection (needs unfolding in Agda!).
      -- Pure `dataUnit` declarations only check constructor type well-formedness (`Type`) and strict positivity
      -- without unfolding slow value bodies, so keeping `dataUnit` in `FastFocus` preserves full Lean `inductive`!
      let isPureData := match u.kind with | .dataUnit _ _ _ _ _ => true | _ => false
      if !isPureData && u.sigQNames.any (slowValCanons.contains ·) then
        sccSlow := true
      -- Boundary taint 2: references a slow unit that cannot even be exposed as a Lean `axiom` stub
      let allLocalDeps := unitLocalAllDeps units u
      if allLocalDeps.any (unboundarySlowIds.contains ·) then
        sccSlow := true

    if sccSlow then
      slowIds := slowIds ++ scc
      for u in sccUnits do
        slowValCanons := (slowValCanons ++ u.valueCanons).eraseDups
        match emitSlowBoundaryStub probeCtx u with
        | .translated _ => pure ()
        | _ => unboundarySlowIds := u.uid :: unboundarySlowIds
    else
      fastIds := fastIds ++ scc

  let ownSlowExports :=
    (units.filter (fun u => slowIds.contains u.uid)).flatMap (·.valueCanons) |>.eraseDups
  let updatedExp : ExportedModule :=
    { curExp with slowExports := ownSlowExports }
  let plan : SlicePlan :=
    { headers          := headers
    , units            := units
    , sccs             := sccs
    , slowUnitIds      := slowIds
    , fastUnitIds      := fastIds
    , slowExportCanons := ownSlowExports
    , coindRecCanons   := allCoindRecs }
  .translated (plan, updatedExp)

-- §5 Emit Complete Lean 4 File for a `CodeMod` + `SlicePlan`

def leanModuleFileName (modPath : List String) : String :=
  "PrismGen_" ++ String.intercalate "_" modPath

partial def emitLeanModuleWithPlan (depMods : List (CodeMod × ExportedModule))
    (curMod : CodeMod) (curExp : ExportedModule) (plan : SlicePlan)
    (mode : EmitMode) (emitMainEntry : Bool := false) (withAxiomGuard : Bool := false) :
    PrismOutcome String := do
  let ctx := buildBaseEmitCtx depMods curMod curExp mode
  let ns := leanModNamespace curMod.modName.full
  let depImports := depMods.map (fun (dm, _) => s!"import {leanModuleFileName dm.modName.full}")
  let baseImports :=
    if withAxiomGuard then
      ["import AgdaMirror.Core", "import AgdaMirror.Context", "import AgdaMirror.World", "import AgdaMirror.Protocol", "import AgdaMirror.AxiomGuard"]
    else
      ["import AgdaMirror.Core", "import AgdaMirror.Context", "import AgdaMirror.World", "import AgdaMirror.Protocol"]

  let hasPostulate := plan.units.any fun u =>
    match u.kind with | .postulateUnit _ _ _ => true | _ => false
  let modHasPostulate (ds : List Decl) : Bool :=
    let fnSet := ds.filterMap fun | .fun_ _ fn _ => some fn | _ => none
    ds.any fun
      | .sig _ nm _ => nm != "_" && !fnSet.contains nm
      | _ => false
  let anyPostulateInBundle :=
    hasPostulate || depMods.any (fun (dm, _) => modHasPostulate dm.decls)
  let noncompOpen := if mode == .hybridCheck || (mode == .pureFast && !emitMainEntry && anyPostulateInBundle) then ["noncomputable section"] else []
  let noncompClose := if mode == .hybridCheck || (mode == .pureFast && !emitMainEntry && anyPostulateInBundle) then ["end"] else []
  let erasedWitness :=
    if mode == .erasedExec && plan.hasSlowUnits then
      [ "axiom _erased_nonempty_witness.{u} : ∀ {α : Sort u}, Nonempty α"
      , "attribute [local instance] _erased_nonempty_witness"
      , "" ]
    else []

  let headerLines :=
    baseImports ++
    depImports ++
    [ ""
    , "set_option autoImplicit false"
    , "set_option relaxedAutoImplicit false"
    , "set_option maxRecDepth 100000"
    , "set_option maxHeartbeats 2000000"
    , "" ] ++
    noncompOpen ++
    [ s!"namespace {ns}"
    , "" ] ++
    erasedWitness

  let mut emittedBlocks : List String := []
  let mut guardNames : List String := []
  let mut hasMain : Bool := false

  for u in plan.units do
    if let .funUnit _ "main" _ _ := u.kind then
      hasMain := true

  for scc in plan.sccs do
    let sccUnits := scc.filterMap (fun uid => plan.units.find? (·.uid == uid))
    let isSlowSCC := scc.any (plan.slowUnitIds.contains ·)
    if !isSlowSCC then
      if !(sccUnits.drop 1).isEmpty && sccUnits.all (fun u => match u.kind with | .dataUnit _ _ _ _ _ => true | _ => false) then
        let (code, gs) ← emitMutualDataSCC ctx ns sccUnits
        if !code.isEmpty then
          emittedBlocks := emittedBlocks ++ [code]
        guardNames := guardNames ++ gs
      else
        for u in sccUnits do
          let (code, gOpt) ← emitFastUnit ctx ns u
          if !code.isEmpty then
            emittedBlocks := emittedBlocks ++ [code]
          if let some g := gOpt then
            guardNames := guardNames ++ [g]
    else
      match mode with
      | .pureFast =>
          PrismOutcome.bot "module contains slow residual units in pureFast mode"
      | .hybridCheck =>
          for u in sccUnits do
            let stub ← emitSlowBoundaryStub ctx u
            if !stub.isEmpty then
              emittedBlocks := emittedBlocks ++ [stub]
      | .erasedExec =>
          let blocks ← emitSlowSCCErased ctx sccUnits
          emittedBlocks := emittedBlocks ++ blocks

  let axiomLine :=
    if !withAxiomGuard || guardNames.isEmpty || mode != .pureFast || anyPostulateInBundle then ""
    else "#agda_prism_guard_axioms " ++ String.intercalate " " guardNames ++ "\n"

  let mainFooter :=
    if emitMainEntry && hasMain then
      s!"\ndef main (_args : List String) : IO Unit := do\n  AgdaMirror._agdaArgsRef.set (some _args)\n  let _ ← {ns}.{leanMangleIdent "main"}\n  pure ()\n"
    else ""

  if emitMainEntry && !hasMain then
    .syntaxErr "build-exe: module must export an executable 'main'"
  else
    let closeNs := s!"\n\nend {ns}\n" ++ (if noncompClose.isEmpty then "\n" else "end\n\n")
    let fullText :=
      String.intercalate "\n" headerLines ++
      String.intercalate "\n\n" emittedBlocks ++
      closeNs ++ axiomLine ++ mainFooter
    .translated fullText

end Prism