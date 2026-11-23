import Lean
import LojitaCtx
import Lojita

open Lean Elab Command

/- Iterate by defining module, also visiting private names, generated helpers
    and projections. The import closure is the same one exposed to nodes. -/
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut seen : Nat := 0
  let mut modules : NameSet := {}
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let objectModule := (`LojitaCtx).isPrefixOf mod
    unless objectModule || mod == `Lojita.Ownership.Core do continue
    seen := seen + 1
    modules := modules.insert mod
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError "{mod} declaration {name} depends on {ax}"
    if info.isUnsafe || (mod == `Lojita.Ownership.Core && info.isPartial) ||
        isExtern env name || (Compiler.getImplementedBy? env name).isSome then
      throwError "{mod} contains a native override or unchecked declaration {name}"
    for used in info.getUsedConstantsAsSet do
      if #[`IO, `BaseIO, `EIO, `EST, `EStateM.RealWorld].any (·.isPrefixOf used) then
        throwError "{name} refers to effectful constant {used}"
  for source in ← (System.FilePath.mk "LojitaCtx").readDir do
    if source.path.extension == some "lean" then
      let mod := Name.str `LojitaCtx (source.path.fileStem.getD "")
      unless env.header.moduleNames.contains mod do throwError "missing pure module {mod}"
  unless modules.contains `Lojita.Ownership.Core && modules.contains `LojitaCtx.Countermodel &&
      modules.contains `LojitaCtx.Protocol do throwError "incomplete foundation imports"
  logInfo m!"Audited {seen} constants in {modules.size} foundation modules"


namespace Test.S1Foundation
open Lojita.Ownership

variable {A B Q R I : Type} {n m : String} {Γ Δ : Ctx} {t r : St} {F : I → St}

example (a : A) (k : A → Prog [mkSpec n [] (.ten (.dat A) .end_)] (.dir Γ) t B)
    (ms : Models ((n, .dir []) :: Γ)) :
    evalProg (dataEnv n a) (dataCut a k) ms = evalProg (dataEnv n a) (k a) ms.2 := rfl

example (fresh : member m ((n, .chan (.ten (.res r) .end_)) :: Γ) = false)
    (k : Prog [mkSpec n [] (echoSession r)] (.dir ((m, r) :: Γ)) t B)
    (ms : Models ((m, r) :: (n, .dir []) :: Γ)) :
    evalProg (echoEnv n r) (resCut fresh k) ms = evalProg (echoEnv n r) k (ms.1, ms.2.2) := rfl

example (p : Proc [] Δ (.srvI Q R I F)) (q : Q)
    (k : R → Prog [mkSpec n Δ (.srvI Q R I F)] (.dir ((n, .chan (.srvI Q R I F)) :: Γ)) t B)
    (ms : Models ((n, .dir Δ) :: Γ)) :
    evalProg (machineEnv n p) (callCut q k) ms =
      let (a, next) := Running.call (evalProc Env.nil p ms.1) q
      evalProg (machineEnv n p) (k a) (next, ms.2) := rfl

example (p : Proc [] Δ (.srvI Q R I F))
    (k : (i : I) → Prog [mkSpec n Δ (.srvI Q R I F)] (.dir ((n, F i) :: Γ)) t B)
    (ms : Models ((n, .dir Δ) :: Γ)) :
    evalProg (machineEnv n p) (stopCut k) ms =
      let v := Running.stop (evalProc Env.nil p ms.1)
      evalProg (machineEnv n p) (k v.1) (v.2, ms.2) := rfl

private def localWork : Prog [] (.dir []) (.dir []) Nat :=
  (create "count" 17).bind fun _ =>
    (inside "count" (p := read)).bind fun v =>
      (unlink "count").bind fun _ => .done v

example (v : Model (.file String)) : evalProg Env.nil
    (withEphemeral (Γ := [("keep", .file String)]) "tmp" localWork) (v, ⟨()⟩) = ((v, ⟨()⟩), 17) := rfl

private abbrev frameCtx : Ctx := [("keep", .file String), ("work", .dir [])]
private def framed := inside (Γ := frameCtx) "work" localWork

example (v : Model (.file String)) : evalProg Env.nil framed (v, ⟨()⟩, ⟨()⟩) = ((v, ⟨()⟩, ⟨()⟩), 17) := rfl

private abbrev homeFiles : Ctx := [("token", .file Nat), ("label", .file String)]
private abbrev side (n : String) : Ctx := [(n, .dir homeFiles)]
private abbrev delayed := mkSpec "delayed" homeFiles (.ten (.dat Nat) (.ten (.res (.dir homeFiles)) .end_))

private def branch (n : String) : Prog [delayed] (.dir (side n)) (.dir (side n)) Nat :=
  .exec (.here rfl) (.here rfl) () rfl <|
  .step (.recvD (.here rfl) rfl) fun answer =>
  .step (.recover (.here rfl) rfl) fun _ => .done answer

private def sides : SplitCtx (side "east" ++ side "west") (side "west") (side "east") :=
  .right _ (by decide) (.left _ rfl .nil)

private def bothSides := Prog.par sides (by decide) (branch "west") (branch "east")
  (fun a b => .done (a, b))

private def sideEnv : Env [delayed] := Env.cons (spec := delayed) (fun _ ms =>
  (ms.1, (⟨ms.1.down + 1⟩, ms.2), ⟨()⟩)) Env.nil

example (a b : Nat) (x y : String) :
    evalProg sideEnv bothSides ((⟨a⟩, ⟨x⟩, ⟨()⟩), (⟨b⟩, ⟨y⟩, ⟨()⟩), ⟨()⟩) =
      (((⟨b + 1⟩, ⟨y⟩, ⟨()⟩), (⟨a + 1⟩, ⟨x⟩, ⟨()⟩), ⟨()⟩), (b, a)) := rfl

example (env : Env [delayed]) (ms : Models (side "east" ++ side "west")) :
    evalProg env bothSides ms = evalProg env
      (.par sides.swap (by decide) (branch "east") (branch "west") fun b a =>
        .step (.reorder (Reorder.swapAppend (side "west") (side "east"))) fun _ => .done (a, b)) ms :=
  evalProg_par_swap env sides (by decide) (by decide) (branch "west") (branch "east") _ ms

private abbrev jobHome (_ : Nat) := St.dir homeFiles
private abbrev Job := Session.workerI Nat Nat jobHome
private abbrev slots := workCtx Nat Nat jobHome

private def countingJob (readyAt : Nat) : Proc [] homeFiles Job :=
  .worker (G := fun _ : Nat => homeFiles)
    (fun j => .tell (if j + 1 == readyAt then some (j + 1) else none) (.giveExDir (j + 1) rfl))
    (fun j => .giveExDir j rfl) 0

private def awaitOne : Prog [] (.dir (slots ["w"])) (.dir (side "w")) (Option Nat × Nat) :=
  .awaitI (.here rfl) rfl fun opt i => .done (opt, i)

private def abortOne : Prog [] (.dir (slots ["w"])) (.dir (side "w")) Nat :=
  .abortI (.here rfl) rfl fun i => .done i

example (ms : Models homeFiles) :
    evalProg Env.nil awaitOne (evalProc Env.nil (countingJob 2) ms, ⟨()⟩) =
      ((ms, ⟨()⟩), none, 1) := rfl
example (ms : Models homeFiles) :
    evalProg Env.nil abortOne (evalProc Env.nil (countingJob 2) ms, ⟨()⟩) = ((ms, ⟨()⟩), 0) := rfl

private def phaseHome : Bool → St
  | false => .dir []
  | true => .file Nat

private def phaseCtx : Bool → Ctx
  | false => []
  | true => [("answer", .file Nat)]

private def indexedJob : Proc [] [] (.workerI Unit Bool phaseHome) :=
  .worker (G := phaseCtx)
    (fun
      | false => .run (create "answer" 41) fun _ => .tell (some ()) (.giveExDir true rfl)
      | true => .tell (some ()) (.giveExDir true rfl))
    (fun
      | false => .giveExDir false rfl
      | true => .giveExAt true (.here rfl) rfl .end_) false

example :
    let w := evalProc Env.nil indexedJob ⟨()⟩
    (w.abort, w.stepOne.1, w.stepOne.2.abort) = (⟨false, ⟨()⟩⟩, some (), ⟨true, ⟨41⟩⟩) := rfl

private inductive Selection (names : List String) where
  | pending
  | ready (n : String) (p : Position id n names) (result index : Nat)

private def selectedDir {names : List String} : Selection names → St
  | .pending => .dir (slots names)
  | .ready _ p _ i => .dir (setAt (workPos Nat Nat jobHome p) (jobHome i))

private def selectJob (names : List String) (hne : names ≠ [] := by decide) :
    Proc [] (slots names) (Halt (Selection names) selectedDir) :=
  .awaitAnyP names hne
    (fun n p r i => .giveExDir (.ready n p r i) rfl)
    (.giveExDir .pending rfl)

-- The middle occurrence wins. Even a pending sibling probed before it keeps its original state.
example (a b c : Models homeFiles) :
    let later := evalProc Env.nil (countingJob 2) a
    let ready := evalProc Env.nil (countingJob 1)
    (evalProc Env.nil (selectJob ["same", "same", "last"]) (later, ready b, ready c, ⟨()⟩)).1 =
      ⟨.ready "same" (.there (.here rfl)) 1 1, (later, b, ready c, ⟨()⟩)⟩ := rfl

example (a b c : Models homeFiles) :
    let w := evalProc Env.nil (countingJob 2)
    (evalProc Env.nil (selectJob ["a", "b", "c"]) (w a, w b, w c, ⟨()⟩)).1 =
      ⟨.pending, ((w a).stepOne.2, (w b).stepOne.2, (w c).stepOne.2, ⟨()⟩)⟩ := rfl

private def nestedState : Option Nat → Ctx
  | none => slots ["inner"]
  | some _ => side "inner"

private def nestedTurn : (j : Option Nat) → Proc [] (nestedState j) (WorkerTurn Nat (Option Nat) nestedState)
  | none => .awaitAnyP ["inner"] (by decide)
      (fun _ p r i => by
        cases p with
        | here => exact .tell (some r) (.giveExDir (some i) rfl)
        | there q => exact nomatch q)
      (.tell none (.giveExDir none rfl))
  | some i => .tell (some i) (.giveExDir (some i) rfl)

private def recoverJob (n : String) : Proc [] (slots [n]) (Halt Nat jobHome) :=
  .abortP (.here rfl) rfl fun i => .giveExAt i (.here rfl) rfl .end_

private def nestedJob : Proc [] (slots ["inner"]) Job :=
  .worker nestedTurn (fun
    | none => recoverJob "inner"
    | some i => .giveExAt i (.here rfl) rfl .end_) none

-- The inner worker crosses the outer worker's small storage between the two turns.
example (ms : Models homeFiles) :
    let inner := evalProc Env.nil (countingJob 2) ms
    let outer := evalProc Env.nil nestedJob (inner, ⟨()⟩)
    let (first, w₁) := outer.stepOne
    let (second, w₂) := w₁.stepOne
    (first, w₁.abort, second, w₂.abort) = (none, ⟨1, ms⟩, some 2, ⟨2, ms⟩) := rfl

open LojitaCtx LojitaCtx.Terminal LojitaCtx.World LojitaCtx.Protocol

example : Utf8.decode [0xc3, 0xa9] = ['é'] := rfl
example : PosixChannel.evalScanner PosixChannel.oneByteScanner (PosixChannel.openPipe [0, 255]) =
    (.emit (some 0), PosixChannel.openPipe [255]) := rfl
example : (runWorldPure (Cli.readExactBytesW (Δ := [.stdioCap]) .here 2)
    (pipeSimWorld "cand" [] [0, 255, 10] false)).1 = [0, 255] := rfl
example : (runWorldPure (lookupEnvW (Δ := [.envCap]) .here "S1")
    { defaultSimWorld with env := { emptyProcessEnv with envVars := [("S1", "ok")] } }).1 = some "ok" := rfl
example (p : Proto Nat) : dual (.pSend 7 p) = .pRecv 7 (dual p) := rfl
example (bs : Bytes) :
    coupleEndpoints (Payload := fun _ : Unit => Bytes) (Δ := []) (.epSend (t := ()) bs (.epDone ()))
      (.epRecv fun msg => .epDone msg) = .pure ((), bs) := rfl

section
open LojitaCtx.TranscodeCategory

-- Reachability terminates on a cycle. Removing bodies first keeps the
-- private dependency out of a signature-only upstream shell.
private def rows := [decl "x" .sweetBody ["y"] ["extra"], decl "y" .baseType ["x"] [],
  decl "extra" .baseType [] []]

example : ((checkPoint rows).map fun m => dom (projectUpstreamShell m ["x"]).entries) =
    some ["x", "y"] := rfl
example : ((checkPoint rows).map fun m => dom (computeSharedBase m).entries) = some ["extra"] := rfl
example : (checkPoint [decl true .sweetBody [false] []]).isNone = true := rfl

example : (do
    let base ← checkPoint (Sym := String) []
    let left ← checkPoint [decl "x" .sweetBody [] []]
    let right ← checkPoint [decl "x" .exoBody [] []]
    return (← checkedPushoutGlue base left right).val).isNone = true := rfl
example : evalThunkedCost (spineChain 50) = 101 := rfl

end

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def home (n : Nat) (label : String) : ModelsIO homeFiles := (n, label, ())
private def contents (m : ModelsIO homeFiles) : Nat × String := (m.1, m.2.1)

private def testParallel : IO Unit := do
  let env : EnvIO [delayed] := EnvIO.cons (spec := delayed) (fun _ ms => pure do
    IO.sleep 150
    return (ms.1, pure ((Nat.succ ms.1, ms.2), ()))) EnvIO.nil
  let input := (home 11 "east", home 37 "west", ())
  let start ← IO.monoMsNow
  let (owned, a, b) ← evalIO env bothSides input
  let elapsed := (← IO.monoMsNow) - start
  check ((a, b) == (37, 11) && contents owned.1 == (38, "west") &&
    contents owned.2.1 == (12, "east")) "parallel branch answers or rejoined directories"
  check (elapsed < 260) s!"parallel 150 ms branches took {elapsed} ms"
  IO.println s!"Parallel 150 ms branches finished in {elapsed} ms"

  let finished ← IO.mkRef false
  let failing : EnvIO [delayed] := EnvIO.cons (spec := delayed) (fun _ ms => pure do
    if BEq.beq (α := Nat) ms.1 11 then throw (IO.userError "east failed")
    IO.sleep 20
    finished.set true
    return (ms.1, pure (ms, ()))) EnvIO.nil
  let .error (.userError "east failed") ← (evalIO failing bothSides input).toBaseIO
    | throw (IO.userError "lost parallel branch error")
  check (← finished.get) "parallel branch still running after its sibling threw"

-- A native timer service owns its directory until it fires or its cancellation hook wakes it.
private def timedJob (delay : UInt64) (index : Nat) (ms : ModelsIO homeFiles) : IO (OfferIO Job) := do
  let wc ← WorkerCancel.new
  let timer ← Std.Internal.UV.Timer.mk delay false
  let alarm ← timer.next
  wc.onCancel do
    timer.stop
    alarm.resolve ()
  let wait : IO (Option Nat × ((i : Nat) × ModelIO (jobHome i))) := do
    IO.wait alarm.result!
    return (if ← wc.cancelled.get then none else some ms.1, ⟨index, ms⟩)
  return ⟨wc, ← IO.asTask wait .dedicated⟩

private def selectIO (names : List String) (ms : ModelsIO (slots names)) (hne : names ≠ [] := by decide) :
    IO ((s : Selection names) × ModelIO (selectedDir s)) := do
  return (← (← evalProcIO EnvIO.nil (selectJob names hne) ms)).1

private def testWorkerRace : IO Unit := do
  let start ← IO.monoMsNow
  let timer₁ ← timedJob 80 1 (home 11 "slow1")
  let timer₂ ← timedJob 5000 3 (home 33 "slow2")
  let slow₁ ← evalProcIO EnvIO.nil nestedJob (timer₁, ())
  let inner ← evalProcIO EnvIO.nil nestedJob (timer₂, ())
  let slow₂ ← evalProcIO EnvIO.nil nestedJob (inner, ())
  let timerFast ← timedJob 20 2 (home 22 "fast")
  let fast ← evalProcIO EnvIO.nil nestedJob (timerFast, ())

  let ⟨.ready n (.there (.here _)) r i, first⟩ ←
      selectIO ["slow1", "fast", "slow2"] (slow₁, fast, slow₂, ())
    | throw (IO.userError "the middle worker did not win")
  let fastMs := (← IO.monoMsNow) - start
  check (n == "fast" && r == 22 && i == 2 && contents first.2.1 == (22, "fast") && fastMs < 100)
    s!"incorrect fast worker result or latency ({fastMs} ms)"

  let ⟨.ready n (.here _) r i, second⟩ ← selectIO ["slow1", "slow2"] (first.1, first.2.2)
    | throw (IO.userError "slow1 did not survive the first selection")
  let slowMs := (← IO.monoMsNow) - start
  check (n == "slow1" && r == 11 && i == 1 && contents second.1 == (11, "slow1") &&
    !(← timer₁.cancel.cancelled.get) && slowMs < 180) s!"incorrect slow1 result or latency ({slowMs} ms)"

  let stopping ← IO.monoMsNow
  let ⟨i, recovered⟩ := (← (← evalProcIO EnvIO.nil (recoverJob "slow2") second.2)).1
  let abortMs := (← IO.monoMsNow) - stopping
  check (i == 3 && contents recovered == (33, "slow2") && (← inner.cancel.cancelled.get) &&
    (← timer₂.cancel.cancelled.get) && (← IO.hasFinished timer₂.task) && abortMs < 150)
    s!"nested abort did not recover the live directory in time ({abortMs} ms)"
  IO.println s!"Worker completion at {fastMs} and {slowMs} ms, nested abort in {abortMs} ms"

private def waitingBeforeFailure (seen : IO.Ref (Array (OfferIO Job))) : (names : List String) →
    IO (ModelsIO (slots (names ++ ["failed"])))
  | [] => do
    let failed : OfferIO Job := ⟨← WorkerCancel.new, Task.pure (.error (.userError "last slot failed"))⟩
    return (failed, ())
  | n :: ns => do
    let wc ← WorkerCancel.new
    let w : OfferIO Job := ⟨wc, wc.promise.result!.map (fun _ => .ok (none, ⟨0, home 0 n⟩)) (sync := true)⟩
    seen.modify (·.push w)
    return (w, ← waitingBeforeFailure seen ns)

private def testWorkerCleanup : IO Unit := do
  let immediate : Running Unit (Option Nat) Unit := ⟨Unit, (), fun _ _ => (some 7, ()), id⟩
  check (pollN 1000000000000 immediate == some 7) "existing server polling did not return its first answer"
  let w ← evalProcIO EnvIO.nil (countingJob 2048) (home 7 "turns")
  let (owned, opt, i) ← evalIO EnvIO.nil awaitOne (w, ())
  check (opt == some 2048 && i == 2048 && contents owned.1 == (7, "turns")) "autonomous worker turns"
  let w ← timedJob 5000 9 (home 8 "abort")
  let (owned, i) ← evalIO EnvIO.nil abortOne (w, ())
  check (i == 9 && contents owned.1 == (8, "abort") && (← w.cancel.cancelled.get)) "single-slot abort"

  let a ← timedJob 5000 1 (home 1 "a")
  let b ← timedJob 5000 2 (home 2 "b")
  let failed : OfferIO Job := ⟨← WorkerCancel.new, Task.pure (.error (.userError "child failed"))⟩
  let .error (.userError "child failed") ← (selectIO ["a", "failed", "b"] (a, failed, b, ())).toBaseIO
    | throw (IO.userError "lost selected child error")
  check ((← a.cancel.cancelled.get) && (← b.cancel.cancelled.get) &&
    (← IO.hasFinished a.task) && (← IO.hasFinished b.task)) "failed selection left a live sibling"

  let names := (List.range 128).map toString
  let seen ← IO.mkRef #[]
  let wide ← waitingBeforeFailure seen names
  let .error (.userError "last slot failed") ← (selectIO (names ++ ["failed"]) wide (by simp)).toBaseIO
    | throw (IO.userError "missed the last of 129 slots")
  for worker in ← seen.get do
    check ((← worker.cancel.cancelled.get) && (← IO.hasFinished worker.task)) "wide selection leaked a sibling"

  let wc ← WorkerCancel.new
  let hooks ← IO.mkRef #[]
  wc.onCancel do
    hooks.modify (·.push 1)
    throw (IO.userError "hook failed")
  wc.onCancel (hooks.modify (·.push 2))
  let .error (.userError "hook failed") ← wc.trigger.toBaseIO | throw (IO.userError "lost hook error")
  wc.onCancel (hooks.modify (·.push 3))
  wc.trigger
  check ((← hooks.get) == #[1, 2, 3] && (← wc.promise.isResolved)) "cancellation hook delivery"

-- Only the test executable instruments this pure callback. The native
-- implementation observes invocation, including premature calls by the evaluator.
initialize finishCount : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)
private unsafe def countedImpl (n : Nat) : Nat :=
  match unsafeIO (finishCount.modify fun (count, _) => (count + 1, n)) with
  | .ok _ => n
  | .error e => panic! e.toString
@[noinline, implemented_by countedImpl] private def counted (n : Nat) := n

private abbrev Counter := Session.srvI Unit Nat Nat (fun _ => .dir [])
private def counter (start : Nat) : Proc [] [] Counter :=
  .machine (G := fun _ : Nat => [])
    (fun n => .ask fun _ => .tell (n + 1) (.giveExDir (n + 1) rfl))
    (fun n => .giveExDir (counted n) rfl) start

private def callMany (fuel last : Nat) (server : Offer Counter) : Nat × Offer Counter :=
  match fuel with
  | 0 => (last, server)
  | n+1 => let (a, next) := Running.call server (); callMany n a next
termination_by structural fuel

@[noinline] private def forceNat (n : Nat) : IO Nat := pure n

private def stressServer : IO Unit := do
  finishCount.set (0, 0)
  let initial := (← finishCount.get).1
  let (answer, server) := callMany 100000 initial (evalProc Env.nil (counter initial) ⟨()⟩)
  let last ← forceNat answer
  check (last == 100000 && (← finishCount.get).1 == 0) "premature shutdown or incorrect machine turn"
  let finalState ← forceNat (Running.stop server).1
  check (last == finalState && (← finishCount.get).1 == 1) "incorrect final state or shutdown count"

private abbrev innerCtx : Ctx := [("inner", .chan Counter)]

-- Both the inner channel and its changing state cross a machine boundary.
private def nestedCounter : Proc [] innerCtx Counter :=
  .machine (G := fun _ : Unit => innerCtx)
    (fun _ => .ask fun _ => .run (.step (.call (.here rfl) rfl ()) .done) fun n =>
      .tell n (.giveExDir () rfl))
    (fun _ => .stopP (.here rfl) rfl fun i =>
      .run (.step (.rmdir (.here rfl) rfl) .done) fun _ => .giveExDir i rfl) ()

private def checkNested : IO Unit := do
  finishCount.set (0, 0)
  let initial := (← finishCount.get).1 + 5
  let inner := evalProc Env.nil (counter initial) ⟨()⟩
  let enclosing := evalProc Env.nil nestedCounter (inner, ⟨()⟩)
  let (answer, next) := callMany 5 initial enclosing
  let value ← forceNat answer
  check (value == 10 && (← finishCount.get).1 == 0) "nested server lost state or stopped early"
  let stopped ← forceNat (Running.stop next).1
  let (calls, lastStop) ← finishCount.get
  check (stopped == 10 && calls == 1 && lastStop == stopped) s!"nested server stopped at {stopped}, shutdowns {calls}"

private def payloadProgram (bs : Bytes) : WorldProg [.fsCap] Bytes := do
  let .inr () ← writeFileW .here "payload" bs | return []
  let .inr result ← readFileW .here "payload" | return []
  return result

private def stressTraversal (length : Nat) : IO Unit := do
  let start ← IO.monoNanosNow
  let xs := (List.replicate (length / 5) "a🦊").foldl String.append ""
  let bs := bytes xs
  let cs := Utf8.decode bs
  let pending := bs.foldl (fun (p : PendingOutput) b => p.add ⟨[], [b], [], none⟩) {}
  let fromWorld := (runWorldPure (payloadProgram bs) defaultSimWorld).1
  let coupled := coupleEndpoints (Payload := fun _ : Unit => Bytes) (Δ := [])
    (.epSend (t := ()) fromWorld (.epDone ())) (.epRecv fun received => .epDone received)
  let proto := (List.range length).foldl (fun p i => Proto.pSend i p) (.pEnd : Proto Nat)
  let depth := countRecvs (dual proto) 0
  check (bs.length == length && cs.length == length / 5 * 2 && String.ofList cs == xs && Utf8.fromBytes? (Utf8.toBytes xs) == some xs &&
    (runWorldPure coupled defaultSimWorld).1.2 == bs && depth == length && pending.toObs.stdoutOut == bs)
    "UTF-8, terminal output, World or Protocol traversal"
  let ns := (← IO.monoNanosNow) - start
  check (ns < 1000000000) s!"{length} byte traversal took {ns} ns"
  IO.println s!"{length} bytes, including UTF-8 decode, World and Protocol: {ns / 1000000} ms"
where
  countRecvs : Proto Nat → Nat → Nat
    | .pRecv _ rest, n => countRecvs rest (n + 1)
    | _, n => n
  termination_by structural p _ => p

private def fsRoundtrip : WorldProg [.fsCap] (Bool × Bytes × Bool) := do
  let .inr () ← mkdirW .here "dir" 493 | return (false, [], false)
  let .inr () ← writeFileW .here "dir/file" [0, 255, 65] | return (false, [], false)
  let .inr .regularNode ← statW .here "dir/file" | return (false, [], false)
  let .inr bs ← readFileW .here "dir/file" | return (false, [], false)
  let .inr () ← unlinkW .here "dir/file" | return (false, bs, false)
  let .inl .fsNotFound ← readFileW .here "dir/file" | return (true, bs, false)
  return (true, bs, true)

private def clockCheck : WorldProg [.clockCap] Bool := do
  let start ← nowMonoW .here
  sleepW .here 2
  let finish ← nowMonoW .here
  return finish ≥ start + 1

private def reactive : ReactiveApp [.clockCap] Nat :=
  ⟨.pure 5, fun _ n => if n == 5 then .pure (.inl 6) else .pure (.inr (n + 11))⟩

private def testWorld : IO Unit := do
  let simulated := (runWorldPure fsRoundtrip defaultSimWorld).1
  check (simulated == (true, [0, 255, 65], true) && (← Lojita.WorldRunner.runWorldIO fsRoundtrip) == simulated)
    "pure and native filesystem results differ"
  check ((runWorldPure clockCheck defaultSimWorld).1 && (← Lojita.WorldRunner.runWorldIO clockCheck))
    "clock failed to advance"
  let env := lookupEnvW (Δ := [.envCap]) .here "LOJITA_S1_ENV"
  let w := { defaultSimWorld with env := { emptyProcessEnv with envVars := [("LOJITA_S1_ENV", "session-one")] } }
  check ((← Lojita.WorldRunner.runWorldIO env) == (runWorldPure env w).1) "environment lookup differs"
  let channels : WorldProg CliCaps (Bool × Bool × Bool × Bool) := do
    return (← isTTYStdinW stdioInCli, ← isTTYStdoutW stdioInCli,
      ← hasTTYW ttyInCli, ← writeTTYW ttyInCli [])
  let (inTTY, outTTY, attached, wrote) ← Lojita.WorldRunner.runWorldIO channels
  check (inTTY == (← (← IO.getStdin).isTty) && outTTY == (← (← IO.getStdout).isTty) &&
    (!wrote || attached)) "standard descriptor and controlling terminal observations differ"
  let tick : Event [.clockCap] := ⟨.here, .evTickMs 0⟩
  let (.inr result, _) := runReactivePure reactive [tick, tick] w | throw (IO.userError "reactive app did not exit")
  check (result == 17 && (← Lojita.WorldRunner.runReactiveIO reactive).toNat == result) "reactive results differ"
  check ((← Lojita.WorldRunner.runCliIO (Δ := []) (.pure 263)) == 7) "CLI exit status"

open Lojita.Ownership.Tools

private def termCfg : TermConfig :=
  ⟨.localSandbox, .pipeStdioWithTTY, "/bin/cat", ["input"], [], 24, 80, ["input"]⟩
private def fsCfg : FsSandbox.FsConfig := ⟨.localSandbox, [], ["output"], []⟩
private abbrev registry := [Term.ptySpec, Fs.fsSpec]
private abbrev dirs : Ctx :=
  [("terminal", .dir (filesCtx String termCfg.files)), ("disk", .dir (filesCtx Bytes fsCfg.ownedFiles))]

private def relayProgram : Prog registry (.dir dirs) (.dir dirs) (Bytes × Bool) :=
  .exec (.here rfl) (.here rfl) termCfg rfl <|
  .exec (.there (.here rfl)) (.there (.here rfl)) fsCfg rfl <|
  .step (.call (.here rfl) rfl TermStep.drainRaw) fun t =>
  .step (.call (.there (.here rfl)) rfl (FsSandbox.FsStep.writeFileStep "output" t.stdoutOut)) fun _ =>
  .step (.call (.there (.here rfl)) rfl FsSandbox.FsStep.snapshotStep) fun obs =>
  .step (.stop (.here rfl) rfl) fun _ =>
  .step (.stop (.there (.here rfl)) rfl) fun _ =>
  .done (t.stdoutOut, obs.entries.any fun e => e.entryPath == "output" && e.entryBytes == t.stdoutOut)

private def testRelays (bin scratch : System.FilePath) : IO Unit := do
  let env : EnvIO registry := EnvIO.cons (Term.ptyTool (bin / "term-relay") scratch)
    (EnvIO.cons (Fs.fsTool (bin / "fs-relay") scratch) EnvIO.nil)
  let input := "relay π\n"
  let (owned, out, snapshot) ← evalIO env relayProgram ((input, ()), ([], ()), ())
  check (out == bytes input && snapshot && BEq.beq (α := String) owned.1.1 input && BEq.beq (α := Bytes) owned.2.1.1 out)
    "terminal to filesystem ownership transfer or recovery"
  let restricted : FsSandbox.FsConfig := ⟨.localSandbox, [], ["locked/file"],
    [.fixDir "locked" 0, .fixDir "closed" 0]⟩
  let disk ← Fs.fsTool (bin / "fs-relay") scratch restricted (bytes "owned", ())
  check (BEq.beq (α := Bytes) (← disk.stopIO).2.1 (bytes "owned")) "restricted directory recovery"
  let gitCfg : GitSandbox.GitConfig := ⟨.localSandbox, "main", "Session One", "s1@local", 1, [], ["tracked"]⟩
  let g ← Git.gitTool (bin / "git-relay") scratch gitCfg (bytes "git", ())
  discard <| g.callIO .gitStageAll
  let commit ← g.callIO (.gitCommit "first" 0)
  let info ← g.callIO .gitStatus
  check (commit.commitHash.length == 40 && (info.summary.map (·.commitCount)) == some 1) "Git commit and summary"
  check (BEq.beq (α := Bytes) (← g.stopIO).2.1 (bytes "git")) "Git owned file"
  let netCfg : NetSandbox.NetConfig := ⟨.localSandbox, .tcpStubMode [⟨bytes "ping", bytes "pong"⟩], [], []⟩
  let n ← Net.netTool (bin / "net-relay") scratch netCfg ()
  let response ← n.callIO (.tcpProbe (bytes "ping") 1000)
  check (!response.timedOut && response.wireReply == bytes "pong" && response.capturedReqs == [bytes "ping"])
    "loopback TCP relay"
  discard n.stopIO
  let canvas ← Web.webTool (bin / "web-relay") scratch ⟨.localSandbox, 2, 3, ["out.ppm"]⟩ ([], ())
  let .frame _ _ ← canvas.callIO (.flush "") | throw (IO.userError "canvas frame")
  check ((← canvas.callIO (.pixel 1 1)) == .pixelObs false 0 0 0) "empty canvas pixel"
  let .frame 1 _ ← canvas.callIO (.flush "FILL 9 8 7 0 0 2 3") | throw (IO.userError "painted frame")
  check ((← canvas.callIO (.pixel 1 1)) == .pixelObs true 9 8 7) "painted canvas pixel"
  discard <| canvas.callIO (.exportPPM "out.ppm")
  check ((bytes "P6").isPrefixOf (← canvas.stopIO).2.1) "canvas export"

def run : IO Unit := do
  testParallel
  testWorkerRace
  testWorkerCleanup
  stressServer
  checkNested
  IO.println "100000 machine calls, one explicit shutdown"
  stressTraversal 50000
  let some root ← IO.getEnv "LOJITA_S1_SCRATCH" | throw (IO.userError "missing test scratch directory")
  let some bin ← IO.getEnv "LOJITA_S1_RELAYS" | throw (IO.userError "missing relay directory")
  let cwd ← IO.Process.getCurrentDir
  IO.Process.setCurrentDir root
  try
    testWorld
    testRelays bin (System.FilePath.mk root / "sessions")
  finally IO.Process.setCurrentDir cwd
  IO.println "WorldRunner and five static C relays passed"

end Test.S1Foundation

def main : IO Unit := Test.S1Foundation.run
