import Lojita.Harness.PlanPreview

namespace Lojita.Harness
open Lojita.Ownership Lojita.Kernel Lojita.Transport

abbrev ChildS := Session.workerI Verdict HomeShape HomeSt
abbrev AgentS := Session.arr (.dat NodeTask) ChildS
abbrev ActiveSlots := List String
abbrev Work (active : ActiveSlots) : Ctx := workCtx Verdict HomeShape HomeSt active
private abbrev Homes := Std.HashMap String Frozen

/-- Kernel evidence for one birth. The parent reads it only after reclaiming the
    channel. In particular, abortP returns a directory without its worker verdict. -/
inductive ChildCheck where
  | sealed
  | refuted (units : List QName)
  deriving Nonempty

structure ChildWork where
  task : NodeTask
  home : Frozen
  checked : IO.Promise ChildCheck
  cancel : IO.Promise WorkerCancel

structure InFlightInfo where
  spec : LeanMod
  deps : List LeanMod
  allowedAncestors : Option (List QName)
  lifts : Array (LeanMod × LiftSpec)
  checked : IO.Promise ChildCheck
  cancel : IO.Promise WorkerCancel

structure NodeState where
  task : NodeTask
  original : Frozen
  current : Frozen
  candidate : Option Candidate := none
  verified : Homes := {}
  inFlight : Std.HashMap String InFlightInfo := {}
  salvaged : Homes := {}
  obstructing : Option Verdict := none
  diagnostic : Option NarrowingCertificate := none
  verdict : Option Verdict := none
  sealedHome : Option Frozen := none

private def orderedHomes (specs : List LeanMod) (homes : Homes) :=
  specs.filterMap fun spec =>
    let n := toString spec.modName
    (n, ·) <$> homes[n]?

def freezeVerifiedKids (s : NodeState) : Frozen :=
  let combined := s.salvaged.fold (fun m n h => if m.contains n then m else m.insert n h) s.verified
  let first := orderedHomes (s.candidate.map (·.specs) |>.getD []) combined
  let named := Std.HashSet.ofList (first.map Prod.fst)
  let rest := combined.toList.filter fun (n, _) => !named.contains n
  .frozen s.original.code s.original.memory s.original.spec (first ++ rest.mergeSort (fun a b => a.1 ≤ b.1))

private def harvest (s : NodeState) (h : Frozen) : NodeState :=
  {s with salvaged := h.children.foldl (fun m (n, kid) => m.insert n kid) s.salvaged}

private def normalizeChildSpec (s : NodeState) (n : String) (h : Frozen) : Frozen :=
  match s.candidate.bind (fun c => c.specs.find? (fun spec => toString spec.modName == n)) with
  | some spec => .frozen h.code h.memory spec h.children
  | none => h

private def survivingSlots (s : NodeState) (c : Candidate) : IO (Std.HashSet String) := do
  let permissions := childPermissions s.task
  let mut keep := {}
  for spec in c.specs do
    let q := spec.modName
    let n := toString q
    let some info := s.inFlight[n]? | continue
    unless permissions q == info.allowedAncestors && c.childLifts[q]?.getD #[] == info.lifts do continue
    let same ← if spec == info.spec && c.deps == info.deps then pure true
      else pure (← (eqIface info.spec spec c.deps).toBaseIO).isOk
    if same then keep := keep.insert n
  return keep

private def reusableHome (t : NodeTask) (deps : List LeanMod) (spec : LeanMod) (h : Frozen)
    (lifts : Array (LeanMod × LiftSpec)) : IO Bool := do
  unless (← (checkSaved deps spec h).toBaseIO).isOk do return false
  if lifts.isEmpty then return true
  let owner := t.delta.child
  let q := spec.modName
  let one := Frozen.frozen t.delta.newIface [] t.delta.newIface [(toString q, h)]
  let identity := TransportSpec.transportSpecTree owner owner [.keepChild q q] []
  t.lifts.allM fun (_, ls) => do
    return (← (checkKeptLifts deps [(one, identity)] ls).toBaseIO).toOption.any List.isEmpty

structure PlanResult where
  current : Frozen
  verified : Homes
  toSpawn : List ChildWork

/-- Reconcile after invalidated channels have returned their homes. The planning snapshot
    carries every accepted child interface, including the imports and opens needed by old stubs. -/
def reconcileChildren (s : NodeState) (c : Candidate) : IO PlanResult := do
  let saved := Std.HashMap.ofList s.original.children
  let kept := Std.HashMap.ofList c.kept
  let horizontal := nestedBindings s.task.transports
  let permissions := childPermissions s.task
  let sources := s.current.code.imports.filterMap (fun i => do
    let n := toString i.imod
    return (n, ← s.verified[n]? <|> s.salvaged[n]?)) ++ s.original.children ++ s.task.transports.flatMap (·.1.children)
  let mut origins := s.current.memory.toArray
  let mut seen : Std.HashSet String := {}
  for (n, h) in sources do
    if seen.contains n then continue
    seen := seen.insert n
    for (o, notes) in h.memory do
      if let .unit q := o then origins := origins.push (.ext (renameQ h.code.modName (qualified n) q), notes)
  let routed := routeChildren c.plan origins.toList (c.specs.map (·.modName))
  let mut verified : Homes := {}
  let mut births := #[]
  let mut interfaces := #[]
  for spec in c.specs do
    let q := spec.modName
    let n := toString q
    let blank := Frozen.frozen ⟨q, [], [], []⟩ [] spec []
    interfaces := interfaces.push (n, blank)
    if s.inFlight.contains n then continue
    if let some h := kept[q]? then
      verified := verified.insert n h
      continue
    let sub := horizontal[q]?.getD []
    let lifts := c.childLifts[q]?.getD #[]
    let recent := [s.verified[n]?, s.salvaged[n]?].reduceOption
    let existing := recent ++ saved[n]?.toList
    if sub.isEmpty then
      if let some h ← existing.findM? (fun h => reusableHome s.task c.deps spec h lifts) then
        verified := verified.insert n h
        continue
    let seed := existing.headD blank
    let pinned := if recent.isEmpty && saved.contains n then
      (s.task.otherChildHistory.bind (fun (slots,ms) => if slots.contains n then some ms else none)) <|>
        s.task.oldBaseModules
      else none
    let child := {s.task with
      delta := ⟨q, seed.spec.units, spec⟩, baseModules := c.deps, transports := sub,
      oldBaseModules := pinned, otherChildHistory := none, currentOnLiveBases := false,
      allowedAncestors := permissions q, maybeLift := lifts[0]?, otherLifts := lifts.toList.drop 1}
    let home := Frozen.frozen seed.code (seed.memory ++ routed[q]?.getD []) seed.spec seed.children
    births := births.push ⟨child, home, ← IO.Promise.new, ← IO.Promise.new⟩
  let code := withChildIfaces (apply c.plan s.current.code) c.specs
  let current := Frozen.frozen code (inherit c.plan s.current.memory) s.current.spec interfaces.toList
  return ⟨current, verified, births.toList⟩

private def absorbDeadMemory (s : NodeState) (c : Candidate) : Memory := Id.run do
  let slots := Std.HashSet.ofList (c.specs.map (·.modName))
  let kept := Std.HashSet.ofList (s.task.transports.flatMap fun (_,ts) => (directKeeps ts).map Prod.fst)
  let moved := Std.HashSet.ofList (s.task.transports.flatMap fun (_,ts) => ts.childMoves.flatMap fun
    | .moveChildren os ns _ => os.filter (fun o => ns != [o])
    | _ => [])
  let mapped := Std.HashSet.ofList (c.plan.moves.map (·.src))
  let mut seen : Std.HashSet String := {}
  let mut dead := #[]
  for (n,h) in s.original.children ++ s.task.transports.flatMap (·.1.children) do
    let slot := qualified n
    if seen.contains n || kept.contains slot || (slots.contains slot && !moved.contains slot) then continue
    seen := seen.insert n
    for (o, notes) in h.memory do
      let .unit q := o | continue
      unless mapped.contains (.ext (renameQ h.code.modName slot q)) do dead := dead ++ notes.toArray
  if dead.isEmpty then return s.current.memory
  let (buried, rest) := s.current.memory.partition (·.1 == .bot)
  return rest ++ [(.bot, buried.flatMap Prod.snd ++ dead.toList)]

/-- Only a closed link of all implementations in the accepted import order can return success. -/
def finish (s : NodeState) (c : Candidate) : IO Frozen := do
  let kids := orderedHomes c.specs s.verified
  unless kids.length == c.specs.length do throw (IO.userError "MISSING_VERIFIED_CHILD")
  let home := Frozen.frozen c.code (absorbDeadMemory s c) s.task.delta.newIface kids
  verifyClosure c.deps home
  return home

private def evidence (t : NodeTask) (sub : Submission) : IO (Verdict × List QName) := do
  let spec := t.delta.newIface
  let bases ← IO.ofExcept (mergeModules (t.baseModules ++ t.lifts.map Prod.fst))
  match sub with
  | .plan .. => throw (IO.userError "EXPECTED_WITNESS")
  | .contradiction r =>
    witnessBoundary bases spec r
    let snap ← checkRefutation bases (stubOf spec) r
    return (.contradiction r, extractCulpritAssumptions spec snap)
  | .refuteLift why r =>
    if bases.isEmpty then throw (IO.userError "NO_LIFT: no closed base modules")
    let units ← checkLiftRefutation bases spec r
    return (.liftObstruction why units r, units)
  | .countermodel why m r =>
    let snap ← checkCountermodel bases spec m r
    return (.countermodel why m r, extractCulpritAssumptions spec snap [`CountermodelCheck.VerifiedClaim])

private def childRefutation (used : List QName) (n why : String) (model : Option LeanMod) (proof : LeanMod) :
    NarrowingCertificate × Memory :=
  let culprits := if used.isEmpty then [qualified n] else used
  let kind := if model.isSome then "child_countermodel" else "child_contradiction"
  let witness := s!"{n} ({String.intercalate ", " (culprits.map toString)})"
  let cause := String.intercalate "\n" ([why] ++ model.toList.map renderLeanMod ++ [renderLeanMod proof])
  let conclusion := model.elim "implies False" (fun m => s!"admits countermodel {m.modName}")
  let note := s!"{kind}: {n} {conclusion} (proof {proof.modName})."
  let detour := "Your subspec for this child is unimplementable as proven above. Submit an incremental Plan from CURRENT CODE revising this child's subspec and any affected parent glue; unaffected siblings will be reused or continue running uninterrupted."
  (⟨kind, witness, cause, detour⟩, culprits.map fun q => (.ext q, [note]))

private inductive Action where
  | propose (req : AIRequest)
  | gates (s : NodeState) (p : Plan) (subs : List LeanMod)
  | reconcile (s : NodeState) (c : Candidate)
  | seal (s : NodeState) (c : Candidate)
  | witness (t : NodeTask) (sub : Submission)
  | childCheck (info : InFlightInfo)
  | triggerCancel (targets : List (IO.Promise WorkerCancel))

private def Action.Result : Action → Type
  | .propose _ => Option String
  | .gates .. => GateReport × Option (Candidate × Std.HashSet String)
  | .reconcile .. => PlanResult
  | .seal .. => Except String Frozen
  | .witness .. => Except String Verdict
  | .childCheck .. => Option ChildCheck
  | .triggerCancel _ => Unit

private inductive Job where
  | run (act : Action)
  | attempt (act : Action)
  | raise (err : IO.Error)

private def Job.Result : Job → Type
  | .run a => a.Result
  | .attempt a => Except IO.Error a.Result
  | .raise _ => Empty

private structure ChildStart where
  shape : HomeShape
  salvaged : Homes
  checked : IO.Promise ChildCheck
  cancel : IO.Promise WorkerCancel

private def service : Spec := ⟨"node-service", Job, fun _ => [], fun j => .ten (.dat j.Result) .end_⟩
private def supply : Spec := ⟨"home", HomeValue, fun _ => [], fun v => .ten (.res (HomeSt v.1)) .end_⟩
private def childSpec : Spec := ⟨"child", ChildStart, fun i => Home (HomeCtx i.shape), fun _ => AgentS⟩
abbrev NodeΨ := [service, supply, childSpec]

private abbrev serviceDir := "__node_service__"

private structure Frame where
  active : ActiveSlots
  fresh : serviceDir ∉ active

private theorem freshWork {n : String} {ns : ActiveSlots} (h : n ∉ ns) : member n (Work ns) = false := by
  induction ns with
  | nil => rfl
  | cons x xs ih =>
    have ne : x ≠ n := fun e => h (e ▸ List.mem_cons_self)
    have tail := ih (fun hm => h (List.mem_cons_of_mem x hm))
    change ((if e : x = n then some (.here e) else (Position.find Prod.fst n (Work xs)).map .there) :
      Option (MemCtx n ((x, .chan ChildS) :: Work xs))).isSome = false
    simpa [ne, member] using tail

private def Frame.remove (f : Frame) {n} (p : Position id n f.active) : Frame :=
  ⟨p.remove, fun h => f.fresh (subset p h)⟩
where
  subset {ns : ActiveSlots} (p : Position id n ns) : p.remove ⊆ ns := by
    induction p with
    | here => exact fun _ hm => List.mem_cons_of_mem _ hm
    | there _ ih => exact List.cons_subset_cons _ ih

private def perform (f : Frame) (j : Job) : Prog NodeΨ (.dir (Work f.active)) (.dir (Work f.active)) j.Result :=
  .step (.mkdir serviceDir (freshWork f.fresh)) fun _ =>
  .exec (.here rfl) (.here rfl) j rfl <|
  .step (.recvD (.here rfl) rfl) fun a => .step (.close (.here rfl) rfl) fun _ => .done a

private def receiveHome {Γ : Ctx} (n : String) (fresh : member n Γ = false) (v : HomeValue) :
    Prog NodeΨ (.dir Γ) (.dir ((n, HomeSt v.1) :: Γ)) Unit :=
  .step (.mkdir n fresh) fun _ =>
  .exec (.here rfl) (.there (.here rfl)) v rfl (.step (.recover (.here rfl) rfl) .done)

private abbrev J := Frame × NodeState
private abbrev Reply := WorkerTurn Verdict J (fun j => Work j.1.active)

private def respond (f : Frame) (s : NodeState) : Proc NodeΨ (Work f.active) Reply :=
  .tell s.verdict (.giveExDir (f, s) rfl)

private def retry (f : Frame) (s : NodeState) (cert : NarrowingCertificate) : Proc NodeΨ (Work f.active) Reply :=
  let cur := s.current
  let kids := cur.children.map fun (n, stub) =>
    let home := s.verified[n]?.map fun h => Frozen.frozen h.code h.memory stub.spec h.children
    (n, home.getD stub)
  respond f {s with current := .frozen cur.code cur.memory cur.spec kids, diagnostic := some cert, candidate := none}

private def failed (f : Frame) (s : NodeState) (msg : String) :=
  retry f s (problem ((msg.splitOn ":").headD "node_error") s.task.delta.child msg "Revise the submission and retry.")

private def sealNode (f : Frame) (s : NodeState) (c : Candidate) : Proc NodeΨ (Work f.active) Reply :=
  .run (perform f (.run (.seal s c))) fun
    | .error e => failed f s e
    | .ok h => respond f {s with sealedHome := some h, verdict := some .ok}

private def afterChildren (f : Frame) (s : NodeState) : Proc NodeΨ (Work f.active) Reply :=
  if !f.active.isEmpty then respond f s else
  if let some obs := s.obstructing then respond f {s with verdict := some obs, sealedHome := some (freezeVerifiedKids s)} else
  if let some c := s.candidate then sealNode f s c else failed f s "MISSING_CANDIDATE"

private def birthChildren (f : Frame) (s : NodeState) : List ChildWork → Proc NodeΨ (Work f.active) Reply
  | [] => afterChildren f s
  | kid :: rest =>
    let n := toString kid.task.delta.child
    if hres : serviceDir = n then
      failed f s s!"RESERVED_CHILD_SLOT: {n}"
    else if hdup : n ∈ f.active then
      failed f s s!"DUPLICATE_CHILD_SLOT: {n}"
    else
      let next := Frame.mk (n :: f.active) (by simp [hres, f.fresh])
      let v := thawHome kid.home
      let info := InFlightInfo.mk kid.task.delta.newIface kid.task.baseModules kid.task.allowedAncestors
        kid.task.lifts.toArray kid.checked kid.cancel
      let kidSalvaged := s.salvaged.filter fun k _ => k != n && under kid.task.delta.child (qualified k)
      .run (receiveHome n (freshWork hdup) v) fun _ =>
      .run (.exec (.here rfl) (.there (.there (.here rfl))) ⟨v.1, kidSalvaged, kid.checked, kid.cancel⟩ rfl
        (.step (.sendD (.here rfl) rfl kid.task) .done)) fun _ =>
      birthChildren next {s with inFlight := s.inFlight.insert n info} rest

private def drainSlot {ns : ActiveSlots} {n : String} (p : Position id n ns) (sh : HomeShape) :
    Prog NodeΨ (.dir (setAt (workPos Verdict HomeShape HomeSt p) (HomeSt sh))) (.dir (Work p.remove)) Frozen := by
  let x := workPos Verdict HomeShape HomeSt p
  let dir := x.afterSet (HomeSt sh)
  have eq := stateOf_afterSet x (HomeSt sh)
  apply Prog.focus dir (eq.symm ▸ drainHome sh)
  intro home
  exact .step (.rmdir (dir.afterSet (.dir [])) (stateOf_afterSet ..)) fun _ => by
    simpa only [dir, x, removeAt_afterSet, removeAt_workPos] using (Prog.done (Ψ := NodeΨ) (s := .dir (Work p.remove)) home)

private def abortSlot {S : Session} (f : Frame) {n : String} (p : Position id n f.active) (s : NodeState)
    (k : Option Frozen → NodeState → Proc NodeΨ (Work p.remove) S) : Proc NodeΨ (Work f.active) S :=
  .abortP (workPos Verdict HomeShape HomeSt p) (stateOf_workPos ..) fun sh =>
  .run (drainSlot p sh) fun h =>
    let next := harvest {s with inFlight := s.inFlight.erase n} h
    if let some i := s.inFlight[n]? then
      .run (perform (f.remove p) (.run (.childCheck i))) fun
        | some .sealed => k (some h) {next with salvaged := next.salvaged.insert n h}
        | _ => k none next
    else k none next

private def cancelTargets (s : NodeState) (names : List String) : List (IO.Promise WorkerCancel) :=
  names.filterMap fun n => (s.inFlight[n]?).map (·.cancel)

private def abortInvalidatedLoop {S : Session} (f : Frame) (s : NodeState) (invalid : List String)
    (k : (next : Frame) → NodeState → Proc NodeΨ (Work next.active) S) : Proc NodeΨ (Work f.active) S :=
  match invalid with
  | [] => k f s
  | n :: rest => match Position.find id n f.active with
    | none => abortInvalidatedLoop f s rest k
    | some p => abortSlot f p s fun _ next => abortInvalidatedLoop (f.remove p) next rest k

private def abortInvalidated {S : Session} (f : Frame) (s : NodeState) (invalid : List String)
    (k : (next : Frame) → NodeState → Proc NodeΨ (Work next.active) S) : Proc NodeΨ (Work f.active) S :=
  let targets := cancelTargets s (invalid.filter (f.active.contains ·))
  if targets.isEmpty then abortInvalidatedLoop f s invalid k
  else .run (perform f (.run (.triggerCancel targets))) fun _ => abortInvalidatedLoop f s invalid k

private def abortAllActiveLoop {S : Session} (ns : ActiveSlots) (fresh : serviceDir ∉ ns) (s : NodeState)
    (k : NodeState → Proc NodeΨ [] S) : Proc NodeΨ (Work ns) S :=
  match ns with
  | [] => k s
  | n :: rest =>
    let f : Frame := ⟨n :: rest, fresh⟩
    abortSlot f (.here rfl) s fun sealed next =>
      let verified := match s.sealedHome, sealed with
        | none, some h => next.verified.insert n (normalizeChildSpec s n h)
        | _, _ => next.verified
      abortAllActiveLoop rest (fun hm => fresh (List.mem_cons_of_mem n hm)) {next with verified} k

private def abortAllActive {S : Session} (ns : ActiveSlots) (fresh : serviceDir ∉ ns) (s : NodeState)
    (k : NodeState → Proc NodeΨ [] S) : Proc NodeΨ (Work ns) S :=
  let targets := cancelTargets s ns
  if targets.isEmpty then abortAllActiveLoop ns fresh s k
  else
    let f : Frame := ⟨ns, fresh⟩
    .run (perform f (.run (.triggerCancel targets))) fun _ => abortAllActiveLoop ns fresh s k

private def runJob (f : Frame) (s : NodeState) (a : Action) (k : a.Result → Proc NodeΨ (Work f.active) Reply) :
    Proc NodeΨ (Work f.active) Reply :=
  .run (perform f (.attempt a)) fun
    | .ok r => k r
    | .error err => abortAllActive f.active f.fresh s fun _ =>
      let empty : Frame := ⟨[], by simp⟩
      .run (perform empty (.raise err)) Empty.elim

private def proposed (f : Frame) (s : NodeState) (sub : Submission) : Proc NodeΨ (Work f.active) Reply :=
  match sub with
  | .plan p subs => runJob f s (.gates s p subs) fun (report, result) =>
    match report.certificate, result with
    | some cert, _ => retry f s cert
    | none, some (c, keep) =>
      abortInvalidated f s (f.active.filter (!keep.contains ·)) fun next st =>
      runJob next st (.reconcile st c) fun r =>
        let saved := st.verified.fold (fun m n h => m.insert n h) st.salvaged
        birthChildren next {st with
          task := {st.task with currentOnLiveBases := true}
          candidate := some c, current := r.current, verified := r.verified, diagnostic := none, salvaged := saved} r.toSpawn
    | _, _ => failed f s "MISSING_CANDIDATE"
  | sub => runJob f s (.witness s.task sub) fun
    | .error e => failed f s e
    | .ok v@(.liftObstruction ..) => afterChildren f {s with obstructing := some v, diagnostic := none}
    | .ok v => abortAllActive f.active f.fresh s fun st =>
      respond ⟨[], by simp⟩ {st with verdict := some v, sealedHome := some (freezeVerifiedKids st), diagnostic := none}

private def proposeTurn (f : Frame) (s : NodeState) : Proc NodeΨ (Work f.active) Reply :=
  runJob f s (.propose ⟨s.task, s.current.code, s.current.memory, s.diagnostic, some s.current⟩) fun
    | none => respond f s
    | some text => match parseSubmission text s.task.drafts with
      | .error err => failed f s err
      | .ok sub => proposed f s sub

private def completed (f : Frame) (s : NodeState) (n : String) (v : Verdict) (h : Frozen) : Proc NodeΨ (Work f.active) Reply :=
  let info := s.inFlight[n]?
  let s := {s with inFlight := s.inFlight.erase n}
  let refuted := fun (why : String) model proof =>
    if let some i := info then
      .run (perform f (.run (.childCheck i))) fun
        | some (.refuted used) =>
          let (cert, notes) := childRefutation used n why model proof
          let cur := s.current
          let current := Frozen.frozen cur.code (cur.memory ++ notes) cur.spec cur.children
          retry f {harvest s h with current} cert
        | _ => failed f (harvest s h) s!"MISSING_REFUTATION_PROVENANCE: {n}"
    else failed f (harvest s h) s!"MISSING_CHILD_INFO: {n}"
  match v, s.obstructing with
  | .ok, _ => afterChildren f {s with verified := s.verified.insert n (normalizeChildSpec s n h)}
  | _, some _ => afterChildren f (harvest s h)
  | obs@(.liftObstruction ..), none => afterChildren f {harvest s h with obstructing := some obs}
  | .contradiction proof, none => refuted "The child interface implies False." none proof
  | .countermodel why model proof, none => refuted why (some model) proof

private def oneTurn (j : J) : Proc NodeΨ (Work j.1.active) Reply :=
  let (f, s) := j
  if s.verdict.isSome then respond f s else
  if s.obstructing.isNone && s.candidate.isNone then proposeTurn f s else
  if hne : f.active ≠ [] then
    .awaitAnyP f.active hne (fun n p v sh =>
      .run (drainSlot p sh) fun home => completed (f.remove p) s n v home) (respond f s)
  else afterChildren f s

private def returnHome (home : Frozen) : Proc NodeΨ [] (Halt HomeShape HomeSt) :=
  let v := thawHome home
  .run (receiveHome "home" rfl v) fun _ => .giveExAt v.1 (.here rfl) rfl .end_

private def shutdownState (j : J) : Proc NodeΨ (Work j.1.active) (Halt HomeShape HomeSt) :=
  abortAllActive j.1.active j.1.fresh j.2 fun s => returnHome <|
    match s.sealedHome with
    | some h => h
    | none => if s.verified.isEmpty && s.salvaged.isEmpty && s.obstructing.isNone then s.original else freezeVerifiedKids s

private def startAgent (sh : HomeShape) (salvaged : Homes) : Proc NodeΨ (Home (HomeCtx sh)) AgentS :=
  .ask fun task => .run (drainHome sh) fun original =>
    .worker oneTurn shutdownState (⟨[], by simp⟩, {task, original, current := original, salvaged})

def nodeAgent (sh : HomeShape) : Proc NodeΨ (Home (HomeCtx sh)) AgentS := startAgent sh {}

abbrev Proposer := AIRequest → IO String
abbrev AcceptNode := NodeTask → String → IO Unit

private def handleAction (propose : AIRequest → IO (Option String)) (accept : AcceptNode)
    (record : ChildCheck → IO Unit) (a : Action) : IO a.Result :=
  match a with
  | .propose req => propose req
  | .gates s p subs => do
    let (report, cand) ← checkCandidateGates s.task s.current p subs
    return (report, ← cand.mapM fun c => return (c, ← survivingSlots s c))
  | .reconcile s c => reconcileChildren s c
  | .seal s c => do
    let result ← catchError (finish s c)
    if let .ok _ := result then
      notifyAccept s.task (c.plan.why ++ "\n" ++ renderLeanMod c.code)
      record .sealed
    return result
  | .witness t sub => do
    let result ← catchError (evidence t sub)
    if let .ok (v, units) := result then
      notifyAccept t (reprStr v)
      record (.refuted units)
    return result.map Prod.fst
  | .childCheck info => do
    if ← info.checked.isResolved then IO.wait info.checked.result? else return none
  | .triggerCancel targets => do
    for p in targets do
      if ← p.isResolved then
        if let some wc ← IO.wait p.result? then
          if let .error err ← wc.trigger.toBaseIO then
            discard (IO.eprintln s!"warning: child cancel hook failed: {err}").toBaseIO
where
  catchError {α : Type} (act : IO α) : IO (Except String α) := return (← act.toBaseIO).mapError toString
  notifyAccept (task : NodeTask) (semantic : String) : IO Unit := do
    if let .error err ← (accept task semantic).toBaseIO then
      discard (IO.eprintln s!"warning: post-verification accept failed for {task.delta.child}: {err}").toBaseIO

private def handleJob (propose : AIRequest → IO (Option String)) (accept : AcceptNode)
    (record : ChildCheck → IO Unit) (j : Job) : IO j.Result :=
  match j with
  | .run a => handleAction propose accept record a
  | .attempt a => (handleAction propose accept record a).toBaseIO
  | .raise err => throw err

/-- Child workers install their owner's cancellation hook before publishing the channel. -/
def withNodeEnvIO {α : Type} (ai : Proposer) (useEnv : EnvIO NodeΨ → IO α)
    (accept : AcceptNode := fun _ _ => pure ()) (cancelOwner : String → IO Unit := fun _ => pure ())
    (childProposer : BaseIO Bool → Proposer := fun _ => ai) : IO α := do
  let child ← IO.mkRef (none : Option (Option (IO.Promise WorkerCancel) → HandlerIO childSpec))
  let supplyIO : HandlerIO supply := fun v _ => pure (pure (v.2, ()))
  let env (parentCancel : Option (IO.Promise WorkerCancel)) (propose : AIRequest → IO (Option String))
      (acceptNode : AcceptNode) (record : ChildCheck → IO Unit) : EnvIO NodeΨ :=
    let childIO : HandlerIO childSpec := fun i ms => do
      let some start ← child.get | throw (IO.userError "missing child handler")
      start parentCancel i ms
    EnvIO.cons (spec := service) (fun j _ => pure (do return (← handleJob propose acceptNode record j, ())))
      (EnvIO.cons supplyIO (EnvIO.cons childIO EnvIO.nil))
  child.set (some (fun parentCancel i ms => do
    return fun t => do
      let stopping ← IO.mkRef false
      let selfCancel ← IO.Promise.new
      -- A terminated proposer can return an IO error. Let the worker reach its halt
      -- boundary with the channels it still owns, even when a replan was interrupted.
      let propose := fun req => do
        if ← stopping.get then return none
        let result ← (childProposer stopping.get req).toBaseIO
        if ← stopping.get then return none
        return some (← EIO.ofExcept result)
      let acceptChild : AcceptNode := fun task semantic => do
        if ← stopping.get then return
        try accept task semantic
        catch e => unless ← stopping.get do throw e
      let worker ← (← evalProcIO (env (some selfCancel) propose acceptChild (fun check => i.checked.resolve check))
        (startAgent i.shape i.salvaged) ms) t
      worker.cancel.onCancel do
        stopping.set true
        cancelOwner (toString t.delta.child)
      selfCancel.resolve worker.cancel
      if let some p := parentCancel then
        if let some parentWc ← IO.wait p.result? then
          parentWc.attachWorker worker
      i.cancel.resolve worker.cancel
      return worker))
  try useEnv (env none (fun req => some <$> ai req) accept (fun _ => pure ()))
  finally child.set none

end Lojita.Harness
