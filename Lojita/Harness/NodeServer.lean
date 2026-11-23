import Lojita.Harness.PlanPreview

namespace Lojita.Harness
open Lojita.Ownership Lojita.Kernel Lojita.Transport

abbrev ChildS := Session.srvI Unit (Option Verdict) HomeShape HomeSt
abbrev AgentS := Session.arr (.dat NodeTask) ChildS

inductive Slots where
  | idle
  | active (name : String)

private def work : Slots → Ctx
  | .idle => []
  | .active _ => [("child", .chan ChildS)]

structure ChildWork where
  task : NodeTask
  home : Frozen

structure Children where
  verified : Array (String × Frozen) := #[]
  pending : List ChildWork := []

structure NodeState where
  task : NodeTask
  original : Frozen
  candidate : Option Candidate := none
  children : Children := {}
  diagnostic : Option NarrowingCertificate := none
  verdict : Option Verdict := none
  sealedHome : Option Frozen := none

def freezeVerifiedKids (s : NodeState) : Frozen :=
  .frozen s.original.code s.original.memory s.original.spec s.children.verified.toList

/-- Check an identity before starting a child. Each target receives only the
    history attached to the source endpoints routed to it by the parent. -/
def reconcileChildren (t : NodeTask) (old : Frozen) (cand : Candidate) : IO Children := do
  let saved := Std.HashMap.ofList old.children
  let kept := Std.HashMap.ofList cand.kept
  let horizontal := nestedBindings t.transports
  let permissions := childPermissions t
  let sources := old.children ++ t.transports.flatMap (·.1.children)
  let mut origins := old.memory.toArray
  let mut seen : Std.HashSet String := {}
  for (n,h) in sources do
    if seen.contains n then continue
    seen := seen.insert n
    for (o,notes) in h.memory do
      if let .unit q := o then origins := origins.push (.ext q, notes)
  let routed := routeChildren cand.plan origins.toList (cand.specs.map (·.modName))
  let mut verified := #[]
  let mut pending := #[]
  for spec in cand.specs do
    let q := spec.modName
    if let some h := kept[q]? then
      verified := verified.push (toString q,h)
    else
      let existing := saved[toString q]?
      let sub := horizontal[q]?.getD []
      let lifts := cand.childLifts[q]?.getD #[]
      if let some h := existing then
        if sub.isEmpty && (← (checkSaved cand.deps spec h).toBaseIO).isOk then
          let reusable ← if lifts.isEmpty then pure true else do
            let keep := TransportSpec.transportSpecTree old.code.modName old.code.modName [.keepChild q q] []
            t.lifts.allM fun (_,s) => do
              let result ← (checkKeptLifts cand.deps [(old,keep)] s).toBaseIO
              return result.toOption.any List.isEmpty
          if reusable then
            verified := verified.push (toString q,h)
            continue
      let incoming := routed[q]?.getD []
      let seed := existing.getD (.frozen ⟨q, [], [], []⟩ [] spec [])
      let home := Frozen.frozen seed.code (seed.memory ++ incoming) seed.spec seed.children
      let child := {t with
        delta := ⟨q,seed.spec.units,spec⟩
        baseModules := cand.deps
        transports := sub
        allowedAncestors := permissions q
        maybeLift := lifts[0]?
        otherLifts := lifts.toList.drop 1}
      pending := pending.push ⟨child, home⟩
  return ⟨verified, pending.toList⟩

/-- Seal the actual linked implementations, including every reused descendant.
    Only this path can construct the successful node verdict. -/
def finish (s : NodeState) (c : Candidate) : IO Frozen := do
  let kids := s.children.verified.toList
  let names := Std.HashSet.ofList (kids.map Prod.fst)
  unless c.specs.all (fun m => names.contains (toString m.modName)) do
    throw (IO.userError "MISSING_VERIFIED_CHILD")
  let home := Frozen.frozen c.code (inherit c.plan s.original.memory) s.task.delta.newIface kids
  verifyClosure c.deps home
  return home

private def evidence (t : NodeTask) (sub : Submission) : IO Verdict := do
  let spec := t.delta.newIface
  let bases ← IO.ofExcept (mergeModules (t.baseModules ++ t.lifts.map Prod.fst))
  match sub with
  | .plan .. => throw (IO.userError "EXPECTED_WITNESS")
  | .contradiction r =>
    witnessBoundary bases spec r
    discard <| checkRefutation bases (stubOf spec) r
    return .contradiction r
  | .refuteLift why r =>
    if bases.isEmpty then throw (IO.userError "NO_LIFT: no closed base modules")
    let culprits ← checkLiftRefutation bases spec r
    return .liftObstruction why culprits r
  | .countermodel why m r =>
    discard <| checkCountermodel bases spec m r
    return .countermodel why m r

private inductive Job where
  | propose (req : AIRequest)
  | gates (s : NodeState) (p : Plan) (subs : List LeanMod)
  | reconcile (s : NodeState) (c : Candidate)
  | seal (s : NodeState) (c : Candidate)
  | witness (t : NodeTask) (sub : Submission)

private def Job.Result : Job → Type
  | .propose _ => String
  | .gates .. => GateReport × Option Candidate
  | .reconcile .. => Except String Children
  | .seal .. => Except String Frozen
  | .witness .. => Except String Verdict

private def service : Spec := ⟨"node-service", Job, fun _ => [], fun j => .ten (.dat j.Result) .end_⟩
private def supply : Spec := ⟨"home", HomeValue, fun _ => [], fun v => .ten (.res (HomeSt v.1)) .end_⟩
private def childSpec : Spec := ⟨"child", HomeShape, fun sh => Home (HomeCtx sh), fun _ => AgentS⟩
abbrev NodeΨ := [service, supply, childSpec]

private def perform (j : Job) : Prog NodeΨ (.dir []) (.dir []) j.Result :=
  .step (.mkdir "service" rfl) fun _ =>
  .exec (.here rfl) (.here rfl) j rfl <|
  .step (.recvD (.here rfl) rfl) fun a => .step (.close (.here rfl) rfl) fun _ => .done a

private def receiveHome (v : HomeValue) : Prog NodeΨ (.dir []) (.dir [("child", HomeSt v.1)]) Unit :=
  .step (.mkdir "child" rfl) fun _ =>
  .exec (.here rfl) (.there (.here rfl)) v rfl (.step (.recover (.here rfl) rfl) .done)

private abbrev J := Slots × NodeState
private abbrev Work (j : J) := work j.1
private abbrev Reply := Session.ten (.dat (Option Verdict)) (Halt J (fun j => .dir (Work j)))

private def respond (ks : Slots) (s : NodeState) : Proc NodeΨ (work ks) Reply :=
  .tell s.verdict (.giveExDir (ks,s) rfl)

private def retry (s : NodeState) (cert : NarrowingCertificate) : Proc NodeΨ [] Reply :=
  respond .idle {s with diagnostic := some cert, candidate := none, children := {}}

private def failed (s : NodeState) (msg : String) :=
  retry s (problem ((msg.splitOn ":").headD "node_error") s.task.delta.child msg "Revise the submission and retry.")

private def sealNode (s : NodeState) (c : Candidate) : Proc NodeΨ [] Reply :=
  .run (perform (.seal s c)) fun
    | .error e => failed s e
    | .ok h => respond .idle {s with sealedHome := some h, verdict := some .ok}

/-- At most one child is active in a node. A sibling becomes a plain sealed
    value before the next is born, so an obstruction cannot consume it. -/
def birthChildren (s : NodeState) (c : Candidate) : Proc NodeΨ [] Reply :=
  match s.children.pending with
  | [] => sealNode s c
  | kid :: rest =>
    let v := thawHome kid.home
    .run (receiveHome v) fun _ =>
    .run (.exec (.here rfl) (.there (.there (.here rfl))) v.1 rfl
      (.step (.sendD (.here rfl) rfl kid.task) .done)) fun _ =>
    respond (.active (toString kid.task.delta.child)) {s with children := {s.children with pending := rest}}

private def proposed (s : NodeState) (sub : Submission) : Proc NodeΨ [] Reply :=
  match sub with
  | .plan p subs => .run (perform (.gates s p subs)) fun (report, candidate) =>
    match report.certificate, candidate with
    | some cert, _ => retry s cert
    | none, some c => .run (perform (.reconcile s c)) fun
      | .error err => failed s err
      | .ok kids => birthChildren {s with candidate := some c, diagnostic := none, children := kids} c
    | _, _ => failed s "MISSING_CANDIDATE"
  | sub => .run (perform (.witness s.task sub)) fun
    | .error err => failed s err
    | .ok v@(.liftObstruction ..) =>
      respond .idle {s with verdict := some v, sealedHome := some (freezeVerifiedKids s), diagnostic := none}
    | .ok v => respond .idle {s with verdict := some v, diagnostic := none}

private def reap {S : Session} (k : Frozen → Proc NodeΨ [] S) : Proc NodeΨ [("child", .chan ChildS)] S :=
  .stopP (.here rfl) rfl fun sh =>
    .run (.focus (.here rfl) (drainHome sh) fun h =>
      .step (.rmdir (.here rfl) rfl) fun _ => .done h) k

private def idleTurn (s : NodeState) : Proc NodeΨ [] Reply :=
  if s.verdict.isSome then respond .idle s else
  .run (perform (.propose ⟨s.task,s.original.code,s.original.memory,s.diagnostic,some s.original⟩)) fun text =>
    match parseSubmission text s.task.drafts with
    | .error err => failed s err
    | .ok sub => proposed s sub

def oneTurn (j : J) : Proc NodeΨ (Work j) (Turn Unit (Option Verdict) J Work) :=
  match j with
  | (.idle,s) => .ask fun _ => idleTurn s
  | (.active n,s) => .ask fun _ =>
    .run (.step (.call (.here rfl) rfl ()) .done) fun answer =>
      match answer with
      | none => respond (.active n) s
      | some v => reap fun home =>
        match v, s.candidate with
        | .ok, some c => birthChildren {s with children := {s.children with verified := s.children.verified.push (n,home)}} c
        | .ok, none => failed s "MISSING_CANDIDATE"
        | .liftObstruction .., _ => respond .idle {s with verdict := some v, sealedHome := some (freezeVerifiedKids s)}
        | _, _ => respond .idle {s with verdict := some v}

private def returnHome (f : Frozen) : Proc NodeΨ [] (Halt HomeShape HomeSt) :=
  let v := thawHome f
  .run (receiveHome v) fun _ => .giveExAt v.1 (.here rfl) rfl .end_

def shutdownState (j : J) : Proc NodeΨ (Work j) (Halt HomeShape HomeSt) :=
  match j with
  | (.idle,s) => returnHome (s.sealedHome.getD s.original)
  | (.active _,s) => reap fun _ => returnHome s.original

def nodeAgent (sh : HomeShape) : Proc NodeΨ (Home (HomeCtx sh)) AgentS :=
  .ask fun task => .run (drainHome sh) fun original =>
    .machine oneTurn shutdownState (.idle, {task, original})

abbrev Proposer := AIRequest → IO String

abbrev AcceptNode := NodeTask → String → IO Unit

private def handleJob (ai : Proposer) (accept : AcceptNode) (j : Job) : IO j.Result :=
  match j with
  | .propose req => ai req
  | .gates s p subs => checkCandidateGates s.task s.original p subs
  | .reconcile s c => catchError (reconcileChildren s.task s.original c)
  | .seal s c => do
    let result ← catchError (finish s c)
    if let .ok _ := result then accept s.task (c.plan.why ++ "\n" ++ renderLeanMod c.code)
    return result
  | .witness t sub => do
    let result ← catchError (evidence t sub)
    if let .ok v := result then accept t (reprStr v)
    return result
where
  catchError {α : Type} (act : IO α) : IO (Except String α) := return (← act.toBaseIO).mapError toString

/-- Drive agents for the duration of the callback. Child birth enters this
    handler on demand, and shutdown of the scope releases its self-reference. -/
def withNodeEnvIO {α : Type} (ai : Proposer) (useEnv : EnvIO NodeΨ → IO α)
    (accept : AcceptNode := fun _ _ => pure ()) : IO α := do
  let child ← IO.mkRef (none : Option (HandlerIO childSpec))
  let serviceIO : HandlerIO service := fun j _ => pure (do return (← handleJob ai accept j, ()))
  let supplyIO : HandlerIO supply := fun v _ => pure (pure (v.2, ()))
  let childIO : HandlerIO childSpec := fun sh ms => do
    let some start ← child.get | throw (IO.userError "missing child handler")
    start sh ms
  let env : EnvIO NodeΨ := EnvIO.cons serviceIO (EnvIO.cons supplyIO (EnvIO.cons childIO EnvIO.nil))
  child.set (some (fun sh => evalProcIO env (nodeAgent sh)))
  try useEnv env finally child.set none

end Lojita.Harness
