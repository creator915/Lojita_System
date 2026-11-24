import Lojita.Ownership.Core
import Std.Sync.Mutex

namespace Lojita.Ownership

structure RunningIO (Q R M : Type) where
  callIO : Q → IO R
  stopIO : IO M

structure WorkerCancel where
  cancelled : IO.Ref Bool
  promise : IO.Promise Unit
  hooks : Std.Mutex (Nat × Array (Nat × IO Unit))
  children : Std.Mutex (Nat × Array (Nat × BaseIO Unit × BaseIO Unit))
  deriving Nonempty

def WorkerCancel.new : IO WorkerCancel := do
  return ⟨← IO.mkRef false, ← IO.Promise.new, ← Std.Mutex.new (0, #[]), ← Std.Mutex.new (0, #[])⟩

def WorkerCancel.onCancelHandle (wc : WorkerCancel) (act : IO Unit) : IO (BaseIO Unit) := do
  let id? ← wc.hooks.atomically do
    if ← wc.cancelled.get then return none
    let (nextId, hs) ← get
    set (nextId + 1, hs.push (nextId, act))
    return some nextId
  match id? with
  | none =>
    act
    return pure ()
  | some id =>
    return wc.hooks.atomically do
      let (nextId, hs) ← get
      set (nextId, hs.filter (·.1 != id))

def WorkerCancel.onCancel (wc : WorkerCancel) (act : IO Unit) : IO Unit := do
  discard <| wc.onCancelHandle act

def WorkerCancel.trigger (wc : WorkerCancel) : IO Unit := do
  let actions ← wc.hooks.atomically do
    if ← wc.cancelled.get then return #[]
    wc.cancelled.set true
    wc.promise.resolve ()
    modifyGet fun (nextId, hooks) => (hooks, (nextId, #[]))
  -- Run hooks outside the lock, including the remaining hooks if one fails.
  let mut result : Except IO.Error Unit := .ok ()
  for (_, act) in actions do
    let next ← act.toBaseIO
    if result.isOk then result := next
  EIO.ofExcept result

def WorkerCancel.joinChildren (wc : WorkerCancel) : BaseIO Unit := do
  let cs ← wc.children.atomically (return (← get).2)
  for (_, cancelIfLive, _) in cs do cancelIfLive
  for (_, _, join) in cs do join

structure WorkerIO (R M : Type) where
  cancel : WorkerCancel
  task : Task (Except IO.Error (Option R × M))

def WorkerCancel.attachWorker {R M : Type} (parent : WorkerCancel) (child : WorkerIO R M) : IO Unit := do
  if ← IO.hasFinished child.task then return
  let alive ← IO.mkRef true
  let cancelIfLive : BaseIO Unit := do
    if (← alive.get) && !(← IO.hasFinished child.task) then
      discard child.cancel.trigger.toBaseIO
  let unregisterHook ← parent.onCancelHandle cancelIfLive
  let childId ← parent.children.atomically do
    let (nextId, cs) ← get
    set (nextId + 1, cs.push (nextId, cancelIfLive, discard (IO.wait child.task)))
    return nextId
  let detach : BaseIO Unit := do
    alive.set false
    unregisterHook
    parent.children.atomically do
      let (nextId, cs) ← get
      set (nextId, cs.filter (·.1 != childId))
  discard <| BaseIO.mapTask (fun _ => detach) child.task (sync := true)

def WorkerIO.awaitIO {R M : Type} (w : WorkerIO R M) : IO (Option R × M) := do
  EIO.ofExcept (← IO.wait w.task)

def WorkerIO.abortIO {R M : Type} (w : WorkerIO R M) : IO M := do
  let signal ← w.cancel.trigger.toBaseIO
  if let .error err := signal then
    discard (IO.eprintln s!"warning: worker cancel hook failed: {err}").toBaseIO
  let result ← IO.wait w.task
  return (← EIO.ofExcept result).2

mutual
  def ModelIO : St → Type
    | .file A => A
    | .dir es => ModelsIO es
    | .chan S => OfferIO S
  termination_by structural s => s

  def ModelsIO : Ctx → Type
    | [] => Unit
    | e :: es => EntryIO e × ModelsIO es
  termination_by structural es => es

  def EntryIO : String × St → Type
    | (_, s) => ModelIO s
  termination_by structural e => e

  def MsgIO : Ty → Type
    | .dat A => A
    | .res s => ModelIO s
    | .exRes I F => (i : I) × ModelIO (F i)
  termination_by structural t => t

  def OfferIO : Session → Type
    | .end_ => Unit
    | .ten t S => IO (MsgIO t × OfferIO S)
    | .arr t S => MsgIO t → IO (OfferIO S)
    | .srvI Q R I F => RunningIO Q R ((i : I) × ModelIO (F i))
    | .workerI R I F => WorkerIO R ((i : I) × ModelIO (F i))
  termination_by structural S => S
end

variable {Γ Δ : Ctx} {Ψ : List Spec} {n m : String} {s t : St}
variable {S : Session} {A B Q R I J : Type} {F : I → St} {G : J → Ctx}

abbrev HandlerIO (spec : Spec) := (i : spec.Idx) → ModelsIO (spec.ctx i) → IO (OfferIO (spec.session i))
abbrev EnvIO (Ψ : List Spec) := {m : String} → (h : MemSpec m Ψ) → HandlerIO h.value

def EnvIO.nil : EnvIO [] := fun h => nomatch h
def EnvIO.cons {spec : Spec} (f : HandlerIO spec) (env : EnvIO Ψ) : EnvIO (spec :: Ψ)
  | _, .here _ => f
  | _, .there h => env h

def getAtIO : {Γ : Ctx} → (x : MemCtx n Γ) → ModelsIO Γ → ModelIO (stateOf x)
  | (_, _) :: _, .here _, ms => ms.1
  | (_, _) :: _, .there p, ms => getAtIO p ms.2
termination_by structural _ x _ => x

def putAtIO {s : St} : {Γ : Ctx} → (x : MemCtx n Γ) → ModelsIO Γ → ModelIO s → ModelsIO (setAt x s)
  | (_, _) :: _, .here _, ms, v => (v, ms.2)
  | (_, _) :: _, .there p, ms, v => (ms.1, putAtIO p ms.2 v)
termination_by structural _ x _ _ => x

def delAtIO : {Γ : Ctx} → (x : MemCtx n Γ) → ModelsIO Γ → ModelsIO (removeAt x)
  | (_, _) :: _, .here _, ms => ms.2
  | (_, _) :: _, .there p, ms => (ms.1, delAtIO p ms.2)
termination_by structural _ x _ => x

def splitModelsIO {Γ Γ₁ Γ₂ : Ctx} (sp : SplitCtx Γ Γ₁ Γ₂) (ms : ModelsIO Γ) : ModelsIO Γ₁ × ModelsIO Γ₂ :=
  match sp with
  | .nil => (ms, ms)
  | .left _ _ tail =>
    let (l, r) := splitModelsIO tail ms.2
    ((ms.1, l), r)
  | .right _ _ tail =>
    let (l, r) := splitModelsIO tail ms.2
    (l, (ms.1, r))
termination_by structural sp

def joinModelsIO : (Δ₁ Δ₂ : Ctx) → ModelsIO Δ₁ → ModelsIO Δ₂ → ModelsIO (Δ₁ ++ Δ₂)
  | [], _, _, r => r
  | _ :: xs, ys, l, r => (l.1, joinModelsIO xs ys l.2 r)
termination_by structural xs _ _ _ => xs

def permuteIO : {Γ Δ : Ctx} → Reorder Γ Δ → ModelsIO Γ → ModelsIO Δ
  | _, _, .refl, ms => ms
  | _, _, .cons (_, _) p, ms => (ms.1, permuteIO p ms.2)
  | _, _, .swap (_, _) (_, _), ms => (ms.2.1, ms.1, ms.2.2)
  | _, _, .trans p q, ms => permuteIO q (permuteIO p ms)
termination_by structural _ _ p _ => p

def asModelIO {s t : St} (h : s = t) (v : ModelIO s) : ModelIO t := h ▸ v


def evalCmdIO : {s t : St} → {A : Type} → Cmd s t A → ModelIO s → IO (ModelIO t × A)
  | _, _, _, .read, m => pure (m, m)
  | _, _, _, .reorder p, m => pure (permuteIO p m, ())
  | _, _, _, .create _ _ a, m => pure ((a, m), ())
  | _, _, _, .mkdir _ _, m => pure (((), m), ())
  | _, _, _, .unlink x _, m => pure (delAtIO x m, ())
  | _, _, _, .rmdir x _, m => pure (delAtIO x m, ())
  | _, _, _, .link x _ _ _, m => pure ((getAtIO x m, m), ())
  | _, _, _, .up x e z _, m =>
    let d := asModelIO e (getAtIO x m)
    pure ((getAtIO z d, putAtIO x m (delAtIO z d)), ())
  | _, _, _, .down z x e _, m =>
    let rest := delAtIO z m
    pure (putAtIO x rest (getAtIO z m, asModelIO e (getAtIO x rest)), ())
  | _, _, _, .recv c e _ _, m => do
    let (v, k) ← asModelIO e (getAtIO c m)
    return ((v, putAtIO c m k), ())
  | _, _, _, .recvD c e, m => do
    let (a, k) ← asModelIO e (getAtIO c m)
    return (putAtIO c m k, a)
  | _, _, _, .send z c e, m => do
    let rest := delAtIO z m
    let k ← asModelIO e (getAtIO c rest) (getAtIO z m)
    return (putAtIO c rest k, ())
  | _, _, _, .sendD c e a, m => do
    return (putAtIO c m (← asModelIO e (getAtIO c m) a), ())
  | _, _, _, .close x _, m => pure (delAtIO x m, ())
  | _, _, _, .recover x e, m => do return (putAtIO x m (← asModelIO e (getAtIO x m)).1, ())
  | _, _, _, .call x e q, m => do
    let h := asModelIO e (getAtIO x m)
    return (putAtIO x m h, ← RunningIO.callIO h q)
  | _, _, _, .stop x e, m => do
    return (putAtIO x m (← RunningIO.stopIO (asModelIO e (getAtIO x m))).2, ())

private def triggerOfferIO : (S : Session) → OfferIO S → BaseIO Unit
  | .workerI _ _ _, w => do
    if !(← IO.hasFinished w.task) then discard w.cancel.trigger.toBaseIO
  | _, _ => pure ()

mutual
  private def triggerModelIO : (s : St) → ModelIO s → BaseIO Unit
    | .file _, _ => pure ()
    | .dir es, ms => triggerModelsIO es ms
    | .chan S, o => triggerOfferIO S o
  termination_by structural s => s

  private def triggerModelsIO : (Γ : Ctx) → ModelsIO Γ → BaseIO Unit
    | [], _ => pure ()
    | (_, s) :: es, (v, rest) => do
      triggerModelIO s v
      triggerModelsIO es rest
  termination_by structural Γ => Γ
end

mutual
  private partial def cleanupModelIO : (s : St) → ModelIO s → BaseIO Unit
    | .file _, _ => pure ()
    | .dir es, ms => cleanupModelsIO es ms
    | .chan S, o => cleanupOfferIO S o

  private partial def cleanupModelsIO : (Γ : Ctx) → ModelsIO Γ → BaseIO Unit
    | [], _ => pure ()
    | (_, s) :: es, (v, rest) => do
      cleanupModelIO s v
      cleanupModelsIO es rest

  private partial def cleanupOfferIO : (S : Session) → OfferIO S → BaseIO Unit
    | .srvI _ _ _ F, r => do
      if let .ok ⟨i, v⟩ ← r.stopIO.toBaseIO then cleanupModelIO (F i) v
    | .workerI _ _ F, w => do
      if !(← IO.hasFinished w.task) then discard w.cancel.trigger.toBaseIO
      if let .ok (_, ⟨i, v⟩) ← IO.wait w.task then cleanupModelIO (F i) v
    | _, _ => pure ()
end

private def reclaimModelsIO (Γ : Ctx) (ms : ModelsIO Γ) : BaseIO Unit := do
  triggerModelsIO Γ ms
  cleanupModelsIO Γ ms

def evalIO (env : EnvIO Ψ) : {s t : St} → {A : Type} → Prog Ψ s t A → ModelIO s → IO (ModelIO t × A)
  | _, _, _, .done a, m => pure (m, a)
  | _, _, _, .step c k, m => do
    let (v, a) ← evalCmdIO c m
    evalIO env (k a) v
  | _, _, _, .focus x p k, m => do
    let (v, a) ← evalIO env p (getAtIO x m)
    evalIO env (k a) (putAtIO x m v)
  | _, _, _, .exec x h i e k, m => do
    evalIO env k (putAtIO x m (← env h i (asModelIO e (getAtIO x m))))
  | _, _, _, .stopI x e k, m => do
    let v ← RunningIO.stopIO (asModelIO e (getAtIO x m))
    evalIO env (k v.1) (putAtIO x m v.2)
  | _, _, _, .par sp _ p₁ p₂ k, m => do
    let (m₁, m₂) := splitModelsIO sp m
    let left ← IO.asTask (evalIO env p₁ m₁) .dedicated
    let right ← (evalIO env p₂ m₂).toBaseIO
    let leftRes ← IO.wait left
    match leftRes, right with
    | .ok (l, a), .ok (r, b) =>
      evalIO env (k a b) (joinModelsIO _ _ l r)
    | .error err, .ok (r, _) =>
      reclaimModelsIO _ r
      throw err
    | .ok (l, _), .error err =>
      reclaimModelsIO _ l
      throw err
    | .error err, .error _ =>
      throw err
  | _, _, _, .awaitI c e k, m => do
    let (opt, v) ← WorkerIO.awaitIO (asModelIO e (getAtIO c m))
    evalIO env (k opt v.1) (putAtIO c m v.2)
  | _, _, _, .abortI c e k, m => do
    let v ← WorkerIO.abortIO (asModelIO e (getAtIO c m))
    evalIO env (k v.1) (putAtIO c m v.2)
termination_by structural _ _ _ p _ => p

def RunningIO.machine {State : Type} (init : State)
    (step : State → Q → IO (R × State)) (finish : State → IO A) : IO (RunningIO Q R A) := do
  let cell ← Std.Mutex.new (some init)
  return {
    callIO := fun q => cell.atomically do
      let some s ← get | throw (IO.userError "server stopped")
      set (none : Option State)
      let (a, next) ← step s q
      set (some next)
      return a
    stopIO := cell.atomically do
      let some s ← get | throw (IO.userError "server stopped")
      set (none : Option State)
      finish s }

private partial def runWorkerIO {State R M : Type} (wc : WorkerCancel)
    (turn : State → IO (Option R × State)) (halt : State → IO M)
    (cleanup : State → BaseIO Unit) (state : State) : IO (Option R × M) := do
  let runHalt (st : State) : IO M := do
    try halt st
    catch err =>
      discard wc.trigger.toBaseIO
      wc.joinChildren
      cleanup st
      throw err
  if ← wc.cancelled.get then return (none, ← runHalt state)
  let (opt, next) ← try turn state
    catch err =>
      discard wc.trigger.toBaseIO
      wc.joinChildren
      cleanup state
      throw err
  match opt with
  | some r =>
    let cancelled ← wc.cancelled.get
    return (if cancelled then none else some r, ← runHalt next)
  | none => runWorkerIO wc turn halt cleanup next

private def workerSlots (R I : Type) (F : I → St) : (names : List String) →
    ModelsIO (workCtx R I F names) → List (WorkerIO R ((i : I) × ModelIO (F i)))
  | [], _ => []
  | _ :: ns, ms => ms.1 :: workerSlots R I F ns ms.2

private def slotPosition? : (names : List String) → Nat → Option ((n : String) × Position id n names)
  | [], _ => none
  | n :: _, 0 => some ⟨n, .here rfl⟩
  | _ :: ns, i + 1 => (slotPosition? ns i).map fun ⟨n, p⟩ => ⟨n, .there p⟩

private def waitForWorker {R M : Type} (wc : Option WorkerCancel) (head : WorkerIO R M)
    (tail : List (WorkerIO R M)) : BaseIO (Option (Nat × Except IO.Error (Option R × M))) :=
  let tag (idx : Nat) (w : WorkerIO R M) := w.task.map (fun res => some (idx, res)) (sync := true)
  let tasks := tag 0 head :: tail.mapIdx (fun i w => tag (i + 1) w)
  match wc with
  | none => IO.waitAny tasks
  | some wc => IO.waitAny (wc.promise.result?.map (fun _ => none) (sync := true) :: tasks)

private def selectWorkerIO (wc : Option WorkerCancel) (R I : Type) (F : I → St) : (names : List String) →
    names ≠ [] → ModelsIO (workCtx R I F names) →
    IO (Option ((n : String) × Position id n names × R × ((i : I) × ModelIO (F i))))
  | [], h, _ => False.elim (h rfl)
  | name :: ns, _, ms => do
    let tail := workerSlots R I F ns ms.2
    let some (idx, result) ← waitForWorker wc ms.1 tail | return none
    try
      let (opt, v) ← EIO.ofExcept result
      let some r := opt | throw (IO.userError "selected worker stopped without a result")
      let some ⟨n, p⟩ := slotPosition? (name :: ns) idx | throw (IO.userError "invalid worker position")
      return some ⟨n, p, r, v⟩
    catch err =>
      -- Signal every sibling before joining any of them. Preserve the selected error.
      let siblings := (ms.1 :: tail).eraseIdx idx
      for w in siblings do
        if !(← IO.hasFinished w.task) then discard w.cancel.trigger.toBaseIO
      for w in siblings do discard (IO.wait w.task)
      throw err

/-- An autonomous turn listens to its own cancellation promise. Its halt process
    runs to completion and explicitly reclaims any children it still owns. -/
def evalProcWithCancelIO (wc : Option WorkerCancel) (env : EnvIO Ψ) {Γ : Ctx} {S : Session}
    (p : Proc Ψ Γ S) : ModelsIO Γ → IO (OfferIO S) :=
  match p with
  | .run p k => fun m => do
    let (v, a) ← evalIO env p m
    evalProcWithCancelIO wc env (k a) v
  | .end_ => fun _ => pure ()
  | .giveAt x k => fun m => pure (do return (getAtIO x m, ← evalProcWithCancelIO wc env k (delAtIO x m)))
  | .tell a k => fun m => pure (do return (a, ← evalProcWithCancelIO wc env k m))
  | .takeAt _ _ k => fun m => pure (fun v => evalProcWithCancelIO wc env k (v, m))
  | .ask k => fun m => pure (fun a => evalProcWithCancelIO wc env (k a) m)
  | .giveExAt i x e k => fun m => pure (do
    return (⟨i, asModelIO e (getAtIO x m)⟩, ← evalProcWithCancelIO wc env k (delAtIO x m)))
  | @Proc.machine _ _ _ _ J _ family turn halt j => fun m =>
    RunningIO.machine (State := (i : J) × ModelsIO (family i)) ⟨j, m⟩
      (fun ⟨i, v⟩ q => do
        let request ← evalProcWithCancelIO wc env (turn i) v
        let answer ← request q
        let (a, resource) ← answer
        return (a, (← resource).1))
      (fun ⟨i, v⟩ => do return (← (← evalProcWithCancelIO wc env (halt i) v)).1)
  | .giveExDir i e => fun m => pure (pure (⟨i, asModelIO e m⟩, ()))
  | .stopP x e k => fun m => do
    let v ← RunningIO.stopIO (asModelIO e (getAtIO x m))
    evalProcWithCancelIO wc env (k v.1) (putAtIO x m v.2)
  | @Proc.worker _ _ _ J _ family turn halt j => fun m => do
    let child ← WorkerCancel.new
    let task ← IO.asTask (prio := .dedicated) <|
      runWorkerIO (State := (i : J) × ModelsIO (family i)) child
        (fun ⟨i, v⟩ => do
          let (opt, resource) ← (← evalProcWithCancelIO (some child) env (turn i) v)
          return (opt, (← resource).1))
        (fun ⟨i, v⟩ => do return (← (← evalProcWithCancelIO none env (halt i) v)).1)
        (fun ⟨i, v⟩ => reclaimModelsIO (family i) v)
        ⟨j, m⟩
    let w : WorkerIO _ _ := ⟨child, task⟩
    if let some parent := wc then
      parent.attachWorker w
    return w
  | .abortP x e k => fun m => do
    let v ← WorkerIO.abortIO (asModelIO e (getAtIO x m))
    evalProcWithCancelIO wc env (k v.1) (putAtIO x m v.2)
  | @Proc.awaitAnyP _ R I F _ names hne done pending => fun m => do
    let some ⟨n, p, r, i, v⟩ ← selectWorkerIO wc R I F names hne m
      | evalProcWithCancelIO wc env pending m
    evalProcWithCancelIO wc env (done n p r i) (putAtIO (workPos R I F p) m v)
termination_by structural p

def evalProcIO (env : EnvIO Ψ) {Γ : Ctx} {S : Session} (p : Proc Ψ Γ S) : ModelsIO Γ → IO (OfferIO S) :=
  evalProcWithCancelIO none env p

end Lojita.Ownership
