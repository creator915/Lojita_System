import Lojita.Ownership.Core
import Std.Sync.Mutex

namespace Lojita.Ownership

structure RunningIO (Q R M : Type) where
  callIO : Q → IO R
  stopIO : IO M

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

def evalProcIO (env : EnvIO Ψ) {Γ : Ctx} {S : Session} (p : Proc Ψ Γ S) : ModelsIO Γ → IO (OfferIO S) :=
  match p with
  | .run p k => fun m => do
    let (v, a) ← evalIO env p m
    evalProcIO env (k a) v
  | .end_ => fun _ => pure ()
  | .giveAt x k => fun m => pure (do return (getAtIO x m, ← evalProcIO env k (delAtIO x m)))
  | .tell a k => fun m => pure (do return (a, ← evalProcIO env k m))
  | .takeAt _ _ k => fun m => pure (fun v => evalProcIO env k (v, m))
  | .ask k => fun m => pure (fun a => evalProcIO env (k a) m)
  | .giveExAt i x e k => fun m => pure (do return (⟨i, asModelIO e (getAtIO x m)⟩, ← evalProcIO env k (delAtIO x m)))
  | @Proc.machine _ _ _ _ J _ family turn halt j => fun m =>
    RunningIO.machine (State := (i : J) × ModelsIO (family i)) ⟨j, m⟩
      (fun ⟨i, v⟩ q => do
        let request ← evalProcIO env (turn i) v
        let answer ← request q
        let (a, resource) ← answer
        return (a, (← resource).1))
      (fun ⟨i, v⟩ => do return (← (← evalProcIO env (halt i) v)).1)
  | .giveExDir i e => fun m => pure (pure (⟨i, asModelIO e m⟩, ()))
  | .stopP x e k => fun m => do
    let v ← RunningIO.stopIO (asModelIO e (getAtIO x m))
    evalProcIO env (k v.1) (putAtIO x m v.2)
termination_by structural p

end Lojita.Ownership
