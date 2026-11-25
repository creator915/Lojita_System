import LojitaCtx.Posix.Syscall

namespace LojitaCtx.Posix

/-- One transition of a user-level machine with private state S. -/
inductive Request (Δ : List Cap) (A S : Type) where
  | done (result : A)
  | ask (op : SysOp) (allowed : op.cap ∈ Δ) (next : Ret op.Result → S)

/-- Finite observation of an interaction. A suspended observation has not terminated. -/
inductive Prefix (Δ : List Cap) (A : Type) where
  | done (result : A)
  | ask (op : SysOp) (allowed : op.cap ∈ Δ) (next : Ret op.Result → Prefix Δ A)
  | suspended

def Prefix.ctorIdx {Δ A} : Prefix Δ A → Nat
  | .done .. => 0
  | .ask .. => 1
  | .suspended => 2

/-- A finite, total interaction tree. Each reply selects a typed continuation. -/
inductive FreeSys (Δ : List Cap) (A : Type) where
  | pure (value : A)
  | step (op : SysOp) (allowed : op.cap ∈ Δ) (next : Ret op.Result → FreeSys Δ A)

def FreeSys.ctorIdx {Δ A} : FreeSys Δ A → Nat
  | .pure _ => 0
  | .step .. => 1

/-- A streaming program. State is private to the application and each round is finite. -/
structure PosixMachine (Δ : List Cap) (S A : Type) where
  init : S
  step : S → FreeSys Δ (Sum S A)

variable {Δ : List Cap} {A B S T : Type}

def FreeSys.bind (p : FreeSys Δ A) (f : A → FreeSys Δ B) : FreeSys Δ B :=
  match p with
  | .pure a => f a
  | .step op h next => .step op h fun r => (next r).bind f

instance : Monad (FreeSys Δ) where
  pure := .pure
  bind := FreeSys.bind

instance {Δ : List Cap} : LawfulMonad (FreeSys Δ) := LawfulMonad.mk' _
  (id_map := by
    intro A p
    change p.bind (fun a => .pure a) = p
    induction p with
    | pure _ => rfl
    | step op allowed next ih =>
      dsimp only [FreeSys.bind]
      exact congrArg (FreeSys.step op allowed) (funext ih))
  (pure_bind := by intros; rfl)
  (bind_assoc := by
    intro A B C p f g
    change (p.bind f).bind g = p.bind fun a => (f a).bind g
    induction p with
    | pure _ => rfl
    | step op allowed next ih =>
      dsimp only [FreeSys.bind]
      exact congrArg (FreeSys.step op allowed) (funext ih))

def FreeSys.call (op : SysOp) (h : op.cap ∈ Δ) : FreeSys Δ (Ret op.Result) := .step op h .pure

def FreeSys.toPrefix (p : FreeSys Δ A) (f : A → Prefix Δ B) : Prefix Δ B :=
  match p with
  | .pure a => f a
  | .step op h next => .ask op h fun r => (next r).toPrefix f

def PosixMachine.ofFree (p : FreeSys Δ A) : PosixMachine Δ Unit A :=
  ⟨(), fun _ => p.bind fun a => .pure (.inr a)⟩

def PosixMachine.unfold (initial : S) (f : S → Request Δ A S) : PosixMachine Δ S A :=
  ⟨initial, fun s => match f s with
    | .done a => .pure (.inr a)
    | .ask op h next => .step op h fun r => .pure (.inl (next r))⟩

def PosixMachine.map (p : PosixMachine Δ S A) (f : A → B) : PosixMachine Δ S B :=
  ⟨p.init, fun s => (p.step s).bind fun
    | .inl n => .pure (.inl n)
    | .inr a => .pure (.inr (f a))⟩

def PosixMachine.andThen (p : PosixMachine Δ S A) (q : PosixMachine Δ T B) : PosixMachine Δ (S ⊕ T) B :=
  ⟨.inl p.init, fun
    | .inl s => (p.step s).bind fun
      | .inl n => .pure (.inl (.inl n))
      | .inr _ => .pure (.inl (.inr q.init))
    | .inr t => (q.step t).bind fun
      | .inl n => .pure (.inl (.inr n))
      | .inr b => .pure (.inr b)⟩

def PosixMachine.bind (p : PosixMachine Δ S A) (f : A → PosixMachine Δ T B) :
    PosixMachine Δ (S ⊕ (A × T)) B :=
  ⟨.inl p.init, fun
    | .inl s => (p.step s).bind fun
      | .inl n => .pure (.inl (.inl n))
      | .inr a => .pure (.inl (.inr (a,(f a).init)))
    | .inr (a,t) => ((f a).step t).bind fun
      | .inl n => .pure (.inl (.inr (a,n)))
      | .inr b => .pure (.inr b)⟩

def Prefix.bind (p : Prefix Δ A) (f : A → Prefix Δ B) : Prefix Δ B :=
  match p with
  | .done a => f a
  | .suspended => .suspended
  | .ask op h next => .ask op h fun r => (next r).bind f

/-- Observe at most this many state-machine rounds. Even at zero, a final pure return
    is visible; no syscall or internal state transition can pass the round boundary. -/
def PosixMachine.observeFrom (p : PosixMachine Δ S A) (budget : Nat) (s : S) : Prefix Δ A :=
  match budget with
  | 0 => match p.step s with
    | .pure (.inr a) => .done a
    | _ => .suspended
  | n+1 => (p.step s).toPrefix fun
    | .inr a => .done a
    | .inl t => p.observeFrom n t

def PosixMachine.observe (p : PosixMachine Δ S A) (budget : Nat) : Prefix Δ A :=
  p.observeFrom budget p.init

def PosixMachine.unfoldPrefix (step : S → Request Δ A S) (n : Nat) (state : S) : Prefix Δ A :=
  match step state with
  | .done a => .done a
  | .ask op h next =>
    match n with
    | 0 => .suspended
    | k+1 => .ask op h fun r => unfoldPrefix step k (next r)
termination_by structural n

theorem PosixMachine.observe_unfold (s : S) (f : S → Request Δ A S) (n : Nat) :
    (unfold s f).observe n = unfoldPrefix f n s := by
  unfold observe
  change (unfold s f).observeFrom n s = _
  suffices h : ∀ t, (unfold s f).observeFrom n t = unfoldPrefix f n t from h s
  induction n with
  | zero => intro t; rw [unfoldPrefix]; cases h : f t <;> simp [observeFrom,unfold,h]
  | succ n ih =>
    intro t
    rw [unfoldPrefix]
    cases h : f t with
    | done a => simp [h,observeFrom,unfold,FreeSys.toPrefix]
    | ask op allowed next =>
      simp only [observeFrom,unfold,h,FreeSys.toPrefix]
      congr 1
      funext r
      exact ih (next r)

private theorem FreeSys.toPrefix_bind_result {X Y Z W : Type} (p : FreeSys Δ X)
    (f : X → FreeSys Δ Y) (g : Y → Prefix Δ Z) (k : X → Prefix Δ W) (h : W → Prefix Δ Z)
    (leaf : ∀ x, (f x).toPrefix g = (k x).bind h) :
    (p.bind f).toPrefix g = (p.toPrefix k).bind h := by
  induction p with
  | pure x => exact leaf x
  | step op allowed next ih =>
    simp only [FreeSys.bind,FreeSys.toPrefix,Prefix.bind]
    congr 1
    funext r
    exact ih r

theorem PosixMachine.observe_map (p : PosixMachine Δ S A) (f : A → B) (n : Nat) :
    (p.map f).observe n = (p.observe n).bind (fun a => .done (f a)) := by
  suffices h : ∀ t, (p.map f).observeFrom n t =
      (p.observeFrom n t).bind (fun a => .done (f a)) from h p.init
  induction n with
  | zero =>
    intro t
    cases h : p.step t with
    | pure result =>
      cases result <;> simp [observeFrom,map,h,FreeSys.bind,Prefix.bind]
    | step op allowed next => simp [observeFrom,map,h,FreeSys.bind,Prefix.bind]
  | succ n ih =>
    intro t
    simp only [observeFrom]
    apply FreeSys.toPrefix_bind_result (p.step t)
    intro x
    cases x with
    | inl t => exact ih t
    | inr a => rfl

/-- A larger observation may only replace suspended leaves with further behavior. -/
inductive Prefix.Extends : Prefix Δ A → Prefix Δ A → Prop where
  | suspended (q : Prefix Δ A) : Extends .suspended q
  | done (a : A) : Extends (.done a) (.done a)
  | ask (op : SysOp) (allowed : op.cap ∈ Δ) (f g : Ret op.Result → Prefix Δ A)
      (h : ∀ r, Extends (f r) (g r)) : Extends (.ask op allowed f) (.ask op allowed g)

private theorem FreeSys.extends_toPrefix (p : FreeSys Δ S) (f g : S → Prefix Δ A)
    (h : ∀ x, Prefix.Extends (f x) (g x)) : Prefix.Extends (p.toPrefix f) (p.toPrefix g) := by
  induction p with
  | pure a => exact h a
  | step op allowed next ih => exact .ask op allowed _ _ ih

theorem PosixMachine.observe_coherent (p : PosixMachine Δ S A) {small large : Nat} (le : small ≤ large) :
    Prefix.Extends (p.observe small) (p.observe large) := by
  suffices h : ∀ s, Prefix.Extends (p.observeFrom small s) (p.observeFrom large s) from h p.init
  induction small generalizing large with
  | zero =>
    intro s
    cases h : p.step s with
    | pure result =>
      cases result <;> cases large <;> simp only [observeFrom,h,FreeSys.toPrefix] <;>
        first | exact .done _ | exact .suspended _
    | step op allowed next => cases large <;> simp only [observeFrom,h] <;> exact .suspended _
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      intro s
      apply FreeSys.extends_toPrefix
      intro result
      cases result with
      | inl state => exact ih (Nat.le_of_succ_le_succ le) state
      | inr a => exact .done a

/-- A typed reply transcript used when expanding a finite observation. -/
structure Answer where
  kind : ResultKind
  value : Ret kind.denote

def Answer.get (a : Answer) (op : SysOp) : Ret op.Result :=
  if h : a.kind = op.kind then cast (congrArg (fun k => Ret (ResultKind.denote k)) h) a.value else .err .EIO

def Prefix.after (p : Prefix Δ A) : List Answer → Prefix Δ A
  | [] => p
  | a :: rest => match p with
    | .ask op _ next => (next (a.get op)).after rest
    | other => other

end LojitaCtx.Posix
