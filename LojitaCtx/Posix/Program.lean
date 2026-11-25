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

/-- All finite observations of a potentially unbounded program. No existential state
    universe or unrestricted effect is needed. -/
structure PosixProg (Δ : List Cap) (A : Type) where
  observe : Nat → Prefix Δ A

variable {Δ : List Cap} {A B S : Type}

def Prefix.bind (p : Prefix Δ A) (f : A → Prefix Δ B) : Prefix Δ B :=
  match p with
  | .done a => f a
  | .suspended => .suspended
  | .ask op h next => .ask op h fun r => (next r).bind f

instance : Monad (PosixProg Δ) where
  pure a := ⟨fun _ => .done a⟩
  bind m f := ⟨fun n => (m.observe n).bind fun a => (f a).observe n⟩

def PosixProg.call (op : SysOp) (h : op.cap ∈ Δ) : PosixProg Δ (Ret op.Result) :=
  ⟨fun _ => .ask op h .done⟩

def PosixProg.unfoldPrefix (step : S → Request Δ A S) (n : Nat) (state : S) : Prefix Δ A :=
  match step state with
  | .done a => .done a
  | .ask op h next =>
    match n with
    | 0 => .suspended
    | k+1 => .ask op h fun r => unfoldPrefix step k (next r)
termination_by structural n

def PosixProg.unfold (initial : S) (step : S → Request Δ A S) : PosixProg Δ A :=
  ⟨fun n => unfoldPrefix step n initial⟩

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
