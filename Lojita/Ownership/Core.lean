set_option genCtorIdx false

namespace Lojita.Ownership
universe u

mutual
  inductive St : Type 1 where
    | file (A : Type)
    | dir (entries : List (String × St))
    | chan (session : Session)

  inductive Ty : Type 1 where
    | res (s : St)
    | exRes (I : Type) (family : I → St)
    | dat (A : Type)

  inductive Session : Type 1 where
    | end_
    | ten (t : Ty) (rest : Session)
    | arr (t : Ty) (rest : Session)
    | srvI (Q R I : Type) (family : I → St)
    | workerI (R I : Type) (family : I → St)
end

abbrev Ctx := List (String × St)
abbrev srv (Q R : Type) (s : St) := Session.srvI Q R Unit (fun _ => s)

structure Spec where
  specI ::
  name : String
  Idx : Type
  ctx : Idx → Ctx
  session : Idx → Session
export Spec (specI)

def mkSpec (n : String) (Γ : Ctx) (S : Session) : Spec :=
  ⟨n, Unit, fun _ => Γ, fun _ => S⟩

/-- A selected occurrence. Distinct positions can have the same name. -/
inductive Position {α : Type u} (key : α → String) (n : String) : List α → Type u where
  | here {x : α} {xs : List α} : key x = n → Position key n (x :: xs)
  | there {x : α} {xs : List α} : Position key n xs → Position key n (x :: xs)

namespace Position
variable {α : Type u} {key : α → String} {n : String} {xs : List α}

def value : {xs : List α} → Position key n xs → α
  | x :: _, .here _ => x
  | _ :: _, .there p => p.value
termination_by structural _ p => p

def replace (f : α → α) : {xs : List α} → Position key n xs → List α
  | x :: xs, .here _ => f x :: xs
  | x :: _, .there p => x :: p.replace f
termination_by structural _ p => p

def remove : {xs : List α} → Position key n xs → List α
  | _ :: xs, .here _ => xs
  | x :: _, .there p => x :: p.remove
termination_by structural _ p => p

def find (key : α → String) (n : String) : (xs : List α) → Option (Position key n xs)
  | [] => none
  | x :: xs => if h : key x = n then some (.here h) else (find key n xs).map .there
termination_by structural xs => xs

end Position

abbrev MemCtx := Position (α := String × St) Prod.fst
abbrev MemSpec := Position Spec.name
variable {Γ Δ : Ctx} {Ψ : List Spec} {n m : String} {s t u r : St}
variable {S : Session} {A B Q R I J : Type} {F : I → St} {G : J → Ctx}

def member (n : String) (Γ : Ctx) := (Position.find Prod.fst n Γ).isSome
def lookupSt (n : String) (Γ : Ctx) := ((Position.find Prod.fst n Γ).map (·.value.2)).getD (.dir [])
abbrev stateOf (x : MemCtx n Γ) := x.value.2
abbrev setAt (x : MemCtx n Γ) (s : St) := x.replace (fun e => (e.1, s))
abbrev removeAt (x : MemCtx n Γ) := x.remove

def MemCtx.afterSet {Γ : Ctx} (x : MemCtx n Γ) (s : St) : MemCtx n (setAt x s) :=
  match x with
  | .here h => .here h
  | .there p => .there (MemCtx.afterSet p s)
termination_by structural x

theorem stateOf_afterSet (x : MemCtx n Γ) (s : St) : stateOf (MemCtx.afterSet x s) = s := by
  induction x with
  | here => rfl
  | there _ ih => exact ih

theorem removeAt_afterSet (x : MemCtx n Γ) (s : St) :
    removeAt (MemCtx.afterSet x s) = removeAt x := by
  induction x with
  | here => rfl
  | there _ ih => exact congrArg (_ :: ·) ih

def workCtx (R I : Type) (F : I → St) (names : List String) : Ctx :=
  names.map (fun n => (n, .chan (.workerI R I F)))

def workPos (R I : Type) (F : I → St) {names : List String} (p : Position id n names) :
    MemCtx n (workCtx R I F names) :=
  match p with
  | .here h => .here h
  | .there q => .there (workPos R I F q)
termination_by structural p

theorem stateOf_workPos (R I : Type) (F : I → St) {names : List String} (p : Position id n names) :
    stateOf (workPos R I F p) = .chan (.workerI R I F) := by
  induction p with
  | here => rfl
  | there _ ih => exact ih

theorem removeAt_workPos (R I : Type) (F : I → St) {names : List String} (p : Position id n names) :
    removeAt (workPos R I F p) = workCtx R I F p.remove := by
  induction p with
  | here => rfl
  | there _ ih => exact congrArg (_ :: ·) ih

def DisjointCtx (Γ₁ Γ₂ : Ctx) : Bool :=
  Γ₁.all (fun e => !member e.1 Γ₂)

private theorem find_cons {α : Type u} (key : α → String) (n : String) (x : α) (xs : List α) :
    Position.find key n (x :: xs) =
      (if h : key x = n then some (.here h) else (Position.find key n xs).map .there) := rfl

private theorem member_false_iff (n : String) (Γ : Ctx) :
    member n Γ = false ↔ ∀ e ∈ Γ, e.1 ≠ n := by
  induction Γ with
  | nil => exact ⟨(fun _ _ h => nomatch h), fun _ => rfl⟩
  | cons e Γ ih =>
    by_cases h : e.1 = n
    · simp [member, find_cons, h]
    · simpa [member, find_cons, h] using ih

theorem DisjointCtx.symm {Γ₁ Γ₂ : Ctx} (h : DisjointCtx Γ₁ Γ₂ = true) : DisjointCtx Γ₂ Γ₁ = true := by
  simp only [DisjointCtx, List.all_eq_true, Bool.not_eq_true', member_false_iff] at h ⊢
  exact fun b hb a ha => Ne.symm (h a ha b hb)

inductive SplitCtx : Ctx → Ctx → Ctx → Type 1 where
  | nil : SplitCtx [] [] []
  | left (e : String × St) {Γ Γ₁ Γ₂ : Ctx} :
      member e.1 Γ₂ = false → SplitCtx Γ Γ₁ Γ₂ → SplitCtx (e :: Γ) (e :: Γ₁) Γ₂
  | right (e : String × St) {Γ Γ₁ Γ₂ : Ctx} :
      member e.1 Γ₁ = false → SplitCtx Γ Γ₁ Γ₂ → SplitCtx (e :: Γ) Γ₁ (e :: Γ₂)

def SplitCtx.swap {Γ Γ₁ Γ₂ : Ctx} (sp : SplitCtx Γ Γ₁ Γ₂) : SplitCtx Γ Γ₂ Γ₁ :=
  match sp with
  | .nil => .nil
  | .left e h tail => .right e h tail.swap
  | .right e h tail => .left e h tail.swap
termination_by structural sp

inductive Prefix where
  | root
  | push (entry : String × St) (outer : Prefix)

def plug : Prefix → Ctx → Ctx
  | .root, Γ => Γ
  | .push e p, Γ => plug p (e :: Γ)
termination_by structural p _ => p

def Prefix.position : (p : Prefix) → {Γ : Ctx} → MemCtx n Γ → MemCtx n (plug p Γ)
  | .root, _, x => x
  | .push _ p, _, x => p.position (.there x)
termination_by structural p _ _ => p

def St.isFile : St → Bool | .file _ => true | _ => false

/-- A permutation carries the actual moves so it can reindex dependent storage. -/
inductive Reorder : Ctx → Ctx → Type 1 where
  | refl {Γ : Ctx} : Reorder Γ Γ
  | cons {Γ Δ : Ctx} (e : String × St) : Reorder Γ Δ → Reorder (e :: Γ) (e :: Δ)
  | swap {Γ : Ctx} (a b : String × St) : Reorder (a :: b :: Γ) (b :: a :: Γ)
  | trans {Γ Δ : Ctx} {Θ : Ctx} : Reorder Γ Δ → Reorder Δ Θ → Reorder Γ Θ

private def Reorder.appendNil : (xs : Ctx) → Reorder xs (xs ++ [])
  | [] => .refl
  | x :: xs => .cons x (appendNil xs)
termination_by structural xs => xs

private def Reorder.moveRight (e : String × St) (xs ys : Ctx) :
    Reorder (e :: (xs ++ ys)) (xs ++ (e :: ys)) :=
  match xs with
  | [] => .refl
  | x :: xs => .trans (.swap e x) (.cons x (moveRight e xs ys))
termination_by structural xs

def Reorder.swapAppend (Δ₁ : Ctx) : (Δ₂ : Ctx) → Reorder (Δ₂ ++ Δ₁) (Δ₁ ++ Δ₂)
  | [] => appendNil Δ₁
  | e :: es => .trans (.cons e (swapAppend Δ₁ es)) (moveRight e Δ₁ es)
termination_by structural Δ₂ => Δ₂

inductive Cmd : St → St → Type → Type 1 where
  | read {A : Type} : Cmd (.file A) (.file A) A
  | reorder {Γ Δ : Ctx} : Reorder Γ Δ → Cmd (.dir Γ) (.dir Δ) Unit
  | create {Γ : Ctx} {A : Type} (n : String) : member n Γ = false → A → Cmd (.dir Γ) (.dir ((n, .file A) :: Γ)) Unit
  | unlink {Γ : Ctx} {n : String} (x : MemCtx n Γ) : (stateOf x).isFile → Cmd (.dir Γ) (.dir (removeAt x)) Unit
  | mkdir {Γ : Ctx} (n : String) : member n Γ = false → Cmd (.dir Γ) (.dir ((n, .dir []) :: Γ)) Unit
  | rmdir {Γ : Ctx} {n : String} (x : MemCtx n Γ) : stateOf x = .dir [] → Cmd (.dir Γ) (.dir (removeAt x)) Unit
  | link {Γ : Ctx} {n : String} (x : MemCtx n Γ) : (stateOf x).isFile → (m : String) → member m Γ = false →
      Cmd (.dir Γ) (.dir ((m, stateOf x) :: Γ)) Unit
  | up {Γ Δ : Ctx} {n m : String} (x : MemCtx m Γ) : stateOf x = .dir Δ → (z : MemCtx n Δ) → member n Γ = false →
      Cmd (.dir Γ) (.dir ((n, stateOf z) :: setAt x (.dir (removeAt z)))) Unit
  | down {Γ Δ : Ctx} {n m : String} (z : MemCtx n Γ) (x : MemCtx m (removeAt z)) : stateOf x = .dir Δ → member n Δ = false →
      Cmd (.dir Γ) (.dir (setAt x (.dir ((n, stateOf z) :: Δ)))) Unit
  | recv {Γ : Ctx} {m : String} {r : St} {S : Session} (c : MemCtx m Γ) : stateOf c = .chan (.ten (.res r) S) → (n : String) → member n Γ = false →
      Cmd (.dir Γ) (.dir ((n, r) :: setAt c (.chan S))) Unit
  | recvD {Γ : Ctx} {m : String} {S : Session} {A : Type} (c : MemCtx m Γ) : stateOf c = .chan (.ten (.dat A) S) → Cmd (.dir Γ) (.dir (setAt c (.chan S))) A
  | send {Γ : Ctx} {n m : String} {S : Session} (z : MemCtx n Γ) (c : MemCtx m (removeAt z)) : stateOf c = .chan (.arr (.res (stateOf z)) S) →
      Cmd (.dir Γ) (.dir (setAt c (.chan S))) Unit
  | sendD {Γ : Ctx} {m : String} {S : Session} {A : Type} (c : MemCtx m Γ) : stateOf c = .chan (.arr (.dat A) S) → A → Cmd (.dir Γ) (.dir (setAt c (.chan S))) Unit
  | close {Γ : Ctx} {m : String} (c : MemCtx m Γ) : stateOf c = .chan .end_ → Cmd (.dir Γ) (.dir (removeAt c)) Unit
  | recover {Γ : Ctx} {m : String} {r : St} (c : MemCtx m Γ) : stateOf c = .chan (.ten (.res r) .end_) → Cmd (.dir Γ) (.dir (setAt c r)) Unit
  | call {Γ : Ctx} {n : String} {Q R I : Type} {F : I → St} (c : MemCtx n Γ) : stateOf c = .chan (.srvI Q R I F) → Q →
      Cmd (.dir Γ) (.dir (setAt c (.chan (.srvI Q R I F)))) R
  | stop {Γ : Ctx} {n : String} {s : St} {Q R : Type} (c : MemCtx n Γ) : stateOf c = .chan (srv Q R s) → Cmd (.dir Γ) (.dir (setAt c s)) Unit

inductive Prog (Ψ : List Spec) : St → St → Type → Type 1 where
  | done {s : St} {A : Type} : A → Prog Ψ s s A
  | step {s t u : St} {A B : Type} : Cmd s t A → (A → Prog Ψ t u B) → Prog Ψ s u B
  | focus {Γ : Ctx} {n : String} {t u : St} {A B : Type} (x : MemCtx n Γ) : Prog Ψ (stateOf x) t A → (A → Prog Ψ (.dir (setAt x t)) u B) → Prog Ψ (.dir Γ) u B
  | exec {Γ : Ctx} {n m : String} {u : St} {A : Type} (x : MemCtx n Γ) (h : MemSpec m Ψ) (i : h.value.Idx) : stateOf x = .dir (h.value.ctx i) →
      Prog Ψ (.dir (setAt x (.chan (h.value.session i)))) u A → Prog Ψ (.dir Γ) u A
  | stopI {Γ : Ctx} {n : String} {u : St} {A Q R I : Type} {F : I → St} (c : MemCtx n Γ) : stateOf c = .chan (.srvI Q R I F) →
      ((i : I) → Prog Ψ (.dir (setAt c (F i))) u A) → Prog Ψ (.dir Γ) u A
  | par {Γ Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {u : St} {A B C : Type} :
      SplitCtx Γ Γ₁ Γ₂ → DisjointCtx Δ₁ Δ₂ = true →
      Prog Ψ (.dir Γ₁) (.dir Δ₁) A → Prog Ψ (.dir Γ₂) (.dir Δ₂) B →
      (A → B → Prog Ψ (.dir (Δ₁ ++ Δ₂)) u C) → Prog Ψ (.dir Γ) u C
  | awaitI {Γ : Ctx} {n : String} {u : St} {A R I : Type} {F : I → St} (c : MemCtx n Γ) :
      stateOf c = .chan (.workerI R I F) →
      (Option R → (i : I) → Prog Ψ (.dir (setAt c (F i))) u A) → Prog Ψ (.dir Γ) u A
  | abortI {Γ : Ctx} {n : String} {u : St} {A R I : Type} {F : I → St} (c : MemCtx n Γ) :
      stateOf c = .chan (.workerI R I F) →
      ((i : I) → Prog Ψ (.dir (setAt c (F i))) u A) → Prog Ψ (.dir Γ) u A

def Prog.bind {s t u : St} {A B : Type} (p : Prog Ψ s t A) (f : A → Prog Ψ t u B) : Prog Ψ s u B :=
  match p with
  | .done a => f a
  | .step c k => .step c (fun a => (k a).bind f)
  | .focus x child k => .focus x child (fun a => (k a).bind f)
  | .exec x h i e k => .exec x h i e (k.bind f)
  | .stopI c e k => .stopI c e (fun i => (k i).bind f)
  | .par sp dj p₁ p₂ k => .par sp dj p₁ p₂ (fun a b => (k a b).bind f)
  | .awaitI c e k => .awaitI c e (fun r i => (k r i).bind f)
  | .abortI c e k => .abortI c e (fun i => (k i).bind f)
termination_by structural p

instance : Monad (Prog Ψ s s) where
  pure := .done
  bind := Prog.bind

abbrev Turn (Q R J : Type) (G : J → Ctx) :=
  Session.arr (.dat Q) (.ten (.dat R) (.ten (.exRes J (fun j => .dir (G j))) .end_))
abbrev Halt (I : Type) (F : I → St) := Session.ten (.exRes I F) .end_
abbrev WorkerTurn (R J : Type) (G : J → Ctx) :=
  Session.ten (.dat (Option R)) (.ten (.exRes J (fun j => .dir (G j))) .end_)

inductive Proc (Ψ : List Spec) : Ctx → Session → Type 1 where
  | run {Γ Δ : Ctx} {S : Session} {A : Type} : Prog Ψ (.dir Γ) (.dir Δ) A → (A → Proc Ψ Δ S) → Proc Ψ Γ S
  | end_  : Proc Ψ [] .end_
  | giveAt {Γ : Ctx} {n : String} {S : Session} (x : MemCtx n Γ) : Proc Ψ (removeAt x) S → Proc Ψ Γ (.ten (.res (stateOf x)) S)
  | tell {Γ : Ctx} {S : Session} {A : Type} : A → Proc Ψ Γ S → Proc Ψ Γ (.ten (.dat A) S)
  | takeAt {Γ : Ctx} {r : St} {S : Session} (n : String) : member n Γ = false → Proc Ψ ((n, r) :: Γ) S → Proc Ψ Γ (.arr (.res r) S)
  | ask {Γ : Ctx} {S : Session} {A : Type} : (A → Proc Ψ Γ S) → Proc Ψ Γ (.arr (.dat A) S)
  | giveExAt {Γ : Ctx} {n : String} {S : Session} {I : Type} {F : I → St} (i : I) (x : MemCtx n Γ) : stateOf x = F i → Proc Ψ (removeAt x) S → Proc Ψ Γ (.ten (.exRes I F) S)
  | machine {Q R I J : Type} {F : I → St} {G : J → Ctx} (onCall : (j : J) → Proc Ψ (G j) (Turn Q R J G))
      (onStop : (j : J) → Proc Ψ (G j) (Halt I F)) (init : J) : Proc Ψ (G init) (.srvI Q R I F)
  | giveExDir {Γ : Ctx} {I : Type} {F : I → St} (i : I) : St.dir Γ = F i → Proc Ψ Γ (Halt I F)
  | stopP {Γ : Ctx} {n : String} {S : Session} {Q R I : Type} {F : I → St} (c : MemCtx n Γ) : stateOf c = .chan (.srvI Q R I F) →
      ((i : I) → Proc Ψ (setAt c (F i)) S) → Proc Ψ Γ S
  | worker {R I J : Type} {F : I → St} {G : J → Ctx}
      (onStep : (j : J) → Proc Ψ (G j) (WorkerTurn R J G))
      (onHalt : (j : J) → Proc Ψ (G j) (Halt I F))
      (init : J) : Proc Ψ (G init) (.workerI R I F)
  | abortP {Γ : Ctx} {n : String} {S : Session} {R I : Type} {F : I → St} (c : MemCtx n Γ) :
      stateOf c = .chan (.workerI R I F) →
      ((i : I) → Proc Ψ (setAt c (F i)) S) → Proc Ψ Γ S
  | awaitAnyP {R I : Type} {F : I → St} {S : Session} (names : List String) (hne : names ≠ [])
      (onDone : (n : String) → (p : Position id n names) → R → (i : I) →
        Proc Ψ (setAt (workPos R I F p) (F i)) S)
      (onPending : Proc Ψ (workCtx R I F names) S) : Proc Ψ (workCtx R I F names) S

def named (n : String) (Γ : Ctx) (h : member n Γ := by decide) : MemCtx n Γ :=
  (Position.find Prod.fst n Γ).get h

def namedSpec (m : String) (Ψ : List Spec) (h : (Position.find Spec.name m Ψ).isSome := by decide) : MemSpec m Ψ :=
  (Position.find Spec.name m Ψ).get h

def read : Prog Ψ (.file A) (.file A) A := .step .read .done
def create (n : String) (a : A) (h : member n Γ = false := by decide) :
    Prog Ψ (.dir Γ) (.dir ((n, .file A) :: Γ)) Unit := .step (.create n h a) .done
def mkdir (n : String) (h : member n Γ = false := by decide) :
    Prog Ψ (.dir Γ) (.dir ((n, .dir []) :: Γ)) Unit := .step (.mkdir n h) .done
def unlink (n : String) (h : member n Γ := by decide) (file : (stateOf (named n Γ h)).isFile := by decide) :=
  Prog.step (Ψ := Ψ) (.unlink (named n Γ h) file) .done
def rmdir (n : String) (h : member n Γ := by decide) (empty : stateOf (named n Γ h) = .dir [] := by rfl) :=
  Prog.step (Ψ := Ψ) (.rmdir (named n Γ h) empty) .done
def inside {source : St} (n : String) (p : Prog Ψ source s A) (h : member n Γ := by decide)
    (e : stateOf (named n Γ h) = source := by rfl) :=
  Prog.focus (named n Γ h) (e.symm ▸ p) .done
def openAs (n m : String) (hw : member n Γ := by decide) (hs : (Position.find Spec.name m Ψ).isSome := by decide)
    (i : (namedSpec m Ψ hs).value.Idx)
    (e : stateOf (named n Γ hw) = .dir ((namedSpec m Ψ hs).value.ctx i) := by rfl) :=
  Prog.exec (named n Γ hw) (namedSpec m Ψ hs) i e (.done ())
def call (n : String) (q : Q) (h : member n Γ := by decide)
    (e : stateOf (named n Γ h) = .chan (.srvI Q R I F) := by rfl) :=
  Prog.step (Ψ := Ψ) (.call (named n Γ h) e q) .done
def stop (n : String) (h : member n Γ := by decide) (e : stateOf (named n Γ h) = .chan (srv Q R s) := by rfl) :=
  Prog.step (Ψ := Ψ) (.stop (named n Γ h) e) .done
def give (n : String) (h : member n Γ := by decide) (p : Proc Ψ (removeAt (named n Γ h)) S) :=
  Proc.giveAt (named n Γ h) p
def take (n : String) (p : Proc Ψ ((n, r) :: Γ) S) (h : member n Γ = false := by decide) := Proc.takeAt n h p

def withEphemeral (n : String) (p : Prog Ψ (.dir []) (.dir []) A) (fresh : member n Γ = false := by decide) :
    Prog Ψ (.dir Γ) (.dir Γ) A :=
  .step (.mkdir n fresh) fun _ => .focus (.here rfl) p fun a => .step (.rmdir (.here rfl) rfl) fun _ => .done a

structure Running (Q R : Type) (M : Type u) : Type (max 1 u) where
  State : Type
  init : State
  step : State → Q → R × State
  finish : State → M

def Running.call {M : Type u} (r : Running Q R M) (q : Q) : R × Running Q R M :=
  let (a, s) := r.step r.init q
  (a, { r with init := s })

def Running.stop {M : Type u} (r : Running Q R M) := r.finish r.init

structure Worker (R : Type) (M : Type u) : Type (max 1 u) where
  State : Type
  init : State
  step : State → Option R × State
  finish : State → M

def Worker.stepOne {M : Type u} (w : Worker R M) : Option R × Worker R M :=
  let (r, s) := w.step w.init
  (r, { w with init := s })

def Worker.abort {M : Type u} (w : Worker R M) : M := w.finish w.init

def observeN {M : Type u} : Nat → Running Unit (Option A) M → Option A × Running Unit (Option A) M
  | 0, r => (none, r)
  | n+1, r => match r.call () with
    | (some a, next) => (some a, next)
    | (none, next) => observeN n next
termination_by structural n _ => n

def pollN {M : Type u} (n : Nat) (r : Running Unit (Option A) M) := (observeN n r).1

/-- A server's public carrier quantifies over small types and hence lives in
    the next universe. For storage inside another machine, finite observations
    give a small presentation. File data stays in its native type. -/
structure Presentation where
  Value : Type 1
  Stored : Type
  store : Value → Stored
  load : Stored → Value

namespace Presentation

def data (A : Type) : Presentation := ⟨ULift A, A, ULift.down, ULift.up⟩
def pair (a b : Presentation) : Presentation :=
  ⟨a.Value × b.Value, a.Stored × b.Stored, Prod.map a.store b.store, Prod.map a.load b.load⟩
def arrow (a b : Presentation) : Presentation :=
  ⟨a.Value → b.Value, a.Stored → b.Stored,
   fun f x => b.store (f (a.load x)), fun f x => b.load (f (a.store x))⟩
def existsRes (I : Type) (f : I → Presentation) : Presentation :=
  ⟨(i : I) × (f i).Value, (i : I) × (f i).Stored,
   fun x => ⟨x.1, (f x.1).store x.2⟩, fun x => ⟨x.1, (f x.1).load x.2⟩⟩

/-- Histories are kept in reverse order when extending an observed server. -/
def server (Q R : Type) (m : Presentation) : Presentation where
  Value := Running Q R m.Value
  Stored := (List Q → Q → R) × (List Q → m.Stored)
  store r :=
    let replay := fun (qs : List Q) => qs.foldr (fun q s => (r.step s q).2) r.init
    (fun qs q => (r.step (replay qs) q).1, fun qs => m.store (r.finish (replay qs)))
  load obs := ⟨List Q, [], fun qs q => (obs.1 qs q, q :: qs), fun qs => m.load (obs.2 qs)⟩

def worker (R : Type) (m : Presentation) : Presentation where
  Value := Worker R m.Value
  Stored := (Nat → Option R) × (Nat → m.Stored)
  store w :=
    let replay := fun n => Nat.repeat (fun s => (w.step s).2) n w.init
    (fun n => (w.step (replay n)).1, fun n => m.store (w.finish (replay n)))
  load obs := ⟨Nat, 0, fun n => (obs.1 n, n + 1), fun n => m.load (obs.2 n)⟩

end Presentation

mutual
  def stateType : St → Presentation
    | .file A => .data A
    | .dir es => contextType es
    | .chan S => offerType S
  termination_by structural s => s

  def contextType : Ctx → Presentation
    | [] => .data Unit
    | e :: es => .pair (entryType e) (contextType es)
  termination_by structural es => es

  def entryType : String × St → Presentation
    | (_, s) => stateType s
  termination_by structural e => e

  def msgType : Ty → Presentation
    | .dat A => .data A
    | .res s => stateType s
    | .exRes I F => .existsRes I (fun i => stateType (F i))
  termination_by structural t => t

  def offerType : Session → Presentation
    | .end_ => .data Unit
    | .ten t S => .pair (msgType t) (offerType S)
    | .arr t S => .arrow (msgType t) (offerType S)
    | .srvI Q R I F => .server Q R (.existsRes I (fun i => stateType (F i)))
    | .workerI R I F => .worker R (.existsRes I (fun i => stateType (F i)))
  termination_by structural S => S
end

abbrev Model (s : St) := (stateType s).Value
abbrev Models (Γ : Ctx) := (contextType Γ).Value
abbrev Msg (t : Ty) := (msgType t).Value
abbrev Offer (S : Session) := (offerType S).Value

abbrev Env (Ψ : List Spec) := {m : String} → (h : MemSpec m Ψ) →
  (i : h.value.Idx) → Models (h.value.ctx i) → Offer (h.value.session i)

def Env.nil : Env [] := fun h => nomatch h
def Env.cons {spec : Spec} (f : (i : spec.Idx) → Models (spec.ctx i) → Offer (spec.session i))
    (env : Env Ψ) : Env (spec :: Ψ)
  | _, .here _ => f
  | _, .there h => env h

def getAt : {Γ : Ctx} → (x : MemCtx n Γ) → Models Γ → Model (stateOf x)
  | (_, _) :: _, .here _, ms => ms.1
  | (_, _) :: _, .there p, ms => getAt p ms.2
termination_by structural _ x _ => x

def putAt {s : St} : {Γ : Ctx} → (x : MemCtx n Γ) → Models Γ → Model s → Models (setAt x s)
  | (_, _) :: _, .here _, ms, v => (v, ms.2)
  | (_, _) :: _, .there p, ms, v => (ms.1, putAt p ms.2 v)
termination_by structural _ x _ _ => x

def delAt : {Γ : Ctx} → (x : MemCtx n Γ) → Models Γ → Models (removeAt x)
  | (_, _) :: _, .here _, ms => ms.2
  | (_, _) :: _, .there p, ms => (ms.1, delAt p ms.2)
termination_by structural _ x _ => x

def splitModels {Γ Γ₁ Γ₂ : Ctx} (sp : SplitCtx Γ Γ₁ Γ₂) : Models Γ → Models Γ₁ × Models Γ₂ :=
  match sp with
  | .nil => fun ms => (ms, ms)
  | .left _ _ tail => fun ms =>
    let (l, r) := splitModels tail ms.2
    ((ms.1, l), r)
  | .right _ _ tail => fun ms =>
    let (l, r) := splitModels tail ms.2
    (l, (ms.1, r))
termination_by structural sp

def joinModels (Δ₁ Δ₂ : Ctx) : Models Δ₁ → Models Δ₂ → Models (Δ₁ ++ Δ₂) :=
  match Δ₁ with
  | [] => fun _ r => r
  | _ :: xs => fun l r => (l.1, joinModels xs Δ₂ l.2 r)
termination_by structural Δ₁

private theorem splitModels_swap {Γ₁ Γ₂ : Ctx} (sp : SplitCtx Γ Γ₁ Γ₂) (ms : Models Γ) :
    splitModels sp.swap ms = (splitModels sp ms).swap := by
  induction sp with
  | nil => rfl
  | left _ _ sp ih =>
    exact congrArg (fun lr => (lr.1, (ms.1, lr.2))) (ih ms.2)
  | right _ _ sp ih =>
    exact congrArg (fun lr => ((ms.1, lr.1), lr.2)) (ih ms.2)

def permute {Γ Δ : Ctx} (p : Reorder Γ Δ) : Models Γ → Models Δ :=
  match p with
  | .refl => id
  | .cons _ q => fun ms => (ms.1, permute q ms.2)
  | .swap _ _ => fun ms => (ms.2.1, ms.1, ms.2.2)
  | .trans q r => fun ms => permute r (permute q ms)
termination_by structural p

private theorem permute_appendNil (xs : Ctx) (l : Models xs) (r : Models []) :
    permute (Reorder.appendNil xs) l = joinModels xs [] l r := by
  induction xs with
  | nil => exact Subsingleton.elim (α := ULift Unit) l r
  | cons e xs ih => exact congrArg (l.1, ·) (ih l.2)

private theorem permute_moveRight (e : String × St) (xs ys : Ctx) (v : (entryType e).Value)
    (l : Models xs) (r : Models ys) :
    permute (Reorder.moveRight e xs ys) (v, joinModels xs ys l r) =
      joinModels xs (e :: ys) l (v, r) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (l.1, ·) (ih l.2)

private theorem permute_swapAppend (xs ys : Ctx) (l : Models xs) (r : Models ys) :
    permute (Reorder.swapAppend xs ys) (joinModels ys xs r l) = joinModels xs ys l r := by
  induction ys with
  | nil => exact permute_appendNil xs l r
  | cons y ys ih =>
    change permute (Reorder.moveRight y xs ys)
      (r.1, permute (Reorder.swapAppend xs ys) (joinModels ys xs r.2 l)) = _
    exact (congrArg (fun tail => permute (Reorder.moveRight y xs ys) (r.1, tail)) (ih r.2)).trans
      (permute_moveRight y xs ys r.1 l r.2)

def asModel {s t : St} (h : s = t) (v : Model s) : Model t := h ▸ v

def evalCmd : {s t : St} → {A : Type} → Cmd s t A → Model s → Model t × A
  | _, _, _, .read, m => (m, m.down)
  | _, _, _, .reorder p, m => (permute p m, ())
  | _, _, _, .create _ _ a, m => ((⟨a⟩, m), ())
  | _, _, _, .mkdir _ _, m => ((⟨()⟩, m), ())
  | _, _, _, .unlink x _, m => (delAt x m, ())
  | _, _, _, .rmdir x _, m => (delAt x m, ())
  | _, _, _, .link x _ _ _, m => ((getAt x m, m), ())
  | _, _, _, .up x e z _, m =>
    let d := asModel e (getAt x m)
    ((getAt z d, putAt x m (delAt z d)), ())
  | _, _, _, .down z x e _, m =>
    let rest := delAt z m
    (putAt x rest (getAt z m, asModel e (getAt x rest)), ())
  | _, _, _, .recv c e _ _, m =>
    let v := asModel e (getAt c m)
    ((v.1, putAt c m v.2), ())
  | _, _, _, .recvD c e, m =>
    let v := asModel e (getAt c m)
    (putAt c m v.2, v.1.down)
  | _, _, _, .send z c e, m =>
    let rest := delAt z m
    (putAt c rest (asModel e (getAt c rest) (getAt z m)), ())
  | _, _, _, .sendD c e a, m => (putAt c m (asModel e (getAt c m) ⟨a⟩), ())
  | _, _, _, .close x _, m => (delAt x m, ())
  | _, _, _, .recover x e, m => (putAt x m (asModel e (getAt x m)).1, ())
  | _, _, _, .call x e q, m =>
    let (a, next) := Running.call (asModel e (getAt x m)) q
    (putAt x m next, a)
  | _, _, _, .stop x e, m => (putAt x m (Running.stop (asModel e (getAt x m))).2, ())

def evalProg (env : Env Ψ) {s t : St} {A : Type} (p : Prog Ψ s t A) : Model s → Model t × A :=
  match p with
  | .done a => fun m => (m, a)
  | .step c k => fun m =>
    let (v, a) := evalCmd c m
    evalProg env (k a) v
  | .focus x child k => fun m =>
    let (v, a) := evalProg env child (getAt x m)
    evalProg env (k a) (putAt x m v)
  | .exec x h i e k => fun m => evalProg env k (putAt x m (env h i (asModel e (getAt x m))))
  | .stopI x e k => fun m =>
    let v := Running.stop (asModel e (getAt x m))
    evalProg env (k v.1) (putAt x m v.2)
  | .par sp _ p₁ p₂ k => fun m =>
    let (m₁, m₂) := splitModels sp m
    let (l, a) := evalProg env p₁ m₁
    let (r, b) := evalProg env p₂ m₂
    evalProg env (k a b) (joinModels _ _ l r)
  | .awaitI c e k => fun m =>
    let (opt, next) := Worker.stepOne (asModel e (getAt c m))
    let v := next.abort
    evalProg env (k opt v.1) (putAt c m v.2)
  | .abortI c e k => fun m =>
    let v := Worker.abort (asModel e (getAt c m))
    evalProg env (k v.1) (putAt c m v.2)
termination_by structural p

private theorem eval_par {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {C : Type} (env : Env Ψ) (sp : SplitCtx Γ Γ₁ Γ₂)
    (dj : DisjointCtx Δ₁ Δ₂ = true)
    (p₁ : Prog Ψ (.dir Γ₁) (.dir Δ₁) A) (p₂ : Prog Ψ (.dir Γ₂) (.dir Δ₂) B)
    (k : A → B → Prog Ψ (.dir (Δ₁ ++ Δ₂)) u C) (m : Models Γ) :
    evalProg env (.par sp dj p₁ p₂ k) m =
      let (l, a) := evalProg env p₁ (splitModels sp m).1
      let (r, b) := evalProg env p₂ (splitModels sp m).2
      evalProg env (k a b) (joinModels Δ₁ Δ₂ l r) := rfl

private theorem eval_reorder {u : St} (env : Env Ψ) (p : Reorder Γ Δ)
    (k : Unit → Prog Ψ (.dir Δ) u A) (m : Models Γ) :
    evalProg env (.step (.reorder p) k) m = evalProg env (k ()) (permute p m) := rfl

theorem evalProg_par_swap {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {C : Type} (env : Env Ψ) (sp : SplitCtx Γ Γ₁ Γ₂)
    (dj₁₂ : DisjointCtx Δ₁ Δ₂ = true) (dj₂₁ : DisjointCtx Δ₂ Δ₁ = true)
    (p₁ : Prog Ψ (.dir Γ₁) (.dir Δ₁) A) (p₂ : Prog Ψ (.dir Γ₂) (.dir Δ₂) B)
    (k : A → B → Prog Ψ (.dir (Δ₁ ++ Δ₂)) u C) (m : Models Γ) :
    evalProg env (.par sp dj₁₂ p₁ p₂ k) m =
      evalProg env (.par sp.swap dj₂₁ p₂ p₁ (fun b a =>
        .step (.reorder (Reorder.swapAppend Δ₁ Δ₂)) (fun _ => k a b))) m := by
  simp only [eval_par, eval_reorder, splitModels_swap, Prod.swap]
  exact congrArg (evalProg env _) (permute_swapAppend Δ₁ Δ₂ _ _).symm

/-- The initial directory is captured by the transitions. Subsequent states
    store exactly the new directory and index returned by the previous turn. -/
def machineRunning
    (turn : (j : J) → Models (G j) → Q → R × ((i : J) × Models (G i)))
    (halt : (j : J) → Models (G j) → (i : I) × Model (F i))
    (j : J) (m : Models (G j)) : Running Q R ((i : I) × Model (F i)) :=
  let unpack : Option ((i : J) × (contextType (G i)).Stored) → (i : J) × Models (G i)
    | none => ⟨j, m⟩
    | some ⟨i, v⟩ => ⟨i, (contextType (G i)).load v⟩
  { State := Option ((i : J) × (contextType (G i)).Stored)
    init := none
    step := fun s q =>
      let ⟨i, v⟩ := unpack s
      let (a, ⟨k, w⟩) := turn i v q
      (a, some ⟨k, (contextType (G k)).store w⟩)
    finish := fun s => let ⟨i, v⟩ := unpack s; halt i v }

def workerRunning
    (turn : (j : J) → Models (G j) → Option R × ((i : J) × Models (G i)))
    (halt : (j : J) → Models (G j) → (i : I) × Model (F i))
    (j : J) (m : Models (G j)) : Worker R ((i : I) × Model (F i)) :=
  let run := machineRunning (fun i v (_ : Unit) => turn i v) halt j m
  ⟨run.State, run.init, fun s => run.step s (), run.finish⟩

/-- A ready slot carries its original position. Advanced siblings are committed
    together only when the whole directory is pending. -/
private abbrev WorkerStep (R I : Type) (F : I → St) (names : List String) :=
  Sum ((n : String) × Position id n names × R × ((i : I) × Model (F i))) (Models (workCtx R I F names))

private def stepWorkers (R I : Type) (F : I → St) :
    (names : List String) → Models (workCtx R I F names) → WorkerStep R I F names
  | [], ms => .inr ms
  | n :: ns, ms =>
    let (opt, next) := Worker.stepOne ms.1
    match opt with
    | some r => .inl ⟨n, .here rfl, r, next.abort⟩
    | none =>
      match stepWorkers R I F ns ms.2 with
      | .inl ⟨name, p, r, v⟩ => .inl ⟨name, .there p, r, v⟩
      | .inr tail => .inr (next, tail)
termination_by structural names _ => names

def evalProc (env : Env Ψ) {Γ : Ctx} {S : Session} (p : Proc Ψ Γ S) (m : Models Γ) : Offer S :=
  match p with
  | .run p k =>
    let (v, a) := evalProg env p m
    evalProc env (k a) v
  | .end_ => ⟨()⟩
  | .giveAt x k => (getAt x m, evalProc env k (delAt x m))
  | .tell a k => (⟨a⟩, evalProc env k m)
  | .takeAt _ _ k => fun v => evalProc env k (v, m)
  | .ask k => fun a => evalProc env (k a.down) m
  | .giveExAt i x e k => (⟨i, asModel e (getAt x m)⟩, evalProc env k (delAt x m))
  | @Proc.machine _ _ _ _ _ _ family turn halt j =>
    machineRunning (fun i v q =>
        let answer := evalProc env (turn i) v ⟨q⟩
        (answer.1.down, answer.2.1))
      (fun i v => (evalProc env (halt i) v).1) j m
  | .giveExDir i e => (⟨i, asModel e m⟩, ⟨()⟩)
  | .stopP x e k =>
    let v := Running.stop (asModel e (getAt x m))
    evalProc env (k v.1) (putAt x m v.2)
  | @Proc.worker _ _ _ _ _ family turn halt j =>
    workerRunning (fun i v =>
        let answer := evalProc env (turn i) v
        (answer.1.down, answer.2.1))
      (fun i v => (evalProc env (halt i) v).1) j m
  | .abortP x e k =>
    let v := Worker.abort (asModel e (getAt x m))
    evalProc env (k v.1) (putAt x m v.2)
  | @Proc.awaitAnyP _ R I F _ names _ done pending =>
    match stepWorkers R I F names m with
    | .inl ⟨n, pos, r, i, v⟩ => evalProc env (done n pos r i) (putAt (workPos R I F pos) m v)
    | .inr advanced => evalProc env pending advanced
termination_by structural p

/-- Opening an island, receiving its value and closing it cuts to the client
    continuation with the original directory frame. -/
abbrev dataEnv (n : String) (a : A) : Env [mkSpec n [] (.ten (.dat A) .end_)] :=
  Env.cons (fun _ => evalProc Env.nil (.tell a .end_)) Env.nil

def dataCut (_a : A) (k : A → Prog [mkSpec n [] (.ten (.dat A) .end_)] (.dir Γ) t B) :
    Prog [mkSpec n [] (.ten (.dat A) .end_)] (.dir ((n, .dir []) :: Γ)) t B :=
  .exec (.here rfl) (.here rfl) () rfl <|
    .step (.recvD (.here rfl) rfl) fun v => .step (.close (.here rfl) rfl) fun _ => k v

theorem link_data (a : A) (k : A → Prog [mkSpec n [] (.ten (.dat A) .end_)] (.dir Γ) t B)
    (ms : Models ((n, .dir []) :: Γ)) :
    evalProg (dataEnv n a) (dataCut a k) ms = evalProg (dataEnv n a) (k a) ms.2 := rfl

abbrev echoSession (r : St) := Session.arr (.res r) (.ten (.res r) .end_)
def echo (r : St) : Proc [] [] (echoSession r) := .takeAt "x" rfl (.giveAt (.here rfl) .end_)
abbrev echoEnv (n : String) (r : St) : Env [mkSpec n [] (echoSession r)] :=
  Env.cons (fun _ => evalProc Env.nil (echo r)) Env.nil

def resCut (fresh : member m ((n, .chan (.ten (.res r) .end_)) :: Γ) = false)
    (k : Prog [mkSpec n [] (echoSession r)] (.dir ((m, r) :: Γ)) t B) :
    Prog [mkSpec n [] (echoSession r)] (.dir ((m, r) :: (n, .dir []) :: Γ)) t B :=
  .exec (.there (.here rfl)) (.here rfl) () rfl <|
    .step (.send (Γ := (m, r) :: (n, .chan (echoSession r)) :: Γ) (S := .ten (.res r) .end_) (.here rfl) (.here rfl) rfl) fun _ =>
    .step (.recv (r := r) (S := .end_) (.here rfl) rfl m fresh) fun _ =>
    .step (.close (.there (.here rfl)) rfl) fun _ => k

theorem link_res (fresh : member m ((n, .chan (.ten (.res r) .end_)) :: Γ) = false)
    (k : Prog [mkSpec n [] (echoSession r)] (.dir ((m, r) :: Γ)) t B)
    (ms : Models ((m, r) :: (n, .dir []) :: Γ)) :
    evalProg (echoEnv n r) (resCut fresh k) ms = evalProg (echoEnv n r) k (ms.1, ms.2.2) := rfl

abbrev machineEnv (n : String) (p : Proc [] Δ (.srvI Q R I F)) :
    Env [mkSpec n Δ (.srvI Q R I F)] := Env.cons (fun _ => evalProc Env.nil p) Env.nil

def callCut (q : Q)
    (k : R → Prog [mkSpec n Δ (.srvI Q R I F)] (.dir ((n, .chan (.srvI Q R I F)) :: Γ)) t B) :
    Prog [mkSpec n Δ (.srvI Q R I F)] (.dir ((n, .dir Δ) :: Γ)) t B :=
  .exec (.here rfl) (.here rfl) () rfl (.step (.call (.here rfl) rfl q) k)

theorem link_call (p : Proc [] Δ (.srvI Q R I F)) (q : Q)
    (k : R → Prog [mkSpec n Δ (.srvI Q R I F)] (.dir ((n, .chan (.srvI Q R I F)) :: Γ)) t B)
    (ms : Models ((n, .dir Δ) :: Γ)) :
    evalProg (machineEnv n p) (callCut q k) ms =
      let (a, next) := Running.call (evalProc Env.nil p ms.1) q
      evalProg (machineEnv n p) (k a) (next, ms.2) := rfl

def stopCut (k : (i : I) → Prog [mkSpec n Δ (.srvI Q R I F)] (.dir ((n, F i) :: Γ)) t B) :
    Prog [mkSpec n Δ (.srvI Q R I F)] (.dir ((n, .dir Δ) :: Γ)) t B :=
  .exec (.here rfl) (.here rfl) () rfl (.stopI (.here rfl) rfl k)

theorem link_stop (p : Proc [] Δ (.srvI Q R I F))
    (k : (i : I) → Prog [mkSpec n Δ (.srvI Q R I F)] (.dir ((n, F i) :: Γ)) t B)
    (ms : Models ((n, .dir Δ) :: Γ)) :
    evalProg (machineEnv n p) (stopCut k) ms =
      let v := Running.stop (evalProc Env.nil p ms.1)
      evalProg (machineEnv n p) (k v.1) (v.2, ms.2) := rfl
end Lojita.Ownership
