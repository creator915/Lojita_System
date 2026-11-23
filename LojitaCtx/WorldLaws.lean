import LojitaCtx.ToolLaws
import LojitaCtx.HttpLaws

namespace LojitaCtx.WorldLaws

open LojitaCtx.Terminal

open World

theorem bindPureLeft {Δ : List Cap} {A B : Type} (a : A) (k : A → WorldProg Δ B) :
    worldBind (.pure a) k = k a :=
  rfl

theorem bindPureLeftRun {Δ : List Cap} {A B : Type} (a : A) (k : A → WorldProg Δ B) (w : SimWorld) :
    runWorldPure (worldBind (.pure a) k) w = runWorldPure (k a) w :=
  rfl

theorem bindPureRightRun {Δ : List Cap} {A : Type} :
    (m : WorldProg Δ A) → (w : SimWorld) → runWorldPure (worldBind m .pure) w = runWorldPure m w
  | .pure _, _ => rfl
  | .step _ op k, w =>
    let rw := stepWorldPure op w
    bindPureRightRun (k rw.1) rw.2
termination_by structural x _ => x

theorem runWorldPureBind {Δ : List Cap} {A B : Type} :
    (m : WorldProg Δ A) →
      (k : A → WorldProg Δ B) →
        (w : SimWorld) →
          runWorldPure (worldBind m k) w =
            let r := runWorldPure m w;
            runWorldPure (k r.1) r.2
  | .pure _, _, _ => rfl
  | .step _ op f, k, w =>
    let rw := stepWorldPure op w
    runWorldPureBind (f rw.1) k rw.2
termination_by structural x _ _ => x

theorem bindAssocRun {Δ : List Cap} {A B C : Type} :
    (m : WorldProg Δ A) →
      (f : A → WorldProg Δ B) →
        (g : B → WorldProg Δ C) →
          (w : SimWorld) →
            runWorldPure (worldBind (worldBind m f) g) w =
              runWorldPure (worldBind m fun x => worldBind (f x) g) w
  | .pure _, _, _, _ => rfl
  | .step _ op k, f, g, w =>
    let rw := stepWorldPure op w
    bindAssocRun (k rw.1) f g rw.2
termination_by structural x _ _ _ => x

theorem mapWorldPure {Δ : List Cap} {A B : Type} (f : A → B) (a : A) :
    mapWorld (Δ := Δ) f (.pure a) = .pure (f a) :=
  rfl

theorem mapWorldRun {Δ : List Cap} {A B : Type} (f : A → B) :
    (m : WorldProg Δ A) →
      (w : SimWorld) →
        runWorldPure (mapWorld f m) w = Prod.mk (f (runWorldPure m w).1) (runWorldPure m w).2
  | .pure _, _ => rfl
  | .step _ op k, w =>
    let rw := stepWorldPure op w
    mapWorldRun f (k rw.1) rw.2
termination_by structural x _ => x

theorem liftWorldPure {Δ₁ Δ₂ : List Cap} {A : Type} (sub : CapSub Δ₁ Δ₂) (a : A) :
    liftWorld sub (.pure a) = .pure a :=
  rfl

theorem liftWorldPreservesRun {Δ₁ Δ₂ : List Cap} {A : Type} (sub : CapSub Δ₁ Δ₂) :
    (m : WorldProg Δ₁ A) → (w : SimWorld) → runWorldPure (liftWorld sub m) w = runWorldPure m w
  | .pure _, _ => rfl
  | .step _ op k, w =>
    let rw := stepWorldPure op w
    liftWorldPreservesRun sub (k rw.1) rw.2
termination_by structural x _ => x

theorem liftWorldBindRun {Δ₁ Δ₂ : List Cap} {A B : Type} (sub : CapSub Δ₁ Δ₂) (m : WorldProg Δ₁ A)
    (k : A → WorldProg Δ₁ B) (w : SimWorld) :
    runWorldPure (liftWorld sub (worldBind m k)) w =
      runWorldPure (worldBind (liftWorld sub m) fun a => liftWorld sub (k a)) w :=
  Eq.trans (liftWorldPreservesRun sub (worldBind m k) w)
    (Eq.trans (runWorldPureBind m k w)
      (Eq.symm
        (Eq.trans (runWorldPureBind (liftWorld sub m) (fun a => liftWorld sub (k a)) w)
          (Eq.trans
            (congrArg (fun r => runWorldPure (liftWorld sub (k r.1)) r.2)
              (liftWorldPreservesRun sub m w))
            (liftWorldPreservesRun sub (k (runWorldPure m w).1) (runWorldPure m w).2)))))

theorem stepPreservesClock {c : Cap} (neq : c = .clockCap → False) (op : Op c) (w : SimWorld) :
    (stepWorldPure op w).2.clock = w.clock := by
  cases op <;> first | rfl | exact (neq rfl).elim

theorem stepPreservesEnv {c : Cap} (op : Op c) (w : SimWorld) :
    (stepWorldPure op w).2.env = w.env := by
  cases op <;> rfl

theorem stepPreservesStdio {c : Cap} (neq : c = .stdioCap → False) (op : Op c) (w : SimWorld) :
    (stepWorldPure op w).2.stdio = w.stdio := by
  cases op <;> first | rfl | exact (neq rfl).elim

theorem stepPreservesTty {c : Cap} (neq : c = .ttyCap → False) (op : Op c) (w : SimWorld) :
    (stepWorldPure op w).2.tty = w.tty := by
  cases op <;> first | rfl | exact (neq rfl).elim

theorem stepPreservesFs {c : Cap} (neq : c = .fsCap → False) (op : Op c) (w : SimWorld) :
    (stepWorldPure op w).2.fs = w.fs := by
  cases op <;> first | rfl | exact (neq rfl).elim

theorem stepPreservesNet {c : Cap} (neq : c = .netCap → False) (op : Op c) (w : SimWorld) :
    (stepWorldPure op w).2.net = w.net := by
  cases op <;> first | rfl | exact (neq rfl).elim

theorem stepPreservesGit {c : Cap} (neq : c = .gitCap → False) (op : Op c) (w : SimWorld) :
    (stepWorldPure op w).2.git = w.git := by
  cases op <;> first | rfl | exact (neq rfl).elim

theorem stepPreservesWeb {c : Cap} (neq : c = .webCap → False) (op : Op c) (w : SimWorld) :
    (stepWorldPure op w).2.web = w.web := by
  cases op <;> first | rfl | exact (neq rfl).elim

private def substMem {x y : Cap} {cs : List Cap} : (x = y) → CapMem x cs → CapMem y cs
  | rfl, m => m

theorem eqCapRefl : (c : Cap) → eqCap c c = true
  | .clockCap => rfl
  | .envCap => rfl
  | .stdioCap => rfl
  | .ttyCap => rfl
  | .fsCap => rfl
  | .netCap => rfl
  | .gitCap => rfl
  | .webCap => rfl

private theorem orFalseLeft : (a b : Bool) → (a || b) = false → a = false
  | false, _, _ => rfl
  | true, _, h => nomatch h

private theorem orFalseRight : (a b : Bool) → (a || b) = false → b = false
  | false, _, h => h
  | true, _, h => nomatch h

theorem notHasCapNotIn : {c : Cap} → {Δ : List Cap} → hasCap c Δ = false → CapMem c Δ → False
  | c, _ :: ds, eq, .here =>
    nomatch Eq.trans (Eq.symm (eqCapRefl c)) (orFalseLeft (eqCap c c) (hasCap c ds) eq)
  | c, d :: ds, eq, .there m => notHasCapNotIn (orFalseRight (eqCap c d) (hasCap c ds) eq) m
termination_by structural _ x _ _ => x

private theorem progPreservesField {Δ : List Cap} {A F : Type} (field : SimWorld → F)
    (preserved : ∀ {c : Cap}, CapMem c Δ → (op : Op c) → (w : SimWorld) →
      field (stepWorldPure op w).2 = field w) :
    (m : WorldProg Δ A) → (w : SimWorld) → field (runWorldPure m w).2 = field w
  | .pure _, _ => rfl
  | .step h op k, w =>
    let r := stepWorldPure op w
    Eq.trans (progPreservesField field preserved (k r.1) r.2) (preserved h op w)
termination_by structural m _ => m

theorem progPreservesClock {Δ : List Cap} {A : Type} (absent : CapMem .clockCap Δ → False)
    (m : WorldProg Δ A) (w : SimWorld) : (runWorldPure m w).2.clock = w.clock :=
  progPreservesField SimWorld.clock (fun h => stepPreservesClock (fun eq => absent (substMem eq h))) m w

theorem progPreservesEnv {Δ : List Cap} {A : Type}
    (m : WorldProg Δ A) (w : SimWorld) : (runWorldPure m w).2.env = w.env :=
  progPreservesField SimWorld.env (fun _ => stepPreservesEnv) m w

theorem progPreservesStdio {Δ : List Cap} {A : Type} (absent : CapMem .stdioCap Δ → False)
    (m : WorldProg Δ A) (w : SimWorld) : (runWorldPure m w).2.stdio = w.stdio :=
  progPreservesField SimWorld.stdio (fun h => stepPreservesStdio (fun eq => absent (substMem eq h))) m w

theorem progPreservesTty {Δ : List Cap} {A : Type} (absent : CapMem .ttyCap Δ → False)
    (m : WorldProg Δ A) (w : SimWorld) : (runWorldPure m w).2.tty = w.tty :=
  progPreservesField SimWorld.tty (fun h => stepPreservesTty (fun eq => absent (substMem eq h))) m w

theorem progPreservesFs {Δ : List Cap} {A : Type} (absent : CapMem .fsCap Δ → False)
    (m : WorldProg Δ A) (w : SimWorld) : (runWorldPure m w).2.fs = w.fs :=
  progPreservesField SimWorld.fs (fun h => stepPreservesFs (fun eq => absent (substMem eq h))) m w

theorem progPreservesNet {Δ : List Cap} {A : Type} (absent : CapMem .netCap Δ → False)
    (m : WorldProg Δ A) (w : SimWorld) : (runWorldPure m w).2.net = w.net :=
  progPreservesField SimWorld.net (fun h => stepPreservesNet (fun eq => absent (substMem eq h))) m w

theorem progPreservesGit {Δ : List Cap} {A : Type} (absent : CapMem .gitCap Δ → False)
    (m : WorldProg Δ A) (w : SimWorld) : (runWorldPure m w).2.git = w.git :=
  progPreservesField SimWorld.git (fun h => stepPreservesGit (fun eq => absent (substMem eq h))) m w

theorem progPreservesWeb {Δ : List Cap} {A : Type} (absent : CapMem .webCap Δ → False)
    (m : WorldProg Δ A) (w : SimWorld) : (runWorldPure m w).2.web = w.web :=
  progPreservesField SimWorld.web (fun h => stepPreservesWeb (fun eq => absent (substMem eq h))) m w

def continueReactiveAfter {Δ : List Cap} {S : Type} (a : ReactiveApp Δ S) (es : List (Event Δ)) :
    Sum S ExitCode → SimWorld → Sum S ExitCode × SimWorld
  | .inl s', w' => runReactiveSteps a s' es w'
  | .inr code, w' => Prod.mk (.inr code) w'

theorem runReactiveStepsAppend {Δ : List Cap} {S : Type} (app : ReactiveApp Δ S) :
    (s : S) →
      (evs₁ evs₂ : List (Event Δ)) →
        (w : SimWorld) →
          runReactiveSteps app s (List.append evs₁ evs₂) w =
            let r₁ := runReactiveSteps app s evs₁ w
            continueReactiveAfter app evs₂ r₁.1 r₁.2
  | _, [], _, _ => rfl
  | s, e :: es, evs₂, w =>
    id
      (by
        simp only [List.append, runReactiveSteps]
        cases h : (runWorldPure (app.onStep e s) w).1 with
        | inl s' =>
          exact id (runReactiveStepsAppend app s' es evs₂ (runWorldPure (app.onStep e s) w).2)
        | inr code => rfl)
termination_by structural _ x _ _ => x

end LojitaCtx.WorldLaws
