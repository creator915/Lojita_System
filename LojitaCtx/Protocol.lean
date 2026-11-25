import LojitaCtx.WorldLaws

namespace LojitaCtx.Protocol

open LojitaCtx
open LojitaCtx.Clock
open LojitaCtx.FsSandbox
open LojitaCtx.World
open LojitaCtx.WorldLaws

/-! ## §1 Typed Dual Session Protocol (`Proto`, `dual`, `dual_involutive`) -/

inductive Proto (Tag : Type) : Type where
  | pEnd    : Proto Tag
  | pSend   : Tag → Proto Tag → Proto Tag
  | pRecv   : Tag → Proto Tag → Proto Tag
  | pSelect : Proto Tag → Proto Tag → Proto Tag
  | pOffer  : Proto Tag → Proto Tag → Proto Tag

-- The dependent endpoint matcher discriminates protocol constructors using
-- this kernel definition of the tag.
def Proto.ctorIdx {Tag : Type} : Proto Tag → Nat
  | .pEnd => 0
  | .pSend .. => 1
  | .pRecv .. => 2
  | .pSelect .. => 3
  | .pOffer .. => 4

def dual {Tag : Type} : Proto Tag → Proto Tag
  | .pEnd        => .pEnd
  | .pSend t P   => .pRecv t (dual P)
  | .pRecv t P   => .pSend t (dual P)
  | .pSelect P Q => .pOffer (dual P) (dual Q)
  | .pOffer P Q  => .pSelect (dual P) (dual Q)
termination_by structural P => P

theorem dual_involutive {Tag : Type} : (P : Proto Tag) → dual (dual P) = P
  | .pEnd => rfl
  | .pSend t P => congrArg (Proto.pSend t) (dual_involutive P)
  | .pRecv t P => congrArg (Proto.pRecv t) (dual_involutive P)
  | .pSelect P Q =>
    by change Proto.pSelect (dual (dual P)) (dual (dual Q)) = _; rw [dual_involutive P, dual_involutive Q]
  | .pOffer P Q =>
    by change Proto.pOffer (dual (dual P)) (dual (dual Q)) = _; rw [dual_involutive P, dual_involutive Q]
termination_by structural P => P

/-! ## §2 Closed-World Effectful Session Endpoints (`Endpoint`) -/

inductive EndpointCore {Tag : Type} (Δ : List Cap) (Payload : Tag → Type) (A : Type) : Proto Tag → Type where
  | epDone    : A → EndpointCore Δ Payload A .pEnd
  | epStep    : {P : Proto Tag} → {c : Cap} → CapMem c Δ → (op : Op c) → (Ret op → EndpointCore Δ Payload A P) → EndpointCore Δ Payload A P
  | epSend    : {t : Tag} → {P : Proto Tag} → Payload t → EndpointCore Δ Payload A P → EndpointCore Δ Payload A (.pSend t P)
  | epRecv    : {t : Tag} → {P : Proto Tag} → (Payload t → EndpointCore Δ Payload A P) → EndpointCore Δ Payload A (.pRecv t P)
  | epSelectL : {P Q : Proto Tag} → EndpointCore Δ Payload A P → EndpointCore Δ Payload A (.pSelect P Q)
  | epSelectR : {P Q : Proto Tag} → EndpointCore Δ Payload A Q → EndpointCore Δ Payload A (.pSelect P Q)
  | epOffer   : {P Q : Proto Tag} → EndpointCore Δ Payload A P → EndpointCore Δ Payload A Q → EndpointCore Δ Payload A (.pOffer P Q)

abbrev Endpoint {Tag : Type} (Δ : List Cap) (Payload : Tag → Type) (P : Proto Tag) (A : Type) : Type :=
  EndpointCore Δ Payload A P

def mapEndpoint {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (f : A → B) : Endpoint Δ Payload P A → Endpoint Δ Payload P B
  | .epDone a        => .epDone (f a)
  | .epStep h op k   => .epStep h op (fun r => mapEndpoint f (k r))
  | .epSend msg ep   => .epSend msg (mapEndpoint f ep)
  | .epRecv k        => .epRecv (fun msg => mapEndpoint f (k msg))
  | .epSelectL ep    => .epSelectL (mapEndpoint f ep)
  | .epSelectR ep    => .epSelectR (mapEndpoint f ep)
  | .epOffer epL epR => .epOffer (mapEndpoint f epL) (mapEndpoint f epR)
termination_by structural ep => ep

def liftProgToEndpoint {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type} :
    WorldProg Δ A → (A → Endpoint Δ Payload P B) → Endpoint Δ Payload P B
  | .pure a,      k => k a
  | .step h op f, k => .epStep h op (fun r => liftProgToEndpoint (f r) k)
termination_by structural prog _ => prog

def liftEndpoint {Tag : Type} {Δ₁ Δ₂ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A : Type}
    (sub : CapSub Δ₁ Δ₂) : Endpoint Δ₁ Payload P A → Endpoint Δ₂ Payload P A
  | .epDone a        => .epDone a
  | .epStep h op k   => .epStep (sub h) op (fun r => liftEndpoint sub (k r))
  | .epSend msg ep   => .epSend msg (liftEndpoint sub ep)
  | .epRecv k        => .epRecv (fun msg => liftEndpoint sub (k msg))
  | .epSelectL ep    => .epSelectL (liftEndpoint sub ep)
  | .epSelectR ep    => .epSelectR (liftEndpoint sub ep)
  | .epOffer epL epR => .epOffer (liftEndpoint sub epL) (liftEndpoint sub epR)
termination_by structural ep => ep

/-! ## §3 Deadlock-Free Closed-World Session Cut (`coupleEndpoints`) -/

private inductive ReadyEndpoint {Tag : Type} (Δ : List Cap) (Payload : Tag → Type) (A : Type) : Proto Tag → Type where
  | rDone    : A → ReadyEndpoint Δ Payload A .pEnd
  | rSend    : {t : Tag} → {P : Proto Tag} → Payload t → Endpoint Δ Payload P A → ReadyEndpoint Δ Payload A (.pSend t P)
  | rRecv    : {t : Tag} → {P : Proto Tag} → (Payload t → Endpoint Δ Payload P A) → ReadyEndpoint Δ Payload A (.pRecv t P)
  | rSelectL : {P Q : Proto Tag} → Endpoint Δ Payload P A → ReadyEndpoint Δ Payload A (.pSelect P Q)
  | rSelectR : {P Q : Proto Tag} → Endpoint Δ Payload Q A → ReadyEndpoint Δ Payload A (.pSelect P Q)
  | rOffer   : {P Q : Proto Tag} → Endpoint Δ Payload P A → Endpoint Δ Payload Q A → ReadyEndpoint Δ Payload A (.pOffer P Q)

private def peelEndpoint {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A R : Type}
    (cont : ReadyEndpoint Δ Payload A P → WorldProg Δ R) : Endpoint Δ Payload P A → WorldProg Δ R
  | .epDone a        => cont (.rDone a)
  | .epStep h op k   => .step h op (fun r => peelEndpoint cont (k r))
  | .epSend msg ep   => cont (.rSend msg ep)
  | .epRecv k        => cont (.rRecv k)
  | .epSelectL ep    => cont (.rSelectL ep)
  | .epSelectR ep    => cont (.rSelectR ep)
  | .epOffer epL epR => cont (.rOffer epL epR)
termination_by structural ep => ep

private def coupleProto {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {A B : Type} :
    (P : Proto Tag) → Endpoint Δ Payload P A → Endpoint Δ Payload (dual P) B → WorldProg Δ (A × B)
  | .pEnd, epA, epB =>
    peelEndpoint
      (fun ra =>
        peelEndpoint
          (fun rb =>
            match ra, rb with
            | .rDone a, .rDone b => .pure (Prod.mk a b))
          epB)
      epA
  | .pSend _ P', epA, epB =>
    peelEndpoint
      (fun ra =>
        peelEndpoint
          (fun rb =>
            match ra, rb with
            | .rSend msg epA', .rRecv kB => coupleProto P' epA' (kB msg))
          epB)
      epA
  | .pRecv _ P', epA, epB =>
    peelEndpoint
      (fun ra =>
        peelEndpoint
          (fun rb =>
            match ra, rb with
            | .rRecv kA, .rSend msg epB' => coupleProto P' (kA msg) epB')
          epB)
      epA
  | .pSelect P Q, epA, epB =>
    peelEndpoint
      (fun ra =>
        peelEndpoint
          (fun rb =>
            match ra, rb with
            | .rSelectL epA', .rOffer epBL _ => coupleProto P epA' epBL
            | .rSelectR epA', .rOffer _ epBR => coupleProto Q epA' epBR)
          epB)
      epA
  | .pOffer P Q, epA, epB =>
    peelEndpoint
      (fun ra =>
        peelEndpoint
          (fun rb =>
            match ra, rb with
            | .rOffer epAL _, .rSelectL epB' => coupleProto P epAL epB'
            | .rOffer _ epAR, .rSelectR epB' => coupleProto Q epAR epB')
          epB)
      epA
termination_by structural P _ _ => P

def coupleEndpoints {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (epA : Endpoint Δ Payload P A) (epB : Endpoint Δ Payload (dual P) B) : WorldProg Δ (A × B) :=
  coupleProto P epA epB

private def stepOptService {Δᵢ Δ : List Cap} {Sᵢ : Type}
    (sub : CapSub Δᵢ Δ) (app : ReactiveApp Δᵢ Sᵢ) (sᵢ : Sᵢ) :
    Option (Event Δᵢ) → WorldProg Δ (Sum Sᵢ ExitCode)
  | .none    => .pure (.inl sᵢ)
  | .some evᵢ   => liftWorld sub (app.onStep evᵢ sᵢ)

private def finishSecondPair {S₁ S₂ : Type} (x : S₁) : Sum S₂ ExitCode → Sum (S₁ × S₂) ExitCode
  | .inl y => .inl (Prod.mk x y)
  | .inr code => .inr code

private def continueSecondService {Δ₂ Δ : List Cap} {S₁ S₂ : Type} (sub₂ : CapSub Δ₂ Δ)
    (app₂ : ReactiveApp Δ₂ S₂) (s₂ : S₂) (mev₂ : Option (Event Δ₂)) :
    Sum S₁ ExitCode → WorldProg Δ (Sum (S₁ × S₂) ExitCode)
  | .inr code => .pure (.inr code)
  | .inl s₁' => mapWorld (finishSecondPair s₁') (stepOptService sub₂ app₂ s₂ mev₂)

private def mergeTurnOutcomes {S₁ S₂ : Type} :
    Sum S₁ ExitCode → Sum S₂ ExitCode → Sum (S₁ × S₂) ExitCode
  | .inr code, _ => .inr code
  | .inl _, .inr code => .inr code
  | .inl s₁', .inl s₂' => .inl (Prod.mk s₁' s₂')

def composeReactive {Δ₁ Δ₂ Δ : List Cap} {S₁ S₂ : Type} (sub₁ : CapSub Δ₁ Δ) (sub₂ : CapSub Δ₂ Δ)
    (app₁ : ReactiveApp Δ₁ S₁) (app₂ : ReactiveApp Δ₂ S₂)
    (routeEv : Event Δ → Option (Event Δ₁) × Option (Event Δ₂)) : ReactiveApp Δ (S₁ × S₂) :=
  ReactiveApp.reactiveApp
    (worldBind (liftWorld sub₁ app₁.init) fun s₁ =>
      worldBind (liftWorld sub₂ app₂.init) fun s₂ => .pure (Prod.mk s₁ s₂))
    fun ev st =>
    let routed := routeEv ev
    worldBind (stepOptService sub₁ app₁ st.1 routed.1)
      (continueSecondService sub₂ app₂ st.2 routed.2)

def coupleReactiveTurn {Tag : Type} {Δ₁ Δ₂ Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag}
    {S₁ S₂ : Type} (sub₁ : CapSub Δ₁ Δ) (sub₂ : CapSub Δ₂ Δ)
    (turn₁ : Event Δ → S₁ → Endpoint Δ₁ Payload P (Sum S₁ ExitCode))
    (turn₂ : S₂ → Endpoint Δ₂ Payload (dual P) (Sum S₂ ExitCode)) (ev : Event Δ) (st : S₁ × S₂) :
    WorldProg Δ (Sum (S₁ × S₂) ExitCode) :=
  mapWorld (fun r => mergeTurnOutcomes r.1 r.2)
    (coupleEndpoints (liftEndpoint sub₁ (turn₁ ev st.1)) (liftEndpoint sub₂ (turn₂ st.2)))

def coupleReactive {Tag : Type} {Δ₁ Δ₂ Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag}
    {S₁ S₂ : Type} (sub₁ : CapSub Δ₁ Δ) (sub₂ : CapSub Δ₂ Δ) (init₁ : WorldProg Δ₁ S₁)
    (init₂ : WorldProg Δ₂ S₂) (turn₁ : Event Δ → S₁ → Endpoint Δ₁ Payload P (Sum S₁ ExitCode))
    (turn₂ : S₂ → Endpoint Δ₂ Payload (dual P) (Sum S₂ ExitCode)) : ReactiveApp Δ (S₁ × S₂) :=
  ReactiveApp.reactiveApp
    (worldBind (liftWorld sub₁ init₁) fun s₁ =>
      worldBind (liftWorld sub₂ init₂) fun s₂ => .pure (Prod.mk s₁ s₂))
    (coupleReactiveTurn sub₁ sub₂ turn₁ turn₂)

theorem coupleDone {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {A B : Type} (a : A) (b : B) :
    coupleEndpoints (Tag := Tag) (Δ := Δ) (Payload := Payload) (.epDone a) (.epDone b) =
      .pure (Prod.mk a b) :=
  rfl

theorem coupleSendRecv {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {t : Tag} {P : Proto Tag}
    {A B : Type} (msg : Payload t) (epA : Endpoint Δ Payload P A)
    (kB : Payload t → Endpoint Δ Payload (dual P) B) :
    coupleEndpoints (.epSend msg epA) (.epRecv kB) = coupleEndpoints epA (kB msg) :=
  rfl

theorem coupleRecvSend {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {t : Tag} {P : Proto Tag}
    {A B : Type} (kA : Payload t → Endpoint Δ Payload P A) (msg : Payload t)
    (epB : Endpoint Δ Payload (dual P) B) :
    coupleEndpoints (.epRecv kA) (.epSend msg epB) = coupleEndpoints (kA msg) epB :=
  rfl

theorem coupleSelectLOffer {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag}
    {A B : Type} (epA : Endpoint Δ Payload P A) (epBL : Endpoint Δ Payload (dual P) B)
    (epBR : Endpoint Δ Payload (dual Q) B) :
    coupleEndpoints (.epSelectL epA) (.epOffer epBL epBR) = coupleEndpoints epA epBL :=
  rfl

theorem coupleSelectROffer {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag}
    {A B : Type} (epA : Endpoint Δ Payload Q A) (epBL : Endpoint Δ Payload (dual P) B)
    (epBR : Endpoint Δ Payload (dual Q) B) :
    coupleEndpoints (.epSelectR epA) (.epOffer epBL epBR) = coupleEndpoints epA epBR :=
  rfl

theorem coupleOfferSelectL {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag}
    {A B : Type} (epAL : Endpoint Δ Payload P A) (epAR : Endpoint Δ Payload Q A)
    (epB : Endpoint Δ Payload (dual P) B) :
    coupleEndpoints (.epOffer epAL epAR) (.epSelectL epB) = coupleEndpoints epAL epB :=
  rfl

theorem coupleOfferSelectR {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag}
    {A B : Type} (epAL : Endpoint Δ Payload P A) (epAR : Endpoint Δ Payload Q A)
    (epB : Endpoint Δ Payload (dual Q) B) :
    coupleEndpoints (.epOffer epAL epAR) (.epSelectR epB) = coupleEndpoints epAR epB :=
  rfl

theorem coupleStepLeft {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    {c : Cap} (h : CapMem c Δ) (op : Op c) (kA : Ret op → Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B) :
    coupleEndpoints (.epStep h op kA) epB = .step h op fun r => coupleEndpoints (kA r) epB :=
  match P, kA, epB with
  | .pEnd, _, _ => rfl
  | .pSend _ _, _, _ => rfl
  | .pRecv _ _, _, _ => rfl
  | .pSelect _ _, _, _ => rfl
  | .pOffer _ _, _, _ => rfl

theorem couple_preserves_clock {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag}
    {A B : Type} (absent : CapMem .clockCap Δ → False) (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B) (w : SimWorld) :
    (runWorldPure (coupleEndpoints epA epB) w).2.clock = w.clock :=
  progPreservesClock absent (coupleEndpoints epA epB) w

theorem couple_preserves_env {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag}
    {A B : Type} (epA : Endpoint Δ Payload P A) (epB : Endpoint Δ Payload (dual P) B) (w : SimWorld) :
    (runWorldPure (coupleEndpoints epA epB) w).2.env = w.env :=
  progPreservesEnv (coupleEndpoints epA epB) w

theorem couple_preserves_stdio {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag}
    {A B : Type} (absent : CapMem .stdioCap Δ → False) (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B) (w : SimWorld) :
    (runWorldPure (coupleEndpoints epA epB) w).2.stdio = w.stdio :=
  progPreservesStdio absent (coupleEndpoints epA epB) w

theorem couple_preserves_fs {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag}
    {A B : Type} (absent : CapMem .fsCap Δ → False) (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B) (w : SimWorld) :
    (runWorldPure (coupleEndpoints epA epB) w).2.fs = w.fs :=
  progPreservesFs absent (coupleEndpoints epA epB) w

theorem couple_preserves_net {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag}
    {A B : Type} (absent : CapMem .netCap Δ → False) (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B) (w : SimWorld) :
    (runWorldPure (coupleEndpoints epA epB) w).2.net = w.net :=
  progPreservesNet absent (coupleEndpoints epA epB) w

theorem couple_preserves_tty {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag}
    {A B : Type} (absent : CapMem .ttyCap Δ → False) (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B) (w : SimWorld) :
    (runWorldPure (coupleEndpoints epA epB) w).2.tty = w.tty :=
  progPreservesTty absent (coupleEndpoints epA epB) w

end LojitaCtx.Protocol
