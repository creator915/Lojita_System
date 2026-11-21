import AgdaMirror.Core
import AgdaMirror.Context
import AgdaMirror.World

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
# `AgdaMirror.Protocol`: Constructive Mirror of `Context.Protocol`

Mirrors typed dual session protocols (`Proto`, `dual`, `dualInvolutive`), closed-world
effectful session endpoints (`Endpoint`, `mapEndpoint`, `liftProgToEndpoint`, `liftEndpoint`),
deadlock-free session cut (`coupleEndpoints`), multi-`ReactiveApp` composition
(`composeReactive`, `coupleReactiveTurn`, `coupleReactive`), and all universal algebraic
and capability frame laws with 100% definitional alignment and zero axioms.
-/

namespace AgdaMirror.Protocol

open AgdaMirror
open AgdaMirror.Clock
open AgdaMirror.FsSandbox
open AgdaMirror.World
open AgdaMirror.WorldLaws

/-! ## §1 Typed Dual Session Protocol (`Proto`, `dual`, `dualInvolutive`) -/

inductive Proto (Tag : Type) : Type where
  | pEnd    : Proto Tag
  | pSend   : Tag → Proto Tag → Proto Tag
  | pRecv   : Tag → Proto Tag → Proto Tag
  | pSelect : Proto Tag → Proto Tag → Proto Tag
  | pOffer  : Proto Tag → Proto Tag → Proto Tag

def dual {Tag : Type} : Proto Tag → Proto Tag
  | .pEnd        => .pEnd
  | .pSend t P   => .pRecv t (dual P)
  | .pRecv t P   => .pSend t (dual P)
  | .pSelect P Q => .pOffer (dual P) (dual Q)
  | .pOffer P Q  => .pSelect (dual P) (dual Q)
termination_by structural P => P

def dualInvolutive {Tag : Type} : (P : Proto Tag) → AgdaId (dual (dual P)) P
  | .pEnd        => .refl
  | .pSend t P   => idCong (Proto.pSend t) (dualInvolutive P)
  | .pRecv t P   => idCong (Proto.pRecv t) (dualInvolutive P)
  | .pSelect P Q => idCong2 Proto.pSelect (dualInvolutive P) (dualInvolutive Q)
  | .pOffer P Q  => idCong2 Proto.pOffer (dualInvolutive P) (dualInvolutive Q)
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
    (P : Proto Tag) → Endpoint Δ Payload P A → Endpoint Δ Payload (dual P) B → WorldProg Δ (AgdaPair A B)
  | .pEnd, epA, epB =>
      peelEndpoint (fun ra =>
        peelEndpoint (fun rb =>
          match ra, rb with
          | .rDone a, .rDone b => .pure (AgdaPair.mk a b)) epB) epA
  | .pSend _ P', epA, epB =>
      peelEndpoint (fun ra =>
        peelEndpoint (fun rb =>
          match ra, rb with
          | .rSend msg epA', .rRecv kB => coupleProto P' epA' (kB msg)) epB) epA
  | .pRecv _ P', epA, epB =>
      peelEndpoint (fun ra =>
        peelEndpoint (fun rb =>
          match ra, rb with
          | .rRecv kA, .rSend msg epB' => coupleProto P' (kA msg) epB') epB) epA
  | .pSelect P Q, epA, epB =>
      peelEndpoint (fun ra =>
        peelEndpoint (fun rb =>
          match ra, rb with
          | .rSelectL epA', .rOffer epBL _    => coupleProto P epA' epBL
          | .rSelectR epA', .rOffer _    epBR => coupleProto Q epA' epBR) epB) epA
  | .pOffer P Q, epA, epB =>
      peelEndpoint (fun ra =>
        peelEndpoint (fun rb =>
          match ra, rb with
          | .rOffer epAL _,    .rSelectL epB' => coupleProto P epAL epB'
          | .rOffer _    epAR, .rSelectR epB' => coupleProto Q epAR epB') epB) epA
termination_by structural P _ _ => P

private def coupleProtoSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {A B : Type} :
    (P : Proto Tag) → Endpoint Δ Payload P A → Endpoint Δ Payload (dual P) B → WorldProg Δ (AgdaProd A B)
  | .pEnd, epA, epB =>
      peelEndpoint (fun ra =>
        peelEndpoint (fun rb =>
          match ra, rb with
          | .rDone a, .rDone b => .pure (AgdaSigma.mk a b)) epB) epA
  | .pSend _ P', epA, epB =>
      peelEndpoint (fun ra =>
        peelEndpoint (fun rb =>
          match ra, rb with
          | .rSend msg epA', .rRecv kB => coupleProtoSigma P' epA' (kB msg)) epB) epA
  | .pRecv _ P', epA, epB =>
      peelEndpoint (fun ra =>
        peelEndpoint (fun rb =>
          match ra, rb with
          | .rRecv kA, .rSend msg epB' => coupleProtoSigma P' (kA msg) epB') epB) epA
  | .pSelect P Q, epA, epB =>
      peelEndpoint (fun ra =>
        peelEndpoint (fun rb =>
          match ra, rb with
          | .rSelectL epA', .rOffer epBL _    => coupleProtoSigma P epA' epBL
          | .rSelectR epA', .rOffer _    epBR => coupleProtoSigma Q epA' epBR) epB) epA
  | .pOffer P Q, epA, epB =>
      peelEndpoint (fun ra =>
        peelEndpoint (fun rb =>
          match ra, rb with
          | .rOffer epAL _,    .rSelectL epB' => coupleProtoSigma P epAL epB'
          | .rOffer _    epAR, .rSelectR epB' => coupleProtoSigma Q epAR epB') epB) epA
termination_by structural P _ _ => P

def coupleEndpoints {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (epA : Endpoint Δ Payload P A) (epB : Endpoint Δ Payload (dual P) B) : WorldProg Δ (AgdaPair A B) :=
  coupleProto P epA epB

def coupleEndpointsSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (epA : Endpoint Δ Payload P A) (epB : Endpoint Δ Payload (dual P) B) : WorldProg Δ (AgdaProd A B) :=
  coupleProtoSigma P epA epB

/-! ## §4 Multi-`ReactiveApp` Closed-World Composition -/

private def stepOptService {Δᵢ Δ : List Cap} {Sᵢ : Type}
    (sub : CapSub Δᵢ Δ) (app : ReactiveApp Δᵢ Sᵢ) (sᵢ : Sᵢ) :
    AgdaMaybe (Event Δᵢ) → WorldProg Δ (AgdaSum Sᵢ ExitCode)
  | .nothing    => .pure (.inj₁ sᵢ)
  | .just evᵢ   => liftWorld sub (app.onStep evᵢ sᵢ)

private def finishSecondPair {S₁ S₂ : Type} (x : S₁) :
    AgdaSum S₂ ExitCode → AgdaSum (AgdaPair S₁ S₂) ExitCode
  | .inj₁ y    => .inj₁ (AgdaPair.mk x y)
  | .inj₂ code => .inj₂ code

private def finishSecondSigma {S₁ S₂ : Type} (x : S₁) :
    AgdaSum S₂ ExitCode → AgdaSum (AgdaProd S₁ S₂) ExitCode
  | .inj₁ y    => .inj₁ (AgdaSigma.mk x y)
  | .inj₂ code => .inj₂ code

private def continueSecondService {Δ₂ Δ : List Cap} {S₁ S₂ : Type}
    (sub₂ : CapSub Δ₂ Δ) (app₂ : ReactiveApp Δ₂ S₂) (s₂ : S₂) (mev₂ : AgdaMaybe (Event Δ₂)) :
    AgdaSum S₁ ExitCode → WorldProg Δ (AgdaSum (AgdaPair S₁ S₂) ExitCode)
  | .inj₂ code => .pure (.inj₂ code)
  | .inj₁ s₁'  => mapWorld (finishSecondPair s₁') (stepOptService sub₂ app₂ s₂ mev₂)

private def continueSecondServiceSigma {Δ₂ Δ : List Cap} {S₁ S₂ : Type}
    (sub₂ : CapSub Δ₂ Δ) (app₂ : ReactiveApp Δ₂ S₂) (s₂ : S₂) (mev₂ : AgdaMaybe (Event Δ₂)) :
    AgdaSum S₁ ExitCode → WorldProg Δ (AgdaSum (AgdaProd S₁ S₂) ExitCode)
  | .inj₂ code => .pure (.inj₂ code)
  | .inj₁ s₁'  => mapWorld (finishSecondSigma s₁') (stepOptService sub₂ app₂ s₂ mev₂)

private def mergeTurnOutcomes {S₁ S₂ : Type} :
    AgdaSum S₁ ExitCode → AgdaSum S₂ ExitCode → AgdaSum (AgdaPair S₁ S₂) ExitCode
  | .inj₂ code, _          => .inj₂ code
  | .inj₁ _,    .inj₂ code => .inj₂ code
  | .inj₁ s₁',  .inj₁ s₂'  => .inj₁ (AgdaPair.mk s₁' s₂')

private def mergeTurnOutcomesSigma {S₁ S₂ : Type} :
    AgdaSum S₁ ExitCode → AgdaSum S₂ ExitCode → AgdaSum (AgdaProd S₁ S₂) ExitCode
  | .inj₂ code, _          => .inj₂ code
  | .inj₁ _,    .inj₂ code => .inj₂ code
  | .inj₁ s₁',  .inj₁ s₂'  => .inj₁ (AgdaSigma.mk s₁' s₂')

def composeReactive {Δ₁ Δ₂ Δ : List Cap} {S₁ S₂ : Type}
    (sub₁ : CapSub Δ₁ Δ)
    (sub₂ : CapSub Δ₂ Δ)
    (app₁ : ReactiveApp Δ₁ S₁)
    (app₂ : ReactiveApp Δ₂ S₂)
    (routeEv : Event Δ → AgdaPair (AgdaMaybe (Event Δ₁)) (AgdaMaybe (Event Δ₂))) :
    ReactiveApp Δ (AgdaPair S₁ S₂) :=
  ReactiveApp.reactiveApp
    (worldBind (liftWorld sub₁ app₁.init) (fun s₁ =>
     worldBind (liftWorld sub₂ app₂.init) (fun s₂ =>
     .pure (AgdaPair.mk s₁ s₂))))
    (fun ev st =>
      let routed := routeEv ev
      worldBind (stepOptService sub₁ app₁ st.proj₁ routed.proj₁)
                (continueSecondService sub₂ app₂ st.proj₂ routed.proj₂))

def composeReactiveSigma {Δ₁ Δ₂ Δ : List Cap} {S₁ S₂ : Type}
    (sub₁ : CapSub Δ₁ Δ)
    (sub₂ : CapSub Δ₂ Δ)
    (app₁ : ReactiveApp Δ₁ S₁)
    (app₂ : ReactiveApp Δ₂ S₂)
    (routeEv : Event Δ → AgdaProd (AgdaMaybe (Event Δ₁)) (AgdaMaybe (Event Δ₂))) :
    ReactiveApp Δ (AgdaProd S₁ S₂) :=
  ReactiveApp.reactiveApp
    (worldBind (liftWorld sub₁ app₁.init) (fun s₁ =>
     worldBind (liftWorld sub₂ app₂.init) (fun s₂ =>
     .pure (AgdaSigma.mk s₁ s₂))))
    (fun ev st =>
      let routed := routeEv ev
      worldBind (stepOptService sub₁ app₁ st.proj₁ routed.proj₁)
                (continueSecondServiceSigma sub₂ app₂ st.proj₂ routed.proj₂))

def coupleReactiveTurn {Tag : Type} {Δ₁ Δ₂ Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {S₁ S₂ : Type}
    (sub₁ : CapSub Δ₁ Δ)
    (sub₂ : CapSub Δ₂ Δ)
    (turn₁ : Event Δ → S₁ → Endpoint Δ₁ Payload P (AgdaSum S₁ ExitCode))
    (turn₂ : S₂ → Endpoint Δ₂ Payload (dual P) (AgdaSum S₂ ExitCode))
    (ev : Event Δ)
    (st : AgdaPair S₁ S₂) :
    WorldProg Δ (AgdaSum (AgdaPair S₁ S₂) ExitCode) :=
  mapWorld (fun r => mergeTurnOutcomes r.proj₁ r.proj₂)
    (coupleEndpoints
      (liftEndpoint sub₁ (turn₁ ev st.proj₁))
      (liftEndpoint sub₂ (turn₂ st.proj₂)))

def coupleReactiveTurnSigma {Tag : Type} {Δ₁ Δ₂ Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {S₁ S₂ : Type}
    (sub₁ : CapSub Δ₁ Δ)
    (sub₂ : CapSub Δ₂ Δ)
    (turn₁ : Event Δ → S₁ → Endpoint Δ₁ Payload P (AgdaSum S₁ ExitCode))
    (turn₂ : S₂ → Endpoint Δ₂ Payload (dual P) (AgdaSum S₂ ExitCode))
    (ev : Event Δ)
    (st : AgdaProd S₁ S₂) :
    WorldProg Δ (AgdaSum (AgdaProd S₁ S₂) ExitCode) :=
  mapWorld (fun r => mergeTurnOutcomesSigma r.proj₁ r.proj₂)
    (coupleEndpointsSigma
      (liftEndpoint sub₁ (turn₁ ev st.proj₁))
      (liftEndpoint sub₂ (turn₂ st.proj₂)))

def coupleReactive {Tag : Type} {Δ₁ Δ₂ Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {S₁ S₂ : Type}
    (sub₁ : CapSub Δ₁ Δ)
    (sub₂ : CapSub Δ₂ Δ)
    (init₁ : WorldProg Δ₁ S₁)
    (init₂ : WorldProg Δ₂ S₂)
    (turn₁ : Event Δ → S₁ → Endpoint Δ₁ Payload P (AgdaSum S₁ ExitCode))
    (turn₂ : S₂ → Endpoint Δ₂ Payload (dual P) (AgdaSum S₂ ExitCode)) :
    ReactiveApp Δ (AgdaPair S₁ S₂) :=
  ReactiveApp.reactiveApp
    (worldBind (liftWorld sub₁ init₁) (fun s₁ =>
     worldBind (liftWorld sub₂ init₂) (fun s₂ =>
     .pure (AgdaPair.mk s₁ s₂))))
    (coupleReactiveTurn sub₁ sub₂ turn₁ turn₂)

def coupleReactiveSigma {Tag : Type} {Δ₁ Δ₂ Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {S₁ S₂ : Type}
    (sub₁ : CapSub Δ₁ Δ)
    (sub₂ : CapSub Δ₂ Δ)
    (init₁ : WorldProg Δ₁ S₁)
    (init₂ : WorldProg Δ₂ S₂)
    (turn₁ : Event Δ → S₁ → Endpoint Δ₁ Payload P (AgdaSum S₁ ExitCode))
    (turn₂ : S₂ → Endpoint Δ₂ Payload (dual P) (AgdaSum S₂ ExitCode)) :
    ReactiveApp Δ (AgdaProd S₁ S₂) :=
  ReactiveApp.reactiveApp
    (worldBind (liftWorld sub₁ init₁) (fun s₁ =>
     worldBind (liftWorld sub₂ init₂) (fun s₂ =>
     .pure (AgdaSigma.mk s₁ s₂))))
    (coupleReactiveTurnSigma sub₁ sub₂ turn₁ turn₂)

/-! ## §5 Universal Algebraic & Capability Frame Laws -/

def coupleDone {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {A B : Type} (a : A) (b : B) :
    AgdaId (coupleEndpoints (Tag := Tag) (Δ := Δ) (Payload := Payload) (.epDone a) (.epDone b))
           (.pure (AgdaPair.mk a b)) := .refl

def coupleDoneSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {A B : Type} (a : A) (b : B) :
    AgdaId (coupleEndpointsSigma (Tag := Tag) (Δ := Δ) (Payload := Payload) (.epDone a) (.epDone b))
           (.pure (AgdaSigma.mk a b)) := .refl

def coupleSendRecv {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {t : Tag} {P : Proto Tag} {A B : Type}
    (msg : Payload t) (epA : Endpoint Δ Payload P A) (kB : Payload t → Endpoint Δ Payload (dual P) B) :
    AgdaId (coupleEndpoints (.epSend msg epA) (.epRecv kB))
           (coupleEndpoints epA (kB msg)) := .refl

def coupleSendRecvSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {t : Tag} {P : Proto Tag} {A B : Type}
    (msg : Payload t) (epA : Endpoint Δ Payload P A) (kB : Payload t → Endpoint Δ Payload (dual P) B) :
    AgdaId (coupleEndpointsSigma (.epSend msg epA) (.epRecv kB))
           (coupleEndpointsSigma epA (kB msg)) := .refl

def coupleRecvSend {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {t : Tag} {P : Proto Tag} {A B : Type}
    (kA : Payload t → Endpoint Δ Payload P A) (msg : Payload t) (epB : Endpoint Δ Payload (dual P) B) :
    AgdaId (coupleEndpoints (.epRecv kA) (.epSend msg epB))
           (coupleEndpoints (kA msg) epB) := .refl

def coupleRecvSendSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {t : Tag} {P : Proto Tag} {A B : Type}
    (kA : Payload t → Endpoint Δ Payload P A) (msg : Payload t) (epB : Endpoint Δ Payload (dual P) B) :
    AgdaId (coupleEndpointsSigma (.epRecv kA) (.epSend msg epB))
           (coupleEndpointsSigma (kA msg) epB) := .refl

def coupleSelectLOffer {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag} {A B : Type}
    (epA : Endpoint Δ Payload P A) (epBL : Endpoint Δ Payload (dual P) B) (epBR : Endpoint Δ Payload (dual Q) B) :
    AgdaId (coupleEndpoints (.epSelectL epA) (.epOffer epBL epBR))
           (coupleEndpoints epA epBL) := .refl

def coupleSelectLOfferSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag} {A B : Type}
    (epA : Endpoint Δ Payload P A) (epBL : Endpoint Δ Payload (dual P) B) (epBR : Endpoint Δ Payload (dual Q) B) :
    AgdaId (coupleEndpointsSigma (.epSelectL epA) (.epOffer epBL epBR))
           (coupleEndpointsSigma epA epBL) := .refl

def coupleSelectROffer {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag} {A B : Type}
    (epA : Endpoint Δ Payload Q A) (epBL : Endpoint Δ Payload (dual P) B) (epBR : Endpoint Δ Payload (dual Q) B) :
    AgdaId (coupleEndpoints (.epSelectR epA) (.epOffer epBL epBR))
           (coupleEndpoints epA epBR) := .refl

def coupleSelectROfferSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag} {A B : Type}
    (epA : Endpoint Δ Payload Q A) (epBL : Endpoint Δ Payload (dual P) B) (epBR : Endpoint Δ Payload (dual Q) B) :
    AgdaId (coupleEndpointsSigma (.epSelectR epA) (.epOffer epBL epBR))
           (coupleEndpointsSigma epA epBR) := .refl

def coupleOfferSelectL {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag} {A B : Type}
    (epAL : Endpoint Δ Payload P A) (epAR : Endpoint Δ Payload Q A) (epB : Endpoint Δ Payload (dual P) B) :
    AgdaId (coupleEndpoints (.epOffer epAL epAR) (.epSelectL epB))
           (coupleEndpoints epAL epB) := .refl

def coupleOfferSelectLSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag} {A B : Type}
    (epAL : Endpoint Δ Payload P A) (epAR : Endpoint Δ Payload Q A) (epB : Endpoint Δ Payload (dual P) B) :
    AgdaId (coupleEndpointsSigma (.epOffer epAL epAR) (.epSelectL epB))
           (coupleEndpointsSigma epAL epB) := .refl

def coupleOfferSelectR {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag} {A B : Type}
    (epAL : Endpoint Δ Payload P A) (epAR : Endpoint Δ Payload Q A) (epB : Endpoint Δ Payload (dual Q) B) :
    AgdaId (coupleEndpoints (.epOffer epAL epAR) (.epSelectR epB))
           (coupleEndpoints epAR epB) := .refl

def coupleOfferSelectRSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P Q : Proto Tag} {A B : Type}
    (epAL : Endpoint Δ Payload P A) (epAR : Endpoint Δ Payload Q A) (epB : Endpoint Δ Payload (dual Q) B) :
    AgdaId (coupleEndpointsSigma (.epOffer epAL epAR) (.epSelectR epB))
           (coupleEndpointsSigma epAR epB) := .refl

def coupleStepLeft {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type} {c : Cap}
    (h : CapMem c Δ) (op : Op c) (kA : Ret op → Endpoint Δ Payload P A) (epB : Endpoint Δ Payload (dual P) B) :
    AgdaId (coupleEndpoints (.epStep h op kA) epB)
           (.step h op (fun r => coupleEndpoints (kA r) epB)) :=
  match P, kA, epB with
  | .pEnd,       _, _ => .refl
  | .pSend _ _,  _, _ => .refl
  | .pRecv _ _,  _, _ => .refl
  | .pSelect _ _, _, _ => .refl
  | .pOffer _ _, _, _ => .refl

def coupleStepLeftSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type} {c : Cap}
    (h : CapMem c Δ) (op : Op c) (kA : Ret op → Endpoint Δ Payload P A) (epB : Endpoint Δ Payload (dual P) B) :
    AgdaId (coupleEndpointsSigma (.epStep h op kA) epB)
           (.step h op (fun r => coupleEndpointsSigma (kA r) epB)) :=
  match P, kA, epB with
  | .pEnd,       _, _ => .refl
  | .pSend _ _,  _, _ => .refl
  | .pRecv _ _,  _, _ => .refl
  | .pSelect _ _, _, _ => .refl
  | .pOffer _ _, _, _ => .refl

def couplePreservesClock {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (absent : CapMem .clockCap Δ → AgdaBot)
    (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B)
    (w : SimWorld) :
    AgdaId (runWorldPure (coupleEndpoints epA epB) w).proj₂.clock w.clock :=
  progPreservesClock absent (coupleEndpoints epA epB) w

def couplePreservesClockSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (absent : CapMem .clockCap Δ → AgdaBot)
    (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B)
    (w : SimWorld) :
    AgdaId (runWorldPureSigma (coupleEndpointsSigma epA epB) w).proj₂.clock w.clock :=
  progPreservesClock absent (coupleEndpointsSigma epA epB) w

def couplePreservesFs {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (absent : CapMem .fsCap Δ → AgdaBot)
    (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B)
    (w : SimWorld) :
    AgdaId (runWorldPure (coupleEndpoints epA epB) w).proj₂.fs w.fs :=
  progPreservesFs absent (coupleEndpoints epA epB) w

def couplePreservesFsSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (absent : CapMem .fsCap Δ → AgdaBot)
    (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B)
    (w : SimWorld) :
    AgdaId (runWorldPureSigma (coupleEndpointsSigma epA epB) w).proj₂.fs w.fs :=
  progPreservesFs absent (coupleEndpointsSigma epA epB) w

def couplePreservesNet {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (absent : CapMem .netCap Δ → AgdaBot)
    (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B)
    (w : SimWorld) :
    AgdaId (runWorldPure (coupleEndpoints epA epB) w).proj₂.net w.net :=
  progPreservesNet absent (coupleEndpoints epA epB) w

def couplePreservesNetSigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (absent : CapMem .netCap Δ → AgdaBot)
    (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B)
    (w : SimWorld) :
    AgdaId (runWorldPureSigma (coupleEndpointsSigma epA epB) w).proj₂.net w.net :=
  progPreservesNet absent (coupleEndpointsSigma epA epB) w

def couplePreservesTty {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (absent : CapMem .ttyCap Δ → AgdaBot)
    (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B)
    (w : SimWorld) :
    AgdaId (runWorldPure (coupleEndpoints epA epB) w).proj₂.tty w.tty :=
  progPreservesTty absent (coupleEndpoints epA epB) w

def couplePreservesTtySigma {Tag : Type} {Δ : List Cap} {Payload : Tag → Type} {P : Proto Tag} {A B : Type}
    (absent : CapMem .ttyCap Δ → AgdaBot)
    (epA : Endpoint Δ Payload P A)
    (epB : Endpoint Δ Payload (dual P) B)
    (w : SimWorld) :
    AgdaId (runWorldPureSigma (coupleEndpointsSigma epA epB) w).proj₂.tty w.tty :=
  progPreservesTty absent (coupleEndpointsSigma epA epB) w

end AgdaMirror.Protocol
