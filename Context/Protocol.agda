{-# OPTIONS --safe #-}
module Context.Protocol where

open import Data.Empty using (⊥)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Context.World
open import Context.WorldLaws using
  ( prog-preserves-clock; prog-preserves-fs; prog-preserves-net; prog-preserves-tty )

------------------------------------------------------------------------
-- §1 Typed Dual Session Protocol (`Proto Tag`, `dual`, `dual-involutive`)
------------------------------------------------------------------------

data Proto (Tag : Set) : Set where
  pEnd    : Proto Tag
  pSend   : Tag → Proto Tag → Proto Tag
  pRecv   : Tag → Proto Tag → Proto Tag
  pSelect : Proto Tag → Proto Tag → Proto Tag
  pOffer  : Proto Tag → Proto Tag → Proto Tag

dual : ∀ {Tag : Set} → Proto Tag → Proto Tag
dual pEnd          = pEnd
dual (pSend t P)   = pRecv t (dual P)
dual (pRecv t P)   = pSend t (dual P)
dual (pSelect P Q) = pOffer (dual P) (dual Q)
dual (pOffer P Q)  = pSelect (dual P) (dual Q)

dual-involutive : ∀ {Tag : Set} (P : Proto Tag) → dual (dual P) ≡ P
dual-involutive pEnd          = refl
dual-involutive (pSend t P)   = cong (pSend t) (dual-involutive P)
dual-involutive (pRecv t P)   = cong (pRecv t) (dual-involutive P)
dual-involutive (pSelect P Q) = cong₂ pSelect (dual-involutive P) (dual-involutive Q)
dual-involutive (pOffer P Q)  = cong₂ pOffer (dual-involutive P) (dual-involutive Q)

------------------------------------------------------------------------
-- §2 Closed-World Effectful Session Endpoints (`Endpoint Δ Payload P A`)
------------------------------------------------------------------------

data EndpointCore {Tag : Set} (Δ : List Cap) (Payload : Tag → Set) (A : Set) : Proto Tag → Set where
  epDone    : A → EndpointCore Δ Payload A pEnd
  epStep    : ∀ {P c} → c ∈ Δ → (op : Op c) → (Ret op → EndpointCore Δ Payload A P) → EndpointCore Δ Payload A P
  epSend    : ∀ {t P} → Payload t → EndpointCore Δ Payload A P → EndpointCore Δ Payload A (pSend t P)
  epRecv    : ∀ {t P} → (Payload t → EndpointCore Δ Payload A P) → EndpointCore Δ Payload A (pRecv t P)
  epSelectL : ∀ {P Q} → EndpointCore Δ Payload A P → EndpointCore Δ Payload A (pSelect P Q)
  epSelectR : ∀ {P Q} → EndpointCore Δ Payload A Q → EndpointCore Δ Payload A (pSelect P Q)
  epOffer   : ∀ {P Q} → EndpointCore Δ Payload A P → EndpointCore Δ Payload A Q → EndpointCore Δ Payload A (pOffer P Q)

Endpoint : ∀ {Tag : Set} → List Cap → (Tag → Set) → Proto Tag → Set → Set
Endpoint Δ Payload P A = EndpointCore Δ Payload A P

mapEndpoint : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {A B : Set} →
  (A → B) → Endpoint Δ Payload P A → Endpoint Δ Payload P B
mapEndpoint f (epDone a)        = epDone (f a)
mapEndpoint f (epStep h op k)   = epStep h op (λ r → mapEndpoint f (k r))
mapEndpoint f (epSend msg ep)   = epSend msg (mapEndpoint f ep)
mapEndpoint f (epRecv k)        = epRecv (λ msg → mapEndpoint f (k msg))
mapEndpoint f (epSelectL ep)    = epSelectL (mapEndpoint f ep)
mapEndpoint f (epSelectR ep)    = epSelectR (mapEndpoint f ep)
mapEndpoint f (epOffer epL epR) = epOffer (mapEndpoint f epL) (mapEndpoint f epR)

liftProgToEndpoint : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {A B : Set} →
  WorldProg Δ A → (A → Endpoint Δ Payload P B) → Endpoint Δ Payload P B
liftProgToEndpoint (pure a)      k = k a
liftProgToEndpoint (step h op f) k = epStep h op (λ r → liftProgToEndpoint (f r) k)

liftEndpoint : ∀ {Tag : Set} {Δ₁ Δ₂ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {A : Set} →
  Δ₁ ⊆ Δ₂ → Endpoint Δ₁ Payload P A → Endpoint Δ₂ Payload P A
liftEndpoint _   (epDone a)        = epDone a
liftEndpoint sub (epStep h op k)   = epStep (sub h) op (λ r → liftEndpoint sub (k r))
liftEndpoint sub (epSend msg ep)   = epSend msg (liftEndpoint sub ep)
liftEndpoint sub (epRecv k)        = epRecv (λ msg → liftEndpoint sub (k msg))
liftEndpoint sub (epSelectL ep)    = epSelectL (liftEndpoint sub ep)
liftEndpoint sub (epSelectR ep)    = epSelectR (liftEndpoint sub ep)
liftEndpoint sub (epOffer epL epR) = epOffer (liftEndpoint sub epL) (liftEndpoint sub epR)

------------------------------------------------------------------------
-- §3 Deadlock-Free Closed-World Session Cut (`coupleEndpoints`)
------------------------------------------------------------------------

private
  data ReadyEndpoint {Tag : Set} (Δ : List Cap) (Payload : Tag → Set) (A : Set) : Proto Tag → Set where
    rDone    : A → ReadyEndpoint Δ Payload A pEnd
    rSend    : ∀ {t P} → Payload t → Endpoint Δ Payload P A → ReadyEndpoint Δ Payload A (pSend t P)
    rRecv    : ∀ {t P} → (Payload t → Endpoint Δ Payload P A) → ReadyEndpoint Δ Payload A (pRecv t P)
    rSelectL : ∀ {P Q} → Endpoint Δ Payload P A → ReadyEndpoint Δ Payload A (pSelect P Q)
    rSelectR : ∀ {P Q} → Endpoint Δ Payload Q A → ReadyEndpoint Δ Payload A (pSelect P Q)
    rOffer   : ∀ {P Q} → Endpoint Δ Payload P A → Endpoint Δ Payload Q A → ReadyEndpoint Δ Payload A (pOffer P Q)

  peelEndpoint : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {A R : Set} →
    (ReadyEndpoint Δ Payload A P → WorldProg Δ R) → Endpoint Δ Payload P A → WorldProg Δ R
  peelEndpoint cont (epDone a)        = cont (rDone a)
  peelEndpoint cont (epStep h op k)   = step h op (λ r → peelEndpoint cont (k r))
  peelEndpoint cont (epSend msg ep)   = cont (rSend msg ep)
  peelEndpoint cont (epRecv k)        = cont (rRecv k)
  peelEndpoint cont (epSelectL ep)    = cont (rSelectL ep)
  peelEndpoint cont (epSelectR ep)    = cont (rSelectR ep)
  peelEndpoint cont (epOffer epL epR) = cont (rOffer epL epR)

  doneReady : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {A B : Set} →
    ReadyEndpoint Δ Payload A pEnd → ReadyEndpoint Δ Payload B pEnd → WorldProg Δ (A × B)
  doneReady (rDone a) (rDone b) = pure (a , b)

  mutual
    coupleProto : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {A B : Set} →
      (P : Proto Tag) → Endpoint Δ Payload P A → Endpoint Δ Payload (dual P) B → WorldProg Δ (A × B)
    coupleProto pEnd          epA epB = peelEndpoint (λ rA → peelEndpoint (doneReady rA) epB) epA
    coupleProto (pSend _ P′)  epA epB = peelEndpoint (λ rA → peelEndpoint (sendReady P′ rA) epB) epA
    coupleProto (pRecv _ P′)  epA epB = peelEndpoint (λ rA → peelEndpoint (recvReady P′ rA) epB) epA
    coupleProto (pSelect P Q) epA epB = peelEndpoint (λ rA → peelEndpoint (selectReady P Q rA) epB) epA
    coupleProto (pOffer P Q)  epA epB = peelEndpoint (λ rA → peelEndpoint (offerReady P Q rA) epB) epA

    sendReady : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {t : Tag} {A B : Set}
      (P′ : Proto Tag) →
      ReadyEndpoint Δ Payload A (pSend t P′) →
      ReadyEndpoint Δ Payload B (pRecv t (dual P′)) →
      WorldProg Δ (A × B)
    sendReady P′ (rSend msg epA′) (rRecv kB) = coupleProto P′ epA′ (kB msg)

    recvReady : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {t : Tag} {A B : Set}
      (P′ : Proto Tag) →
      ReadyEndpoint Δ Payload A (pRecv t P′) →
      ReadyEndpoint Δ Payload B (pSend t (dual P′)) →
      WorldProg Δ (A × B)
    recvReady P′ (rRecv kA) (rSend msg epB′) = coupleProto P′ (kA msg) epB′

    selectReady : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {A B : Set}
      (P Q : Proto Tag) →
      ReadyEndpoint Δ Payload A (pSelect P Q) →
      ReadyEndpoint Δ Payload B (pOffer (dual P) (dual Q)) →
      WorldProg Δ (A × B)
    selectReady P _ (rSelectL epA′) (rOffer epBL _)    = coupleProto P epA′ epBL
    selectReady _ Q (rSelectR epA′) (rOffer _    epBR) = coupleProto Q epA′ epBR

    offerReady : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {A B : Set}
      (P Q : Proto Tag) →
      ReadyEndpoint Δ Payload A (pOffer P Q) →
      ReadyEndpoint Δ Payload B (pSelect (dual P) (dual Q)) →
      WorldProg Δ (A × B)
    offerReady P _ (rOffer epAL _)    (rSelectL epB′) = coupleProto P epAL epB′
    offerReady _ Q (rOffer _    epAR) (rSelectR epB′) = coupleProto Q epAR epB′

coupleEndpoints : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {A B : Set} →
  Endpoint Δ Payload P A →
  Endpoint Δ Payload (dual P) B →
  WorldProg Δ (A × B)
coupleEndpoints {P = P} epA epB = coupleProto P epA epB

------------------------------------------------------------------------
-- §4 Multi-`ReactiveApp` Closed-World Composition
------------------------------------------------------------------------

private
  stepOptService : ∀ {Δᵢ Δ : List Cap} {Sᵢ : Set} →
    Δᵢ ⊆ Δ → ReactiveApp Δᵢ Sᵢ → Sᵢ → Maybe (Event Δᵢ) → WorldProg Δ (Sᵢ ⊎ ExitCode)
  stepOptService _   _   sᵢ nothing    = pure (inj₁ sᵢ)
  stepOptService sub app sᵢ (just evᵢ) = liftWorld sub (onStep app evᵢ sᵢ)

  finishSecondPair : ∀ {S₁ S₂ : Set} → S₁ → (S₂ ⊎ ExitCode) → (S₁ × S₂) ⊎ ExitCode
  finishSecondPair x (inj₁ y)    = inj₁ (x , y)
  finishSecondPair _ (inj₂ code) = inj₂ code

  continueSecondService : ∀ {Δ₂ Δ : List Cap} {S₁ S₂ : Set} →
    Δ₂ ⊆ Δ → ReactiveApp Δ₂ S₂ → S₂ → Maybe (Event Δ₂) → (S₁ ⊎ ExitCode) → WorldProg Δ ((S₁ × S₂) ⊎ ExitCode)
  continueSecondService _    _    _  _    (inj₂ code) = pure (inj₂ code)
  continueSecondService sub₂ app₂ s₂ mev₂ (inj₁ s₁′) =
    mapWorld (finishSecondPair s₁′) (stepOptService sub₂ app₂ s₂ mev₂)

  mergeTurnOutcomes : ∀ {S₁ S₂ : Set} → (S₁ ⊎ ExitCode) → (S₂ ⊎ ExitCode) → (S₁ × S₂) ⊎ ExitCode
  mergeTurnOutcomes (inj₂ code) _           = inj₂ code
  mergeTurnOutcomes (inj₁ _)    (inj₂ code) = inj₂ code
  mergeTurnOutcomes (inj₁ s₁′)  (inj₁ s₂′)  = inj₁ (s₁′ , s₂′)

composeReactive : ∀ {Δ₁ Δ₂ Δ : List Cap} {S₁ S₂ : Set} →
  Δ₁ ⊆ Δ →
  Δ₂ ⊆ Δ →
  ReactiveApp Δ₁ S₁ →
  ReactiveApp Δ₂ S₂ →
  (Event Δ → Maybe (Event Δ₁) × Maybe (Event Δ₂)) →
  ReactiveApp Δ (S₁ × S₂)
composeReactive sub₁ sub₂ app₁ app₂ routeEv =
  reactiveApp
    (liftWorld sub₁ (init app₁) >>=w λ s₁ →
     liftWorld sub₂ (init app₂) >>=w λ s₂ →
     pure (s₁ , s₂))
    (λ ev st →
      let routed = routeEv ev
      in stepOptService sub₁ app₁ (proj₁ st) (proj₁ routed) >>=w
         continueSecondService sub₂ app₂ (proj₂ st) (proj₂ routed))

coupleReactiveTurn : ∀ {Tag : Set} {Δ₁ Δ₂ Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {S₁ S₂ : Set} →
  Δ₁ ⊆ Δ →
  Δ₂ ⊆ Δ →
  (Event Δ → S₁ → Endpoint Δ₁ Payload P (S₁ ⊎ ExitCode)) →
  (S₂ → Endpoint Δ₂ Payload (dual P) (S₂ ⊎ ExitCode)) →
  Event Δ →
  (S₁ × S₂) →
  WorldProg Δ ((S₁ × S₂) ⊎ ExitCode)
coupleReactiveTurn sub₁ sub₂ turn₁ turn₂ ev st =
  mapWorld (λ r → mergeTurnOutcomes (proj₁ r) (proj₂ r))
    (coupleEndpoints
      (liftEndpoint sub₁ (turn₁ ev (proj₁ st)))
      (liftEndpoint sub₂ (turn₂ (proj₂ st))))

coupleReactive : ∀ {Tag : Set} {Δ₁ Δ₂ Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {S₁ S₂ : Set} →
  Δ₁ ⊆ Δ →
  Δ₂ ⊆ Δ →
  WorldProg Δ₁ S₁ →
  WorldProg Δ₂ S₂ →
  (Event Δ → S₁ → Endpoint Δ₁ Payload P (S₁ ⊎ ExitCode)) →
  (S₂ → Endpoint Δ₂ Payload (dual P) (S₂ ⊎ ExitCode)) →
  ReactiveApp Δ (S₁ × S₂)
coupleReactive sub₁ sub₂ init₁ init₂ turn₁ turn₂ =
  reactiveApp
    (liftWorld sub₁ init₁ >>=w λ s₁ →
     liftWorld sub₂ init₂ >>=w λ s₂ →
     pure (s₁ , s₂))
    (coupleReactiveTurn sub₁ sub₂ turn₁ turn₂)

------------------------------------------------------------------------
-- §5 Universal Algebraic & Capability Frame Laws (`--safe`, Zero Funext)
------------------------------------------------------------------------

couple-done : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {A B : Set}
  (a : A) (b : B) →
  coupleEndpoints {Tag} {Δ} {Payload} (epDone a) (epDone b) ≡ pure (a , b)
couple-done _ _ = refl

couple-send-recv : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {t : Tag} {P : Proto Tag} {A B : Set}
  (msg : Payload t)
  (epA : Endpoint Δ Payload P A)
  (kB  : Payload t → Endpoint Δ Payload (dual P) B) →
  coupleEndpoints (epSend msg epA) (epRecv kB) ≡ coupleEndpoints epA (kB msg)
couple-send-recv _ _ _ = refl

couple-recv-send : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {t : Tag} {P : Proto Tag} {A B : Set}
  (kA  : Payload t → Endpoint Δ Payload P A)
  (msg : Payload t)
  (epB : Endpoint Δ Payload (dual P) B) →
  coupleEndpoints (epRecv kA) (epSend msg epB) ≡ coupleEndpoints (kA msg) epB
couple-recv-send _ _ _ = refl

couple-selectL-offer : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P Q : Proto Tag} {A B : Set}
  (epA  : Endpoint Δ Payload P A)
  (epBL : Endpoint Δ Payload (dual P) B)
  (epBR : Endpoint Δ Payload (dual Q) B) →
  coupleEndpoints (epSelectL epA) (epOffer epBL epBR) ≡ coupleEndpoints epA epBL
couple-selectL-offer _ _ _ = refl

couple-selectR-offer : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P Q : Proto Tag} {A B : Set}
  (epA  : Endpoint Δ Payload Q A)
  (epBL : Endpoint Δ Payload (dual P) B)
  (epBR : Endpoint Δ Payload (dual Q) B) →
  coupleEndpoints (epSelectR epA) (epOffer epBL epBR) ≡ coupleEndpoints epA epBR
couple-selectR-offer _ _ _ = refl

couple-offer-selectL : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P Q : Proto Tag} {A B : Set}
  (epAL : Endpoint Δ Payload P A)
  (epAR : Endpoint Δ Payload Q A)
  (epB  : Endpoint Δ Payload (dual P) B) →
  coupleEndpoints (epOffer epAL epAR) (epSelectL epB) ≡ coupleEndpoints epAL epB
couple-offer-selectL _ _ _ = refl

couple-offer-selectR : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P Q : Proto Tag} {A B : Set}
  (epAL : Endpoint Δ Payload P A)
  (epAR : Endpoint Δ Payload Q A)
  (epB  : Endpoint Δ Payload (dual Q) B) →
  coupleEndpoints (epOffer epAL epAR) (epSelectR epB) ≡ coupleEndpoints epAR epB
couple-offer-selectR _ _ _ = refl

couple-step-left : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {A B : Set} {c : Cap}
  (h   : c ∈ Δ)
  (op  : Op c)
  (kA  : Ret op → Endpoint Δ Payload P A)
  (epB : Endpoint Δ Payload (dual P) B) →
  coupleEndpoints (epStep h op kA) epB ≡ step h op (λ r → coupleEndpoints (kA r) epB)
couple-step-left {P = pEnd}        _ _ _ _ = refl
couple-step-left {P = pSend _ _}   _ _ _ _ = refl
couple-step-left {P = pRecv _ _}   _ _ _ _ = refl
couple-step-left {P = pSelect _ _} _ _ _ _ = refl
couple-step-left {P = pOffer _ _}  _ _ _ _ = refl

couple-preserves-clock : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {A B : Set} →
  (clockCap ∈ Δ → ⊥) →
  (epA : Endpoint Δ Payload P A) →
  (epB : Endpoint Δ Payload (dual P) B) →
  ∀ (w : SimWorld) →
  clock (proj₂ (runWorldPure (coupleEndpoints epA epB) w)) ≡ clock w
couple-preserves-clock absent epA epB = prog-preserves-clock absent (coupleEndpoints epA epB)

couple-preserves-fs : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {A B : Set} →
  (fsCap ∈ Δ → ⊥) →
  (epA : Endpoint Δ Payload P A) →
  (epB : Endpoint Δ Payload (dual P) B) →
  ∀ (w : SimWorld) →
  fs (proj₂ (runWorldPure (coupleEndpoints epA epB) w)) ≡ fs w
couple-preserves-fs absent epA epB = prog-preserves-fs absent (coupleEndpoints epA epB)

couple-preserves-net : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {A B : Set} →
  (netCap ∈ Δ → ⊥) →
  (epA : Endpoint Δ Payload P A) →
  (epB : Endpoint Δ Payload (dual P) B) →
  ∀ (w : SimWorld) →
  net (proj₂ (runWorldPure (coupleEndpoints epA epB) w)) ≡ net w
couple-preserves-net absent epA epB = prog-preserves-net absent (coupleEndpoints epA epB)

couple-preserves-tty : ∀ {Tag : Set} {Δ : List Cap} {Payload : Tag → Set} {P : Proto Tag} {A B : Set} →
  (ttyCap ∈ Δ → ⊥) →
  (epA : Endpoint Δ Payload P A) →
  (epB : Endpoint Δ Payload (dual P) B) →
  ∀ (w : SimWorld) →
  tty (proj₂ (runWorldPure (coupleEndpoints epA epB) w)) ≡ tty w
couple-preserves-tty absent epA epB = prog-preserves-tty absent (coupleEndpoints epA epB)
