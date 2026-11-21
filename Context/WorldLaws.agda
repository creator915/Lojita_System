{-# OPTIONS --safe #-}
module Context.WorldLaws where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Context.Tools.Clock using (SimClock)
open import Context.Tools.FsSandbox using (VirtualFs)
open import Context.Tools.GitSandbox using (PureGitRepo)
open import Context.World

------------------------------------------------------------------------
-- §1 `WorldProg` Monad Laws (Syntactic & Semantic under `runWorldPure`)
------------------------------------------------------------------------

bind-pure-left : ∀ {Δ A B} (a : A) (k : A → WorldProg Δ B) →
  (pure a >>=w k) ≡ k a
bind-pure-left _ _ = refl

bind-pure-left-run : ∀ {Δ A B} (a : A) (k : A → WorldProg Δ B) (w : SimWorld) →
  runWorldPure (pure a >>=w k) w ≡ runWorldPure (k a) w
bind-pure-left-run _ _ _ = refl

bind-pure-right-run : ∀ {Δ A} (m : WorldProg Δ A) (w : SimWorld) →
  runWorldPure (m >>=w pure) w ≡ runWorldPure m w
bind-pure-right-run (pure _)      _ = refl
bind-pure-right-run (step _ op k) w =
  let rw = stepWorldPure op w
  in bind-pure-right-run (k (proj₁ rw)) (proj₂ rw)

runWorldPure-bind : ∀ {Δ A B} (m : WorldProg Δ A) (k : A → WorldProg Δ B) (w : SimWorld) →
  runWorldPure (m >>=w k) w ≡
  (let r = runWorldPure m w in runWorldPure (k (proj₁ r)) (proj₂ r))
runWorldPure-bind (pure _)      _ _ = refl
runWorldPure-bind (step _ op f) k w =
  let rw = stepWorldPure op w
  in runWorldPure-bind (f (proj₁ rw)) k (proj₂ rw)

bind-assoc-run : ∀ {Δ A B C}
  (m : WorldProg Δ A) (f : A → WorldProg Δ B) (g : B → WorldProg Δ C) (w : SimWorld) →
  runWorldPure ((m >>=w f) >>=w g) w ≡ runWorldPure (m >>=w (λ x → f x >>=w g)) w
bind-assoc-run (pure _)      _ _ _ = refl
bind-assoc-run (step _ op k) f g w =
  let rw = stepWorldPure op w
  in bind-assoc-run (k (proj₁ rw)) f g (proj₂ rw)

mapWorld-pure : ∀ {Δ A B} (f : A → B) (a : A) →
  mapWorld {Δ} f (pure a) ≡ pure (f a)
mapWorld-pure _ _ = refl

mapWorld-run : ∀ {Δ A B} (f : A → B) (m : WorldProg Δ A) (w : SimWorld) →
  runWorldPure (mapWorld f m) w ≡ (f (proj₁ (runWorldPure m w)) , proj₂ (runWorldPure m w))
mapWorld-run _ (pure _)      _ = refl
mapWorld-run f (step _ op k) w =
  let rw = stepWorldPure op w
  in mapWorld-run f (k (proj₁ rw)) (proj₂ rw)

------------------------------------------------------------------------
-- §2 Capability Subtyping (`liftWorld`) Semantics Preservation Laws
------------------------------------------------------------------------

liftWorld-pure : ∀ {Δ₁ Δ₂ A} (sub : Δ₁ ⊆ Δ₂) (a : A) →
  liftWorld sub (pure a) ≡ pure a
liftWorld-pure _ _ = refl

liftWorld-preserves-run : ∀ {Δ₁ Δ₂ A} (sub : Δ₁ ⊆ Δ₂) (m : WorldProg Δ₁ A) (w : SimWorld) →
  runWorldPure (liftWorld sub m) w ≡ runWorldPure m w
liftWorld-preserves-run _   (pure _)      _ = refl
liftWorld-preserves-run sub (step _ op k) w =
  let rw = stepWorldPure op w
  in liftWorld-preserves-run sub (k (proj₁ rw)) (proj₂ rw)

liftWorld-bind-run : ∀ {Δ₁ Δ₂ A B} (sub : Δ₁ ⊆ Δ₂)
  (m : WorldProg Δ₁ A) (k : A → WorldProg Δ₁ B) (w : SimWorld) →
  runWorldPure (liftWorld sub (m >>=w k)) w ≡
  runWorldPure (liftWorld sub m >>=w (λ a → liftWorld sub (k a))) w
liftWorld-bind-run sub m k w =
  trans (liftWorld-preserves-run sub (m >>=w k) w)
    (trans (runWorldPure-bind m k w)
      (sym (trans (runWorldPure-bind (liftWorld sub m) (λ a → liftWorld sub (k a)) w)
        (trans (cong (λ r → runWorldPure (liftWorld sub (k (proj₁ r))) (proj₂ r))
                     (liftWorld-preserves-run sub m w))
               (liftWorld-preserves-run sub (k (proj₁ (runWorldPure m w))) (proj₂ (runWorldPure m w)))))))

------------------------------------------------------------------------
-- §3 Whole-Program Capability Non-Interference (Multi-Step Frame Laws!)
--    Any `WorldProg Δ A` whose capability list `Δ` excludes `c`
--    provably leaves `c`'s component in `SimWorld` 100% untouched!
------------------------------------------------------------------------

eqCap-refl : ∀ (c : Cap) → eqCap c c ≡ true
eqCap-refl clockCap = refl
eqCap-refl envCap   = refl
eqCap-refl ttyCap   = refl
eqCap-refl fsCap    = refl
eqCap-refl netCap   = refl
eqCap-refl gitCap   = refl
eqCap-refl webCap   = refl

notHasCap⇒∉ : ∀ {c Δ} → hasCap c Δ ≡ false → c ∈ Δ → ⊥
notHasCap⇒∉ {c} {_ ∷ ds} eq here =
  true≢false (trans (sym (eqCap-refl c)) (or-false-left (eqCap c c) (hasCap c ds) eq))
  where
    or-false-left : ∀ (a b : Bool) → (a ∨ b) ≡ false → a ≡ false
    or-false-left false _ _  = refl
    or-false-left true  _ ()

    true≢false : true ≡ false → ⊥
    true≢false ()
notHasCap⇒∉ {c} {d ∷ ds} eq (there m∈) =
  notHasCap⇒∉ (or-false-right (eqCap c d) (hasCap c ds) eq) m∈
  where
    or-false-right : ∀ (a b : Bool) → (a ∨ b) ≡ false → b ≡ false
    or-false-right false _ r = r
    or-false-right true  _ ()

step-preserves-clock : ∀ {c} → (c ≡ clockCap → ⊥) → (op : Op c) → ∀ (w : SimWorld) →
  clock (proj₂ (stepWorldPure op w)) ≡ clock w
step-preserves-clock neq opNowMono         _ = ⊥-elim (neq refl)
step-preserves-clock neq opNowWall         _ = ⊥-elim (neq refl)
step-preserves-clock neq (opSleepMs _)     _ = ⊥-elim (neq refl)
step-preserves-clock _   opGetProgName     _ = refl
step-preserves-clock _   opGetArgs         _ = refl
step-preserves-clock _   (opLookupEnv _)   _ = refl
step-preserves-clock _   opReadStdinAll    _ = refl
step-preserves-clock _   opReadStdinLine   _ = refl
step-preserves-clock _   opIsTTYStdin      _ = refl
step-preserves-clock _   opIsTTYStdout     _ = refl
step-preserves-clock _   opIsTTYStderr     _ = refl
step-preserves-clock _   opTermSize        _ = refl
step-preserves-clock _   (opWriteStdout _) _ = refl
step-preserves-clock _   (opWriteStderr _) _ = refl
step-preserves-clock _   opReadTTYByte     _ = refl
step-preserves-clock _   (opReadFile _)    _ = refl
step-preserves-clock _   (opWriteFile _ _) _ = refl
step-preserves-clock _   (opMkdir _ _)     _ = refl
step-preserves-clock _   (opSymlink _ _)   _ = refl
step-preserves-clock _   (opUnlink _)      _ = refl
step-preserves-clock _   (opStat _)        _ = refl
step-preserves-clock _   (opTcpExchange _ _ _ _ _) _ = refl
step-preserves-clock _   (opTlsExchange _ _ _ _ _ _ _) _ = refl
step-preserves-clock _   (opGitStep _)     _ = refl
step-preserves-clock _   opGitSummary      _ = refl
step-preserves-clock _   opWebViewport     _ = refl
step-preserves-clock _   (opWebSetTitle _) _ = refl
step-preserves-clock _   (opWebDrawScene _) _ = refl
step-preserves-clock _   (opWebHitTest _ _) _ = refl
step-preserves-clock _   opWebPollInput    _ = refl

step-preserves-fs : ∀ {c} → (c ≡ fsCap → ⊥) → (op : Op c) → ∀ (w : SimWorld) →
  fs (proj₂ (stepWorldPure op w)) ≡ fs w
step-preserves-fs _   opNowMono         _ = refl
step-preserves-fs _   opNowWall         _ = refl
step-preserves-fs _   (opSleepMs _)     _ = refl
step-preserves-fs _   opGetProgName     _ = refl
step-preserves-fs _   opGetArgs         _ = refl
step-preserves-fs _   (opLookupEnv _)   _ = refl
step-preserves-fs _   opReadStdinAll    _ = refl
step-preserves-fs _   opReadStdinLine   _ = refl
step-preserves-fs _   opIsTTYStdin      _ = refl
step-preserves-fs _   opIsTTYStdout     _ = refl
step-preserves-fs _   opIsTTYStderr     _ = refl
step-preserves-fs _   opTermSize        _ = refl
step-preserves-fs _   (opWriteStdout _) _ = refl
step-preserves-fs _   (opWriteStderr _) _ = refl
step-preserves-fs _   opReadTTYByte     _ = refl
step-preserves-fs neq (opReadFile _)    _ = ⊥-elim (neq refl)
step-preserves-fs neq (opWriteFile _ _) _ = ⊥-elim (neq refl)
step-preserves-fs neq (opMkdir _ _)     _ = ⊥-elim (neq refl)
step-preserves-fs neq (opSymlink _ _)   _ = ⊥-elim (neq refl)
step-preserves-fs neq (opUnlink _)      _ = ⊥-elim (neq refl)
step-preserves-fs neq (opStat _)        _ = ⊥-elim (neq refl)
step-preserves-fs _   (opTcpExchange _ _ _ _ _) _ = refl
step-preserves-fs _   (opTlsExchange _ _ _ _ _ _ _) _ = refl
step-preserves-fs _   (opGitStep _)     _ = refl
step-preserves-fs _   opGitSummary      _ = refl
step-preserves-fs _   opWebViewport     _ = refl
step-preserves-fs _   (opWebSetTitle _) _ = refl
step-preserves-fs _   (opWebDrawScene _) _ = refl
step-preserves-fs _   (opWebHitTest _ _) _ = refl
step-preserves-fs _   opWebPollInput    _ = refl

step-preserves-net : ∀ {c} → (c ≡ netCap → ⊥) → (op : Op c) → ∀ (w : SimWorld) →
  net (proj₂ (stepWorldPure op w)) ≡ net w
step-preserves-net _   opNowMono         _ = refl
step-preserves-net _   opNowWall         _ = refl
step-preserves-net _   (opSleepMs _)     _ = refl
step-preserves-net _   opGetProgName     _ = refl
step-preserves-net _   opGetArgs         _ = refl
step-preserves-net _   (opLookupEnv _)   _ = refl
step-preserves-net _   opReadStdinAll    _ = refl
step-preserves-net _   opReadStdinLine   _ = refl
step-preserves-net _   opIsTTYStdin      _ = refl
step-preserves-net _   opIsTTYStdout     _ = refl
step-preserves-net _   opIsTTYStderr     _ = refl
step-preserves-net _   opTermSize        _ = refl
step-preserves-net _   (opWriteStdout _) _ = refl
step-preserves-net _   (opWriteStderr _) _ = refl
step-preserves-net _   opReadTTYByte     _ = refl
step-preserves-net _   (opReadFile _)    _ = refl
step-preserves-net _   (opWriteFile _ _) _ = refl
step-preserves-net _   (opMkdir _ _)     _ = refl
step-preserves-net _   (opSymlink _ _)   _ = refl
step-preserves-net _   (opUnlink _)      _ = refl
step-preserves-net _   (opStat _)        _ = refl
step-preserves-net neq (opTcpExchange _ _ _ _ _) _ = ⊥-elim (neq refl)
step-preserves-net neq (opTlsExchange _ _ _ _ _ _ _) _ = ⊥-elim (neq refl)
step-preserves-net _   (opGitStep _)     _ = refl
step-preserves-net _   opGitSummary      _ = refl
step-preserves-net _   opWebViewport     _ = refl
step-preserves-net _   (opWebSetTitle _) _ = refl
step-preserves-net _   (opWebDrawScene _) _ = refl
step-preserves-net _   (opWebHitTest _ _) _ = refl
step-preserves-net _   opWebPollInput    _ = refl

step-preserves-tty : ∀ {c} → (c ≡ ttyCap → ⊥) → (op : Op c) → ∀ (w : SimWorld) →
  tty (proj₂ (stepWorldPure op w)) ≡ tty w
step-preserves-tty _   opNowMono         _ = refl
step-preserves-tty _   opNowWall         _ = refl
step-preserves-tty _   (opSleepMs _)     _ = refl
step-preserves-tty _   opGetProgName     _ = refl
step-preserves-tty _   opGetArgs         _ = refl
step-preserves-tty _   (opLookupEnv _)   _ = refl
step-preserves-tty _   opReadStdinAll    _ = refl
step-preserves-tty _   opReadStdinLine   _ = refl
step-preserves-tty neq opIsTTYStdin      _ = ⊥-elim (neq refl)
step-preserves-tty neq opIsTTYStdout     _ = ⊥-elim (neq refl)
step-preserves-tty neq opIsTTYStderr     _ = ⊥-elim (neq refl)
step-preserves-tty neq opTermSize        _ = ⊥-elim (neq refl)
step-preserves-tty neq (opWriteStdout _) _ = ⊥-elim (neq refl)
step-preserves-tty neq (opWriteStderr _) _ = ⊥-elim (neq refl)
step-preserves-tty neq opReadTTYByte     _ = ⊥-elim (neq refl)
step-preserves-tty _   (opReadFile _)    _ = refl
step-preserves-tty _   (opWriteFile _ _) _ = refl
step-preserves-tty _   (opMkdir _ _)     _ = refl
step-preserves-tty _   (opSymlink _ _)   _ = refl
step-preserves-tty _   (opUnlink _)      _ = refl
step-preserves-tty _   (opStat _)        _ = refl
step-preserves-tty _   (opTcpExchange _ _ _ _ _) _ = refl
step-preserves-tty _   (opTlsExchange _ _ _ _ _ _ _) _ = refl
step-preserves-tty _   (opGitStep _)     _ = refl
step-preserves-tty _   opGitSummary      _ = refl
step-preserves-tty _   opWebViewport     _ = refl
step-preserves-tty _   (opWebSetTitle _) _ = refl
step-preserves-tty _   (opWebDrawScene _) _ = refl
step-preserves-tty _   (opWebHitTest _ _) _ = refl
step-preserves-tty _   opWebPollInput    _ = refl

prog-preserves-clock : ∀ {Δ A} → (clockCap ∈ Δ → ⊥) → (m : WorldProg Δ A) → ∀ (w : SimWorld) →
  clock (proj₂ (runWorldPure m w)) ≡ clock w
prog-preserves-clock _      (pure _)      _ = refl
prog-preserves-clock absent (step h op k) w =
  let rw = stepWorldPure op w
  in trans (prog-preserves-clock absent (k (proj₁ rw)) (proj₂ rw))
           (step-preserves-clock (λ eq → absent (subst∈ eq h)) op w)
  where
    subst∈ : ∀ {x y cs} → x ≡ y → x ∈ cs → y ∈ cs
    subst∈ refl m∈ = m∈

prog-preserves-fs : ∀ {Δ A} → (fsCap ∈ Δ → ⊥) → (m : WorldProg Δ A) → ∀ (w : SimWorld) →
  fs (proj₂ (runWorldPure m w)) ≡ fs w
prog-preserves-fs _      (pure _)      _ = refl
prog-preserves-fs absent (step h op k) w =
  let rw = stepWorldPure op w
  in trans (prog-preserves-fs absent (k (proj₁ rw)) (proj₂ rw))
           (step-preserves-fs (λ eq → absent (subst∈ eq h)) op w)
  where
    subst∈ : ∀ {x y cs} → x ≡ y → x ∈ cs → y ∈ cs
    subst∈ refl m∈ = m∈

prog-preserves-net : ∀ {Δ A} → (netCap ∈ Δ → ⊥) → (m : WorldProg Δ A) → ∀ (w : SimWorld) →
  net (proj₂ (runWorldPure m w)) ≡ net w
prog-preserves-net _      (pure _)      _ = refl
prog-preserves-net absent (step h op k) w =
  let rw = stepWorldPure op w
  in trans (prog-preserves-net absent (k (proj₁ rw)) (proj₂ rw))
           (step-preserves-net (λ eq → absent (subst∈ eq h)) op w)
  where
    subst∈ : ∀ {x y cs} → x ≡ y → x ∈ cs → y ∈ cs
    subst∈ refl m∈ = m∈

prog-preserves-tty : ∀ {Δ A} → (ttyCap ∈ Δ → ⊥) → (m : WorldProg Δ A) → ∀ (w : SimWorld) →
  tty (proj₂ (runWorldPure m w)) ≡ tty w
prog-preserves-tty _      (pure _)      _ = refl
prog-preserves-tty absent (step h op k) w =
  let rw = stepWorldPure op w
  in trans (prog-preserves-tty absent (k (proj₁ rw)) (proj₂ rw))
           (step-preserves-tty (λ eq → absent (subst∈ eq h)) op w)
  where
    subst∈ : ∀ {x y cs} → x ≡ y → x ∈ cs → y ∈ cs
    subst∈ refl m∈ = m∈

------------------------------------------------------------------------
-- §4 Reactive Event-Trace Concatenation Law (`runReactiveSteps` on `++`)
------------------------------------------------------------------------

continueReactiveAfter : ∀ {Δ S} → ReactiveApp Δ S → List (Event Δ) → S ⊎ ExitCode → SimWorld → (S ⊎ ExitCode) × SimWorld
continueReactiveAfter a es (inj₁ s′)   w′ = runReactiveSteps a s′ es w′
continueReactiveAfter _ _  (inj₂ code) w′ = inj₂ code , w′

runReactiveSteps-++ : ∀ {Δ S} (app : ReactiveApp Δ S) (s : S)
  (evs₁ evs₂ : List (Event Δ)) (w : SimWorld) →
  runReactiveSteps app s (evs₁ ++ evs₂) w ≡
  (let r₁ = runReactiveSteps app s evs₁ w
   in continueReactiveAfter app evs₂ (proj₁ r₁) (proj₂ r₁))
runReactiveSteps-++ _   _ []       _    _ = refl
runReactiveSteps-++ app s (e ∷ es) evs₂ w with runWorldPure (onStep app e s) w
... | inj₁ s′   , w′ = runReactiveSteps-++ app s′ es evs₂ w′
... | inj₂ code , w′ = refl
