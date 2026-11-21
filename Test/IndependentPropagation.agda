{-# OPTIONS --guardedness #-}
module Test.IndependentPropagation where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; [_])
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Ownership hiding (Home; Name; set; open′)
open import Code
open import Code.Transport
open import Code.Harness
open import Code.NodeTransport using (moduleQName)
open import Code.Render using (render)
open import Test.HarnessPure using (q; taskX; homeX; impl; pureEnv; scriptedAI; checks; pureDump)

private
  -- The scripted child has already checked its witness. Its durable home
  -- still contains the original child module, as required on non-ok verdicts.
  reason = "the port requires primitive string reflexivity"

  witness : Code
  witness = code (q "Unprovable") []
    (import′ (q "A") false everything [] ∷ import′ (moduleQName "Context.Taboo") true everything []
     ∷ sig plain "witness" (def (moduleQName "Context.Taboo.SafeTaboo"))
     ∷ fun plain "witness" [ clause (head (moduleQName "Unprovable.witness") [])
       (rhs (app (con (moduleQName "Context.Taboo.SafeTaboo.taboo-primStrRefl"))
                 (vis (def (moduleQName "A.requiredRefl"))))) [] ] ∷ [])

  childChannel : Offer ChildS
  Running.onCall childChannel _ = just (independent reason witness) , childChannel
  Running.onStop childChannel = node [] , impl "A" , [] , [] , tt

  kids : Slots
  kids = [ "A" , awake ]
  candidate = impl "X"

  parent : NodeState
  parent = nodeState taskX (proj₁ homeX) [] candidate (just (plan "factor A" [] [])) ""
             WaitingKids (node [] , tt , homeX)

  result : Maybe Verdict × Σ (Slots × NodeState) (λ j → Models (Work (proj₁ j)))
  result = machineCall (pureEnv [] []) (oneTurn kids parent)
    (provide [] (daemon (checks [])) tt , provide [] (daemon pureDump) tt ,
     provide [] (daemon (scriptedAI [])) tt , childChannel , homeX) tt

  nextSlots = proj₁ (proj₁ (proj₂ result))
  next = proj₂ (proj₁ (proj₂ result))
  resources = proj₂ (proj₂ result)

  stoppedChild : (ks : Slots) → Models (Work ks) → Maybe Code
  stoppedChild ((_ , sleeping sh _) ∷ []) (_ , _ , _ , h , _) = just (codeOf sh h)
  stoppedChild _ _ = nothing

parent-retries : proj₁ result ≡ nothing
parent-retries = refl

parent-plans : NodeState.phase next ≡ Planning
parent-plans = refl

child-was-stopped : nextSlots ≡ [ "A" , sleeping (node []) false ]
child-was-stopped = refl

plan-cleared : NodeState.pending next ≡ nothing
plan-cleared = refl

parent-retains-implementation : NodeState.oldCode next ≡ candidate
parent-retains-implementation = refl

child-retains-implementation : stoppedChild nextSlots resources ≡ just (impl "A")
child-retains-implementation = refl

parent-sees-reason-guidance-and-proof : NodeState.diagnostic next ≡
  ("child independent (--safe unprovability witness — " ++ˢ reason ++ˢ
   "; your subspec is consistent in the standard model, NOT false, so keep intended semantics and replace opaque --safe primitives like primStringEquality/primCharEquality, String roundtrips, or function _≡_ with --safe reflective definitions such as Context.Tools.FsSandbox.eqStr, Data.String.Properties._≟_, Data.Char.Properties._≟_, toℕ, or pointwise equality):\n"
    ++ˢ render witness)
parent-sees-reason-guidance-and-proof = refl
