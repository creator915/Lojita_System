{-# OPTIONS --guardedness #-}
module Test.ProtocolGluingTest where

open import Agda.Builtin.Char using (primCharEquality)
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; any; tails; take; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String; toList; unlines) renaming (_++_ to _++ˢ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import IO.Primitive using (IO; return; _>>=_)
import IO.Primitive.Finite as F

open import Ownership using (Dir; Prog; withEphemeral; mkdir; openAs; call; stop; rmdir; done) renaming (_>>_ to _>>ₒ_; _>>=_ to _>>=ₒ_)
open import OwnershipIO using (RunningIO; evalIO)
open import OwnershipIO.FFI using (failIO; currentDirectory; readProcessAt; ProcResult; procResult)
open import OwnershipIO.MetaFFI using (_>>_; withPrivateTemp)
open import Code using (Obj; mkQ; unit; ext; eqList; _==ˢ_)
open import Code.Transport using (Proarrow; _⇝_)
open import Code.AI using (AIReq; AIReply; aiReply; bindNode; forkNode; accept; propose; ScriptedBackend; ParallelServiceBackend)
open import Code.SessionProtocol using (RefSpec; refSpec; local; build-exe; drive-tree-with)
open import Code.SessionTools using (SessionΨ; sessionTools)
open import Code.SessionRunner using (SessionConfig; sessionConfig; ActionResult; accepted; rejected; finished; executeAction; ensureRelay)
open import Test.HarnessPure using (submission)
open import Context.Terminal using (Bytes; bytes; localSandbox)
import Context.Tools.FsSandbox as Fs

open import Context.World using
  ( Cap; clockCap; ttyCap; fsCap; _∈_; here; there; _⊆_; ⊆-cons; ⊆-nil
  ; SimWorld; fs; pure; reactiveApp; ReactiveApp; runWorldPure; runReactivePure )
open import Context.Protocol using
  ( Proto; pEnd; pSend; pRecv; pSelect; pOffer; dual; dual-involutive
  ; Endpoint; epDone; epSend; epRecv; epSelectL; epSelectR; epOffer
  ; coupleEndpoints; composeReactive; coupleReactiveTurn; coupleReactive
  ; couple-done; couple-send-recv; couple-selectL-offer; couple-selectR-offer; couple-preserves-fs )

------------------------------------------------------------------------
-- §1 Compile-Time Verification of `Context.Protocol` Algebraic & Reactive Laws
------------------------------------------------------------------------

private
  sampleProto : Proto ⊤
  sampleProto = pSelect (pSend tt (pRecv tt pEnd)) (pOffer pEnd pEnd)

  check-dual-involutive : dual (dual sampleProto) ≡ sampleProto
  check-dual-involutive = dual-involutive sampleProto

  check-couple-done :
    coupleEndpoints {⊤} {[]} {λ _ → ℕ} (epDone 11) (epDone 22) ≡ pure (11 , 22)
  check-couple-done = couple-done {⊤} {[]} {λ _ → ℕ} 11 22

  check-couple-send-recv :
    coupleEndpoints {⊤} {[]} {λ _ → ℕ} {pSend tt pEnd}
      (epSend 5 (epDone 1))
      (epRecv (λ msg → epDone (msg + 10)))
      ≡ pure (1 , 15)
  check-couple-send-recv = couple-send-recv {⊤} {[]} {λ _ → ℕ} {tt} {pEnd} 5 (epDone 1) (λ msg → epDone (msg + 10))

  check-selectL-offer :
    coupleEndpoints {⊤} {[]} {λ _ → ℕ} {pSelect pEnd pEnd}
      (epSelectL (epDone 7))
      (epOffer (epDone 8) (epDone 9))
      ≡ pure (7 , 8)
  check-selectL-offer = couple-selectL-offer {⊤} {[]} {λ _ → ℕ} {pEnd} {pEnd} (epDone 7) (epDone 8) (epDone 9)

  check-selectR-offer :
    coupleEndpoints {⊤} {[]} {λ _ → ℕ} {pSelect pEnd pEnd}
      (epSelectR (epDone 7))
      (epOffer (epDone 8) (epDone 9))
      ≡ pure (7 , 9)
  check-selectR-offer = couple-selectR-offer {⊤} {[]} {λ _ → ℕ} {pEnd} {pEnd} (epDone 7) (epDone 8) (epDone 9)

  noFsInClockTty : fsCap ∈ (clockCap ∷ ttyCap ∷ []) → ⊥
  noFsInClockTty (there (there ()))

  check-couple-preserves-fs :
    ∀ (epA : Endpoint (clockCap ∷ ttyCap ∷ []) (λ (_ : ⊤) → ℕ) (pSend tt pEnd) ℕ)
      (epB : Endpoint (clockCap ∷ ttyCap ∷ []) (λ (_ : ⊤) → ℕ) (pRecv tt pEnd) ℕ)
      (w   : SimWorld) →
    fs (proj₂ (runWorldPure (coupleEndpoints epA epB) w)) ≡ fs w
  check-couple-preserves-fs = couple-preserves-fs noFsInClockTty

  clk⊆Combo : (clockCap ∷ []) ⊆ (clockCap ∷ ttyCap ∷ [])
  clk⊆Combo = ⊆-cons here ⊆-nil

  tty⊆Combo : (ttyCap ∷ []) ⊆ (clockCap ∷ ttyCap ∷ [])
  tty⊆Combo = ⊆-cons (there here) ⊆-nil

  svcClock : ReactiveApp (clockCap ∷ []) ℕ
  svcClock = reactiveApp (pure 1) (λ _ s → pure (inj₁ (suc s)))

  svcTty : ReactiveApp (ttyCap ∷ []) ℕ
  svcTty = reactiveApp (pure 10) (λ _ s → pure (inj₁ (suc s)))

  composedReactiveDemo : ReactiveApp (clockCap ∷ ttyCap ∷ []) (ℕ × ℕ)
  composedReactiveDemo =
    composeReactive clk⊆Combo tty⊆Combo svcClock svcTty (λ _ → nothing , nothing)

  coupledReactiveDemo : ReactiveApp (clockCap ∷ ttyCap ∷ []) (ℕ × ℕ)
  coupledReactiveDemo =
    coupleReactive {Tag = ⊤} {Payload = λ _ → ℕ} {P = pSend tt pEnd}
      clk⊆Combo tty⊆Combo
      (pure 2) (pure 3)
      (λ _ s₁ → epSend (suc s₁) (epDone (inj₁ (suc s₁))))
      (λ s₂ → epRecv (λ msg → epDone (inj₁ (s₂ + msg))))

  check-composed-reactive-init :
    proj₁ (runReactivePure composedReactiveDemo [] Context.World.defaultSimWorld) ≡ inj₁ (1 , 10)
  check-composed-reactive-init = refl

  check-coupled-reactive-init :
    proj₁ (runReactivePure coupledReactiveDemo [] Context.World.defaultSimWorld) ≡ inj₁ (2 , 3)
  check-coupled-reactive-init = refl

------------------------------------------------------------------------
-- §2 Multi-Node Dialectica Tree (`Gen.M0.Root` + `Auth` + `Store`)
------------------------------------------------------------------------

private
  infixl 6 _/_
  _/_ : String → String → String
  a / b = a ++ˢ "/" ++ˢ b

  assert : String → Bool → IO ⊤
  assert _ true = return tt
  assert msg false = failIO ("ProtocolGluingTest FAILED: " ++ˢ msg)

  contains : String → String → Bool
  contains needle haystack =
    any (λ s → eqList primCharEquality chars (take (length chars) s)) (tails (toList haystack))
    where chars = toList needle

  expectAccepted : String → ActionResult → IO String
  expectAccepted _     (accepted msg) = return msg
  expectAccepted _     (finished s)   = return s
  expectAccepted label (rejected err) = failIO (label ++ˢ " unexpectedly rejected:\n" ++ˢ err)

  unitQ : List String → Obj
  unitQ ns = unit (mkQ ns)

  extQ : List String → Obj
  extQ ns = ext (mkQ ns)

  -- Root specification (`Gen.M0.Root`)
  rootSpec : String
  rootSpec = unlines
    ( "module Gen.M0.Root where"
    ∷ "open import Data.Bool using (Bool; true; false)"
    ∷ "open import Data.List using ([])"
    ∷ "open import Data.Nat using (ℕ; _≤ᵇ_)"
    ∷ "open import Data.Product using (proj₁; proj₂)"
    ∷ "open import Data.String using (String)"
    ∷ "open import Data.Sum using (inj₂)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
    ∷ "open import Context.Terminal using (Bytes)"
    ∷ "open import Context.Tools.FsSandbox using (virtualFs)"
    ∷ "open import Context.Tools.FsLaws using (ValidFlatFile; CanWriteReg)"
    ∷ "open import Context.World using (CliCaps; CliApp; SimWorld; clock; fs; monoMs; autoTicks; readVirtualFile; runCliPure)"
    ∷ "postulate"
    ∷ "  vaultApp : ℕ → Bytes → CliApp CliCaps"
    ∷ "  vaultCliApp : ℕ → Bytes → CliApp CliCaps"
    ∷ "  vaultAppAt : String → ℕ → Bytes → CliApp CliCaps"
    ∷ "  vault-authorized-exit : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "    autoTicks (clock w) ≡ [] →"
    ∷ "    (monoMs (clock w) ≤ᵇ expiry) ≡ true →"
    ∷ "    fs w ≡ virtualFs [] →"
    ∷ "    proj₁ (runCliPure (vaultApp expiry payload) w) ≡ 0"
    ∷ "  vault-authorized-put-get : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "    autoTicks (clock w) ≡ [] →"
    ∷ "    (monoMs (clock w) ≤ᵇ expiry) ≡ true →"
    ∷ "    fs w ≡ virtualFs [] →"
    ∷ "    readVirtualFile \"vault/record.txt\" (fs (proj₂ (runCliPure (vaultApp expiry payload) w))) ≡ inj₂ payload"
    ∷ "  vaultAt-authorized-put-get : ∀ (path : String) (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "    autoTicks (clock w) ≡ [] →"
    ∷ "    (monoMs (clock w) ≤ᵇ expiry) ≡ true →"
    ∷ "    ValidFlatFile path ≡ true →"
    ∷ "    CanWriteReg path (fs w) ≡ true →"
    ∷ "    readVirtualFile path (fs (proj₂ (runCliPure (vaultAppAt path expiry payload) w))) ≡ inj₂ payload"
    ∷ "  vault-expired-exit : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "    (monoMs (clock w) ≤ᵇ expiry) ≡ false →"
    ∷ "    proj₁ (runCliPure (vaultApp expiry payload) w) ≡ 145"
    ∷ "  vault-expired-preserves-fs : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "    (monoMs (clock w) ≤ᵇ expiry) ≡ false →"
    ∷ "    fs (proj₂ (runCliPure (vaultApp expiry payload) w)) ≡ fs w"
    ∷ "  cliEntry : CliApp CliCaps"
    ∷ [] )

  -- Child A specification (`Gen.M0.Root.Auth`: ONLY `[clockCap]`)
  authSpec : String
  authSpec = unlines
    ( "module Gen.M0.Root.Auth where"
    ∷ "open import Data.Bool using (Bool; true; false)"
    ∷ "open import Data.List using ([]; _∷_)"
    ∷ "open import Data.Nat using (ℕ; _≤ᵇ_)"
    ∷ "open import Data.Product using (_×_; _,_)"
    ∷ "open import Data.String using (String)"
    ∷ "open import Data.Unit using (⊤; tt)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
    ∷ "open import Context.Terminal using (Bytes)"
    ∷ "open import Context.World using (clockCap; opNowMono; here; ExitCode)"
    ∷ "open import Context.Protocol using (pEnd; pSend; pSelect; Endpoint; epDone; epStep; epSend; epSelectL; epSelectR)"
    ∷ "postulate"
    ∷ "  authBranchAt : String → ℕ → ℕ → Bytes → Endpoint (clockCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pSelect (pSend tt pEnd) pEnd) ExitCode"
    ∷ "  authEndpointAt : String → ℕ → Bytes → Endpoint (clockCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pSelect (pSend tt pEnd) pEnd) ExitCode"
    ∷ "  authBranch : ℕ → ℕ → Bytes → Endpoint (clockCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pSelect (pSend tt pEnd) pEnd) ExitCode"
    ∷ "  authEndpoint : ℕ → Bytes → Endpoint (clockCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pSelect (pSend tt pEnd) pEnd) ExitCode"
    ∷ "  authAt-step-law : ∀ (path : String) (expiry : ℕ) (payload : Bytes) →"
    ∷ "    authEndpointAt path expiry payload ≡ epStep here opNowMono (λ t → authBranchAt path t expiry payload)"
    ∷ "  authAt-valid-law : ∀ (path : String) (t expiry : ℕ) (payload : Bytes) →"
    ∷ "    (t ≤ᵇ expiry) ≡ true →"
    ∷ "    authBranchAt path t expiry payload ≡ epSelectL (epSend (path , payload) (epDone 0))"
    ∷ "  authAt-expired-law : ∀ (path : String) (t expiry : ℕ) (payload : Bytes) →"
    ∷ "    (t ≤ᵇ expiry) ≡ false →"
    ∷ "    authBranchAt path t expiry payload ≡ epSelectR (epDone 145)"
    ∷ "  auth-step-law : ∀ (expiry : ℕ) (payload : Bytes) →"
    ∷ "    authEndpoint expiry payload ≡ epStep here opNowMono (λ t → authBranch t expiry payload)"
    ∷ "  auth-valid-law : ∀ (t expiry : ℕ) (payload : Bytes) →"
    ∷ "    (t ≤ᵇ expiry) ≡ true →"
    ∷ "    authBranch t expiry payload ≡ epSelectL (epSend (\"vault/record.txt\" , payload) (epDone 0))"
    ∷ "  auth-expired-law : ∀ (t expiry : ℕ) (payload : Bytes) →"
    ∷ "    (t ≤ᵇ expiry) ≡ false →"
    ∷ "    authBranch t expiry payload ≡ epSelectR (epDone 145)"
    ∷ [] )

  -- Child B specification (`Gen.M0.Root.Store`: ONLY `[fsCap]`)
  storeSpec : String
  storeSpec = unlines
    ( "module Gen.M0.Root.Store where"
    ∷ "open import Data.List using ([]; _∷_)"
    ∷ "open import Data.Product using (_×_; proj₁; proj₂)"
    ∷ "open import Data.String using (String)"
    ∷ "open import Data.Sum using (_⊎_; inj₂)"
    ∷ "open import Data.Unit using (⊤; tt)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
    ∷ "open import Context.Terminal using (Bytes)"
    ∷ "open import Context.World using (fsCap; FsError; opWriteFile; here)"
    ∷ "open import Context.Protocol using (pEnd; pSend; pRecv; pSelect; dual; Endpoint; epDone; epStep; epRecv; epOffer)"
    ∷ "postulate"
    ∷ "  storeWriteBranch : Endpoint (fsCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pRecv tt pEnd) (FsError ⊎ ⊤)"
    ∷ "  storeRejectBranch : Endpoint (fsCap ∷ []) (λ (_ : ⊤) → String × Bytes) pEnd (FsError ⊎ ⊤)"
    ∷ "  storeEndpoint : Endpoint (fsCap ∷ []) (λ (_ : ⊤) → String × Bytes) (dual (pSelect (pSend tt pEnd) pEnd)) (FsError ⊎ ⊤)"
    ∷ "  store-offer-law : storeEndpoint ≡ epOffer storeWriteBranch storeRejectBranch"
    ∷ "  store-write-law : storeWriteBranch ≡ epRecv (λ cred → epStep here (opWriteFile (proj₁ cred) (proj₂ cred)) epDone)"
    ∷ "  store-reject-law : storeRejectBranch ≡ epDone (inj₂ tt)"
    ∷ [] )

  -- Child A implementation (`Gen.M0.Root.Auth`)
  authImpl : String
  authImpl = unlines
    ( "module Gen.M0.Root.Auth where"
    ∷ "open import Data.Bool using (Bool; true; false)"
    ∷ "open import Data.List using (List; []; _∷_)"
    ∷ "open import Data.Nat using (ℕ; _≤ᵇ_)"
    ∷ "open import Data.Product using (_×_; _,_)"
    ∷ "open import Data.String using (String)"
    ∷ "open import Data.Unit using (⊤; tt)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)"
    ∷ "open import Context.Terminal using (Bytes)"
    ∷ "open import Context.World using (Cap; clockCap; Op; opNowMono; _∈_; here; nowMonoW; ExitCode)"
    ∷ "open import Context.Protocol using (Proto; pEnd; pSend; pSelect; Endpoint; epDone; epStep; epSend; epSelectL; epSelectR; liftProgToEndpoint)"
    ∷ ""
    ∷ "authChoice : String → Bytes → Bool → Endpoint (clockCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pSelect (pSend tt pEnd) pEnd) ExitCode"
    ∷ "authChoice targetPath secretPayload true  = epSelectL (epSend (targetPath , secretPayload) (epDone 0))"
    ∷ "authChoice _          _             false = epSelectR (epDone 145)"
    ∷ ""
    ∷ "authBranchAt : String → ℕ → ℕ → Bytes → Endpoint (clockCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pSelect (pSend tt pEnd) pEnd) ExitCode"
    ∷ "authBranchAt targetPath t tokenExpiryMs secretPayload = authChoice targetPath secretPayload (t ≤ᵇ tokenExpiryMs)"
    ∷ ""
    ∷ "authEndpointAt : String → ℕ → Bytes → Endpoint (clockCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pSelect (pSend tt pEnd) pEnd) ExitCode"
    ∷ "authEndpointAt targetPath tokenExpiryMs secretPayload = liftProgToEndpoint (nowMonoW here) (λ t → authBranchAt targetPath t tokenExpiryMs secretPayload)"
    ∷ ""
    ∷ "authBranch : ℕ → ℕ → Bytes → Endpoint (clockCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pSelect (pSend tt pEnd) pEnd) ExitCode"
    ∷ "authBranch = authBranchAt \"vault/record.txt\""
    ∷ ""
    ∷ "authEndpoint : ℕ → Bytes → Endpoint (clockCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pSelect (pSend tt pEnd) pEnd) ExitCode"
    ∷ "authEndpoint = authEndpointAt \"vault/record.txt\""
    ∷ ""
    ∷ "authAt-step-law : ∀ (path : String) (expiry : ℕ) (payload : Bytes) →"
    ∷ "  authEndpointAt path expiry payload ≡ epStep here opNowMono (λ t → authBranchAt path t expiry payload)"
    ∷ "authAt-step-law _ _ _ = refl"
    ∷ ""
    ∷ "authAt-valid-law : ∀ (path : String) (t expiry : ℕ) (payload : Bytes) →"
    ∷ "  (t ≤ᵇ expiry) ≡ true →"
    ∷ "  authBranchAt path t expiry payload ≡ epSelectL (epSend (path , payload) (epDone 0))"
    ∷ "authAt-valid-law path _ _ payload ok = cong (authChoice path payload) ok"
    ∷ ""
    ∷ "authAt-expired-law : ∀ (path : String) (t expiry : ℕ) (payload : Bytes) →"
    ∷ "  (t ≤ᵇ expiry) ≡ false →"
    ∷ "  authBranchAt path t expiry payload ≡ epSelectR (epDone 145)"
    ∷ "authAt-expired-law path _ _ payload ex = cong (authChoice path payload) ex"
    ∷ ""
    ∷ "auth-step-law : ∀ (expiry : ℕ) (payload : Bytes) →"
    ∷ "  authEndpoint expiry payload ≡ epStep here opNowMono (λ t → authBranch t expiry payload)"
    ∷ "auth-step-law = authAt-step-law \"vault/record.txt\""
    ∷ ""
    ∷ "auth-valid-law : ∀ (t expiry : ℕ) (payload : Bytes) →"
    ∷ "  (t ≤ᵇ expiry) ≡ true →"
    ∷ "  authBranch t expiry payload ≡ epSelectL (epSend (\"vault/record.txt\" , payload) (epDone 0))"
    ∷ "auth-valid-law = authAt-valid-law \"vault/record.txt\""
    ∷ ""
    ∷ "auth-expired-law : ∀ (t expiry : ℕ) (payload : Bytes) →"
    ∷ "  (t ≤ᵇ expiry) ≡ false →"
    ∷ "  authBranch t expiry payload ≡ epSelectR (epDone 145)"
    ∷ "auth-expired-law = authAt-expired-law \"vault/record.txt\""
    ∷ [] )

  authPlan : String
  authPlan = submission "implement [clockCap]-only Auth endpoint and its branch laws"
    authImpl
    []
    ( (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "authChoice" ∷ []))
    ∷ [] )

  -- Child B implementation (`Gen.M0.Root.Store`)
  storeImpl : String
  storeImpl = unlines
    ( "module Gen.M0.Root.Store where"
    ∷ "open import Data.List using ([]; _∷_)"
    ∷ "open import Data.Product using (_×_; proj₁; proj₂)"
    ∷ "open import Data.String using (String)"
    ∷ "open import Data.Sum using (_⊎_; inj₂)"
    ∷ "open import Data.Unit using (⊤; tt)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl)"
    ∷ "open import Context.Terminal using (Bytes)"
    ∷ "open import Context.World using (fsCap; FsError; opWriteFile; here; writeFileW)"
    ∷ "open import Context.Protocol using (pEnd; pSend; pRecv; pSelect; dual; Endpoint; epDone; epStep; epRecv; epOffer; liftProgToEndpoint)"
    ∷ ""
    ∷ "storeWriteBranch : Endpoint (fsCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pRecv tt pEnd) (FsError ⊎ ⊤)"
    ∷ "storeWriteBranch = epRecv (λ cred → liftProgToEndpoint (writeFileW here (proj₁ cred) (proj₂ cred)) epDone)"
    ∷ ""
    ∷ "storeRejectBranch : Endpoint (fsCap ∷ []) (λ (_ : ⊤) → String × Bytes) pEnd (FsError ⊎ ⊤)"
    ∷ "storeRejectBranch = epDone (inj₂ tt)"
    ∷ ""
    ∷ "storeEndpoint : Endpoint (fsCap ∷ []) (λ (_ : ⊤) → String × Bytes) (dual (pSelect (pSend tt pEnd) pEnd)) (FsError ⊎ ⊤)"
    ∷ "storeEndpoint = epOffer storeWriteBranch storeRejectBranch"
    ∷ ""
    ∷ "store-offer-law : storeEndpoint ≡ epOffer storeWriteBranch storeRejectBranch"
    ∷ "store-offer-law = refl"
    ∷ ""
    ∷ "store-write-law : storeWriteBranch ≡ epRecv (λ cred → epStep here (opWriteFile (proj₁ cred) (proj₂ cred)) epDone)"
    ∷ "store-write-law = refl"
    ∷ ""
    ∷ "store-reject-law : storeRejectBranch ≡ epDone (inj₂ tt)"
    ∷ "store-reject-law = refl"
    ∷ [] )

  storePlan : String
  storePlan = submission "implement [fsCap]-only Store endpoint and its branch laws"
    storeImpl
    []
    []

  -- Parent gluing implementation (`Gen.M0.Root`)
  rootImpl : String
  rootImpl = unlines
    ( "module Gen.M0.Root where"
    ∷ "open import Data.Bool using (Bool; true; false; if_then_else_)"
    ∷ "open import Data.Char using (Char; toℕ)"
    ∷ "open import Data.List using (List; []; _∷_; foldl)"
    ∷ "open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_)"
    ∷ "open import Data.Product using (_×_; _,_; proj₁; proj₂)"
    ∷ "open import Data.String using (String; toList)"
    ∷ "open import Data.Sum using (_⊎_; inj₁; inj₂)"
    ∷ "open import Data.Unit using (⊤; tt)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)"
    ∷ "open import Context.Terminal using (Bytes; bytes)"
    ∷ "open import Context.Tools.FsSandbox using (VirtualFs; virtualFs)"
    ∷ "open import Context.Tools.FsLaws using (ValidFlatFile; CanWriteReg; read-after-write-same)"
    ∷ "open import Context.Tools.Clock using (popTick)"
    ∷ "open import Context.World using (clockCap; fsCap; CliCaps; clock∈Cli; env∈Cli; fs∈Cli; SimClock; _⊆_; ⊆-cons; ⊆-nil; FsError; SimWorld; clock; fs; monoMs; autoTicks; readMonoMs; _>>=w_; _>>w_; mapWorld; nowMonoW; sleepW; getArgsW; ExitCode; CliApp; readVirtualFile; writeVirtualFile; runWorldPure; runCliPure)"
    ∷ "open import Context.Protocol using (pEnd; pSend; pSelect; dual; Endpoint; epDone; epSend; epOffer; liftEndpoint; coupleEndpoints)"
    ∷ "import Gen.M0.Root.Auth as Auth"
    ∷ "import Gen.M0.Root.Store as Store"
    ∷ ""
    ∷ "-- These clock and filesystem facts use only the trusted Context operations."
    ∷ "readMono-idle-val : ∀ (c : SimClock) → autoTicks c ≡ [] → proj₁ (readMonoMs c) ≡ monoMs c"
    ∷ "readMono-idle-val c ticksEq = cong (λ ts → proj₁ (popTick ts) + monoMs c) ticksEq"
    ∷ ""
    ∷ "expired-step : ∀ (m e : ℕ) → (m ≤ᵇ e) ≡ false → (suc m ≤ᵇ e) ≡ false"
    ∷ "expired-step zero          _       ()"
    ∷ "expired-step (suc _)       zero    _  = refl"
    ∷ "expired-step (suc zero)    (suc _) ()"
    ∷ "expired-step (suc (suc m)) (suc e) eq = expired-step (suc m) e eq"
    ∷ ""
    ∷ "expired-add : ∀ (d m e : ℕ) → (m ≤ᵇ e) ≡ false → ((d + m) ≤ᵇ e) ≡ false"
    ∷ "expired-add zero    _ _ eq = eq"
    ∷ "expired-add (suc d) m e eq = expired-step (d + m) e (expired-add d m e eq)"
    ∷ ""
    ∷ "expired-mono-preserved : ∀ (expiry : ℕ) (c : SimClock) → (monoMs c ≤ᵇ expiry) ≡ false → (proj₁ (readMonoMs c) ≤ᵇ expiry) ≡ false"
    ∷ "expired-mono-preserved expiry c hExp = expired-add (proj₁ (popTick (autoTicks c))) (monoMs c) expiry hExp"
    ∷ ""
    ∷ "store-vault-empty-ok : ∀ (payload : Bytes) → proj₁ (writeVirtualFile \"vault/record.txt\" payload (virtualFs [])) ≡ inj₂ tt"
    ∷ "store-vault-empty-ok _ = refl"
    ∷ ""
    ∷ "store-vault-empty-put-get : ∀ (payload : Bytes) → readVirtualFile \"vault/record.txt\" (proj₂ (writeVirtualFile \"vault/record.txt\" payload (virtualFs []))) ≡ inj₂ payload"
    ∷ "store-vault-empty-put-get _ = refl"
    ∷ ""
    ∷ "store-flat-put-get : ∀ (path : String) (payload : Bytes) (v : VirtualFs) → ValidFlatFile path ≡ true → CanWriteReg path v ≡ true → readVirtualFile path (proj₂ (writeVirtualFile path payload v)) ≡ inj₂ payload"
    ∷ "store-flat-put-get = read-after-write-same"
    ∷ ""
    ∷ "auth⊆Cli : (clockCap ∷ []) ⊆ CliCaps"
    ∷ "auth⊆Cli = ⊆-cons clock∈Cli ⊆-nil"
    ∷ ""
    ∷ "store⊆Cli : (fsCap ∷ []) ⊆ CliCaps"
    ∷ "store⊆Cli = ⊆-cons fs∈Cli ⊆-nil"
    ∷ ""
    ∷ "finalizeVault : ExitCode → (FsError ⊎ ⊤) → ExitCode"
    ∷ "finalizeVault code (inj₂ _) = code"
    ∷ "finalizeVault code (inj₁ _) = if code ≡ᵇ 0 then 2 else code"
    ∷ ""
    ∷ "tickWorldClock : SimWorld → SimWorld"
    ∷ "tickWorldClock w = record w { clock = proj₂ (readMonoMs (clock w)) }"
    ∷ ""
    ∷ "setWorldFs : SimWorld → VirtualFs → SimWorld"
    ∷ "setWorldFs w v = record w { fs = v }"
    ∷ ""
    ∷ "coupleVaultEndpoints :"
    ∷ "  Endpoint (clockCap ∷ []) (λ (_ : ⊤) → String × Bytes) (pSelect (pSend tt pEnd) pEnd) ExitCode →"
    ∷ "  Endpoint (fsCap ∷ []) (λ (_ : ⊤) → String × Bytes) (dual (pSelect (pSend tt pEnd) pEnd)) (FsError ⊎ ⊤) →"
    ∷ "  CliApp CliCaps"
    ∷ "coupleVaultEndpoints epA epB ="
    ∷ "  mapWorld (λ p → finalizeVault (proj₁ p) (proj₂ p))"
    ∷ "    (coupleEndpoints (liftEndpoint auth⊆Cli epA) (liftEndpoint store⊆Cli epB))"
    ∷ ""
    ∷ "vaultAppAt : String → ℕ → Bytes → CliApp CliCaps"
    ∷ "vaultAppAt path expiry payload = coupleVaultEndpoints (Auth.authEndpointAt path expiry payload) Store.storeEndpoint"
    ∷ ""
    ∷ "vaultApp : ℕ → Bytes → CliApp CliCaps"
    ∷ "vaultApp expiry payload = coupleVaultEndpoints (Auth.authEndpoint expiry payload) Store.storeEndpoint"
    ∷ ""
    ∷ "vaultCliApp : ℕ → Bytes → CliApp CliCaps"
    ∷ "vaultCliApp = vaultApp"
    ∷ ""
    ∷ "vault-step-unfold : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "  runCliPure (vaultApp expiry payload) w ≡"
    ∷ "  runWorldPure"
    ∷ "    (coupleVaultEndpoints"
    ∷ "      (Auth.authBranch (proj₁ (readMonoMs (clock w))) expiry payload)"
    ∷ "      (epOffer Store.storeWriteBranch Store.storeRejectBranch))"
    ∷ "    (tickWorldClock w)"
    ∷ "vault-step-unfold expiry payload w ="
    ∷ "  trans"
    ∷ "    (cong (λ a → runCliPure (coupleVaultEndpoints a Store.storeEndpoint) w)"
    ∷ "          (Auth.auth-step-law expiry payload))"
    ∷ "    (cong (λ s → runWorldPure"
    ∷ "      (coupleVaultEndpoints (Auth.authBranch (proj₁ (readMonoMs (clock w))) expiry payload) s)"
    ∷ "      (tickWorldClock w))"
    ∷ "      Store.store-offer-law)"
    ∷ ""
    ∷ "vaultAt-step-unfold : ∀ (path : String) (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "  runCliPure (vaultAppAt path expiry payload) w ≡"
    ∷ "  runWorldPure"
    ∷ "    (coupleVaultEndpoints"
    ∷ "      (Auth.authBranchAt path (proj₁ (readMonoMs (clock w))) expiry payload)"
    ∷ "      (epOffer Store.storeWriteBranch Store.storeRejectBranch))"
    ∷ "    (tickWorldClock w)"
    ∷ "vaultAt-step-unfold path expiry payload w ="
    ∷ "  trans"
    ∷ "    (cong (λ a → runCliPure (coupleVaultEndpoints a Store.storeEndpoint) w)"
    ∷ "          (Auth.authAt-step-law path expiry payload))"
    ∷ "    (cong (λ s → runWorldPure"
    ∷ "      (coupleVaultEndpoints (Auth.authBranchAt path (proj₁ (readMonoMs (clock w))) expiry payload) s)"
    ∷ "      (tickWorldClock w))"
    ∷ "      Store.store-offer-law)"
    ∷ ""
    ∷ "vault-valid-eval : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "  autoTicks (clock w) ≡ [] →"
    ∷ "  (monoMs (clock w) ≤ᵇ expiry) ≡ true →"
    ∷ "  runCliPure (vaultApp expiry payload) w ≡"
    ∷ "  (finalizeVault 0 (proj₁ (writeVirtualFile \"vault/record.txt\" payload (fs w))) ,"
    ∷ "   setWorldFs (tickWorldClock w) (proj₂ (writeVirtualFile \"vault/record.txt\" payload (fs w))))"
    ∷ "vault-valid-eval expiry payload w ticksIdle monoValid ="
    ∷ "  let t = proj₁ (readMonoMs (clock w))"
    ∷ "      tValid : (t ≤ᵇ expiry) ≡ true"
    ∷ "      tValid = trans (cong (λ m → m ≤ᵇ expiry) (readMono-idle-val (clock w) ticksIdle)) monoValid"
    ∷ "  in trans (vault-step-unfold expiry payload w)"
    ∷ "       (trans"
    ∷ "         (cong (λ b → runWorldPure"
    ∷ "           (coupleVaultEndpoints b (epOffer Store.storeWriteBranch Store.storeRejectBranch))"
    ∷ "           (tickWorldClock w))"
    ∷ "           (Auth.auth-valid-law t expiry payload tValid))"
    ∷ "         (cong (λ wb → runWorldPure"
    ∷ "           (mapWorld (λ p → finalizeVault (proj₁ p) (proj₂ p))"
    ∷ "             (coupleEndpoints {⊤} {CliCaps} {λ _ → String × Bytes} {pSend tt pEnd}"
    ∷ "               (epSend (\"vault/record.txt\" , payload) (epDone 0))"
    ∷ "               (liftEndpoint store⊆Cli wb)))"
    ∷ "           (tickWorldClock w))"
    ∷ "           Store.store-write-law))"
    ∷ ""
    ∷ "vaultAt-valid-eval : ∀ (path : String) (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "  autoTicks (clock w) ≡ [] →"
    ∷ "  (monoMs (clock w) ≤ᵇ expiry) ≡ true →"
    ∷ "  runCliPure (vaultAppAt path expiry payload) w ≡"
    ∷ "  (finalizeVault 0 (proj₁ (writeVirtualFile path payload (fs w))) ,"
    ∷ "   setWorldFs (tickWorldClock w) (proj₂ (writeVirtualFile path payload (fs w))))"
    ∷ "vaultAt-valid-eval path expiry payload w ticksIdle monoValid ="
    ∷ "  let t = proj₁ (readMonoMs (clock w))"
    ∷ "      tValid : (t ≤ᵇ expiry) ≡ true"
    ∷ "      tValid = trans (cong (λ m → m ≤ᵇ expiry) (readMono-idle-val (clock w) ticksIdle)) monoValid"
    ∷ "  in trans (vaultAt-step-unfold path expiry payload w)"
    ∷ "       (trans"
    ∷ "         (cong (λ b → runWorldPure"
    ∷ "           (coupleVaultEndpoints b (epOffer Store.storeWriteBranch Store.storeRejectBranch))"
    ∷ "           (tickWorldClock w))"
    ∷ "           (Auth.authAt-valid-law path t expiry payload tValid))"
    ∷ "         (cong (λ wb → runWorldPure"
    ∷ "           (mapWorld (λ p → finalizeVault (proj₁ p) (proj₂ p))"
    ∷ "             (coupleEndpoints {⊤} {CliCaps} {λ _ → String × Bytes} {pSend tt pEnd}"
    ∷ "               (epSend (path , payload) (epDone 0))"
    ∷ "               (liftEndpoint store⊆Cli wb)))"
    ∷ "           (tickWorldClock w))"
    ∷ "           Store.store-write-law))"
    ∷ ""
    ∷ "vault-authorized-exit : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "  autoTicks (clock w) ≡ [] →"
    ∷ "  (monoMs (clock w) ≤ᵇ expiry) ≡ true →"
    ∷ "  fs w ≡ virtualFs [] →"
    ∷ "  proj₁ (runCliPure (vaultApp expiry payload) w) ≡ 0"
    ∷ "vault-authorized-exit expiry payload w ticksIdle monoValid fsEmpty ="
    ∷ "  trans (cong proj₁ (vault-valid-eval expiry payload w ticksIdle monoValid))"
    ∷ "    (trans"
    ∷ "      (cong (λ v → finalizeVault 0 (proj₁ (writeVirtualFile \"vault/record.txt\" payload v))) fsEmpty)"
    ∷ "      (cong (finalizeVault 0) (store-vault-empty-ok payload)))"
    ∷ ""
    ∷ "vault-authorized-put-get : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "  autoTicks (clock w) ≡ [] →"
    ∷ "  (monoMs (clock w) ≤ᵇ expiry) ≡ true →"
    ∷ "  fs w ≡ virtualFs [] →"
    ∷ "  readVirtualFile \"vault/record.txt\" (fs (proj₂ (runCliPure (vaultApp expiry payload) w))) ≡ inj₂ payload"
    ∷ "vault-authorized-put-get expiry payload w ticksIdle monoValid fsEmpty ="
    ∷ "  trans"
    ∷ "    (cong (λ r → readVirtualFile \"vault/record.txt\" (fs (proj₂ r)))"
    ∷ "          (vault-valid-eval expiry payload w ticksIdle monoValid))"
    ∷ "    (trans"
    ∷ "      (cong (λ v → readVirtualFile \"vault/record.txt\" (proj₂ (writeVirtualFile \"vault/record.txt\" payload v))) fsEmpty)"
    ∷ "      (store-vault-empty-put-get payload))"
    ∷ ""
    ∷ "vaultAt-authorized-put-get : ∀ (path : String) (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "  autoTicks (clock w) ≡ [] →"
    ∷ "  (monoMs (clock w) ≤ᵇ expiry) ≡ true →"
    ∷ "  ValidFlatFile path ≡ true →"
    ∷ "  CanWriteReg path (fs w) ≡ true →"
    ∷ "  readVirtualFile path (fs (proj₂ (runCliPure (vaultAppAt path expiry payload) w))) ≡ inj₂ payload"
    ∷ "vaultAt-authorized-put-get path expiry payload w ticksIdle monoValid flatOk canOk ="
    ∷ "  trans"
    ∷ "    (cong (λ r → readVirtualFile path (fs (proj₂ r)))"
    ∷ "          (vaultAt-valid-eval path expiry payload w ticksIdle monoValid))"
    ∷ "    (store-flat-put-get path payload (fs w) flatOk canOk)"
    ∷ ""
    ∷ "vault-expired-eval : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "  (monoMs (clock w) ≤ᵇ expiry) ≡ false →"
    ∷ "  runCliPure (vaultApp expiry payload) w ≡ (145 , tickWorldClock w)"
    ∷ "vault-expired-eval expiry payload w monoExp ="
    ∷ "  let t = proj₁ (readMonoMs (clock w))"
    ∷ "      tExp : (t ≤ᵇ expiry) ≡ false"
    ∷ "      tExp = expired-mono-preserved expiry (clock w) monoExp"
    ∷ "  in trans (vault-step-unfold expiry payload w)"
    ∷ "       (trans"
    ∷ "         (cong (λ b → runWorldPure"
    ∷ "           (coupleVaultEndpoints b (epOffer Store.storeWriteBranch Store.storeRejectBranch))"
    ∷ "           (tickWorldClock w))"
    ∷ "           (Auth.auth-expired-law t expiry payload tExp))"
    ∷ "         (cong (λ rb → runWorldPure"
    ∷ "           (mapWorld (λ p → finalizeVault (proj₁ p) (proj₂ p))"
    ∷ "             (coupleEndpoints {⊤} {CliCaps} {λ _ → String × Bytes} {pEnd}"
    ∷ "               (epDone 145)"
    ∷ "               (liftEndpoint store⊆Cli rb)))"
    ∷ "           (tickWorldClock w))"
    ∷ "           Store.store-reject-law))"
    ∷ ""
    ∷ "vault-expired-exit : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "  (monoMs (clock w) ≤ᵇ expiry) ≡ false →"
    ∷ "  proj₁ (runCliPure (vaultApp expiry payload) w) ≡ 145"
    ∷ "vault-expired-exit expiry payload w monoExp ="
    ∷ "  cong proj₁ (vault-expired-eval expiry payload w monoExp)"
    ∷ ""
    ∷ "vault-expired-preserves-fs : ∀ (expiry : ℕ) (payload : Bytes) (w : SimWorld) →"
    ∷ "  (monoMs (clock w) ≤ᵇ expiry) ≡ false →"
    ∷ "  fs (proj₂ (runCliPure (vaultApp expiry payload) w)) ≡ fs w"
    ∷ "vault-expired-preserves-fs expiry payload w monoExp ="
    ∷ "  cong (λ r → fs (proj₂ r)) (vault-expired-eval expiry payload w monoExp)"
    ∷ ""
    ∷ "parseDec : String → ℕ"
    ∷ "parseDec s = foldl (λ acc c → acc * 10 + (toℕ c ∸ 48)) 0 (toList s)"
    ∷ ""
    ∷ "dispatchCliArgs : List String → CliApp CliCaps"
    ∷ "dispatchCliArgs (sleepMsStr ∷ expiryMsStr ∷ payloadStr ∷ _) ="
    ∷ "  let waitMs   = parseDec sleepMsStr"
    ∷ "      expiryMs = parseDec expiryMsStr"
    ∷ "      payload  = bytes payloadStr"
    ∷ "  in if waitMs ≡ᵇ 0"
    ∷ "       then vaultApp expiryMs payload"
    ∷ "       else (nowMonoW clock∈Cli >>w sleepW clock∈Cli waitMs >>w vaultApp expiryMs payload)"
    ∷ "dispatchCliArgs _ = vaultApp 60000 (bytes \"default-vault-record\")"
    ∷ ""
    ∷ "cliEntry : CliApp CliCaps"
    ∷ "cliEntry = getArgsW env∈Cli >>=w dispatchCliArgs"
    ∷ [] )

  rootPlan : String
  rootPlan = submission "glue [clockCap] Auth and [fsCap] Store via Context.Protocol.coupleEndpoints"
    rootImpl
    ( ("Gen.M0.Root.Auth"  , authSpec)
    ∷ ("Gen.M0.Root.Store" , storeSpec)
    ∷ [] )
    ( -- Local helper units in Gen.M0.Root
      (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "auth⊆Cli" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "store⊆Cli" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "readMono-idle-val" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "expired-step" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "expired-add" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "expired-mono-preserved" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "store-vault-empty-ok" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "store-vault-empty-put-get" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "store-flat-put-get" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "finalizeVault" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "tickWorldClock" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "setWorldFs" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "coupleVaultEndpoints" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "vault-step-unfold" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "vaultAt-step-unfold" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "vault-valid-eval" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "vaultAt-valid-eval" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "vault-expired-eval" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "parseDec" ∷ []))
    ∷ (Code.⊥ ⇝ unitQ ("Gen" ∷ "M0" ∷ "Root" ∷ "dispatchCliArgs" ∷ []))
      -- Child A (`Gen.M0.Root.Auth`) interface units
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "authBranchAt" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "authEndpointAt" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "authBranch" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "authEndpoint" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "authAt-step-law" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "authAt-valid-law" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "authAt-expired-law" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "auth-step-law" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "auth-valid-law" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Auth" ∷ "auth-expired-law" ∷ []))
      -- Child B (`Gen.M0.Root.Store`) interface units
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Store" ∷ "storeWriteBranch" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Store" ∷ "storeRejectBranch" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Store" ∷ "storeEndpoint" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Store" ∷ "store-offer-law" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Store" ∷ "store-write-law" ∷ []))
    ∷ (Code.⊥ ⇝ extQ ("Gen" ∷ "M0" ∷ "Root" ∷ "Store" ∷ "store-reject-law" ∷ []))
    ∷ [] )

  -- `fsbox` runtime probe verifying BOTH:
  -- 1) Authorized token (`0ms` elapsed <= `60000ms` expiry): exit `0`, `"vault/record.txt"` created with exact bytes
  -- 2) Expired token (`25ms` elapsed > `5ms` expiry): exit `145` (`!= 0`), ZERO files/dirs created in `snapshotStep`!
  emptyFsCfg : Fs.FsConfig
  emptyFsCfg = Fs.fsConfig localSandbox [] [] []

  isExitCode : ℕ → Maybe ℕ → Bool
  isExitCode want (just n) = n ≡ᵇ want
  isExitCode _    nothing  = false

  hasVaultRecord : Bytes → List Fs.FsEntryObs → Bool
  hasVaultRecord want es with Fs.lookupEntry "vault/record.txt" es
  ... | nothing = false
  ... | just e  = Fs.eqKind (Fs.entryKind e) Fs.regularNode ∧ Fs.eqBytes (Fs.entryBytes e) want

  fsboxProbeProg : Prog SessionΨ (Dir []) (Dir []) (Fs.RawFsObs × Fs.RawFsObs × Fs.RawFsObs × Fs.RawFsObs)
  fsboxProbeProg = withEphemeral "protoFsProbe"
    (mkdir "fsAuth" >>ₒ openAs "fsAuth" "fsbox" emptyFsCfg >>ₒ
     call "fsAuth" (Fs.runCmd "cand" ("0" ∷ "60000" ∷ "VAULT_AUTH_‿_OK" ∷ []) [] 10000) >>=ₒ λ obsAuth →
     call "fsAuth" Fs.snapshotStep >>=ₒ λ snapAuth →
     stop "fsAuth" >>ₒ rmdir "fsAuth" >>ₒ
     mkdir "fsExp" >>ₒ openAs "fsExp" "fsbox" emptyFsCfg >>ₒ
     call "fsExp" (Fs.runCmd "cand" ("25" ∷ "5" ∷ "UNAUTH_LEAK" ∷ []) [] 10000) >>=ₒ λ obsExp →
     call "fsExp" Fs.snapshotStep >>=ₒ λ snapExp →
     stop "fsExp" >>ₒ rmdir "fsExp" >>ₒ
     done (obsAuth , snapAuth , obsExp , snapExp))

main : IO ⊤
main = do
  repo ← currentDirectory
  withPrivateTemp (repo / "tmp/protocol-gluing") λ tmp → do
    let ws = tmp / "ws-protocol"
        ref = refSpec (local "/bin/cat") [] 30000
        mkProtocolAI : IO (RunningIO AIReq AIReply (⊤ × ⊤))
        mkProtocolAI = do
          slotRef ← OwnershipIO.FFI.newIORef ""
          return (record
            { onCall = λ where
                (bindNode n _) → OwnershipIO.FFI.writeIORef slotRef n >> return (aiReply "bound" n)
                (forkNode n)   → return (aiReply "" n)
                (accept _)     → return (aiReply "accepted" "")
                (propose prompt true _) → failIO ("fixed protocol plan was rejected:\n" ++ˢ prompt)
                (propose _ false _) → OwnershipIO.FFI.readIORef slotRef >>= λ s →
                  if s ==ˢ "Gen.M0.Root" then return (aiReply rootPlan s)
                  else if s ==ˢ "Gen.M0.Root.Auth" then return (aiReply authPlan s)
                  else if s ==ˢ "Gen.M0.Root.Store" then return (aiReply storePlan s)
                  else failIO ("unexpected node slot: " ++ˢ s)
            ; onStop = return (tt , tt) })
        cfg = sessionConfig repo ws "verified dual-protocol Auth + Store microservice tree"
                ref
                (ScriptedBackend [])
                (λ _ → ParallelServiceBackend mkProtocolAI)

    -- 1. Drive multi-node Dialectica tree (`Gen.M0.Root` -> `Gen.M0.Root.Auth` + `Gen.M0.Root.Store`)
    treeOut ← executeAction cfg
                (drive-tree-with "M0" "verified dual-protocol microservice tree" rootSpec [] nothing nothing)
                >>= expectAccepted "M0 drive-tree"
    assert ("expected verdict ok M0, got:\n" ++ˢ treeOut) (contains "ok M0" treeOut)
    assert ("expected Gen.M0.Root.Auth in exported tree, got:\n" ++ˢ treeOut) (contains "Gen.M0.Root.Auth" treeOut)
    assert ("expected Gen.M0.Root.Store in exported tree, got:\n" ++ˢ treeOut) (contains "Gen.M0.Root.Store" treeOut)
    verdictTxt ← F.readFile (ws / "trees/M0/verdict")
    assert ("expected ws/trees/M0/verdict == ok, got: " ++ˢ verdictTxt) (contains "ok" verdictTxt)
    F.putStrLn "PASS  1. Multi-node Dialectica tree (Gen.M0.Root + Gen.M0.Root.Auth + Gen.M0.Root.Store) sealed with verdict = ok"

    -- 2. Compile `Gen.M0.Root.cliEntry` onto single `OwnershipIO.WorldRunner` binary via `build-exe`
    buildOut ← executeAction cfg
                 (build-exe "link verified microservice tree onto single WorldRunner" "Gen.M0.Root.cliEntry")
                 >>= expectAccepted "M0 build-exe"
    assert ("expected candidate sha256 from build-exe, got:\n" ++ˢ buildOut) (contains "candidate sha256=" buildOut)
    (procResult zero fileOut _) ← readProcessAt "" 10000 "file" ((ws / "bin/candidate") ∷ []) ""
      where (procResult _ o e) → failIO ("file check failed: " ++ˢ o ++ˢ e)
    assert ("expected statically linked ELF candidate, got: " ++ˢ fileOut) (contains "statically linked" fileOut)
    F.putStrLn ("PASS  2. Gen.M0.Root.cliEntry linked onto single static WorldRunner binary: " ++ˢ fileOut)

    -- 3. Execute in `fsbox` verifying authorized write (`exit 0`, exact bytes) & expired rejection (`exit 145`, 0 files)
    just relay ← ensureRelay repo
      where nothing → failIO "ensureRelay failed to build sandbox relays"
    let fsEnv = sessionTools ref (ws / "bin/candidate") relay (ws / "tmp/fsbox-probe")
    (_ , obsAuth , snapAuth , obsExp , snapExp) ← evalIO fsEnv fsboxProbeProg tt
    assert "expected authorized vault run to exit 0 in fsbox" (isExitCode 0 (Fs.exitStatus obsAuth))
    assert "expected vault/record.txt with exact secret bytes in fsbox snapshot"
      (hasVaultRecord (bytes "VAULT_AUTH_‿_OK") (Fs.entries snapAuth))
    assert "expected expired vault run to exit 145 in fsbox" (isExitCode 145 (Fs.exitStatus obsExp))
    assert ("expected 0 created files/dirs on expired token, got " ++ˢ show (length (Fs.entries snapExp)))
      (length (Fs.entries snapExp) ≡ᵇ 0)
    F.putStrLn "PASS  3. fsbox verified authorized write (exit 0, vault/record.txt exact bytes) & expired rejection (exit 145, 0 files)"
    F.putStrLn "ALL PROTOCOL GLUING END-TO-END TESTS PASSED"
