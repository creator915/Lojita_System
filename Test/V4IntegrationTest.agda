{-# OPTIONS --guardedness #-}
module Test.V4IntegrationTest where

open import Agda.Builtin.Char using (primCharEquality)
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; any; tails; take; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String.Base using (String; toList; unlines) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (⊤; tt)
open import IO.Primitive using (IO; return; _>>=_)
import IO.Primitive.Finite as F
open import System.Environment.Primitive using (getArgs; setEnv)

open import OwnershipIO using (RunningIO; onCall; onStop)
open import OwnershipIO.FFI
open import OwnershipIO.MetaFFI using (_>>_; withPrivateTemp)
open import OwnershipIO.Tools.NetFFI using (clockMs)
open import Code using (eqList; _==ˢ_; eqBool; mkQ; unit; ext; ⊥)
open import Code.Transport using (Proarrow; _⇝_; keep)
open import Code.AI
open import Code.CLI using (runTaskIn)
open import Code.SessionProtocol using (RefSpec; refSpec; local; docker; SessionAction; build-exe; run-script; drive-tree-with; finish)
open import Code.SessionRunner using (SessionConfig; sessionConfig; ActionResult; accepted; rejected; finished; executeAction)
open import Test.HarnessPure using (submission)

private
  infixl 6 _/_
  _/_ : String → String → String
  a / b = a ++ˢ "/" ++ˢ b

  assert : String → Bool → IO ⊤
  assert _ true = return tt
  assert msg false = failIO ("V4IntegrationTest FAILED: " ++ˢ msg)

  contains : String → String → Bool
  contains needle haystack =
    any (λ s → eqList primCharEquality chars (take (length chars) s)) (tails (toList haystack))
    where chars = toList needle

  expectAccepted : String → ActionResult → IO String
  expectAccepted _ (accepted msg) = return msg
  expectAccepted label (rejected err) = failIO (label ++ˢ " unexpectedly rejected:\n" ++ˢ err)
  expectAccepted label (finished s) = return s

  expectRejected : String → ActionResult → IO String
  expectRejected _ (rejected err) = return err
  expectRejected label (accepted msg) = failIO (label ++ˢ " unexpectedly accepted:\n" ++ˢ msg)
  expectRejected label (finished s) = failIO (label ++ˢ " unexpectedly finished:\n" ++ˢ s)

  sleepMsIO : ℕ → IO ⊤
  sleepMsIO ms =
    readProcessAt "" 30000 "/usr/bin/python3"
      ("-c" ∷ ("import time; time.sleep(" ++ˢ show ms ++ˢ " / 1000.0)") ∷ []) "" >>= λ _ →
    return tt

  ------------------------------------------------------------------------
  -- 1. Parallel Sibling Subpackages (3x Speedup + Instant Cancellation)
  ------------------------------------------------------------------------

  parallelSpec : String
  parallelSpec = unlines
    ( "module Gen.P0.Root where"
    ∷ "open import Data.Nat using (ℕ; _+_)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
    ∷ "postulate"
    ∷ "  total : ℕ → ℕ"
    ∷ "  law   : total 1 ≡ 6"
    ∷ [] )

  subSpecSrc : String → String → ℕ → String
  subSpecSrc modN fn val = unlines
    ( ("module " ++ˢ modN ++ˢ " where")
    ∷ "open import Data.Nat using (ℕ)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
    ∷ "postulate"
    ∷ ("  " ++ˢ fn ++ˢ " : ℕ → ℕ")
    ∷ ("  " ++ˢ fn ++ˢ "-law : " ++ˢ fn ++ˢ " 1 ≡ " ++ˢ show val)
    ∷ [] )

  subImplSrc : String → String → ℕ → String
  subImplSrc modN fn val = unlines
    ( ("module " ++ˢ modN ++ˢ " where")
    ∷ "open import Data.Nat using (ℕ)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl)"
    ∷ (fn ++ˢ " : ℕ → ℕ")
    ∷ (fn ++ˢ " _ = " ++ˢ show val)
    ∷ (fn ++ˢ "-law : " ++ˢ fn ++ˢ " 1 ≡ " ++ˢ show val)
    ∷ (fn ++ˢ "-law = refl")
    ∷ [] )

  parallelRootImpl : String
  parallelRootImpl = unlines
    ( "module Gen.P0.Root where"
    ∷ "open import Data.Nat using (ℕ; _+_)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)"
    ∷ "import Gen.P0.Root.SubA as A"
    ∷ "import Gen.P0.Root.SubB as B"
    ∷ "import Gen.P0.Root.SubC as C"
    ∷ "total : ℕ → ℕ"
    ∷ "total n = (A.fa n + B.fb n) + C.fc n"
    ∷ "law : total 1 ≡ 6"
    ∷ "law = cong₂ _+_ (cong₂ _+_ A.fa-law B.fb-law) C.fc-law"
    ∷ [] )

  extQ : List String → Code.Obj
  extQ ns = ext (mkQ ns)

  parallelRootPlan : String
  parallelRootPlan = submission "decompose into 3 independent siblings"
    parallelRootImpl
    ( ("Gen.P0.Root.SubA" , subSpecSrc "Gen.P0.Root.SubA" "fa" 1)
    ∷ ("Gen.P0.Root.SubB" , subSpecSrc "Gen.P0.Root.SubB" "fb" 2)
    ∷ ("Gen.P0.Root.SubC" , subSpecSrc "Gen.P0.Root.SubC" "fc" 3)
    ∷ [] )
    ( (⊥ ⇝ extQ ("Gen" ∷ "P0" ∷ "Root" ∷ "SubA" ∷ "fa" ∷ []))
    ∷ (⊥ ⇝ extQ ("Gen" ∷ "P0" ∷ "Root" ∷ "SubA" ∷ "fa-law" ∷ []))
    ∷ (⊥ ⇝ extQ ("Gen" ∷ "P0" ∷ "Root" ∷ "SubB" ∷ "fb" ∷ []))
    ∷ (⊥ ⇝ extQ ("Gen" ∷ "P0" ∷ "Root" ∷ "SubB" ∷ "fb-law" ∷ []))
    ∷ (⊥ ⇝ extQ ("Gen" ∷ "P0" ∷ "Root" ∷ "SubC" ∷ "fc" ∷ []))
    ∷ (⊥ ⇝ extQ ("Gen" ∷ "P0" ∷ "Root" ∷ "SubC" ∷ "fc-law" ∷ []))
    ∷ [] )

  min3 : ℕ → ℕ → ℕ → ℕ
  min3 a b c = let m = if a <ᵇ b then a else b in if m <ᵇ c then m else c

  max3 : ℕ → ℕ → ℕ → ℕ
  max3 a b c = let m = if a <ᵇ b then b else a in if m <ᵇ c then c else m

  testParallelSiblings : String → String → IO ⊤
  testParallelSiblings repo tmp = do
    startA ← newIORef zero
    startB ← newIORef zero
    startC ← newIORef zero
    endA   ← newIORef zero
    endB   ← newIORef zero
    endC   ← newIORef zero
    let ws = tmp / "ws-parallel"
        runTimedSibling : IORef ℕ → IORef ℕ → String → String → ℕ → IO AIReply
        runTimedSibling sRef eRef modN fn val = do
          ts ← clockMs
          writeIORef sRef ts
          sleepMsIO 1800
          te ← clockMs
          writeIORef eRef te
          return (aiReply (submission ("impl " ++ˢ fn) (subImplSrc modN fn val) [] []) modN)
        mkParallelAI : IO (RunningIO AIReq AIReply (⊤ × ⊤))
        mkParallelAI = do
          slotRef ← newIORef ""
          return (record
            { onCall = λ where
                (bindNode n _) → writeIORef slotRef n >> return (aiReply "bound" n)
                (forkNode n)   → return (aiReply "" n)
                (accept _)     → return (aiReply "accepted" "")
                (propose _ _)  → readIORef slotRef >>= λ s →
                  if s ==ˢ "Gen.P0.Root" then return (aiReply parallelRootPlan s)
                  else if s ==ˢ "Gen.P0.Root.SubA" then runTimedSibling startA endA "Gen.P0.Root.SubA" "fa" 1
                  else if s ==ˢ "Gen.P0.Root.SubB" then runTimedSibling startB endB "Gen.P0.Root.SubB" "fb" 2
                  else if s ==ˢ "Gen.P0.Root.SubC" then runTimedSibling startC endC "Gen.P0.Root.SubC" "fc" 3
                  else failIO ("unexpected slot " ++ˢ s)
            ; onStop = return (tt , tt) })
        cfg = sessionConfig repo ws "parallel test" (refSpec (local "/bin/cat") [] 30000)
                (ScriptedBackend []) (λ _ → ParallelServiceBackend mkParallelAI)
    _ ← executeAction cfg (drive-tree-with "P0" "test parallel siblings" parallelSpec [] nothing nothing)
          >>= expectAccepted "parallel drive-tree"
    sa ← readIORef startA
    sb ← readIORef startB
    sc ← readIORef startC
    ea ← readIORef endA
    eb ← readIORef endB
    ec ← readIORef endC
    -- 3 siblings * 1800ms serialized would span >= 5400ms; parallel overlaps all 3 into ~1800ms (< 2500ms)!
    let startSpread  = Data.Nat.Base._∸_ (max3 sa sb sc) (min3 sa sb sc)
        siblingsSpan = Data.Nat.Base._∸_ (max3 ea eb ec) (min3 sa sb sc)
    F.putStrLn ("Parallel 3-sibling start spread: " ++ˢ show startSpread ++ˢ "ms, total sibling span: " ++ˢ show siblingsSpan ++ˢ "ms (vs >= 5400ms serial)")
    assert ("expected all 3 siblings to start concurrently (< 600ms spread), got " ++ˢ show startSpread ++ˢ "ms") (startSpread <ᵇ 600)
    assert ("expected parallel 3x speedup (< 2600ms vs 5400ms serial), got " ++ˢ show siblingsSpan ++ˢ "ms") (siblingsSpan <ᵇ 2600)
    F.putStrLn "PASS  1A. 3 independent sibling subpackages execute concurrently in parallel (3x wall-clock speedup)"

    -- Test 1B: Instant sibling cancellation via `stop` when a fast sibling returns `contradiction`!
    let cancelSpec = unlines
          ( "module Gen.C0.Root where"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
          ∷ "postulate"
          ∷ "  ans : ℕ"
          ∷ "  ans-law : ans ≡ 7"
          ∷ [] )
        badSubSpec = unlines
          ( "module Gen.C0.Root.FastBad where"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
          ∷ "postulate"
          ∷ "  v : ℕ"
          ∷ "  p1 : v ≡ 7"
          ∷ "  p2 : v ≡ 8"
          ∷ [] )
        slowSubSpec = unlines
          ( "module Gen.C0.Root.SlowUnused where"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "postulate u : ℕ"
          ∷ [] )
        firstRoot = unlines
          ( "module Gen.C0.Root where"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
          ∷ "import Gen.C0.Root.FastBad as FB"
          ∷ "import Gen.C0.Root.SlowUnused as SU"
          ∷ "ans : ℕ"
          ∷ "ans = FB.v"
          ∷ "ans-law : ans ≡ 7"
          ∷ "ans-law = FB.p1"
          ∷ [] )
        firstPlan = submission "try FastBad and SlowUnused" firstRoot
          (("Gen.C0.Root.FastBad" , badSubSpec) ∷ ("Gen.C0.Root.SlowUnused" , slowSubSpec) ∷ [])
          ( (⊥ ⇝ extQ ("Gen" ∷ "C0" ∷ "Root" ∷ "FastBad" ∷ "v" ∷ []))
          ∷ (⊥ ⇝ extQ ("Gen" ∷ "C0" ∷ "Root" ∷ "FastBad" ∷ "p1" ∷ []))
          ∷ (⊥ ⇝ extQ ("Gen" ∷ "C0" ∷ "Root" ∷ "FastBad" ∷ "p2" ∷ []))
          ∷ (⊥ ⇝ extQ ("Gen" ∷ "C0" ∷ "Root" ∷ "SlowUnused" ∷ "u" ∷ [])) ∷ [] )
        refuteFast = unlines
          ( "(submission (kind contradiction) (refute @r))"
          ∷ "```agda r"
          ∷ "module RefuteFast where"
          ∷ "open import Data.Empty using (⊥)"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)"
          ∷ "import Gen.C0.Root.FastBad as S"
          ∷ "neq : 7 ≡ 8 → ⊥"
          ∷ "neq ()"
          ∷ "absurd : ⊥"
          ∷ "absurd = neq (trans (sym S.p1) S.p2)"
          ∷ "```" ∷ [] )
        fixedRoot = unlines
          ( "module Gen.C0.Root where"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl)"
          ∷ "ans : ℕ"
          ∷ "ans = 7"
          ∷ "ans-law : ans ≡ 7"
          ∷ "ans-law = refl"
          ∷ [] )
        fixedPlan = submission "drop inconsistent children and solve directly" fixedRoot []
          ( (extQ ("Gen" ∷ "C0" ∷ "Root" ∷ "FastBad" ∷ "v" ∷ []) ⇝ ⊥)
          ∷ (extQ ("Gen" ∷ "C0" ∷ "Root" ∷ "FastBad" ∷ "p1" ∷ []) ⇝ ⊥)
          ∷ (extQ ("Gen" ∷ "C0" ∷ "Root" ∷ "FastBad" ∷ "p2" ∷ []) ⇝ ⊥)
          ∷ (extQ ("Gen" ∷ "C0" ∷ "Root" ∷ "SlowUnused" ∷ "u" ∷ []) ⇝ ⊥) ∷ [] )
        mkCancelAI : IO (RunningIO AIReq AIReply (⊤ × ⊤))
        mkCancelAI = do
          slotRef ← newIORef ""
          return (record
            { onCall = λ where
                (bindNode n _) → writeIORef slotRef n >> return (aiReply "bound" n)
                (forkNode n)   → return (aiReply "" n)
                (accept _)     → return (aiReply "accepted" "")
                (propose prompt _) → readIORef slotRef >>= λ s →
                  if s ==ˢ "Gen.C0.Root" then
                    return (aiReply (if contains "child contradiction" prompt then fixedPlan else firstPlan) s)
                  else if s ==ˢ "Gen.C0.Root.FastBad" then return (aiReply refuteFast s)
                  else if s ==ˢ "Gen.C0.Root.SlowUnused" then
                    sleepMsIO 15000 >> return (aiReply (submission "slow" "module Gen.C0.Root.SlowUnused where\nopen import Data.Nat using (ℕ)\nu : ℕ\nu = 0\n" [] []) s)
                  else failIO ("unexpected cancel slot " ++ˢ s)
            ; onStop = return (tt , tt) })
        cfgCancel = sessionConfig repo ws "cancel test" (refSpec (local "/bin/cat") [] 30000)
                      (ScriptedBackend []) (λ _ → ParallelServiceBackend mkCancelAI)
    c0 ← clockMs
    _ ← executeAction cfgCancel (drive-tree-with "C0" "test sibling cancellation" cancelSpec [] nothing nothing)
          >>= expectAccepted "cancel drive-tree"
    c1 ← clockMs
    let cancelElapsed = Data.Nat.Base._∸_ c1 c0
    F.putStrLn ("Cancellation tree elapsed: " ++ˢ show cancelElapsed ++ˢ "ms (vs 15000ms slow sibling)")
    assert ("expected instant sibling stop cancellation (< 5000ms), got " ++ˢ show cancelElapsed ++ˢ "ms")
      (cancelElapsed <ᵇ 5000)
    F.putStrLn "PASS  1B. Sibling contradiction cancels in-flight 15s sibling immediately via clean `stop`"

    -- Test 1C: Dialectica `g`-invariant sibling continuation:
    -- `SubBad` refutes quickly while `SubKeep` runs in flight (700ms). Parent fixes ONLY `SubBad`
    -- without touching `SubKeep`'s interface or `g` references (`impactsChild == false`).
    -- Verify `SubKeep` continues uninterrupted (propose called exactly ONCE!).
    keepCountRef ← newIORef zero
    badCountRef  ← newIORef zero
    let gSpec = unlines
          ( "module Gen.G0.Root where"
          ∷ "open import Data.Nat using (ℕ; _+_)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
          ∷ "postulate"
          ∷ "  res : ℕ"
          ∷ "  res-law : res ≡ 10"
          ∷ [] )
        gBad1 = unlines
          ( "module Gen.G0.Root.SubBad where"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
          ∷ "postulate"
          ∷ "  a : ℕ"
          ∷ "  a1 : a ≡ 4"
          ∷ "  a2 : a ≡ 5"
          ∷ [] )
        gBad2 = unlines
          ( "module Gen.G0.Root.SubBad where"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
          ∷ "postulate"
          ∷ "  a : ℕ"
          ∷ "  a1 : a ≡ 4"
          ∷ [] )
        gKeepSpec = unlines
          ( "module Gen.G0.Root.SubKeep where"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
          ∷ "postulate"
          ∷ "  b : ℕ"
          ∷ "  b1 : b ≡ 6"
          ∷ [] )
        gRootSrc = unlines
          ( "module Gen.G0.Root where"
          ∷ "open import Data.Nat using (ℕ; _+_)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)"
          ∷ "import Gen.G0.Root.SubBad as A"
          ∷ "import Gen.G0.Root.SubKeep as B"
          ∷ "res : ℕ"
          ∷ "res = A.a + B.b"
          ∷ "res-law : res ≡ 10"
          ∷ "res-law = cong₂ _+_ A.a1 B.b1"
          ∷ [] )
        gPlan1 = submission "initial split" gRootSrc
          (("Gen.G0.Root.SubBad" , gBad1) ∷ ("Gen.G0.Root.SubKeep" , gKeepSpec) ∷ [])
          ( (⊥ ⇝ extQ ("Gen" ∷ "G0" ∷ "Root" ∷ "SubBad" ∷ "a" ∷ []))
          ∷ (⊥ ⇝ extQ ("Gen" ∷ "G0" ∷ "Root" ∷ "SubBad" ∷ "a1" ∷ []))
          ∷ (⊥ ⇝ extQ ("Gen" ∷ "G0" ∷ "Root" ∷ "SubBad" ∷ "a2" ∷ []))
          ∷ (⊥ ⇝ extQ ("Gen" ∷ "G0" ∷ "Root" ∷ "SubKeep" ∷ "b" ∷ []))
          ∷ (⊥ ⇝ extQ ("Gen" ∷ "G0" ∷ "Root" ∷ "SubKeep" ∷ "b1" ∷ [])) ∷ [] )
        gPlan2 = submission "fix SubBad only; SubKeep g-component unchanged" gRootSrc
          (("Gen.G0.Root.SubBad" , gBad2) ∷ [])
          ( keep (extQ ("Gen" ∷ "G0" ∷ "Root" ∷ "SubBad" ∷ "a" ∷ []))
          ∷ keep (extQ ("Gen" ∷ "G0" ∷ "Root" ∷ "SubBad" ∷ "a1" ∷ []))
          ∷ (extQ ("Gen" ∷ "G0" ∷ "Root" ∷ "SubBad" ∷ "a2" ∷ []) ⇝ ⊥)
          ∷ keep (extQ ("Gen" ∷ "G0" ∷ "Root" ∷ "SubKeep" ∷ "b" ∷ []))
          ∷ keep (extQ ("Gen" ∷ "G0" ∷ "Root" ∷ "SubKeep" ∷ "b1" ∷ [])) ∷ [] )
        refuteGBad = unlines
          ( "(submission (kind contradiction) (refute @r))"
          ∷ "```agda r"
          ∷ "module RefuteGBad where"
          ∷ "open import Data.Empty using (⊥)"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)"
          ∷ "import Gen.G0.Root.SubBad as S"
          ∷ "neq : 4 ≡ 5 → ⊥"
          ∷ "neq ()"
          ∷ "absurd : ⊥"
          ∷ "absurd = neq (trans (sym S.a1) S.a2)"
          ∷ "```" ∷ [] )
        mkGAI : IO (RunningIO AIReq AIReply (⊤ × ⊤))
        mkGAI = do
          slotRef  ← newIORef ""
          turnsRef ← newIORef zero
          return (record
            { onCall = λ where
                (bindNode n _) → writeIORef slotRef n >> writeIORef turnsRef zero >> return (aiReply "bound" n)
                (forkNode n)   → return (aiReply "" n)
                (accept _)     → return (aiReply "accepted" "")
                (propose prompt isRetry) → do
                  s  ← readIORef slotRef
                  tc ← readIORef turnsRef
                  writeIORef turnsRef (suc tc)
                  (if (isRetry ∧ not (s ==ˢ "Gen.G0.Root" ∧ contains "child contradiction" prompt)) ∨ (2 <ᵇ suc tc)
                     then failIO ("G0 unexpected retry/turn on " ++ˢ s ++ˢ " (tc=" ++ˢ show tc ++ˢ "):\n" ++ˢ prompt)
                     else return tt)
                  (if s ==ˢ "Gen.G0.Root" then
                      return (aiReply (if contains "child contradiction" prompt then gPlan2 else gPlan1) s)
                    else if s ==ˢ "Gen.G0.Root.SubBad" then (do
                      bc ← readIORef badCountRef
                      writeIORef badCountRef (suc bc)
                      return (aiReply (if bc ≡ᵇ zero then refuteGBad
                                       else submission "impl a" "module Gen.G0.Root.SubBad where\nopen import Data.Nat using (ℕ)\nopen import Relation.Binary.PropositionalEquality using (_≡_; refl)\na : ℕ\na = 4\na1 : a ≡ 4\na1 = refl\n" [] []) s))
                    else if s ==ˢ "Gen.G0.Root.SubKeep" then (do
                      cnt ← readIORef keepCountRef
                      writeIORef keepCountRef (suc cnt)
                      sleepMsIO 700
                      return (aiReply (submission "impl b" "module Gen.G0.Root.SubKeep where\nopen import Data.Nat using (ℕ)\nopen import Relation.Binary.PropositionalEquality using (_≡_; refl)\nb : ℕ\nb = 6\nb1 : b ≡ 6\nb1 = refl\n" [] []) s))
                    else failIO ("unexpected G0 slot " ++ˢ s))
            ; onStop = return (tt , tt) })
        cfgG = sessionConfig repo ws "g-invariance test" (refSpec (local "/bin/cat") [] 30000)
                 (ScriptedBackend []) (λ _ → ParallelServiceBackend mkGAI)
    _ ← executeAction cfgG (drive-tree-with "G0" "test g-invariant sibling continuation" gSpec [] nothing nothing)
          >>= expectAccepted "G0 drive-tree"
    keepCalls ← readIORef keepCountRef
    assert ("expected SubKeep to run undisturbed exactly once (g-invariance), got " ++ˢ show keepCalls)
      (keepCalls ≡ᵇ 1)
    F.putStrLn "PASS  1C. Dialectica g-invariance: unaffected sibling continues uninterrupted in background (1 call)"

  ------------------------------------------------------------------------
  -- 2. `build-exe` Static Linking, Entry Gate, WorldRunner Symlink & Cleanroom Docker Replay
  ------------------------------------------------------------------------

  testBuildExeGatesAndCleanroom : String → String → IO ⊤
  testBuildExeGatesAndCleanroom repo tmp = do
    let ws = tmp / "ws-cleanroom"
        logicSpec = unlines
          ( "module Gen.T0.Logic where"
          ∷ "open import Data.String using (String)"
          ∷ "open import Context.World using (CliApp; CliCaps)"
          ∷ "postulate"
          ∷ "  idStr   : String → String"
          ∷ "  candApp : CliApp CliCaps"
          ∷ [] )
        logicImpl = unlines
          ( "module Gen.T0.Logic where"
          ∷ "open import Data.Bool using (Bool; true; false; if_then_else_)"
          ∷ "open import Data.Char using (Char; toℕ)"
          ∷ "open import Data.List using (List; []; _∷_; foldl)"
          ∷ "open import Data.Nat using (ℕ; _+_; _*_; _∸_)"
          ∷ "open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)"
          ∷ "open import Data.Sum using (_⊎_; inj₁; inj₂)"
          ∷ "open import Context.Terminal using (Bytes; bytes)"
          ∷ "open import Context.World using (CliApp; CliCaps; env∈Cli; tty∈Cli; net∈Cli; NetError; describeNetError; getProgNameW; getArgsW; readStdinAllW; writeStdoutW; writeStdoutStrW; writeStderrStrW; tcpExchangeW; decodeUtf8Lossy; _>>=w_; _>>w_; pure)"
          ∷ ""
          ∷ "idStr : String → String"
          ∷ "idStr s = s"
          ∷ ""
          ∷ "endsWithUngron : List Char → Bool"
          ∷ "endsWithUngron ('u' ∷ 'n' ∷ 'g' ∷ 'r' ∷ 'o' ∷ 'n' ∷ []) = true"
          ∷ "endsWithUngron (_ ∷ cs) = endsWithUngron cs"
          ∷ "endsWithUngron [] = false"
          ∷ ""
          ∷ "parseDec : String → ℕ"
          ∷ "parseDec s = foldl (λ acc c → acc * 10 + (toℕ c ∸ 48)) 0 (toList s)"
          ∷ ""
          ∷ "handleTcp : NetError ⊎ Bytes → CliApp CliCaps"
          ∷ "handleTcp (inj₁ err) = writeStderrStrW tty∈Cli (\"TIMEOUT_OR_ERR:\" ++ˢ describeNetError err ++ˢ \"\\n\") >>w pure 2"
          ∷ "handleTcp (inj₂ bs)  = writeStdoutW tty∈Cli bs >>w pure 0"
          ∷ ""
          ∷ "dispatchArgs : List String → CliApp CliCaps"
          ∷ "dispatchArgs (\"--tcp-port\" ∷ portStr ∷ timeoutStr ∷ _) ="
          ∷ "  tcpExchangeW net∈Cli \"127.0.0.1\" (parseDec portStr) (bytes \"GET /test HTTP/1.1\\r\\nHost: 127.0.0.1\\r\\nConnection: close\\r\\n\\r\\n\") false (parseDec timeoutStr) >>=w handleTcp"
          ∷ "dispatchArgs _ = readStdinAllW env∈Cli >>=w λ bs → writeStdoutStrW tty∈Cli (idStr (decodeUtf8Lossy bs)) >>w pure 0"
          ∷ ""
          ∷ "candApp : CliApp CliCaps"
          ∷ "candApp ="
          ∷ "  getProgNameW env∈Cli >>=w λ prog →"
          ∷ "  getArgsW env∈Cli >>=w λ args →"
          ∷ "  if endsWithUngron (toList prog)"
          ∷ "    then (writeStdoutStrW tty∈Cli (\"UNGRON:\" ++ˢ prog ++ˢ \":‿\\n\") >>w pure 0)"
          ∷ "    else dispatchArgs args"
          ∷ [] )
        logicMoves =
          ( (⊥ ⇝ unit (mkQ ("Gen" ∷ "T0" ∷ "Logic" ∷ "endsWithUngron" ∷ [])))
          ∷ (⊥ ⇝ unit (mkQ ("Gen" ∷ "T0" ∷ "Logic" ∷ "parseDec" ∷ [])))
          ∷ (⊥ ⇝ unit (mkQ ("Gen" ∷ "T0" ∷ "Logic" ∷ "handleTcp" ∷ [])))
          ∷ (⊥ ⇝ unit (mkQ ("Gen" ∷ "T0" ∷ "Logic" ∷ "dispatchArgs" ∷ [])))
          ∷ [] )
        cfg = sessionConfig repo ws "cleanroom test"
                (refSpec (docker "programbench/tomnomnom_1776_gron.88a6234:task_cleanroom_v6" "/bin/cat") [] 30000)
                (ScriptedBackend [])
                (λ _ → ScriptedBackend (submission "impl" logicImpl [] logicMoves ∷ []))
    -- Drive a verified tree first
    _ ← executeAction cfg (drive-tree-with "T0" "verified logic" logicSpec [] nothing nothing)
          >>= expectAccepted "T0 drive-tree"

    -- Negative Gate 2A: `build-exe` with forbidden internal namespace MUST be rejected!
    err1a ← executeAction cfg (build-exe "attempt readProcess" "OwnershipIO.FFI.readProcess") >>= expectRejected "readProcess entry gate"
    err1b ← executeAction cfg (build-exe "attempt Harness internal" "Code.Harness.x") >>= expectRejected "Code.Harness entry gate"
    err1c ← executeAction cfg (build-exe "attempt malformed dots" "Gen.T0..Logic.candApp") >>= expectRejected "malformed dots entry gate"
    assert ("expected invalid or forbidden entry diagnostic, got:\n" ++ˢ err1a ++ˢ "\n" ++ˢ err1b ++ˢ "\n" ++ˢ err1c)
      (contains "invalid or forbidden entry" err1a ∧ contains "invalid or forbidden entry" err1b ∧ contains "invalid or forbidden entry" err1c)
    F.putStrLn "PASS  2A. build-exe rejects forbidden internal namespaces OwnershipIO.FFI.readProcess, Code.Harness.x, and malformed entries"

    -- Negative Gate 2B: `build-exe` with unverified module `Gen.Unverified.Root.app` MUST be rejected!
    err2 ← executeAction cfg (build-exe "attempt unverified module" "Gen.Unverified.Root.app") >>= expectRejected "unverified module gate"
    assert ("expected unverified Dialectica tree diagnostic, got:\n" ++ˢ err2)
      (contains "not exported by any verified (ok) Dialectica tree" err2)
    F.putStrLn "PASS  2B. build-exe rejects unverified module Gen.Unverified.Root.app not exported by any ok tree"

    -- Positive Gate 2C: Build verified `Gen.T0.Logic.candApp` via auto-synthesized `WorldRunner` glue
    _ ← executeAction cfg (build-exe "build static WorldRunner candidate" "Gen.T0.Logic.candApp") >>= expectAccepted "candApp build-exe"
    (procResult zero fileOut _) ← readProcessAt "" 10000 "file" ((ws / "bin/candidate") ∷ []) ""
      where (procResult _ o e) → failIO ("file failed: " ++ˢ o ++ˢ e)
    assert ("expected statically linked ELF binary, got: " ++ˢ fileOut) (contains "statically linked" fileOut)
    F.putStrLn ("PASS  2C. build-exe produced 100% static native ELF via Lean 4 WorldRunner: " ++ˢ fileOut)

    -- Run cleanroom container probe exercising:
    -- 1) `procExec` ref vs cand inside GLIBC 2.35 cleanroom Docker with U+203F `‿`
    -- 2) `fsbox` with `fixSymlink "ungron" "cand"` verifying `getProgName` sees `./ungron` inside container
    -- 3) `netbox` fast HTTP loopback stub (`{{PORT}}`) AND slow `httpDelayedStubMode 900` timeout inside container!
    let cleanroomReplay = unlines
          ( "{-# OPTIONS --guardedness #-}"
          ∷ "module CleanroomReplay where"
          ∷ "open import Agda.Builtin.String using (primStringEquality)"
          ∷ "open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)"
          ∷ "open import Data.List using (List; []; _∷_; length)"
          ∷ "open import Data.Maybe using (Maybe; just; nothing)"
          ∷ "open import Data.Nat using (ℕ; _≡ᵇ_)"
          ∷ "open import Data.Product using (_,_; proj₂)"
          ∷ "open import Data.Unit using (⊤; tt)"
          ∷ "import IO.Primitive as IO"
          ∷ "import IO.Primitive.Finite as F"
          ∷ "open import Ownership using (Dir; Prog; withEphemeral; mkdir; open′; openAs; call; stop; rmdir; done; _>>_; _>>=_)"
          ∷ "open import OwnershipIO.FFI using (ProcResult; procResult; exitFailure)"
          ∷ "open import SessionEnv"
          ∷ "import Context.Tools.FsSandbox as Fs"
          ∷ "import Context.Tools.NetSandbox as Net"
          ∷ ""
          ∷ "sameProc : ProcResult → ProcResult → Bool"
          ∷ "sameProc (procResult a o1 e1) (procResult b o2 e2) ="
          ∷ "  (a ≡ᵇ b) ∧ primStringEquality o1 o2 ∧ primStringEquality e1 e2"
          ∷ ""
          ∷ "fsCfg : FsConfig"
          ∷ "fsCfg = fsConfig localSandbox [] [] (fixSymlink \"ungron\" \"cand\" ∷ [])"
          ∷ ""
          ∷ "fastNetCfg : NetConfig"
          ∷ "fastNetCfg = netConfig localSandbox"
          ∷ "  (httpStubMode (httpRoute \"GET\" \"/test\" 200 \"OK\" [] (bytes \"PONG_‿\") ∷ []))"
          ∷ "  [] []"
          ∷ ""
          ∷ "slowNetCfg : NetConfig"
          ∷ "slowNetCfg = netConfig localSandbox"
          ∷ "  (httpDelayedStubMode 900 (httpRoute \"GET\" \"/test\" 200 \"OK\" [] (bytes \"LATE\") ∷ []))"
          ∷ "  [] []"
          ∷ ""
          ∷ "prog : Prog SessionΨ (Dir []) (Dir []) Bool"
          ∷ "prog = withEphemeral \"s\" ("
          ∷ "  mkdir \"procExec\" >> open′ \"procExec\" >>"
          ∷ "  call \"procExec\" (procReq \"ref\" [] \"hello-‿\\n\") >>= λ rRef →"
          ∷ "  call \"procExec\" (procReq \"cand\" [] \"hello-‿\\n\") >>= λ rCand →"
          ∷ "  stop \"procExec\" >> rmdir \"procExec\" >>"
          ∷ "  mkdir \"fs\" >> openAs \"fs\" \"fsbox\" fsCfg >>"
          ∷ "  call \"fs\" (runCmd \"./ungron\" [] [] 5000) >>= λ fsObs →"
          ∷ "  stop \"fs\" >> rmdir \"fs\" >>"
          ∷ "  mkdir \"net1\" >> openAs \"net1\" \"netbox\" fastNetCfg >>"
          ∷ "  call \"net1\" (waitPortReady 3000) >>"
          ∷ "  call \"net1\" (runClient \"cand\" (\"--tcp-port\" ∷ \"{{PORT}}\" ∷ \"3000\" ∷ []) [] 5000) >>= λ nFast →"
          ∷ "  stop \"net1\" >> rmdir \"net1\" >>"
          ∷ "  mkdir \"net2\" >> openAs \"net2\" \"netbox\" slowNetCfg >>"
          ∷ "  call \"net2\" (waitPortReady 3000) >>"
          ∷ "  call \"net2\" (runClient \"cand\" (\"--tcp-port\" ∷ \"{{PORT}}\" ∷ \"200\" ∷ []) [] 5000) >>= λ nSlow →"
          ∷ "  stop \"net2\" >> rmdir \"net2\" >>"
          ∷ "  let ok1 = sameProc rRef rCand"
          ∷ "      ok2 = Fs.eqBytes (Fs.stdoutOut fsObs) (bytes \"UNGRON:./ungron:‿\\n\")"
          ∷ "      ok3 = (length (capturedReqs nFast) ≡ᵇ 1) ∧ (case Net.exitStatus nFast of λ { (just 0) → true ; _ → false })"
          ∷ "      ok4 = case Net.exitStatus nSlow of λ { (just 2) → true ; _ → false }"
          ∷ "  in done (ok1 ∧ ok2 ∧ ok3 ∧ ok4))"
          ∷ "  where open import Function.Base using (case_of_)"
          ∷ ""
          ∷ "main : IO.IO ⊤"
          ∷ "main = evalIO sessionEnv prog tt IO.>>= λ res →"
          ∷ "  if proj₂ res then F.putStrLn \"CLEANROOM_ALL_OK\" else exitFailure"
          ∷ [] )
    obs ← executeAction cfg (run-script "replay in cleanroom docker with fsbox & netbox" cleanroomReplay)
            >>= expectAccepted "cleanroom replay"
    assert ("expected CLEANROOM_ALL_OK, got:\n" ++ˢ obs) (contains "CLEANROOM_ALL_OK" obs)
    _ ← executeAction cfg (finish "verified cleanroom replay") >>= expectAccepted "finish after cleanroom replay"
    F.putStrLn "PASS  2D. Cleanroom Docker container replay (UTF-8 U+203F, fsbox symlink argv[0], netbox loopback HTTP + slow timeout, finish gate)"

    -- Test 2E: Universal structural law + accidental point-test typo (`"<>&"` vs `"<&>"`)
    -- enables formal `contradiction` refutation via Lean 4 instead of dirty special-casing!
    let typoSpec = unlines
          ( "module Gen.Typo0.Gron where"
          ∷ "open import Data.String using (String)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_)"
          ∷ "postulate"
          ∷ "  scalarLine : String → String"
          ∷ "  scalarLine-id : ∀ (s : String) → scalarLine s ≡ s"
          ∷ "  test-angle-typo : scalarLine \"<>&\" ≡ \"<&>\""
          ∷ [] )
        refuteTypo = unlines
          ( "(submission (kind contradiction) (refute @r))"
          ∷ "```agda r"
          ∷ "module RefuteAngleTypo where"
          ∷ "open import Agda.Builtin.String using (primStringEquality)"
          ∷ "open import Data.Bool using (Bool; true; false)"
          ∷ "open import Data.Empty using (⊥)"
          ∷ "open import Data.String using (String)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)"
          ∷ "import Gen.Typo0.Gron as G"
          ∷ "true≢false : true ≡ false → ⊥"
          ∷ "true≢false ()"
          ∷ "absurd : ⊥"
          ∷ "absurd = true≢false (cong (primStringEquality \"<&>\") (trans (sym G.test-angle-typo) (G.scalarLine-id \"<>&\")))"
          ∷ "```" ∷ [] )
        cfgTypo = sessionConfig repo (tmp / "ws-typo") "typo refutation test"
                    (refSpec (local "/bin/cat") [] 30000)
                    (ScriptedBackend [])
                    (λ _ → ScriptedBackend (refuteTypo ∷ []))
    typoOut ← executeAction cfgTypo (drive-tree-with "Typo0" "test angle typo refutation" typoSpec [] nothing nothing)
                >>= expectAccepted "typo drive-tree contradiction verdict"
    assert ("expected formal contradiction verdict on angle typo, got:\n" ++ˢ typoOut)
      (contains "contradiction Typo0" typoOut ∧ contains "RefuteAngleTypo" typoOut)
    F.putStrLn "PASS  2E. Universal structural law + \"<>&\"/\"<&>\" point-test typo formally refuted via Lean 4 contradiction"

  ------------------------------------------------------------------------
  -- 3. Codex CLI `gpt-6.2-sol max ultrafast` + Native Lean 4 MCP Draft Loop
  ------------------------------------------------------------------------

  testCodexConfigAndMCPLoop : String → String → String → IO ⊤
  testCodexConfigAndMCPLoop repo tmp mockCodex = do
    let dCfg = defaultCodex (tmp / "ai-check")
    assert "defaultCodex model is gpt-6.2-sol" (model dCfg ==ˢ "gpt-6.2-sol")
    assert "defaultCodex effort is max" (effort dCfg ==ˢ "max")
    assert "defaultCodex serviceTier is ultrafast" (serviceTier dCfg ==ˢ "ultrafast")
    let sampleArgs = baseArgs dCfg "/tmp/iso" "/tmp/out"
    assert "baseArgs includes gpt-6.2-sol" (any (_==ˢ "gpt-6.2-sol") sampleArgs)
    assert "baseArgs includes service_tier=\"ultrafast\"" (any (_==ˢ "service_tier=\"ultrafast\"") sampleArgs)
    assert "baseArgs disables shell_tool" (any (_==ˢ "features.shell_tool=false") sampleArgs)
    assert "baseArgs disables unified_exec" (any (_==ˢ "features.unified_exec=false") sampleArgs)
    F.putStrLn "PASS  3A. CodexConfig defaults to gpt-6.2-sol + max + ultrafast with shell_tool=false & unified_exec=false"

    -- Test real `codexService` talking to a mock `codex` binary that invokes the
    -- spawned Lean 4 `agda2lean mcp` server (`write_draft` -> `check_agda` fail ->
    -- `patch_draft` -> `check_agda` pass -> returning ONLY `@main` reference without inline fence!)
    let state = tmp / "mcp-node-state"
        spec  = tmp / "mcp-spec.agda"
        ncfg  = record (nodeCodex repo (tmp / "mcp-ai") []) { executable = mockCodex ; timeoutMs = 30000 }
    F.writeFile spec "module Gen.M0.Target where\nopen import Data.Nat using (ℕ)\nopen import Relation.Binary.PropositionalEquality using (_≡_)\npostulate\n  twice : ℕ → ℕ\n  twice-3 : twice 3 ≡ 6\n"
    runTaskIn repo (CodexCLIBackend ncfg) spec state [] nothing
    flagsLog ← F.readFile (tmp / "mcp-codex-flags.log")
    assert "propose passed mcp_servers.codetransport" (contains "mcp_servers.codetransport=" flagsLog)
    assert "propose passed service_tier=\"ultrafast\"" (contains "service_tier=\"ultrafast\"" flagsLog)
    assert "MCP check_agda caught initial type error and passed after patch_draft"
      (contains "MCP_PATCH_LOOP_VERIFIED" flagsLog)
    F.putStrLn "PASS  3B. Codex CLI <-> Lean 4 MCP server incremental write_draft / check_agda / patch_draft loop + @main auto-attachment"

main : IO ⊤
main = do
  repo ← currentDirectory
  (mockCodex ∷ []) ← getArgs where _ → failIO "usage: V4IntegrationTest /path/to/mock-mcp-codex"
  withPrivateTemp "/tmp" λ tmp → do
    setEnv "V4_MCP_LOG" (tmp / "mcp-codex-flags.log")
    setEnv "CODEX_HOME" (tmp / "codex-home")
    testParallelSiblings repo tmp
    testBuildExeGatesAndCleanroom repo tmp
    testCodexConfigAndMCPLoop repo tmp mockCodex
    F.putStrLn "ALL V4 INTEGRATION TESTS PASSED"
