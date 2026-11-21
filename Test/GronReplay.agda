{-# OPTIONS --guardedness #-}
module Test.GronReplay where

open import Data.Bool.Base using (Bool; true; false; not; _∧_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Product using (_×_; _,_)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (⊤; tt)
open import IO.Primitive using (IO; return; _>>=_)
import IO.Primitive.Finite as F
open import System.Environment.Primitive using (getArgs)
open import OwnershipIO.FFI using (failIO)
open import OwnershipIO.MetaFFI using (_>>_)
open import Code using (Code; modName; decls; _==ˢ_)
open import Code.Tree using (node)
open import Code.Codecs using (HomeValue)
open import Code.Transport using (plan; moves; Proarrow; specΔ; alignSpecΔ; mergeMoves; nullᵇ)
open import Code.Protocol using (nodeTask)
open import Code.HarnessCore using (checkCandidateGates)
open import Code.Submission using (Submission; parseSubmission; submitPlan; addMoves)
import Code.Parse as P
open import Code.Render using (render)
open import Code.Encode using (encodeCanonical)
import Code.Lift as L
import Code.PolyTransport as PT
import Store.CAS as CAS
open import Store.Verify using (verifyCommitDAG)

private
  require : ∀ {A : Set} → String → Maybe A → IO A
  require label nothing = failIO ("cannot decode " ++ˢ label)
  require label (just x) = return x

  read : ∀ {A : Set} → (String → Maybe A) → String → IO A
  read decode path = F.readFile path >>= λ txt → require path (decode txt)

  assert : String → Bool → IO ⊤
  assert _ true = return tt
  assert e false = failIO e

  submittedMoves : Submission → Maybe (List Proarrow)
  submittedMoves (submitPlan _ _ [] ms) = just ms
  submittedMoves (addMoves ms _) = just ms
  submittedMoves _ = nothing

  checkPlan : String → String → String → String → String → String → IO ⊤
  checkPlan before after oldSpec newSpec locked reply = do
    old ← read P.parse before
    new ← read P.parse after
    oldDS ← read P.parseDecls oldSpec
    newDS ← read P.parseDecls newSpec
    pending ← read P.parsePlan locked
    submission ← read parseSubmission reply
    ms ← require "plan or add-moves" (submittedMoves submission)
    let delta = alignSpecΔ old oldDS (specΔ (modName new) newDS [])
        pl = plan "gron replay" (decls new) (mergeMoves (moves pending) ms)
    check (checkCandidateGates (nodeTask delta [] nothing) old pl new)
    where
    check : Maybe String → IO ⊤
    check nothing = return tt
    check (just e) = failIO e

  -- v3 saved a vertical keyNotation/renderKey commuting square. Exercise
  -- that same proof as a horizontal descriptor, including a bad endpoint.
  checkLift : String → String → String → String → IO ⊤
  checkLift base upper iface descriptor = do
    b ← read P.parse base
    u ← read P.parse upper
    ds ← read P.parseDecls iface
    l ← read P.parseLift descriptor
    assert "vertical commuting square" (nullᵇ (L.checkLift b u ds l))
    let squares = map (λ e → PT.polySquareRefs (L.baseUnit e ∷ []) (L.upperUnit e ∷ [])
                                (L.squareUnit e) (L.requiredRefs e)) (L.endpoints l)
        horizontal = PT.transportSpecTree (modName b) (modName u) [] squares
        reversed = map (λ e → PT.polySquareRefs (L.upperUnit e ∷ []) (L.baseUnit e ∷ [])
                                 (L.squareUnit e) (L.requiredRefs e)) (L.endpoints l)
        invalid = PT.transportSpecTree (modName b) (modName u) [] reversed
    assert "descriptor has no endpoints" (not (nullᵇ squares))
    assert "horizontal commuting square" (nullᵇ (PT.checkPolyTransport b u ds horizontal))
    assert "reversed endpoint units accepted" (not (nullᵇ (PT.checkPolyTransport b u ds invalid)))

  readLeaf : String → String → String → String → IO HomeValue
  readLeaf prog spec mem shape = do
    c ← read P.parse prog
    ds ← read P.parseDecls spec
    m ← read P.parseMemory mem
    sh ← read P.parseShape shape
    caseShape sh (node [] , c , m , ds , tt)
    where
    caseShape : Code.Tree.HomeShape → HomeValue → IO HomeValue
    caseShape (node []) h = return h
    caseShape (node (_ ∷ _)) _ = failIO "expected archived gron leaf"

  dualView : String → String → String → String → String → String → String → IO ⊤
  dualView store tip fresh prog spec memory shape = do
    commit ← CAS.getCommit store tip >>= require "archived commit"
    assert "missing presentation tree" (is-just (CAS.presentation commit))
    verifyCommitDAG store tip >>= assert "archived commit DAG failed verification"
    readHome ← CAS.newCommitHomeReader store
    loaded ← readHome commit >>= require "dual-view tree"
    replay ← readLeaf prog spec memory shape
    actual ← CAS.storeTreeCommit fresh (CAS.parents commit) (CAS.epoch commit) (CAS.why commit) replay
    assert "replayed commit differs from historical tip" (actual ==ˢ tip)
    restored ← CAS.storeTreeCommit fresh (CAS.parents commit) (CAS.epoch commit) (CAS.why commit) loaded
    assert "restored presentation changed semantic or display root" (restored ==ˢ tip)

  dispatch : List String → IO ⊤
  dispatch ("roundtrip" ∷ f ∷ []) = read P.parse f >>= λ c → F.putStrLn (render c)
  dispatch ("canonical" ∷ f ∷ []) = read P.parse f >>= λ c → F.putStrLn (encodeCanonical c)
  dispatch ("plan" ∷ a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) = checkPlan a b c d e f
  dispatch ("lift" ∷ a ∷ b ∷ c ∷ d ∷ []) = checkLift a b c d
  dispatch ("cas" ∷ a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []) = dualView a b c d e f g
  dispatch _ = failIO "expected roundtrip, canonical, plan, lift or cas"

main : IO ⊤
main = getArgs >>= dispatch
