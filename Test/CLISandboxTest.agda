{-# OPTIONS --guardedness #-}
module Test.CLISandboxTest where

open import Agda.Builtin.Char using (primCharEquality)
open import Data.Bool.Base using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; any; tails; take; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String.Base using (String; toList) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (⊤; tt)
open import IO.Primitive using (IO; return; _>>=_)
import IO.Primitive.Finite as F
open import System.Environment.Primitive using (getArgs; setEnv)
open import OwnershipIO using (RunningIO; onCall; onStop)
open import OwnershipIO.FFI
open import OwnershipIO.MetaFFI using (_>>_; withPrivateTemp)
open import Code using (eqList; _==ˢ_; eqCode; eqDecls; eqBool; unit; mkQ)
open import Code.AI
open import Code.CLI using (runTaskIn)
open import Code.Codecs using (HomeValue; loadHome; eqMemory)
open import Code.Tree using (node)
import Store.CAS as CAS
open import Test.HarnessPure using (submission)

private
  infixl 6 _/_
  _/_ : String → String → String
  dir / file = dir ++ˢ "/" ++ˢ file

  assert : String → Bool → IO ⊤
  assert label true = return tt
  assert label false = failIO ("CLISandboxTest: " ++ˢ label)

  require : ∀ {A : Set} → String → Maybe A → IO A
  require label nothing = failIO ("CLISandboxTest: missing " ++ˢ label)
  require _ (just x) = return x

  contains : String → String → Bool
  contains needle haystack = any (λ s → eqList primCharEquality chars (take (length chars) s)) (tails (toList haystack))
    where chars = toList needle

  header = "module CLINode where\nimport Context.Blueprint\nimport Context.PolyTransport\nopen import Data.Nat using (ℕ)\n"
  body = "x : ℕ\nx = 7\n"
  reason = "x denotes seven"
  forbidden = "sandbox: forbidden module name or import in CLINode"
  syntaxError = "sandbox: expected a named Agda module"

  -- Each proposal must arrive with the diagnostic from the preceding real tool call.
  drafts : List (String × String)
  drafts = ("" , submission "host import" (header ++ˢ "import Code.Harness\n" ++ˢ body) [] []) ∷
           (forbidden , submission "syntax error" (header ++ˢ "x : ℕ\nx = )\n") [] []) ∷
           (syntaxError , submission reason (header ++ˢ body) [] []) ∷ []

  rollout : String → String → String
  rollout tmp tid = tmp / "codex/sessions/2026/11/19" / ("rollout-2026-11-19T08-00-00-" ++ˢ tid ++ˢ ".jsonl")

  checkFiles : String → String → Bool → IO ⊤
  checkFiles tmp tid present = do
    check (tmp / "threads" / (tid ++ˢ ".thread"))
    check (tmp / "threads" / (tid ++ˢ ".jsonl"))
    check (rollout tmp tid)
    where
      check : String → IO ⊤
      check path = fileExists path >>= λ exists → assert ("unexpected file state at " ++ˢ path) (eqBool exists present)

  AI = RunningIO AIReq AIReply (⊤ × ⊤)

  nodeAI : CodexConfig → String → IO AI
  nodeAI cfg tmp = do
    srv ← codexService cfg
    steps ← newIORef drafts
    return (record { onCall = request srv steps ; onStop = onStop srv })
    where
      request : AI → IORef (List (String × String)) → AIReq → IO AIReply
      request srv steps q@(propose prompt retry) = readIORef steps >>= λ where
        [] → failIO ("unexpected CLI retry:\n" ++ˢ prompt)
        ((diagnostic , reply) ∷ rest) → do
          assert ("expected diagnostic " ++ˢ diagnostic)
            (if diagnostic ==ˢ "" then not retry else retry ∧ contains diagnostic prompt)
          writeIORef steps rest
          F.writeFile (tmp / "reply") reply
          onCall srv q
      request srv steps q@(accept _) = do
        [] ← readIORef steps where (_ ∷ _) → failIO "accepted before the corrected proposal"
        tid ← F.readFile (tmp / "fork.id")
        checkFiles tmp tid true
        log ← F.readFile (rollout tmp tid)
        assert "both diagnostics resumed the proposal fork" (contains forbidden log ∧ contains syntaxError log)
        reply ← onCall srv q
        checkFiles tmp tid false
        return reply
      request srv steps q = onCall srv q

  compareHome : HomeValue → HomeValue → Bool
  compareHome (node [] , c , m , i , _) (node [] , c′ , m′ , i′ , _) =
    eqCode c c′ ∧ eqDecls i i′ ∧ eqMemory m m′ ∧
    eqMemory m ((unit (mkQ ("CLINode" ∷ "x" ∷ [])) , reason ∷ []) ∷ [])
  compareHome _ _ = false

  runCLI : String → String → CodexConfig → IO ⊤
  runCLI repo tmp cfg = do
    let state = tmp / "state"
        cas = state / "cas"
        spec = tmp / "spec.agda"
    F.writeFile spec (header ++ˢ "postulate x : ℕ\n")
    runTaskIn repo (ServiceBackend (nodeAI cfg tmp)) spec state [] nothing
    saved ← loadHome state >>= require "CLI generation"
    key ← CAS.readRef cas "current" >>= require "CAS current ref"
    snapshot ← CAS.loadHomeCAS cas key >>= require "verified CAS tree"
    assert "generation and CAS code, interface and accepted memory" (compareHome saved snapshot)
    tid ← F.readFile (sessions cfg / "CLINode.id")
    checkFiles tmp tid true
    log ← F.readFile (rollout tmp tid)
    assert "main thread retained initialization and acceptance"
      (contains "Reply READY" log ∧ contains reason log ∧ not (contains "TRANSIENT DIAGNOSTIC" log))
    F.putStrLn "PASS  closed-node import gate, syntax retry, scratch retirement on accept and CAS round trip"

    -- The absent module also prevents a regressed entry point from reaching a live AI.
    F.writeFile spec "module ForbiddenSpec where\nimport Code.Harness\nimport AbsentCLITestDependency\n"
    let descriptor = tmp / "lift.sexp"
    F.writeFile descriptor "(lift \"CLINode\" \"ForbiddenSpec\" () ())"
    rejectSpec ("node" ∷ spec ∷ tmp / "rejected-node" ∷ [])
    rejectSpec ("lift" ∷ spec ∷ tmp / "rejected-lift" ∷ state ∷ descriptor ∷ [])
    let badTypeSpec = tmp / "bad-type-spec.agda"
    F.writeFile badTypeSpec "module BadTypeSpec where\nopen import Data.Nat using (ℕ)\nopen import Data.String using (String)\nbad : ℕ → ℕ\nbad n = \"not-a-nat\"\npostulate x : ℕ\n"
    readProcessAt repo 120000 (repo / "Main") ("node" ∷ badTypeSpec ∷ tmp / "rejected-type-node" ∷ []) "" >>= λ where
      (procResult zero _ _) → failIO "CLI accepted a spec with a type error"
      (procResult (suc _) out err) →
        let msg = out ++ˢ err in
        assert msg (contains "CLI: specification failed Agda typecheck" msg
                  ∧ not (contains "supported by Cubical Agda" msg))
    dirExists (tmp / "rejected-type-node") >>= λ exists → assert "rejected spec left no CLI state directory" (not exists)
    F.putStrLn "PASS  Main node and Main lift reject the top-level spec before execution"
    where
      rejectSpec : List String → IO ⊤
      rejectSpec args = readProcessAt repo 120000 (repo / "Main") args "" >>= λ where
        (procResult zero _ _) → failIO "CLI accepted the forbidden spec"
        (procResult (suc _) out err) → assert (out ++ˢ err)
          (contains "sandbox: forbidden module name or import in ForbiddenSpec" (out ++ˢ err))

  lifecycle : CodexConfig → String → IO ⊤
  lifecycle cfg tmp = do
    mainId ← F.readFile (sessions cfg / "CLINode.id")
    mainLog ← F.readFile (rollout tmp mainId)
    srv ← codexService cfg
    _ ← onCall srv (bindNode "OtherSlot" (just mainId))
    child ← onCall srv (forkNode "Child")
    let childId = AIReply.threadId child
    childLog ← F.readFile (rollout tmp childId)

    -- A faulty fork reply must never grant deletion rights to these IDs.
    let reportAs = λ tid → F.writeFile (tmp / "reported-id") tid >> onCall srv (propose "draft" false)
        unrelated = rollout tmp "00000000-0000-4000-b000-000000000001"
    F.writeFile unrelated "another instance"
    _ ← reportAs mainId
    _ ← reportAs childId
    _ ← reportAs "*"
    _ ← reportAs ""

    _ ← onCall srv (propose "first draft" false)
    first ← F.readFile (tmp / "fork.id")
    checkFiles tmp first true
    _ ← onCall srv (propose "new turn" false)
    second ← F.readFile (tmp / "fork.id")
    checkFiles tmp first false
    checkFiles tmp second true
    F.writeFile (tmp / "fail-resume") ""
    _ ← onCall srv (propose "full prompt\nTRANSIENT DIAGNOSTIC\nparse error" true)
    last ← F.readFile (tmp / "fork.id")
    checkFiles tmp second false
    checkFiles tmp last true
    let near = sessions cfg / (last ++ˢ ".jsonl.bak")
        outside = tmp / "outside"
    F.writeFile near "keep"
    mkdirP outside
    F.writeFile (outside / (last ++ˢ ".jsonl")) "keep"
    linkPath outside (sessions cfg / "linked")
    _ ← onStop srv
    checkFiles tmp last false
    F.readFile near >>= λ s → assert "similar filename preserved" (s ==ˢ "keep")
    F.readFile (outside / (last ++ˢ ".jsonl")) >>= λ s → assert "linked directory preserved" (s ==ˢ "keep")
    F.readFile unrelated >>= λ s → assert "unrelated session preserved" (s ==ˢ "another instance")
    checkFiles tmp mainId true
    checkFiles tmp childId true
    F.readFile (rollout tmp mainId) >>= λ s → assert "inherited main transcript preserved" (s ==ˢ mainLog)
    F.readFile (rollout tmp childId) >>= λ s → assert "child transcript preserved" (s ==ˢ childLog)
    F.putStrLn "PASS  replacement, failed resume and stop retire only the instance's scratch files"

main : IO ⊤
main = do
  repo ← currentDirectory
  (mock ∷ []) ← getArgs where _ → failIO "usage: CLISandboxTest /path/to/mock-codex"
  withPrivateTemp "/tmp" λ tmp → do
    setEnv "CLI_SANDBOX_FIXTURE" tmp
    setEnv "CODEX_HOME" (tmp / "codex")
    let cfg = record (defaultCodex tmp) { executable = mock ; timeoutMs = 10000 }
    runCLI repo tmp cfg
    lifecycle cfg tmp
