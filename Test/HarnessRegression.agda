{-# OPTIONS --guardedness #-}
module Test.HarnessRegression where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; [_])
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Ownership hiding (Home; Name; set; open′)
open import Code
open import Code.Transport
open import Code.Lift using (LiftSpec)
open import Code.Harness
open import Test.HarnessPure using (q; nat; natImport; submission; refuteSubmission; scriptedAI; checks; childOffer)

local : String → String → QName
local m n = mkQ (m ∷ n ∷ [])

qualified : String → String → QName
qualified m n = qn (m ∷ n ∷ []) (m ++ˢ "." ++ˢ n)

use : String → Decl
use m = import′ (q m) false everything []

body : String → String → List (Arg Pat) → Expr → Decl
body m n ps e = fun plain n [ clause (head (local m n) ps) (rhs e) [] ]

emptyImport boolImport : Decl
emptyImport = import′ (mkQ ("Data" ∷ "Empty" ∷ [])) true everything []
boolImport = import′ (mkQ ("Agda" ∷ "Builtin" ∷ "Bool" ∷ [])) true everything []

bottom bool truth : Expr
bottom = def (mkQ ("Data" ∷ "Empty" ∷ "⊥" ∷ []))
bool = def (mkQ ("Agda" ∷ "Builtin" ∷ "Bool" ∷ "Bool" ∷ []))
truth = con (mkQ ("Agda" ∷ "Builtin" ∷ "Bool" ∷ "true" ∷ []))

k₁ k₂ b₁ b₂ kImpl₁ kImpl₂ bImpl refutation : Code
k₁ = code (q "K") [] (natImport ∷ sig plain "inputRows" nat ∷ [])
k₂ = code (q "K") [] (boolImport ∷ sig plain "inputRows" bool ∷ [])
b₁ = code (q "B") [] (emptyImport ∷ sig plain "ready" bottom ∷ [])
b₂ = code (q "B") [] (natImport ∷ sig plain "ready" nat ∷ [])
kImpl₁ = record k₁ { decls = decls k₁ ++ [ body "K" "inputRows" [] (lit (natL 1)) ] }
kImpl₂ = record k₂ { decls = decls k₂ ++ [ body "K" "inputRows" [] truth ] }
bImpl = record b₂ { decls = decls b₂ ++ [ body "B" "ready" [] (lit (natL 2)) ] }
refutation = code (q "Refute") [] (emptyImport ∷ use "B" ∷ sig plain "absurd" bottom
  ∷ body "Refute" "absurd" [] (def (qualified "B" "ready")) ∷ [])

result rows answer : QName
result = local "P" "result"
rows   = local "K" "inputRows"
answer = local "B" "ready"

parentMain : Expr → Code
parentMain e = code (q "P") [] (natImport ∷ use "B" ∷ use "K"
  ∷ sig plain "result" nat ∷ body "P" "result" [] e ∷ [])

-- P has a previous, durable interface. Its new result starts with a birth seed.
p₀ : Code
p₀ = code (q "P") [] (natImport ∷ sig plain "anchor" nat ∷ body "P" "anchor" [] (lit (natL 0)) ∷ [])

initialMemory : Memory
initialMemory = [ unit (local "P" "anchor") , [ "original P" ] ]

homeP : Model (HomeSt (node []))
homeP = p₀ , initialMemory , (natImport ∷ sig plain "anchor" nat ∷ []) , tt

taskP : NodeTask
taskP = nodeTask (specΔ (q "P") (natImport ∷ sig plain "result" nat ∷ []) [ ⊥ ⇝ ext result ]) [] nothing

data FirstK : Set where
  committed unfinished : FirstK

round₁ : String
round₁ = submission "P round1" "P1" (("K" , "K1") ∷ ("B" , "B1") ∷ [])
  (⊥ ⇝ ext rows ∷ ⊥ ⇝ ext answer ∷ [])

round₂ : FirstK → String
round₂ first = submission "P round2" "P2" (("K" , "K2") ∷ ("B" , "B2") ∷ [])
  (incoming first ∷ keep (ext answer) ∷ [])
  where
    -- Both parent descriptions need translation at the child's actual slot.
    incoming : FirstK → Proarrow
    incoming committed  = ⊥ ⇝ ext rows
    incoming unfinished = keep (ext rows)

-- Each port has its own nominal Setting. Only P imports both modules.
setting : String → List Decl
setting m = dataSig plain "Setting" [] (set 0)
          ∷ dataDef plain "Setting" [] [ "on" , def (local m "Setting") ] ∷ []

onName : String → String → QName
onName m spelling = qn (m ∷ "Setting" ∷ "on" ∷ []) spelling

parser engine parserImpl engineImpl adapterMain : Code
parser = code (q "Parser") [] (setting "Parser" ++ [ sig plain "parse" (def (local "Parser" "Setting")) ])
engine = code (q "Engine") [] (natImport ∷ (setting "Engine" ++
  [ sig plain "run" (fun′ (vis (def (local "Engine" "Setting"))) nat) ]))
parserImpl = record parser { decls = decls parser ++ [ body "Parser" "parse" [] (con (onName "Parser" "on")) ] }
engineImpl = record engine { decls = decls engine ++ [ body "Engine" "run" [ vis wildP ] (lit (natL 1)) ] }
adapterMain = code (q "P") [] (natImport ∷ use "Parser" ∷ use "Engine"
  ∷ sig plain "adapt" (fun′ (vis (def (qualified "Parser" "Setting"))) (def (qualified "Engine" "Setting")))
  ∷ body "P" "adapt" [ vis (conP (onName "Parser" "Parser.on") []) ] (con (onName "Engine" "Engine.on"))
  ∷ sig plain "result" nat ∷ body "P" "result" []
      (app (def (qualified "Engine" "run")) (vis (app (def (local "P" "adapt")) (vis (def (qualified "Parser" "parse"))))))
  ∷ [])

portPlan : String → String
portPlan parserSrc = submission "copy Setting and convert at P" "adapter"
  (("Parser" , parserSrc) ∷ ("Engine" , "engine") ∷ [])
  (⊥ ⇝ unit (local "P" "adapt") ∷ map (λ n → ⊥ ⇝ ext n)
    (local "Parser" "Setting" ∷ local "Parser" "parse" ∷ local "Engine" "Setting" ∷ local "Engine" "run" ∷ []))

-- Dump is deterministic. A subspec can only parse in isolation. The bad
-- Parser still yields an AST, so its rejection exercises the static gate too.
decode : String → List Code → DumpResult
decode "K1" [] = dumped k₁
decode "K2" [] = dumped k₂
decode "B1" [] = dumped b₁
decode "B2" [] = dumped b₂
decode "implK1" [] = dumped kImpl₁
decode "implK2" [] = dumped kImpl₂
decode "implB" [] = dumped bImpl
decode "refute" _ = dumped refutation
decode "P1" _ = dumped (parentMain (def (qualified "K" "inputRows")))
decode "P2" _ = dumped (parentMain (def (qualified "B" "ready")))
decode "P-keep-K" ds = if allᵇ (λ stub → anyᵇ (eqCode stub) ds) (b₂ ∷ k₁ ∷ [])
  then dumped (parentMain (def (qualified "K" "inputRows")))
  else dumpFailed "P needs the revised B and the existing K stub"
decode "parser" [] = dumped parser
decode "badParser" [] = dumped (record parser { decls = use "Engine" ∷ decls parser })
decode "engine" [] = dumped engine
decode "implParser" [] = dumped parserImpl
decode "implEngine" [] = dumped engineImpl
decode "adapter" ds = if eqList eqCode ds (parser ∷ engine ∷ []) then dumped adapterMain
                      else dumpFailed "P needs both independently parsed interfaces"
decode _ _ = dumpFailed "unexpected source or dependency"

isolatedDump : Server [] DumpReq DumpResult [] (Dir [])
ServerI.call isolatedDump = ask λ req → tell (parse req) (daemon isolatedDump)
  where
    parse : DumpReq → DumpResult
    parse (dumpReq src [] ds) = decode src ds
    parse (dumpReq _ (_ ∷ _) _) = dumpFailed "a sibling source reached Dump"
ServerI.stop isolatedDump = give∃Dir tt refl

Checker = Server [] AgdaCheckReq CheckResult [] (Dir [])
Children = (sh : HomeShape) → Models (Home (HomeCtx sh)) → Offer AgentS
TreeValue = Msg (∃Res HomeShape HomeSt)

environment : List String → Checker → Children → Env NodeΨ
environment replies checker kids = (λ _ → provide [] (daemon (scriptedAI replies)))
  ∷ (λ _ → provide [] (daemon isolatedDump)) ∷ (λ _ → provide [] (daemon checker)) ∷ kids ∷ []

leafReplies : FirstK → NodeTask → List String
leafReplies first t with shown (child (δ t))
... | "K" = if eqDecls (newIface (δ t)) (decls k₂) then [ submission "K round2" "implK2" [] [] ] else before first
  where
    before : FirstK → List String
    before committed  = [ submission "K round1" "implK1" [] [] ]
    before unfinished = []
... | "B" = if eqDecls (newIface (δ t)) (decls b₁) then "malformed" ∷ refuteSubmission ∷ []
            else [ submission "B repaired" "implB" [] [] ]
... | "Parser" = [ submission "Parser owns Setting" "implParser" [] [] ]
... | "Engine" = [ submission "Engine owns Setting" "implEngine" [] [] ]
... | _ = []

-- Each tested child runs its own nodeAgent, including planError and commitBelow.
leaves : FirstK → Children
leaves first sh home t = provide (environment (leafReplies first t) (checks []) childOffer) (nodeAgent sh) home t

twoRounds : FirstK → Env NodeΨ
twoRounds first = environment (round₁ ∷ round₂ first ∷ []) (checks []) (leaves first)

startP : Env NodeΨ → Running ⊤ (Maybe Verdict) TreeValue
startP env = provide env (nodeAgent (node [])) homeP taskP

-- Inspect individual oneTurn results as well as polling the external server.
Live = Σ (Slots × NodeState) (λ j → Models (Work (proj₁ j)))

entry : Env NodeΨ → Live
entry (ai ∷ dump ∷ agda ∷ kids ∷ []) =
  ([] , nodeState taskP p₀ initialMemory p₀ nothing "" Planning (node [] , tt , homeP)) ,
  (agda tt tt , dump tt tt , ai tt tt , homeP)

advance : ℕ → Env NodeΨ → Live → Live
advance zero env live = live
advance (suc fuel) env ((ks , s) , m) = advance fuel env (proj₂ (machineCall env (oneTurn ks s) m tt))

-- After glue, K and B start. On the next poll K can commit while B retries
-- once, then B returns its checked contradiction on the fourth oneTurn.
afterEvidence : FirstK → Live
afterEvidence first = advance 4 (twoRounds first) (entry (twoRounds first))

firstHome : Live → Maybe (Kid × TreeValue)
firstHome (((_ , finished) ∷ ks , s) , (_ , _ , _ , r , _)) = just (finished , Running.onStop r)
firstHome (((_ , awake) ∷ ks , s) , (_ , _ , _ , r , _)) = just (awake , Running.onStop r)
firstHome _ = nothing

-- 1. K was durable before its sibling refuted B1. Its second, changed body
-- must pass both extendsSeed and validate, with the old note on inputRows.
k-was-committed : firstHome (afterEvidence committed)
  ≡ just (finished , node [] , kImpl₁ , [ unit rows , [ "K round1" ] ] , decls k₁ , tt)
k-was-committed = refl

committed-child-ok : pollN 9 (startP (twoRounds committed)) ≡ just ok
committed-child-ok = refl

completed : FirstK → TreeValue
completed first = Running.onStop (proj₂ (observeN 9 (startP (twoRounds first))))

firstKMemory : TreeValue → Maybe Memory
firstKMemory (node (("K" , sh) ∷ ks) , (h , _)) = just (memoryOf sh h)
firstKMemory _ = nothing

two-round-memory : firstKMemory (completed committed) ≡ just [ unit rows , ("K round1" ∷ "K round2" ∷ []) ]
two-round-memory = refl

-- 2. Same parent, but K is still awake. Stopping this very channel returns
-- the vacuum (including its spec). Its next keep from P must become a birth.
k-was-still-working : firstHome (afterEvidence unfinished)
  ≡ just (awake , node [] , code (q "K") [] [] , [] , [] , tt)
k-was-still-working = refl

rolled-back-child-ok : pollN 9 (startP (twoRounds unfinished)) ≡ just ok
rolled-back-child-ok = refl

rolled-back-child-memory : firstKMemory (completed unfinished) ≡ just [ unit rows , [ "K round2" ] ]
rolled-back-child-memory = refl

-- 3. At the contradiction checkpoint the conditional plan is the new
-- baseline, while an external stop restores every leaf and the original shape.
replanningState : NodeState
replanningState = proj₂ (proj₁ (afterEvidence committed))

replanning : NodeState.phase replanningState ≡ Planning
replanning = refl

cleared-draft : NodeState.pending replanningState ≡ nothing
cleared-draft = refl

accepted-baseline : NodeState.oldCode replanningState ≡ NodeState.runningCode replanningState
accepted-baseline = refl

reseeded-result : seedArrows (δ (NodeState.task replanningState)) ≡ [ keep (unit result) ]
reseeded-result = refl

accepted-memory : notesOf (NodeState.oldMemory replanningState) (unit result) ≡ [ "P round1" ]
accepted-memory = refl

-- nodeAgent has one initial call before it enters oneTurn.
atomic-stop : Running.onStop (proj₂ (observeN 5 (startP (twoRounds committed)))) ≡ (node [] , homeP)
atomic-stop = refl

-- 4. The negative assertion observes Planning and its actual slots before
-- shutdown (shutdown by itself would roll back even an incorrectly born kid).
badEnv : Env NodeΨ
badEnv = environment [ portPlan "badParser" ] (checks []) (leaves committed)

rejection : Slots × Phase × String
rejection with proj₁ (advance 1 badEnv (entry badEnv))
... | ks , s = ks , NodeState.phase s , NodeState.diagnostic s

isolation-message : String
isolation-message = "subspec: sibling or parent imports are forbidden; copy shared port types/helpers directly into each child's subspec"

sibling-rejected : rejection ≡ ([] , Planning , isolation-message)
sibling-rejected = refl

-- Check what P receives for glue and for final link, in call order. The
-- latter requires the two closed, independent implementations including Setting.
checkDeps : List (List Code) → Checker
ServerI.call (checkDeps []) = ask λ _ → tell (fail "unexpected link") (daemon (checkDeps []))
ServerI.call (checkDeps (ds ∷ rest)) = ask λ req →
  tell (if eqList eqCode ds (dependencies req) then pass else fail "incorrect link dependencies") (daemon (checkDeps rest))
ServerI.stop (checkDeps _) = give∃Dir tt refl

-- B's contradiction triggers a partial revision. P still calls K.inputRows,
-- but submits only B2. K must reach final link with its single original note.
partialRevision : Maybe Verdict × Maybe Memory
partialRevision with observeN 9 (startP (environment (round₁ ∷ reviseB ∷ []) checker (leaves committed)))
  where
    reviseB = submission "repair only B" "P-keep-K" [ "B" , "B2" ] [ keep (ext answer) ]
    checker = checkDeps ((b₁ ∷ k₁ ∷ []) ∷ (b₂ ∷ k₁ ∷ []) ∷ (kImpl₁ ∷ bImpl ∷ []) ∷ [])
... | verdict , next = verdict , firstKMemory (Running.onStop next)

omitted-sibling-survives : partialRevision ≡ (just ok , just [ unit rows , [ "K round1" ] ])
omitted-sibling-survives = refl

copyEnv : Env NodeΨ
copyEnv = environment [ portPlan "parser" ]
  (checkDeps ((parser ∷ engine ∷ []) ∷ (engineImpl ∷ parserImpl ∷ []) ∷ [])) (leaves committed)

copied-ports-link : pollN 4 (startP copyEnv) ≡ just ok
copied-ports-link = refl

-- A parent/alias, duplicate child, and collision with an immutable base are
-- independent gates. A legal base remains importable.
portNames : List QName
portNames = q "Parser" ∷ q "Engine" ∷ []
base : Code
base = code (q "Base") [] []

parent-forbidden : subspecImportProblem (q "P") portNames [] (code (q "Parser") []
  [ import′ (qn [ "P" ] "Alias") false everything [] ]) ≡ just isolation-message
parent-forbidden = refl

duplicate-forbidden : subspecImportProblem (q "P") (q "Parser" ∷ portNames) [] parser
  ≡ just "subspec: duplicate child module name"
duplicate-forbidden = refl

shadow-forbidden : subspecImportProblem (q "P") (q "Base" ∷ portNames) [ base ] parser
  ≡ just "subspec: child module name shadows a sealed ancestor module"
shadow-forbidden = refl

ancestor-allowed : subspecImportProblem (q "P") portNames [ base ] (code (q "Parser") [] [ use "Base" ]) ≡ nothing
ancestor-allowed = refl

only-ancestor-in-child-context : (l : Maybe (Code × LiftSpec)) → baseModules
  (childTask (record taskP { maybeLift = l ; baseModules = p₀ ∷ parser ∷ engine ∷ base ∷ [] })
    (withChildIfaces ((q "Parser" , decls parser) ∷ (q "Engine" , decls engine) ∷ []) adapterMain)
    (plan "" [] []) "Parser") ≡ [ base ]
only-ancestor-in-child-context l = refl

-- Exercise renames, deletes, missing targets/sources and duplicate
-- cancellation together, including an old core name that never landed.
names : List String → List Decl
names = map (λ n → sig plain n nat)

port : String → Obj
port n = ext (local "K" n)

alignment-complete : δarrows (alignSpecΔ
  (code (q "K") [] (names ("stay" ∷ "from" ∷ "dropped" ∷ "retired" ∷ "implicit" ∷ [])))
  (names ("from" ∷ "dropped" ∷ "retired" ∷ "absent" ∷ []))
  (specΔ (q "K") (names ("stay" ∷ "to" ∷ "fresh" ∷ "implicit" ∷ "missing" ∷ []))
    (⊥ ⇝ port "stay" ∷ port "from" ⇝ port "to" ∷ port "absent" ⇝ port "stay"
    ∷ port "absent" ⇝ port "fresh" ∷ port "dropped" ⇝ ⊥ ∷ port "absent" ⇝ ⊥ ∷ [])))
  ≡ (keep (port "stay") ∷ port "from" ⇝ port "to" ∷ ⊥ ⇝ port "fresh" ∷ port "dropped" ⇝ ⊥
    ∷ keep (port "implicit") ∷ ⊥ ⇝ port "missing" ∷ port "retired" ⇝ ⊥ ∷ [])
alignment-complete = refl
