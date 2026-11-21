{-# OPTIONS --guardedness #-}
module Test.HarnessPure where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Ownership hiding (Home; set; open′; Name; specOf)
open import Code
open import Code.Transport
open import Code.Encode
open import Code.Parse using (parse)
open import Code.SExpr using (SExpr; str; sym; list; showSExpr)
open import Code.Harness

q : String → QName
q n = mkQ (n ∷ [])

nat : Expr
nat = def (qn ("Agda" ∷ "Builtin" ∷ "Nat" ∷ "Nat" ∷ []) "Nat")

natImport : Decl
natImport = import′ (qn ("Agda" ∷ "Builtin" ∷ "Nat" ∷ []) "Agda.Builtin.Nat") true everything []

ifaceX : List Decl
ifaceX = natImport ∷ sig plain "x" nat ∷ []

impl : String → Code
impl name = code (q name) [] (ifaceX ++ (fun plain "x" (clause (head (mkQ (name ∷ "x" ∷ [])) []) (rhs (lit (natL 0))) [] ∷ []) ∷ []))

δX : SpecΔ
δX = specΔ (q "X") ifaceX (keep (ext (mkQ ("X" ∷ "x" ∷ []))) ∷ [])

taskX : NodeTask
taskX = nodeTask δX [] nothing

homeX : Model (HomeSt (node []))
homeX = stubOf δX , [] , ifaceX , tt

submission : String → String → List (String × String) → List Proarrow → String
submission reason c subs ms = showSExpr (list
  (sym "submission" ∷ list (sym "kind" ∷ sym "plan" ∷ [])
   ∷ list (sym "why" ∷ str reason ∷ [])
   ∷ list (sym "main" ∷ str c ∷ [])
   ∷ list (sym "subspecs" ∷ map (λ e → list (str (proj₁ e) ∷ str (proj₂ e) ∷ [])) subs)
   ∷ list (sym "moves" ∷ map (λ a → list (sym "move" ∷ encObj (src a) ∷ encObj (tgt a) ∷ [])) ms) ∷ []))

helperCode : Code
helperCode = record (impl "X") { decls = decls (impl "X") ++
  (sig plain "helper" nat ∷ fun plain "helper" (clause (head (mkQ ("X" ∷ "helper" ∷ [])) []) (rhs (lit (natL 1))) [] ∷ []) ∷ []) }

treeCode : Code
treeCode = code (q "X") [] (natImport
  ∷ import′ (q "A") false everything [] ∷ import′ (q "B") false everything []
  ∷ sig plain "x" nat
  ∷ fun plain "x" (clause (head (mkQ ("X" ∷ "x" ∷ [])) []) (rhs (def (qn ("A" ∷ "x" ∷ []) "A.x"))) [] ∷ []) ∷ [])

singleCode : Code
singleCode = record treeCode { decls = filterᵇ keepDecl (decls treeCode) }
  where
    keepDecl : Decl → Bool
    keepDecl (import′ m _ _ _) = not (m ==ᴺ q "B")
    keepDecl _ = true

singlePlan : String
singlePlan = submission "one dynamically growing child" "single"
  (("A" , "A") ∷ []) ((Code.⊥ ⇝ ext (mkQ ("A" ∷ "x" ∷ []))) ∷ [])

refuteCode : Code
refuteCode = code (q "Refute") []
  (import′ (q "X") false everything [] ∷ import′ (mkQ ("Data" ∷ "Empty" ∷ [])) true everything []
   ∷ sig plain "absurd" (def (mkQ ("Data" ∷ "Empty" ∷ "⊥" ∷ [])))
   ∷ fun plain "absurd" (clause (head (mkQ ("Refute" ∷ "absurd" ∷ [])) []) (rhs (def (mkQ ("X" ∷ "impossible" ∷ [])))) [] ∷ []) ∷ [])

onePlan : String
onePlan = submission "x denotes the initial zero" "impl" [] []

treePlan : String
treePlan = submission "factor two independent child interfaces" "tree"
  (("A" , "A") ∷ ("B" , "B") ∷ [])
  ((Code.⊥ ⇝ ext (mkQ ("A" ∷ "x" ∷ []))) ∷ (Code.⊥ ⇝ ext (mkQ ("B" ∷ "x" ∷ []))) ∷ [])

increment : String
increment = "(submission (kind add-moves) (moves (move bot (unit \"X.helper\"))))"

deathPlan : String
deathPlan = submission "the direct constant discharges both child boundaries" "impl" []
  ((ext (mkQ ("A" ∷ "x" ∷ [])) ⇝ Code.⊥) ∷ [])

refuteSubmission : String
refuteSubmission = showSExpr (list (sym "submission" ∷ list (sym "kind" ∷ sym "contradiction" ∷ [])
  ∷ list (sym "refute" ∷ str "refute" ∷ []) ∷ []))

nextReply : List String → AIReq → AIReply × List String
nextReply [] (propose _ _) = aiReply "" "pure" , []
nextReply (r ∷ rs) (propose _ _) = aiReply r "pure" , rs
nextReply rs _ = aiReply "accepted" "pure" , rs

scriptedAI : List String → Server [] AIReq AIReply [] (Dir [])
ServerI.call (scriptedAI rs) = ask λ req →
  let (r , next) = nextReply rs req in tell r (daemon (scriptedAI next))
ServerI.stop (scriptedAI rs) = give∃Dir tt refl

-- Source parsing/type checking is covered by SessionIO with real tools.
-- This deterministic tool table keeps the protocol refl proofs small.
pureDump : Server [] DumpReq DumpResult [] (Dir [])
ServerI.call pureDump = ask λ req → tell (decode (source req)) (daemon pureDump)
  where
    decode : String → DumpResult
    decode "impl" = dumped (impl "X")
    decode "helper" = dumped helperCode
    decode "tree" = dumped treeCode
    decode "single" = dumped singleCode
    decode "A" = dumped (code (q "A") [] ifaceX)
    decode "B" = dumped (code (q "B") [] ifaceX)
    decode "refute" = dumped refuteCode
    decode _ = dumpFailed "parse"
ServerI.stop pureDump = give∃Dir tt refl

checks : List CheckResult → Server [] AgdaCheckReq CheckResult [] (Dir [])
ServerI.call (checks []) = ask λ _ → tell pass (daemon (checks []))
ServerI.call (checks (r ∷ rs)) = ask λ _ → tell r (daemon (checks rs))
ServerI.stop (checks rs) = give∃Dir tt refl

-- Independent scripted children exercise the parent's resource protocol.
childOffer : (sh : HomeShape) → Models (Home (HomeCtx sh)) → Offer AgentS
childOffer sh home task = running [] (nodeLike sh) home
  where
    nodeLike : (sh : HomeShape) → ServerI [] ⊤ (Maybe Verdict) HomeShape (Home (HomeCtx sh)) HomeSt
    ServerI.call (nodeLike (node ks)) = ask λ _ →
      run (commitBelow root ks (impl (shown (child (δ task)))) [] (newIface (δ task))) λ _ →
      tell (just ok) (daemon (nodeLike (node ks)))
    ServerI.stop (nodeLike sh) = give∃Dir sh refl

pureEnv : List String → List CheckResult → Env NodeΨ
pureEnv rs cs = (λ _ → provide [] (daemon (scriptedAI rs)))
             ∷ (λ _ → provide [] (daemon pureDump))
             ∷ (λ _ → provide [] (daemon (checks cs))) ∷ childOffer ∷ []

startX : List String → List CheckResult → Running ⊤ (Maybe Verdict) (Msg (∃Res HomeShape HomeSt))
startX rs cs = provide (pureEnv rs cs) (nodeAgent (node [])) homeX taskX

stoppedMemory : Msg (∃Res HomeShape HomeSt) → Memory
stoppedMemory (sh , m) = memoryOf sh m

growingChild : (sh : HomeShape) → Models (Home (HomeCtx sh)) → Offer AgentS
growingChild (node []) home task = running [] grow home
  where
    grown = node (("Grand" , node []) ∷ [])
    steady : ServerI [] ⊤ (Maybe Verdict) HomeShape (Home (HomeCtx grown)) HomeSt
    ServerI.call steady = ask λ _ → tell (just ok) (daemon steady)
    ServerI.stop steady = give∃Dir grown refl
    idle : ServerI [] ⊤ (Maybe Verdict) HomeShape (Home (HomeCtx (node []))) HomeSt
    ServerI.call idle = ask λ _ → tell nothing (daemon idle)
    ServerI.stop idle = give∃Dir (node []) refl
    grow : ServerI [] ⊤ (Maybe Verdict) HomeShape (Home (HomeCtx (node []))) HomeSt
    ServerI.call grow = ask λ _ →
      run (commitBelow root [] (impl (shown (child (δ task)))) [] (newIface (δ task))) λ _ →
      insertDir root "Grand"
        (run (plantAt root (impl "Grand") [] ifaceX) λ _ → tell (just ok) (daemon steady))
        (tell nothing (daemon idle))
    ServerI.stop grow = give∃Dir (node []) refl
growingChild sh@(node (_ ∷ _)) home task = childOffer sh home task

growingEnv : List String → Env NodeΨ
growingEnv rs = (λ _ → provide [] (daemon (scriptedAI rs)))
  ∷ (λ _ → provide [] (daemon pureDump)) ∷ (λ _ → provide [] (daemon (checks []))) ∷ growingChild ∷ []

grownTree : Msg (∃Res HomeShape HomeSt)
grownTree = Running.onStop (proj₂ (observeN 5 (provide (growingEnv (singlePlan ∷ [])) (nodeAgent (node [])) homeX taskX)))

afterDeath : Msg (∃Res HomeShape HomeSt)
afterDeath with grownTree
... | sh , h = Running.onStop (proj₂ (observeN 4 (provide (pureEnv (deathPlan ∷ []) []) (nodeAgent sh) h taskX)))

treeWithIfaces : Code
treeWithIfaces = withChildIfaces ((q "A" , ifaceX) ∷ (q "B" , ifaceX) ∷ []) treeCode

gChanged : Code
gChanged = record treeWithIfaces { decls = decls treeWithIfaces ++
  (sig plain "testB" nat ∷ fun plain "testB" (clause (head (mkQ ("X" ∷ "testB" ∷ [])) []) (rhs (def (qn ("B" ∷ "x" ∷ []) "B.x"))) [] ∷ []) ∷ []) }

leaf-ok : pollN 3 (startX (onePlan ∷ []) []) ≡ just ok
leaf-ok = refl

-- A failed glue check yields no child births and no leaf/memory updates.
glue-failure : proj₁ (Running.onStop (proj₂ (observeN 2 (startX (onePlan ∷ []) (fail "missing child lemma" ∷ []))))) ≡ node []
glue-failure = refl

retry-hygiene : stoppedMemory (Running.onStop (proj₂ (observeN 4 (startX ("malformed" ∷ onePlan ∷ []) []))))
              ≡ (unit (mkQ ("X" ∷ "x" ∷ [])) , "x denotes the initial zero" ∷ []) ∷ []
retry-hygiene = refl

incremental-completion : pollN 4 (startX (submission "private constant" "helper" [] [] ∷ increment ∷ []) []) ≡ just ok
incremental-completion = refl

multi-child : pollN 4 (startX (treePlan ∷ []) []) ≡ just ok
multi-child = refl

born-shape : proj₁ (Running.onStop (proj₂ (observeN 4 (startX (treePlan ∷ []) []))))
           ≡ node (("B" , node []) ∷ ("A" , node []) ∷ [])
born-shape = refl

no-birth-before-glue : proj₁ (Running.onStop (proj₂ (observeN 2 (startX (treePlan ∷ []) (fail "missing lemma" ∷ []))))) ≡ node []
no-birth-before-glue = refl

sibling-assumes : newIface (restrict (withChildIfaces ((q "A" , ifaceX) ∷ (q "B" , ifaceX) ∷ []) treeCode) (plan "" [] []) (q "A")) ≡ ifaceX
sibling-assumes = refl

-- A child can return a shape that did not exist when its channel was opened.
dynamic-grandchildren : proj₁ grownTree ≡ node (("A" , node (("Grand" , node []) ∷ [])) ∷ [])
dynamic-grandchildren = refl

dynamic-death-cascades : proj₁ afterDeath ≡ node []
dynamic-death-cascades = refl

-- Stopping an unfinished revision restores its original coherent snapshot.
rollback-during-wait : Running.onStop (proj₂ (observeN 2 (startX (treePlan ∷ []) []))) ≡ (node [] , homeX)
rollback-during-wait = refl

g-keeps-A : impactsChild treeWithIfaces gChanged (plan "" [] []) (q "A") ≡ false
g-keeps-A = refl

g-stops-B : impactsChild treeWithIfaces gChanged (plan "" [] []) (q "B") ≡ true
g-stops-B = refl

contradiction-roundtrip : pollN 3 (startX (refuteSubmission ∷ []) []) ≡ just (contradiction refuteCode)
contradiction-roundtrip = refl

contradiction-needs-compiler : pollN 2 (startX (refuteSubmission ∷ []) (fail "no such impossible" ∷ [])) ≡ nothing
contradiction-needs-compiler = refl

-- Instrument the live channels: an original channel stays childless, while
-- the child provider grows Grand on its first call. The final returned shapes
-- therefore witness which sibling was actually stopped and reopened.
originalChild : ServerI [] ⊤ (Maybe Verdict) HomeShape (Home (HomeCtx (node []))) HomeSt
ServerI.call originalChild = ask λ _ → tell nothing (daemon originalChild)
ServerI.stop originalChild = give∃Dir (node []) refl

selectiveSlots : Slots
selectiveSlots = ("A" , awake) ∷ ("B" , awake) ∷ []

selectiveHome : Model (Dir (Work selectiveSlots))
selectiveHome = provide [] (daemon (checks [])) tt
  , provide [] (daemon pureDump) tt , provide [] (daemon (scriptedAI [])) tt
  , provide [] (daemon originalChild) homeX , provide [] (daemon originalChild) homeX , homeX

selectiveResult : Msg (∃Res HomeShape HomeSt)
selectiveResult = proj₁ (provide (growingEnv [])
  (reconcile toolPrefix selectiveSlots taskX treeWithIfaces gChanged (plan "new B theorem" [] []) [] λ next mem →
    pollKids toolPrefix next λ polled _ → shutdown polled) selectiveHome)

g-selective-stop : proj₁ selectiveResult ≡ node (("A" , node []) ∷ ("B" , node (("Grand" , node []) ∷ [])) ∷ [])
g-selective-stop = refl
