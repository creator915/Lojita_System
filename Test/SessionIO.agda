{-# OPTIONS --guardedness #-}
module Test.SessionIO where

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (_≡ᵇ_)
import Data.Char
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership hiding (_>>=_; _>>_; Home; set; Name; open′)
open import OwnershipIO
open import OwnershipIO.FFI
open import Code
open import Code.Transport
open import Code.SExpr using (list; sym; str; showSExpr)
open import Code.Protocol
open import Code.Tree using (HomeSt; node)
open import Code.Harness using (NodeΨ)
open import Code.AI using (ScriptedBackend)
open import Code.Driver using (nodeEnvironment; dumpTool)
open import Code.AgdaTool using (agdaTool)
open import Code.Codecs
open import Code.SessionRunner using (runNode; runAutonomousSession; sessionConfig; driveTree)
open import Code.SessionProtocol using (refSpec; local; parseSessionAction)
open import Code.SessionWorkspace using (readNames; endsWith; filesBelow; loadBases; basesLoaded; basesFailed; includeDirs; fingerprint)
open import Test.SessionFixtures
open import Test.HarnessPure using (homeX; taskX; ifaceX; submission)
open import Test.NegativeGates using (N3-source; N3-child; N5-source; N6-source)
open import Test.EvalIO using (report)

sourcePlan : String → String → String
sourcePlan reason src = showSExpr (list (sym "submission" ∷ list (sym "kind" ∷ sym "plan" ∷ [])
  ∷ list (sym "why" ∷ str reason ∷ []) ∷ list (sym "main" ∷ str src ∷ [])
  ∷ list (sym "subspecs" ∷ []) ∷ list (sym "moves" ∷ []) ∷ []))

good badType : String
good = "module X where\nopen import Agda.Builtin.Nat\nx : Nat\nx = 0\n"
badType = "module X where\nopen import Agda.Builtin.Nat\nopen import Agda.Builtin.Bool\nx : Nat\nx = true\n"

hygiene : String → IO.IO Bool
hygiene cwd = nodeEnvironment (ScriptedBackend
  ("malformed" ∷ sourcePlan "candidate" "module X where\nx :\n" ∷ sourcePlan "candidate" "module X where\nx : Nat\nx =\n" ∷ sourcePlan "candidate" badType
   ∷ sourcePlan "candidate" "module X where\nopen import Agda.Builtin.Nat\nopen import Agda.Builtin.Bool\nx : Nat\nx = suc true\n" ∷ sourcePlan "the initial value is zero" good ∷ []))
  (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/session-tools") (cwd ∷ "/usr/share/agda-stdlib" ∷ []) IO.>>= λ env →
  runNode env taskX (node [] , homeX) IO.>>= λ where
    (ok , result@(node [] , c , m , i , _)) → storeHome "tmp/tests/hygiene" result IO.>>= λ _ →
      IO.return (eqMemory m ((unit (mkQ ("X" ∷ "x" ∷ [])) , "the initial value is zero" ∷ []) ∷ []))
    _ → IO.return false

rejectSource : String → String → IO.IO Bool
rejectSource cwd src = onCall (dumpTool (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/negative-dump") (cwd ∷ "/usr/share/agda-stdlib" ∷ []))
  (dumpReq src [] []) IO.>>= λ where
    (dumpFailed _) → IO.return false
    (dumped c) → onCall (agdaTool (cwd ∷ "/usr/share/agda-stdlib" ∷ []) (cwd ++ˢ "/tmp/tests/negative-agda")) (agdaCheck c []) IO.>>= λ result → IO.return (not (isPass result))

negativeGlue : String → IO.IO Bool
negativeGlue cwd = onCall (dumpTool (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/glue-dump") (cwd ∷ "/usr/share/agda-stdlib" ∷ []))
  (dumpReq N3-source (("ChildGate" , "module ChildGate where\nopen import Agda.Builtin.Nat\nopen import Agda.Builtin.Equality\npostulate\n  x : Nat\n  missingLemma : x ≡ zero\n") ∷ []) []) IO.>>= λ where
    (dumpFailed _) → IO.return false
    (dumped c) → onCall (agdaTool (cwd ∷ "/usr/share/agda-stdlib" ∷ []) (cwd ++ˢ "/tmp/tests/glue-agda"))
      (agdaCheck c (code (mkQ ("ChildGate" ∷ [])) [] ifaceX ∷ [])) IO.>>= λ result → IO.return (not (isPass result))

realRefutation : String → IO.IO Bool
realRefutation cwd = nodeEnvironment (ScriptedBackend
  ("(submission (kind contradiction) (refute \"module RefuteSpec where\\nopen import Data.Empty using (⊥)\\nimport Impossible\\nabsurd : ⊥\\nabsurd = Impossible.impossible\\n\"))" ∷ []))
  (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/refutation") (cwd ∷ "/usr/share/agda-stdlib" ∷ []) IO.>>= λ env →
  runNode env (record (nodeTask d [] nothing) { baseModules = base ∷ [] }) (node [] , stubOf d , [] , newIface d , tt) IO.>>= λ where
    (contradiction c , node [] , old , mem , _ , _) → IO.return (nullᵇ (validRefutation (child d) [] c) ∧ eqMemory mem [])
    _ → IO.return false
  where
    base = code (mkQ ("RefutationBase" ∷ [])) []
      (import′ (mkQ ("Data" ∷ "Empty" ∷ [])) true everything []
       ∷ sig plain "Bottom" (set 0)
       ∷ fun plain "Bottom" (clause (head (mkQ ("RefutationBase" ∷ "Bottom" ∷ [])) [])
           (rhs (def (mkQ ("Data" ∷ "Empty" ∷ "⊥" ∷ [])))) [] ∷ []) ∷ [])
    d = specΔ (mkQ ("Impossible" ∷ []))
      (import′ (mkQ ("RefutationBase" ∷ [])) false everything [] ∷ sig plain "impossible" (def (qn ("RefutationBase" ∷ "Bottom" ∷ []) "RefutationBase.Bottom")) ∷ []) []

contradictionSubmission : String → String
contradictionSubmission src = showSExpr (list (sym "submission"
  ∷ list (sym "kind" ∷ sym "contradiction" ∷ []) ∷ list (sym "refute" ∷ str src ∷ []) ∷ []))

lawTestHeader : String
lawTestHeader = "module LawTest where\nopen import Agda.Builtin.Nat\nopen import Agda.Builtin.Equality\npostulate\n  f : Nat → Nat\n  law : f 0 ≡ 0\n"

-- These specs are deliberately inconsistent. Dump scope-checks the source;
-- runNode must compiler-check a closed proof using the exposed proposition.
lawTestRefutation : String → String → String → IO.IO Bool
lawTestRefutation cwd tests proofName = onCall
  (dumpTool (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/law-test-dump") incs)
  (dumpReq (lawTestHeader ++ˢ tests) [] []) IO.>>= λ where
    (dumpFailed e) → F.putStrLn e IO.>>= λ _ → IO.return false
    (dumped spec) → checkNode (specΔ (modName spec) (decls spec) [])
  where
    incs = cwd ∷ "/usr/share/agda-stdlib" ∷ []
    proof = "module RefuteLawTest where\nopen import Agda.Builtin.Nat\nopen import Data.Empty using (⊥)\nopen import Relation.Binary.PropositionalEquality using (_≡_; trans; sym)\nimport LawTest as Spec\nzero≠one : 0 ≡ 1 → ⊥\nzero≠one ()\nabsurd : ⊥\nabsurd = zero≠one (trans (sym Spec.law) Spec." ++ˢ proofName ++ˢ ")\n"
    checkNode : SpecΔ → IO.IO Bool
    checkNode d = nodeEnvironment (ScriptedBackend (contradictionSubmission proof ∷ []))
      (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/law-test-node") incs IO.>>= λ env →
      runNode env (nodeTask d [] nothing) (node [] , stubOf d , [] , newIface d , tt) IO.>>= λ where
        (contradiction c , node [] , old , mem , iface , _) → IO.return
          (nullᵇ (validRefutation (child d) [] c) ∧ eqCode old (stubOf d)
           ∧ eqMemory mem [] ∧ eqDecls iface (newIface d))
        _ → IO.return false

testLawContradictions : String → IO.IO Bool
testLawContradictions cwd =
  lawTestRefutation cwd "_ : f 0 ≡ 1\n_ = refl\n" "specTest0" IO.>>= λ anon →
  lawTestRefutation cwd "namedTest : f 0 ≡ 1\nnamedTest = refl\n" "namedTest" IO.>>= λ named →
  lawTestRefutation cwd "one : Nat\none = 1\nexpected : Nat\nexpected = one\n_ : f 0 ≡ expected\n_ = refl\n" "specTest0" IO.>>= λ helper →
  lawTestRefutation cwd "specTest0 : Nat\nspecTest0 = 0\n_ : 0 ≡ 0\n_ = refl\n_ : f 0 ≡ 1\n_ = refl\n" "specTest2" IO.>>= λ fresh →
  IO.return (anon ∧ named ∧ helper ∧ fresh)

anonymousSpecHeader anonymousSpecError : String
anonymousSpecHeader = "open import Agda.Builtin.Nat\nopen import Agda.Builtin.Equality\n"
anonymousSpecError = "spec: anonymous '_' declarations must include a definition body (e.g. '_ = refl'); give postulated obligations an explicit name"

anonymousSubspecs : String → IO.IO Bool
anonymousSubspecs cwd = nodeEnvironment (ScriptedBackend
  (submission "invalid anonymous postulate" good
    (("BadSpec" , "module BadSpec where\n" ++ˢ anonymousSpecHeader ++ˢ "postulate\n  _ : 0 ≡ 1\n") ∷ []) []
   ∷ submission "anonymous test has a proof body" good
    (("GoodSpec" , "module GoodSpec where\n" ++ˢ anonymousSpecHeader ++ˢ "_ : 0 ≡ 0\n_ = refl\n") ∷ []) [] ∷ []))
  (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/anonymous-subspecs") (cwd ∷ "/usr/share/agda-stdlib" ∷ []) IO.>>= λ env →
  runNode env taskX (node [] , homeX) IO.>>= λ where
    (ok , node [] , c , mem , _ , _) → IO.return
      (eqList _==ˢ_ (notesOf mem (unit (mkQ ("X" ∷ "x" ∷ [])))) ("anonymous test has a proof body" ∷ []))
    _ → IO.return false

anonymousTreeSpecs : String → IO.IO Bool
anonymousTreeSpecs cwd = withTempDirectory (cwd ++ˢ "/tmp/tests/anonymous-trees") checkTrees
  where
    badSpec = "module BadAnon where\n" ++ˢ anonymousSpecHeader ++ˢ
      "open import Data.Empty using (⊥)\npostulate\n  _ : 0 ≡ 1\n  impossible : ⊥\n"
    validSpec = "module GoodAnon where\n" ++ˢ anonymousSpecHeader ++ˢ "_ : 0 ≡ 0\n_ = refl\n"
    -- If the validation gate disappears, the bad tree can terminate with a
    -- refutation, so the regression fails instead of retrying indefinitely.
    badReply = contradictionSubmission "module RefuteBadAnon where\nopen import Data.Empty using (⊥)\nimport BadAnon\nabsurd : ⊥\nabsurd = BadAnon.impossible\n"
    checkTrees : String → IO.IO Bool
    checkTrees ws = driveTree (cfg ws) "Bad" badSpec [] nothing IO.>>= λ bad →
      driveTree (cfg ws) "Good" validSpec [] nothing IO.>>= λ valid →
      dirExists (ws ++ˢ "/trees/Bad") IO.>>= λ persisted → IO.return (expected bad valid ∧ not persisted)
      where
        cfg : String → Code.SessionRunner.SessionConfig
        cfg ws = sessionConfig cwd ws "validate anonymous specification declarations"
          (refSpec (local "/bin/cat") [] 30000) (ScriptedBackend [])
          (λ name → ScriptedBackend ((if name ==ˢ "Bad" then badReply else
            sourcePlan "anonymous equality has a proof" ("module GoodAnon where\n" ++ˢ anonymousSpecHeader)) ∷ []))
        expected : Code.SessionRunner.ActionResult → Code.SessionRunner.ActionResult → Bool
        expected (Code.SessionRunner.rejected e) (Code.SessionRunner.accepted _) = e ==ˢ anonymousSpecError
        expected _ _ = false

liftPrecheckAndScope : String → IO.IO Bool
liftPrecheckAndScope cwd = withTempDirectory (cwd ++ˢ "/tmp/tests/lift-precheck") checkPrecheck
  where
    incs = cwd ∷ "/usr/share/agda-stdlib" ∷ []
    dump = dumpTool (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/lift-precheck-dump") incs
    t0ChildSrc = "module BaseChild where\nopen import Agda.Builtin.Nat\nk : Nat → Nat\nk n = n\n"
    t0RootSrc = "module BaseRoot where\nopen import Agda.Builtin.Nat\nimport BaseChild\nf : Nat → Nat\nf n = BaseChild.k n\n"
    t1Spec = "module UpperRoot where\nopen import Agda.Builtin.Nat\nopen import Agda.Builtin.Equality\nimport BaseRoot\npostulate\n  g : Nat → Nat\n  sq : (n : Nat) → g n ≡ BaseRoot.f n\n"
    t1Main = "module UpperRoot where\nopen import Agda.Builtin.Nat\nopen import Agda.Builtin.Equality\nimport BaseRoot\nimport BaseChild\ng : Nat → Nat\ng n = BaseChild.k n\nsq : (n : Nat) → g n ≡ BaseRoot.f n\nsq n = refl\n"
    badLift = just "(lift \"BaseRoot\" \"UpperRoot\" () ((\"BaseRoot.f\" \"UpperRoot.g\" \"UpperRoot.sq\")))"
    goodLift = just "(lift \"BaseRoot\" \"UpperRoot\" ((\"BaseChild\" \"BaseChild\")) ((\"BaseRoot.f\" \"UpperRoot.g\" \"UpperRoot.sq\")))"
    scopeScript = "{-# OPTIONS --guardedness #-}\nmodule ScopeClean where\nopen import Data.Unit using (⊤; tt)\nimport IO.Primitive as IO\nimport IO.Primitive.Finite as F\nopen import SessionEnv\nglyph : Bytes\nglyph = bytes \"ok\"\nstate : Bytes\nstate = glyph\ninput : Bytes\ninput = state\nmain : IO.IO ⊤\nmain = F.putStrLn \"scope clean\"\n"
    checkPrecheck : String → IO.IO Bool
    checkPrecheck ws =
      onCall dump (dumpReq t0ChildSrc [] []) IO.>>= λ where
        (dumpFailed _) → IO.return false
        (dumped childCode) → onCall dump (dumpReq t0RootSrc [] (childCode ∷ [])) IO.>>= λ where
          (dumpFailed _) → IO.return false
          (dumped rawRoot) →
            let rootCode = withChildIface (modName childCode) (decls childCode) rawRoot
                t0Home : HomeValue
                t0Home = node (("BaseChild" , node []) ∷ []) ,
                  ((childCode , [] , decls childCode , tt) , rootCode , [] , decls rootCode , tt)
            in storeHome (ws ++ˢ "/trees/T0") t0Home IO.>>= λ _ →
            F.writeFile (ws ++ˢ "/trees/T0/verdict") "ok" IO.>>= λ _ →
            F.writeFile (ws ++ˢ "/trees/T0/bases.sexp") "()" IO.>>= λ _ →
            driveTree (cfg ws true) "T1Bad" t1Spec ("T0" ∷ []) badLift IO.>>= λ badRes →
            driveTree (cfg ws false) "T1Good" t1Spec ("T0" ∷ []) goodLift IO.>>= λ goodRes →
            Code.SessionRunner.runSessionScript (cfg ws true) scopeScript IO.>>= λ scriptRes →
            dirExists (ws ++ˢ "/trees/T1Bad") IO.>>= λ badPersisted →
            IO.return (okBad badRes ∧ okGood goodRes ∧ okScript scriptRes ∧ not badPersisted)
      where
        cfg : String → Bool → Code.SessionRunner.SessionConfig
        cfg ws emptyUpper = sessionConfig cwd ws "verify preflight lift check and SessionEnv scope"
          (refSpec (local "/bin/cat") [] 30000) (ScriptedBackend [])
          (λ _ → if emptyUpper then ScriptedBackend []
            else ScriptedBackend (sourcePlan "retain BaseChild and prove square" t1Main ∷ []))
        okBad : Code.SessionRunner.ActionResult → Bool
        okBad (Code.SessionRunner.rejected _) = true
        okBad _ = false
        okGood : Code.SessionRunner.ActionResult → Bool
        okGood (Code.SessionRunner.accepted _) = true
        okGood _ = false
        okScript : ProcResult → Bool
        okScript (procResult 0 _ _) = true
        okScript _ = false

-- Dump the actual spec, then exercise stub compilation, both forms of named
-- test inclusion, and rejection of a type-correct change to a concrete helper.
helperHeader helperTitle helperNamed helperAnon helperSpec : String
helperHeader = "module HelperNode where\nopen import Agda.Builtin.Nat\nopen import Agda.Builtin.Equality\nrecord Box : Set where\n  constructor box\n"
helperTitle = "title : Nat → Nat\ntitle n = operation n\n"
helperNamed = "ex1 : operation zero ≡ zero\nex1 = refl\n"
helperAnon = "_ : title zero ≡ zero\n_ = refl\n"

helperBodies : Bool → String
helperBodies tampered = "leaf : Nat\nleaf = " ++ˢ (if tampered then "(λ n → n) zero" else "zero") ++ˢ
  "\nhelper : Nat\nhelper = leaf\nboxed : Box\nboxed = box\n"

helperSpec = helperHeader ++ˢ helperBodies false ++ˢ
  "postulate\n  operation : Nat → Nat\n" ++ˢ helperTitle ++ˢ
  "postulate\n  law : operation zero ≡ helper\n  linkLaw : title zero ≡ helper\n  boxLaw : boxed ≡ box\n" ++ˢ
  helperNamed ++ˢ helperAnon

helperMain : Bool → Bool → String
helperMain tampered named = helperHeader ++ˢ helperBodies tampered ++ˢ
  "operation : Nat → Nat\noperation n = n\n" ++ˢ helperTitle ++ˢ
  "law : operation zero ≡ helper\nlaw = refl\nlinkLaw : title zero ≡ helper\nlinkLaw = refl\nboxLaw : boxed ≡ box\nboxLaw = refl\n" ++ˢ
  (if named then helperNamed else "")

helperQName : Name → QName
helperQName n = mkQ ("HelperNode" ∷ n ∷ [])

helperMoves : Bool → List Proarrow
helperMoves named = if named then (⊥ ⇝ unit (helperQName "ex1")) ∷ [] else []

helperAttempt : String → SpecΔ → Bool → IO.IO Bool
helperAttempt cwd d named = nodeEnvironment (ScriptedBackend replies)
  (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/helper-node") (cwd ∷ "/usr/share/agda-stdlib" ∷ []) IO.>>= λ env →
  runNode env (nodeTask d [] nothing) (node [] , stubOf d , [] , newIface d , tt) IO.>>= λ where
    (ok , node [] , c , mem , iface , _) → IO.return
      (satisfies d c ∧ eqDecls iface (newIface d)
       ∧ eqList _==ˢ_ (notesOf mem (unit (helperQName "leaf"))) (accepted ∷ [])
       ∧ (length (filterᵇ anonymousUnit (units c)) ≡ᵇ 1)
       ∧ (length (filterᵇ (λ u → uname u ==ᴺ helperQName "ex1") (units c)) ≡ᵇ 1)
       ∧ (length (imports c) ≡ᵇ 2))
    _ → IO.return false
  where
    accepted = "preserve concrete helpers and discharge laws"
    goodPlan = submission accepted (helperMain false named) [] (helperMoves named)
    -- If the bad proposal is accepted, its reason remains in memory and the
    -- assertion fails instead of silently passing after the first verdict.
    replies = if named then
      submission "tampered helper must be rejected" (helperMain true true) [] (helperMoves true) ∷ goodPlan ∷ []
      else goodPlan ∷ []

concreteSpecHelpers : String → IO.IO Bool
concreteSpecHelpers cwd = onCall dump (dumpReq helperSpec [] []) IO.>>= λ where
    (dumpFailed e) → F.putStrLn e IO.>>= λ _ → IO.return false
    (dumped specCode) → checkSpec (boundary specCode)
  where
    incs = cwd ∷ "/usr/share/agda-stdlib" ∷ []
    dump = dumpTool (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/helper-dump") incs
    compiler = agdaTool incs (cwd ++ˢ "/tmp/tests/helper-agda")
    boundary : Code → SpecΔ
    boundary c = record d { δarrows = map (λ u → keep (Code.ext (uname u))) (units (stubOf d)) }
      where d = specΔ (modName c) (decls c) []
    checkSpec : SpecΔ → IO.IO Bool
    checkSpec d = onCall compiler (agdaCheck (stubOf d) []) IO.>>= λ where
      (fail e) → F.putStrLn e IO.>>= λ _ → IO.return false
      pass → onCall dump (dumpReq (helperMain true true) [] []) IO.>>= λ where
        (dumpFailed e) → F.putStrLn e IO.>>= λ _ → IO.return false
        (dumped tampered) → onCall compiler (agdaCheck (withTests tampered (newIface d)) []) IO.>>= λ checked →
          helperAttempt cwd d false IO.>>= λ omitted →
          helperAttempt cwd d true IO.>>= λ included →
          IO.return (isPass checked ∧ nullᵇ (validate (stubOf d)
            (plan "tampered" (decls tampered) (seedArrows d ++ helperMoves true)) tampered)
            ∧ not (satisfies d tampered) ∧ omitted ∧ included)

Ephemeral : Prog [] (Dir []) (Dir []) String
Ephemeral = withEphemeral "attempt" (create "memory" "transient syntax error" Ownership.>> unlink "memory" Ownership.>> done "observation")

noResidue : IO.IO Bool
noResidue = mkdirP "tmp/tests/ephemeral" IO.>>= λ _ →
  readProcess "find" ("tmp/tests/ephemeral" ∷ "-printf" ∷ "%P %y\n" ∷ []) "" IO.>>= λ before →
  evalIO [] Ephemeral tt IO.>>= λ result →
  store "tmp/tests/ephemeral" {Dir []} tt (proj₁ result) IO.>>= λ _ →
  readProcess "find" ("tmp/tests/ephemeral" ∷ "-printf" ∷ "%P %y\n" ∷ []) "" IO.>>= λ after →
  IO.return (same before after ∧ (proj₂ result ==ˢ "observation"))
  where
    same : ProcResult → ProcResult → Bool
    same (procResult _ a _) (procResult _ b _) = a ==ˢ b

sessionSource : String → String → String → String
sessionSource kind why src = showSExpr (list (sym "session-action"
  ∷ list (sym "kind" ∷ sym kind ∷ []) ∷ list (sym "why" ∷ str why ∷ [])
  ∷ list (sym "source" ∷ str src ∷ []) ∷ []))

treeAction : String → String → List String → Maybe String → String
treeAction name src bases lifting = showSExpr (list (sym "session-action"
  ∷ list (sym "kind" ∷ sym "drive-tree" ∷ []) ∷ list (sym "treeName" ∷ str name ∷ [])
  ∷ list (sym "why" ∷ str "preserve the selected boundary" ∷ []) ∷ list (sym "specSrc" ∷ str src ∷ [])
  ∷ list (sym "baseTrees" ∷ map str bases)
  ∷ list (sym "maybeLiftSrc" ∷ encodeMaybe lifting ∷ []) ∷ []))
  where
    encodeMaybe : Maybe String → Code.SExpr.SExpr
    encodeMaybe nothing = sym "nothing"
    encodeMaybe (just src) = list (sym "just" ∷ str src ∷ [])

doneAction : String
doneAction = "(session-action (kind finish) (summary \"Verified identity pipeline, three trees and real batch replay against /bin/cat.\"))"

-- Failed or orphaned exports are not imports, but every generated Agda source
-- and every tree's modules.tsv still participates in build invalidation.
workspaceInputs : String → IO.IO Bool
workspaceInputs cwd = withTempDirectory (cwd ++ˢ "/tmp/tests/workspace-inputs") λ ws →
  mkdirP (ws ++ˢ "/generated/T0/Nested") IO.>>= λ _ →
  mkdirP (ws ++ˢ "/generated/failed") IO.>>= λ _ →
  mkdirP (ws ++ˢ "/generated/orphan") IO.>>= λ _ →
  mkdirP (ws ++ˢ "/trees/T0") IO.>>= λ _ →
  mkdirP (ws ++ˢ "/trees/failed") IO.>>= λ _ →
  F.writeFile (ws ++ˢ "/trees/T0/verdict") "ok" IO.>>= λ _ →
  F.writeFile (ws ++ˢ "/trees/failed/verdict") "contradiction" IO.>>= λ _ →
  F.writeFile (ws ++ˢ "/trees/T0/modules.tsv") "original manifest" IO.>>= λ _ →
  F.writeFile (ws ++ˢ "/generated/T0/Nested/Base.agda") "module Nested.Base where\n" IO.>>= λ _ →
  F.writeFile (ws ++ˢ "/generated/failed/Old.agda") "module Old where\n" IO.>>= λ _ →
  includeDirs cwd ws IO.>>= λ incs → fingerprint ws IO.>>= λ initial →
  F.writeFile (ws ++ˢ "/generated/T0/Nested/Base.agdai") "ignored cache" IO.>>= λ _ →
  fingerprint ws IO.>>= λ cached →
  F.writeFile (ws ++ˢ "/generated/T0/Nested/Base.agda") "module Nested.Base where\n-- changed\n" IO.>>= λ _ →
  fingerprint ws IO.>>= λ nested →
  F.writeFile (ws ++ˢ "/generated/T0/Nested/Base.agda") "module Nested.Base where\n" IO.>>= λ _ →
  F.writeFile (ws ++ˢ "/generated/failed/Old.agda") "module Old where\n-- changed\n" IO.>>= λ _ →
  fingerprint ws IO.>>= λ failed →
  F.writeFile (ws ++ˢ "/generated/failed/Old.agda") "module Old where\n" IO.>>= λ _ →
  F.writeFile (ws ++ˢ "/trees/T0/modules.tsv") "changed manifest" IO.>>= λ _ →
  fingerprint ws IO.>>= λ metadata →
  IO.return (eqList _==ˢ_ incs ((ws ++ˢ "/generated/T0") ∷ cwd ∷ "/usr/share/agda-stdlib" ∷ [])
    ∧ (initial ==ˢ cached) ∧ not (initial ==ˢ nested) ∧ not (initial ==ˢ failed) ∧ not (initial ==ˢ metadata))

autonomous : String → IO.IO Bool
autonomous cwd = permissions IO.>>= λ before → removeAll ws IO.>>= λ _ → runAutonomousSession cfg IO.>>= λ _ →
  readProcess (ws ++ˢ "/bin/candidate") [] "candidate works\n" IO.>>= λ result →
  fileExists (ws ++ˢ "/MANIFEST.tsv") IO.>>= λ manifest →
  fileExists (ws ++ˢ "/SUMMARY.md") IO.>>= λ summary →
  dirExists (ws ++ˢ "/context") IO.>>= λ taskContext →
  filesBelow (ws ++ˢ "/tmp/scripts") IO.>>= λ residue →
  listDirectory (ws ++ˢ "/tmp/scripts") IO.>>= λ scriptDirs →
  F.readFile (ws ++ˢ "/session-memory.sexp") IO.>>= λ memory →
  F.readFile (ws ++ˢ "/MANIFEST.tsv") IO.>>= λ inventory →
  loadBases ws ("T2" ∷ []) IO.>>= λ bases →
  readNames (ws ++ˢ "/session-memory.sexp") IO.>>= λ turns →
  permissions IO.>>= λ after →
  IO.return (works result ∧ manifest ∧ summary ∧ not taskContext ∧ nullᵇ residue ∧ nullᵇ scriptDirs
    ∧ not (contains "SYNTAX_SPAM" memory) ∧ not (contains "TYPE_SPAM" memory)
    ∧ not (contains "MALFORMED_SPAM" memory) ∧ not (contains "parse error" memory)
    ∧ contains "replay passed" memory ∧ contains "terminal probe passed" memory
    ∧ contains "SESSION_ROOT.id" inventory ∧ contains "T2/Concrete.id" inventory
    ∧ transitive bases ∧ count turns ∧ unchanged before after)
  where
    ws = cwd ++ˢ "/tmp/tests/autonomous"
    permissions = readProcess "stat" ("-c" ∷ "%a" ∷ (cwd ++ˢ "/Code.agda") ∷ (cwd ++ˢ "/.gitignore") ∷ []) ""
    unchanged : ProcResult → ProcResult → Bool
    unchanged (procResult 0 a _) (procResult 0 b _) = a ==ˢ b
    unchanged _ _ = false
    replies = doneAction ∷ "MALFORMED_SPAM"
      ∷ sessionSource "run-script" "observe the target" probeSource
      ∷ sessionSource "run-script" "SYNTAX_SPAM" "module Broken where\nx :\n"
      ∷ sessionSource "run-script" "TYPE_SPAM" "module Broken where\nopen import Data.Nat\nopen import Data.Bool\nx : ℕ\nx = true\n"
      ∷ sessionSource "run-script" "observe parameterized terminal transport" ptySource
      ∷ treeAction "T0" baseSpec [] nothing
      ∷ treeAction "T1" upperSpec ("T0" ∷ []) (just liftOne)
      ∷ treeAction "T2" thirdSpec ("T1" ∷ []) (just liftTwo)
      ∷ "(session-action (kind build-exe) (why \"compile the concrete identity\") (entry \"Concrete.app\"))"
      ∷ sessionSource "run-script" "compare candidate and reference on the same corpus" replaySource
      ∷ doneAction ∷ []
    cfg = sessionConfig cwd ws "Implement cat by shrinking to a finite category and lifting freely."
      (refSpec (local "/bin/cat") [] 30000) (ScriptedBackend replies)
      (λ name → ScriptedBackend (sourcePlan "identity preserves the boundary"
        (if name ==ˢ "T0" then baseSource else if name ==ˢ "T1" then upperSource else thirdSource) ∷ []))
    works : ProcResult → Bool
    works (procResult 0 out _) = out ==ˢ "candidate works\n"
    works _ = false
    contains : String → String → Bool
    contains needle haystack = anyᵇ (λ suffix → charPrefix (Data.String.toList needle) suffix)
      (Data.List.tails (Data.String.toList haystack))
      where
        charPrefix : List Data.Char.Char → List Data.Char.Char → Bool
        charPrefix [] _ = true
        charPrefix (_ ∷ _) [] = false
        charPrefix (x ∷ xs) (y ∷ ys) = (Data.Char.toℕ x ≡ᵇ Data.Char.toℕ y) ∧ charPrefix xs ys
    transitive : Code.SessionWorkspace.BaseResult → Bool
    transitive (basesFailed _) = false
    transitive (basesLoaded cs) = length cs ≡ᵇ 3
    count : Maybe (List String) → Bool
    count nothing = false
    count (just xs) = length xs ≡ᵇ 8

compiledSpecGates : String → IO.IO Bool
compiledSpecGates cwd = withTempDirectory (cwd ++ˢ "/tmp/tests/compiled-specs") checkAll
  where
    open import Backend.Switch using (leanPrism; resolveBackendMode)
    gronDeadlockSpec = "module Gen.BadGron.JSON where\nopen import Data.Nat\nopen import Data.String\nopen import Relation.Binary.PropositionalEquality\ndiagnosticByte : ℕ → ℕ\ndiagnosticByte n = \"bad-helper\"\npostulate\n  parse : ℕ → ℕ\n_ : parse 0 ≡ diagnosticByte 0\n_ = refl\n"
    deadHelperSpec = "module Gen.BadDead.JSON where\nopen import Data.Nat\nopen import Data.String\nopen import Relation.Binary.PropositionalEquality\ndeadHelper : ℕ → ℕ\ndeadHelper n = \"dead-helper\"\npostulate\n  parse : ℕ → ℕ\n_ : parse 0 ≡ 0\n_ = refl\n"
    badTestSigSpec = "module Gen.BadSig.JSON where\nopen import Data.Nat\nopen import Data.String\nopen import Relation.Binary.PropositionalEquality\npostulate\n  parse : ℕ → ℕ\n_ : parse \"not-a-nat\" ≡ 0\n_ = refl\n"
    badHoleSpec = "module Gen.BadHole.JSON where\nopen import Data.Nat\nopen import Relation.Binary.PropositionalEquality\npostulate\n  parse : ℕ → ℕ\n_ : parse 0 ≡ 0\n_ = ?\n"
    whereSpec = "module Gen.GoodWhere.JSON where\nopen import Data.Nat\nopen import Relation.Binary.PropositionalEquality\nclassify : ℕ → ℕ\nclassify n = base\n  where\n    base : ℕ\n    base = 0\npostulate\n  parse : ℕ → ℕ\n  parseLaw : parse 0 ≡ classify 0\n"
    whereImpl = "module Gen.GoodWhere.JSON where\nopen import Data.Nat\nopen import Relation.Binary.PropositionalEquality\nclassify : ℕ → ℕ\nclassify n = base\n  where\n    base : ℕ\n    base = 0\nparse : ℕ → ℕ\nparse n = 0\nparseLaw : parse 0 ≡ classify 0\nparseLaw = refl\n"
    bigNatSpec = "module Gen.GoodBigNat.JSON where\nopen import Data.Nat\nopen import Relation.Binary.PropositionalEquality\ndiagnosticByte : ℕ → ℕ\ndiagnosticByte 19 = 0\ndiagnosticByte 20 = 1\ndiagnosticByte n = n\npostulate\n  parse : ℕ → ℕ\n  parseLaw : parse 20 ≡ diagnosticByte 20\n"
    bigNatImpl = "module Gen.GoodBigNat.JSON where\nopen import Data.Nat\nopen import Relation.Binary.PropositionalEquality\ndiagnosticByte : ℕ → ℕ\ndiagnosticByte 19 = 0\ndiagnosticByte 20 = 1\ndiagnosticByte n = n\nparse : ℕ → ℕ\nparse 19 = 0\nparse 20 = 1\nparse n = n\nparseLaw : parse 20 ≡ diagnosticByte 20\nparseLaw = refl\n"
    badSubHelper = "module BadSub where\nopen import Data.Nat\nopen import Data.String\nbad : ℕ → ℕ\nbad n = \"bad-sub\"\npostulate\n  k : ℕ\n"
    badSubUnused = "module UnusedBad where\nopen import Data.Nat\nopen import Data.String\nopen import Relation.Binary.PropositionalEquality\npostulate\n  bad : 0 ≡ \"str\"\n"
    hasSub : String → String → Bool
    hasSub needle haystack = anyᵇ (λ suffix → pfx (Data.String.toList needle) suffix)
      (Data.List.tails (Data.String.toList haystack))
      where
        pfx : List Data.Char.Char → List Data.Char.Char → Bool
        pfx [] _ = true
        pfx (_ ∷ _) [] = false
        pfx (x ∷ xs) (y ∷ ys) = (Data.Char.toℕ x ≡ᵇ Data.Char.toℕ y) ∧ pfx xs ys
    okGron : Code.SessionRunner.ActionResult → Bool
    okGron (Code.SessionRunner.rejected e) =
      hasSub "specification failed Agda typecheck" e ∧ not (hasSub "Cubical Agda" e)
    okGron _ = false
    okDead : Code.SessionRunner.ActionResult → Bool
    okDead (Code.SessionRunner.rejected e) = hasSub "specification failed Agda typecheck" e
    okDead _ = false
    okRej : Code.SessionRunner.ActionResult → Bool
    okRej (Code.SessionRunner.rejected _) = true
    okRej _ = false
    okAcc : Code.SessionRunner.ActionResult → Bool
    okAcc (Code.SessionRunner.accepted _) = true
    okAcc _ = false
    checkSubGate : IO.IO Bool
    checkSubGate = nodeEnvironment (ScriptedBackend
      (submission "subspec with ill-typed helper" good (("BadSub" , badSubHelper) ∷ []) []
       ∷ submission "unimported subspec with ill-typed postulate" good (("UnusedBad" , badSubUnused) ∷ []) []
       ∷ submission "compiled subspec gates enforced" good [] [] ∷ []))
      (cwd ++ˢ "/dump/dump") (cwd ++ˢ "/tmp/tests/compiled-subspecs") (cwd ∷ "/usr/share/agda-stdlib" ∷ []) IO.>>= λ env →
      runNode env taskX (node [] , homeX) IO.>>= λ where
        (ok , node [] , _ , mem , _ , _) → IO.return
          (eqList _==ˢ_ (notesOf mem (unit (mkQ ("X" ∷ "x" ∷ [])))) ("compiled subspec gates enforced" ∷ []))
        _ → IO.return false
    checkBigNatIfPrism : Code.SessionRunner.SessionConfig → IO.IO Bool
    checkBigNatIfPrism cfg = resolveBackendMode leanPrism IO.>>= λ where
      leanPrism → driveTree cfg "GoodBigNat" bigNatSpec [] nothing IO.>>= λ r → IO.return (okAcc r)
      _         → IO.return true
    checkAll : String → IO.IO Bool
    checkAll ws =
      let cfg = sessionConfig cwd ws "compiler-check all specs before execution"
            (refSpec (local "/bin/cat") [] 30000) (ScriptedBackend [])
            (λ name → if name ==ˢ "GoodWhere" then ScriptedBackend (sourcePlan "where-scope projection preserved" whereImpl ∷ [])
                      else if name ==ˢ "GoodBigNat" then ScriptedBackend (sourcePlan "Agda 2.6.3 accepts Nat literal patterns through 20" bigNatImpl ∷ [])
                      else ScriptedBackend [])
      in
      driveTree cfg "BadGron" gronDeadlockSpec [] nothing IO.>>= λ r1 →
      driveTree cfg "BadDead" deadHelperSpec [] nothing IO.>>= λ r2 →
      driveTree cfg "BadSig" badTestSigSpec [] nothing IO.>>= λ r3 →
      driveTree cfg "BadHole" badHoleSpec [] nothing IO.>>= λ r4 →
      driveTree cfg "GoodWhere" whereSpec [] nothing IO.>>= λ r5 →
      checkBigNatIfPrism cfg IO.>>= λ bigOk →
      dirExists (ws ++ˢ "/trees/BadGron") IO.>>= λ p1 →
      dirExists (ws ++ˢ "/trees/BadDead") IO.>>= λ p2 →
      checkSubGate IO.>>= λ subOk →
      IO.return (okGron r1 ∧ okDead r2 ∧ okRej r3 ∧ okRej r4 ∧ okAcc r5 ∧ bigOk ∧ not p1 ∧ not p2 ∧ subOk)

main : IO.IO ⊤
main = currentDirectory IO.>>= λ cwd →
  report "retry memory hygiene: malformed, two syntax errors, two type errors, accepted" (hygiene cwd) IO.>>= λ a →
  report "N3 real compiler rejects missing child lemma" (negativeGlue cwd) IO.>>= λ b →
  report "N5 real compiler rejects changed category" (rejectSource cwd N5-source) IO.>>= λ c →
  report "N6 real compiler rejects erased body" (rejectSource cwd N6-source) IO.>>= λ d →
  report "withEphemeral leaves zero directory diff" noResidue IO.>>= λ e →
  report "compiler-checked contradiction with supplied base module" (realRefutation cwd) IO.>>= λ f →
  report "autonomous session: probe, retry hygiene, T0/T1/T2, compile, replay, gated finish without task context" (autonomous cwd) IO.>>= λ g →
  report "concrete spec helpers: record constructor, laws, named/anonymous tests, tampering rejected" (concreteSpecHelpers cwd) IO.>>= λ h →
  report "workspace inputs: successful-tree imports and generated-source/manifest fingerprints" (workspaceInputs cwd) IO.>>= λ i →
  report "compiler-checked law/test contradictions: anonymous, named, helper dependencies, fresh names" (testLawContradictions cwd) IO.>>= λ j →
  report "subspecs reject anonymous postulates and accept anonymous proof bodies" (anonymousSubspecs cwd) IO.>>= λ k →
  report "drive-tree rejects anonymous postulates before execution and accepts proof bodies" (anonymousTreeSpecs cwd) IO.>>= λ l →
  report "drive-tree prechecks missing child-map in LiftSpec and keeps SessionEnv scope clean" (liftPrecheckAndScope cwd) IO.>>= λ m →
  report "mandatory Agda compilation gate on drive-tree specs and child subspecs (gron 39/8232 regression)" (compiledSpecGates cwd) IO.>>= λ n →
  if a ∧ b ∧ c ∧ d ∧ e ∧ f ∧ g ∧ h ∧ i ∧ j ∧ k ∧ l ∧ m ∧ n then F.putStrLn "ALL PASS" else exitFailure
