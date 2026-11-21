{-# OPTIONS --guardedness #-}
module Test.HarnessLiftObstruction where

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; unlines; lines) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import System.Environment.Primitive using (getArgs)
open import Ownership hiding (Home; Name; set; open′; _>>=_; _>>_)
import OwnershipIO as O
open import OwnershipIO.FFI using (failIO)
open import OwnershipIO.MetaFFI using (_>>_)
open import Code
open import Code.Transport
open import Code.Lift using (validLiftRefutation; extractCulpritBaseUnits)
open import Code.Submission using (refuteLift; parseSubmission)
open import Code.Harness
open import Code.NodeTransport using (moduleQName)
open import Code.Render using (render)
open import Code.Prompt using (showRefuteProblem)
open import Code.Encode using (encodeCode)
open import Code.Codecs using (eqMemory)
open import Code.SExpr using (list; sym; showSExpr)
open import Code.Driver using (nodeEnvironmentWith)
open import Code.SessionRunner using (runNode)
import Backend.Switch as B
import Test.HarnessPure as Pure

witness-field : parseSubmission "(submission (kind refute-lift) (witness \"source\"))" ≡ just (refuteLift "" "source")
witness-field = refl
ambiguous-witness : parseSubmission "(submission (kind refute-lift) (witness \"a\") (refute \"b\"))" ≡ nothing
ambiguous-witness = refl
unknown-field : parseSubmission "(submission (kind refute-lift) (main \"x\") (refute \"r\"))" ≡ nothing
unknown-field = refl

private
  q = moduleQName
  rootName = q "Gen.T1.Root"
  escape = "Gen.T1.Escape"
  parser = "Gen.T1.ParseLine"
  baseName = q "Gen.T0.ParseLine"
  parseLine = q "Gen.T0.ParseLine.parseLine₀"
  lineTag = q "Gen.T0.ParseLine.LineTag"
  culprits : List QName
  culprits = parseLine ∷ lineTag ∷ []
  reason = "single pass discards reference definitions"
  envelope : String → String
  envelope src = "(submission (kind refute-lift) (why \"" ++ˢ reason ++ˢ "\") (refute @r))\n```agda r\n" ++ˢ src ++ˢ "\n```\n"

  Checks = List (String × Bool)
  assertAll : Checks → IO.IO ⊤
  assertAll [] = IO.return tt
  assertAll ((label , true) ∷ xs) = assertAll xs
  assertAll ((label , false) ∷ _) = failIO ("failed: " ++ˢ label)

  imp : QName → Decl
  imp name = import′ name false everything []

  gateChecks : Code → Code → Checks
  gateChecks base w =
      ("scoped Pandoc proof of bottom" , nullᵇ (gate w))
    ∷ ("builtin empty type" , nullᵇ (gate (changeGoal (q "Agda.Builtin.Empty.⊥"))))
    ∷ ("exact ordered culprits" , eqList _==ᴺ_ (owners w) culprits)
    ∷ ("flat constructor" , owns (con (q "Gen.T0.ParseLine.KRefDef")) lineTag)
    ∷ ("qualified constructor" , owns (con (q "Gen.T0.ParseLine.LineTag.KRefDef")) lineTag)
    ∷ ("witness importing a more specific base" , eqList _==ᴺ_ (owners
        (code (q "Gen.T0") [] (imp baseName ∷ [ badFun (def parseLine) [] ]))) [ parseLine ])
    ∷ ("a base prefix cannot claim a spec unit" , nullᵇ (extractCulpritBaseUnits [ code (q "Gen.T1") [] [] ] pureSpec))
    ∷ ("nearest module fallback" , eqList _==ᴺ_
        (extractCulpritBaseUnits (code (q "Gen.T0") [] [] ∷ [ base ]) (ref (def (q "Gen.T0.ParseLine.opaque")))) [ baseName ])
    ∷ ("hole" , reports (invalidImplementation (containsHole bad)) (extra (badFun hole [])))
    ∷ ("postulate" , reports (invalidImplementation (unimplementedPostulate bad)) (extra (sig plain "bad" (set 0))))
    ∷ ("termination bypass" , reports (invalidImplementation forbiddenTerminationBypass) (extra (pragma "TERMINATING")))
    ∷ ("TrustMe" , reports (invalidImplementation (unsafePrimitive trust)) (extra (imp trust)))
    ∷ ("unit result" , reports missingBottomProof (changeGoal (q "Agda.Builtin.Unit.⊤")))
    ∷ ("SafeTaboo result" , reports missingBottomProof (changeGoal (q "Context.Taboo.SafeTaboo")))
    ∷ ("private bottom" , reports missingBottomProof (record w { decls = map hideBottom (decls w) }))
    ∷ ("module parameters" , reports missingBottomProof (record w { params = [ bind visible [ "A" ] (set 0) ] }))
    ∷ ("unauthorized import" , reports (unauthorizedImport other) (extra (imp other)))
    ∷ ("unused import in where" , reports (unauthorizedImport other) (extra (badFun (set 0) [ imp other ])))
    ∷ ("unauthorized reference" , reports (unauthorizedImport other) (ref (def other)))
    ∷ ("reserved witness module" , reports (unauthorizedImport (q "Main.Forged")) (record w { modName = q "Main.Forged" }))
    ∷ ("pure spec with unused base import" , eqList _==ˢ_ (map showRefuteProblem (gate pureSpec))
        [ showRefuteProblem missingBaseReference ])
    ∷ []
    where
      gate = validLiftRefutation rootName [ base ] []
      owners = extractCulpritBaseUnits [ base ]
      reports : RefuteProblem → Code → Bool
      reports p c = elemᵇ _==ˢ_ (showRefuteProblem p) (map showRefuteProblem (gate c))
      bad = mkQ (full (modName w) ++ [ "bad" ])
      badFun : Expr → List Decl → Decl
      badFun e ds = fun plain "bad" [ clause (head bad []) (rhs e) ds ]
      ref : Expr → Code
      ref e = code (modName w) [] [ badFun e [] ]
      owns : Expr → QName → Bool
      owns e name = eqList _==ᴺ_ (owners (ref e)) [ name ]
      extra : Decl → Code
      extra d = record w { decls = decls w ++ [ d ] }
      other = q "Gen.Other.External"
      trust = q "Agda.Builtin.TrustMe"
      changeGoal : QName → Code
      changeGoal name = record w { decls = map change (decls w) }
        where
          change : Decl → Decl
          change d@(sig m n e) = if bottomExpr e then sig m n (def name) else d
          change d = d
      hideBottom : Decl → Decl
      hideBottom d@(sig m n e) = if bottomExpr e then sig (record m { isPrivate = true }) n e else d
      hideBottom d = d
      pureSpec = code (modName w) [] (imp rootName ∷ imp baseName ∷ sig plain "bad" (def (q "Data.Empty.⊥"))
        ∷ badFun (def (q "Gen.T1.Root.impossible")) [] ∷ [])

  taskFor : Code → Code → NodeTask
  taskFor base spec = record (nodeTask (specΔ (modName spec) (decls spec) []) [] nothing) { baseModules = [ base ] }

  homeFor : NodeTask → Model (HomeSt (node []))
  homeFor t = stubOf (δ t) , [] , newIface (δ t) , tt

  fixedDump : Code → Server [] DumpReq DumpResult [] (Dir [])
  ServerI.call (fixedDump c) = ask λ _ → tell (dumped c) (daemon (fixedDump c))
  ServerI.stop (fixedDump c) = give∃Dir tt refl

  envFor : Code → List String → Env NodeΨ
  envFor c replies = (λ _ → provide [] (daemon (Pure.scriptedAI replies)))
    ∷ (λ _ → provide [] (daemon (fixedDump c)))
    ∷ (λ _ → provide [] (daemon (Pure.checks []))) ∷ Pure.childOffer ∷ []

  obstructionIs : Code → Maybe Verdict → Bool
  obstructionIs w (just (liftObstruction why qs proof)) = (why ==ˢ reason) ∧ eqList _==ᴺ_ qs culprits ∧ eqCode w proof
  obstructionIs _ _ = false

  module Siblings (base spec proof childSpec childProof : Code) where
    parentTask = taskFor base spec
    parseTask = taskFor base childSpec
    escapeTask = nodeTask (specΔ (q escape) Pure.ifaceX [ keep (ext (q "Gen.T1.Escape.x")) ]) [] nothing
    escapeImpl = code (q escape) [] (Pure.ifaceX ++ [ fun plain "x"
      [ clause (head (q "Gen.T1.Escape.x") []) (rhs (lit (natL 0))) [] ] ])
    escapeReply = Pure.submission "verified escaping" "escape" [] []
    memory : Memory
    memory = [ flags , [ "root memory" ] ]
    seedHome = homeFor parentTask
    escapeImport = import′ (q escape) false everything Pure.ifaceX
    conditional = code rootName [] (escapeImport ∷ import′ (q parser) false everything (decls childSpec) ∷ [])
    parent = nodeState parentTask (proj₁ seedHome) memory conditional (just (plan "split" (decls conditional) []))
      "" WaitingKids (node [] , tt , seedHome)
    parentEnv = envFor proof [ envelope "root-proof" ]

    -- Both channels run the real leaf agent. An initial retry on ParseLine
    -- lets us observe Escape's finish/commit before its sibling reports.
    kids : Slots
    kids = (escape , awake) ∷ (parser , awake) ∷ []
    resources : Models (Work kids)
    resources = provide [] (daemon (Pure.checks [])) tt , provide [] (daemon (fixedDump proof)) tt ,
      provide [] (daemon (Pure.scriptedAI [ envelope "root-proof" ])) tt ,
      provide (envFor escapeImpl [ escapeReply ]) (nodeAgent (node [])) (homeFor escapeTask) escapeTask ,
      provide (envFor childProof ("retry" ∷ [ envelope "parse-proof" ])) (nodeAgent (node [])) (homeFor parseTask) parseTask ,
      seedHome

    Turn = Maybe Verdict × Σ (Slots × NodeState) (λ j → Models (Work (proj₁ j)))
    turn : Turn → Turn
    turn (_ , (ks , s) , m) = machineCall parentEnv (oneTurn ks s) m tt
    first = turn (nothing , (kids , parent) , resources)
    second = turn first
    third = turn second
    fourth = turn third

    attempt : NodeTask → CheckResult → Turn
    attempt t cr = turn (nothing , ([] , record parent { task = t ; phase = Planning }) ,
      (provide [] (daemon (Pure.checks [ cr ])) tt , provide [] (daemon (fixedDump proof)) tt ,
       provide [] (daemon (Pure.scriptedAI [ envelope "root-proof" ])) tt , seedHome))

    retriesWith : String → Turn → Bool
    retriesWith msg (nothing , (_ , s) , _) with NodeState.phase s
    ... | Planning = NodeState.diagnostic s ==ˢ msg
    ... | _ = false
    retriesWith _ _ = false

    escapeFinished : Turn → Bool
    escapeFinished (nothing , ((n , finished) ∷ (_ , awake) ∷ [] , s) , _) with NodeState.phase s
    ... | WaitingKids = n ==ˢ escape
    ... | _ = false
    escapeFinished _ = false

    revised : Turn → Bool
    revised (nothing , ((a , finished) ∷ (b , sleeping _ false) ∷ [] , s) , _) with NodeState.phase s
    ... | Planning = (a ==ˢ escape) ∧ (b ==ˢ parser)
      ∧ allᵇ (λ line → elemᵇ _==ˢ_ line (lines (NodeState.diagnostic s)))
        (("child lift-obstruction (" ++ˢ reason ++ˢ ")") ∷ ("CHILD: " ++ˢ parser)
         ∷ "CULPRIT_BASE_UNITS: Gen.T0.ParseLine.parseLine₀ Gen.T0.ParseLine.LineTag" ∷ lines (render childProof))
    ... | _ = false
    revised _ = false

    stopped : Turn → Msg (∃Res HomeShape HomeSt)
    stopped (_ , (ks , s) , m) = Running.onStop (running parentEnv (nodeServer ks s) m)
    preserved : Msg (∃Res HomeShape HomeSt) → Bool
    preserved (node ((n , node []) ∷ []) , (c , cm , ci , _) , shell , mem , iface , _) =
      (n ==ˢ escape) ∧ (showSExpr (encodeCode c) ==ˢ showSExpr (encodeCode escapeImpl))
      ∧ eqDecls ci Pure.ifaceX ∧ eqMemory cm [ unit (q "Gen.T1.Escape.x") , [ "verified escaping" ] ]
      ∧ eqCode shell (code rootName [] [ escapeImport ]) ∧ nullᵇ (closedImplOK [] shell)
      ∧ eqMemory mem memory ∧ nullᵇ iface
    preserved _ = false

    -- Exercise the other two freezeVerifiedKids branches, including all
    -- leaves of a retained grandchild. The awake slot still owns a channel.
    mixed : Slots
    mixed = (parser , awake) ∷ [ escape , sleeping (node [ "Grand" , node [] ]) true ]
    mixedModels : Models (Work mixed)
    mixedModels = provide [] (daemon (Pure.checks [])) tt , provide [] (daemon (fixedDump proof)) tt ,
      provide [] (daemon (Pure.scriptedAI [])) tt ,
      provide (envFor childProof []) (nodeAgent (node [])) (homeFor parseTask) parseTask ,
      ((Pure.impl "Grand" , memory , Pure.ifaceX , tt) , escapeImpl , memory , Pure.ifaceX , tt) , seedHome
    retained : Msg (∃Res HomeShape HomeSt) → Bool
    retained (node ((n , node ((g , node []) ∷ [])) ∷ []) , (grand , c , cm , ci , _) , shell , _)
      = (n ==ˢ escape) ∧ (g ==ˢ "Grand") ∧ eqCode (proj₁ grand) (Pure.impl "Grand")
        ∧ eqMemory (proj₁ (proj₂ grand)) memory ∧ eqCode c escapeImpl ∧ eqMemory cm memory
        ∧ eqDecls ci Pure.ifaceX ∧ eqCode shell (code rootName [] [ escapeImport ])
    retained _ = false

    tests : Checks
    tests = ("Escape commits first" , escapeFinished second)
      ∷ ("ParseLine stops and parent replans with proof" , revised third)
      ∷ ("parent returns its own lift obstruction" , obstructionIs proof (proj₁ fourth))
      ∷ ("a rejected kernel check retries" , retriesWith "ill-typed proof" (attempt parentTask (fail "ill-typed proof")))
      ∷ ("a node without bases retries" , retriesWith
          "refute-lift: node has no base modules to refute; use (kind contradiction) if SPECIFICATION is inconsistent"
          (attempt (record parentTask { baseModules = [] }) pass))
      ∷ ("onStop preserves exactly the committed Escape subtree and root memory" , preserved (stopped fourth))
      ∷ ("retained subtree survives and awake child is dropped" , retained (stopped
          (nothing , (mixed , record parent { phase = Done (liftObstruction reason culprits proof) }) , mixedModels))) ∷ []

  -- Any unexpected retry, including a shadow audit disagreement, fails the
  -- live run immediately and prints the actual diagnostic from the node.
  liveAI : String → O.RunningIO AIReq AIReply (⊤ × ⊤)
  O.onCall (liveAI reply) (propose prompt true _) = failIO prompt
  O.onCall (liveAI reply) (propose _ false _) = IO.return (aiReply reply "pandoc")
  O.onCall (liveAI reply) _ = IO.return (aiReply "" "pandoc")
  O.onStop (liveAI reply) = IO.return (tt , tt)

  runTests : String → String → String → IO.IO ⊤
  runTests suite repo dir = do
    mode ← B.resolveBackendMode B.leanPrism
    let dump = B.switchDump mode (repo ++ˢ "/dump/dump") repo dir []
        scope : String → List Code → IO.IO Code
        scope = λ filename deps → F.readFile (dir ++ˢ "/" ++ˢ filename) IO.>>= λ txt →
          dump (dumpReq txt [] deps) IO.>>= λ where
            (dumped c) → IO.return c
            (dumpFailed e) → failIO e
    base ← scope "base.agda" []
    spec ← scope "spec.agda" [ base ]
    let t = taskFor base spec
        deps = refuteStubOf (δ t) ∷ [ base ]
    w ← scope "proof.agda" deps
    if suite ==ˢ "pure" then (do
      childSpec ← scope "child.agda" [ base ]
      childProof ← scope "child-proof.agda" (refuteStubOf (δ (taskFor base childSpec)) ∷ [ base ])
      assertAll (gateChecks base w ++ Siblings.tests base spec w childSpec childProof)
      F.writeFile (dir ++ˢ "/bundle.sexp") (showSExpr (list (sym "bundle" ∷ encodeCode base ∷ [ encodeCode w ])))
      F.putStrLn "PASS pure gates, ordered culprits, parent revision and verified subtree preservation")
     else (do
      src ← F.readFile (dir ++ˢ "/proof.agda")
      let check = B.switchCheck mode repo dir []
      check (agdaCheck base []) IO.>>= λ where
        (fail e) → failIO e
        pass → do
          env ← nodeEnvironmentWith (IO.return (liveAI (envelope src))) dump check
          runNode env t (node [] , stubOf (δ t) , [] , newIface (δ t) , tt) IO.>>= λ where
            (v , node [] , shell , _ , iface , _) → do
              assertAll (("live verdict/proof/culprits" , obstructionIs w (just v))
                ∷ [ "live shell" , eqCode shell (code rootName [] []) ∧ nullᵇ iface ])
              F.putStrLn ("PASS runNode/switchCheck " ++ˢ B.showBackendMode mode)
            _ → failIO "unexpected live home shape")
    where open IO using (_>>=_)

main : IO.IO ⊤
main = getArgs IO.>>= λ where
  (suite ∷ repo ∷ dir ∷ []) → runTests suite repo dir
  _ → failIO "expected pure|live REPO FIXTURE"
