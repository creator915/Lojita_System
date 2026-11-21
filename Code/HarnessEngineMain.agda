{-# OPTIONS --guardedness #-}
module Code.HarnessEngineMain where

open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.List using (List; []; _∷_; length; map; reverse)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat using (_≡ᵇ_)
open import Data.Product using (_,_)
open import Data.String using (String; intersperse; unlines) renaming (_++_ to _++ˢ_)
import Data.Unit as Unit
open import Data.Unit.Polymorphic using (⊤; tt)
import IO.Primitive as Prim
open import IO using (IO; Main; run; putStrLn; _>>=_; _>>_; pure; lift) renaming (readFiniteFile to readFile)
open import System.Environment using (getArgs)
open import OwnershipIO.FFI using (exitFailure; enableLineBuffering; runPrismCatSelfChecks)

import Context.Blueprint as BP
import Context.PolyTransport as CPT
import Context.Terminal as Term
import Context.Filter as Filter
import Backend.Mode as Mode
open import Code
open import Code.SExpr using (SExpr; parseSExpr; showSExpr; list; sym; str)
open import Code.Shape using (HomeShape; node)
open import Code.Transport
open import Code.Lift using (liftSpec; LiftSpec; endpoints; baseUnits; upperUnits; validLiftRefutation; extractCulpritBaseUnits)
open import Code.Protocol
open import Code.Encode using (encodeCanonical)
open import Code.Parse using (parse; parsePlan; parseLift; decodeQ; decodeCode)
open import Code.Render using (render)
import Code.Namespace as NS
import Code.PolyTransport as PT
import Code.NodeTransport as NT
open import Code.Submission using (Submission; parseSubmission; refuteLift)
open import Code.SessionProtocol using (parseSessionAction)
open import Code.Prompt using (nodePrompt; showRefuteProblem; showImplProblem)
open import Code.HarnessCore
import Code.PlanPreview as Preview
open import Code.PureCLI

private
  liftUnit : Prim.IO Unit.⊤ → IO ⊤
  liftUnit action = lift action >> pure tt

  canonicalText : String → String
  canonicalText txt = maybe′ encodeCanonical "-- parse error" (parse txt)

  checkInterfaceTexts : String → String → String
  checkInterfaceTexts specTxt candTxt with parse specTxt | parse candTxt
  ... | nothing   | _         = "-- parse error (spec)"
  ... | _         | nothing   = "-- parse error (cand)"
  ... | just spec | just cand =
    let d = specΔ (modName spec) (decls spec) []
    in if satisfies d cand then "OK"
       else unlines ("INTERFACE_MISMATCH" ∷ satisfiesDetails d cand)

  refuteStubText : String → String
  refuteStubText txt with parse txt
  ... | nothing = "-- parse error (spec)"
  ... | just c = render (refuteStubOf (specΔ (modName c) (decls c) []))

  checkWitnesses : List String → Code → QName → String
  checkWitnesses allowed c spec with validIndependence spec allowed c
  ... | ps@(_ ∷ _) = unlines ("REFUTE_GATE_ERROR" ∷ map showRefuteProblem ps)
  ... | [] = if nullᵇ (validRefutation spec allowed c)
    then "OK:contradiction" else "OK:independent"

  checkRefuteText : String → List String → String → String
  checkRefuteText specName allowed txt = maybe′
    (λ c → maybe′ (checkWitnesses allowed c) "REFUTE_GATE_ERROR\ninvalid spec name" (decodeQ (str specName)))
    "REFUTE_GATE_ERROR\ninvalid candidate" (parse txt)

  -- check-lift-refute SPEC FILE [FLAG ...] reads (bundle BASE ... CANDIDATE).
  checkLiftBundle : QName → List String → SExpr → String
  checkLiftBundle spec allowed (list (sym "bundle" ∷ modules)) = collect [] modules
    where
      verify : List Code → Code → String
      verify bases c with validLiftRefutation spec bases allowed c
      ... | [] = "OK:liftObstruction\nCULPRIT_BASE_UNITS: " ++ˢ intersperse " " (map NT.moduleKey (extractCulpritBaseUnits bases c))
      ... | ps@(_ ∷ _) = unlines ("REFUTE_GATE_ERROR" ∷ map showRefuteProblem ps)

      collect : List Code → List SExpr → String
      collect acc [] = "REFUTE_GATE_ERROR\nmissing candidate"
      collect acc (x ∷ []) = maybe′ (verify (reverse acc)) "REFUTE_GATE_ERROR\ninvalid candidate" (decodeCode x)
      collect acc (x ∷ y ∷ ys) = maybe′ (λ b → collect (b ∷ acc) (y ∷ ys)) "REFUTE_GATE_ERROR\ninvalid base" (decodeCode x)
  checkLiftBundle _ _ _ = "REFUTE_GATE_ERROR\nexpected (bundle BASE ... CANDIDATE)"

  checkObject : String → List String → Code → String
  checkObject role allowed c with if role ==ˢ "closed" then closedImplOK allowed c else specImplOK allowed c
  ... | p ∷ ps = unlines ("OBJECT_GATE_ERROR" ∷ map showImplProblem (p ∷ ps))
  ... | [] = maybe′ (λ { (kind , detail) → unlines (kind ∷ detail ∷ []) })
    (maybe′ (λ problem → "OBJECT_GATE_ERROR\n" ++ˢ problem) "OK"
      (if role ==ˢ "closed" then nothing else specProblem (decls c)))
    (if role ==ˢ "subspec" then subspecNarrowingProblem c else nothing)

  checkObjectText : String → List String → String → String
  checkObjectText role allowed txt = maybe′ (checkObject role allowed) "OBJECT_GATE_ERROR\ninvalid candidate" (parse txt)

  selfCheckOK : Bool
  selfCheckOK =
    let sampleSexp = "(module \"Demo\" (params) (sig (mods) \"x\" (def \"Agda.Builtin.Nat.Nat\")))"
        parsedC    = parse sampleSexp
        rtOK       = maybe′ (λ c → not (render c ==ˢ "") ∧ not (encodeCanonical c ==ˢ "")) false parsedC
        modeOK     = maybe′ (λ _ → true) false (Mode.parseBackendMode "prism")
        termOK     = length (Term.screenLines (Term.stepANSI (Term.blankScreen 4 10) (Term.bytes "ok\n"))) ≡ᵇ 4
        filtOK     = Filter.expected1 Filter.insensitive (Filter.input Filter.prefix "ab" "ABCD")
        actOK      = maybe′ (λ _ → true) false
                       (parseSessionAction "(session-action (kind finish) (summary \"done\"))")
        subOK      = maybe′ (λ _ → true) false
                       (parseSubmission "(submission (kind contradiction) (refute \"module R where\"))")
        refuteOK   = parsedRefute (parseSubmission "(submission (kind refute-lift) (why \"unliftable\") (refute \"module R where\"))")
        liftOK     = maybe′ (λ _ → true) false (parseLift "(lift \"A\" \"B\" () ())")
        multiOK    = maybe′ parsedMulti false (parseLift "(lift \"A\" \"B\" () (((\"A.x\" \"A.y\") (\"B.x\" \"B.y\") \"B.square\")))")
        polyOK     = maybe′ (λ _ → true) false (PT.parsePolyTransport "(poly-transport \"A\" \"B\" () ())")
        bpOK       = BP.project (BP.keepPort Bool) true
        cptOK      = let _ = CPT.graphPort not in true
        emptyC     = code (mkQ ("Demo" ∷ [])) [] []
        task0      = nodeTask (specΔ (mkQ ("Demo" ∷ [])) [] []) [] nothing
        promptOK   = not (nodePrompt task0 emptyC [] "" ==ˢ "")
        gatesOK    = maybe′ (λ _ → false) true (checkCandidateGates task0 emptyC (mkPlan "id" nothing [] []) emptyC)
        nsOK       = NS.validSegment "Engine" ∧ not (NS.validSegment "module")
        ntOK       = length (NT.exported (NT.frozen emptyC [] [] [])) ≡ᵇ 1
        shOK       = caseShape (node [])
    in rtOK ∧ modeOK ∧ termOK ∧ filtOK ∧ actOK ∧ subOK ∧ refuteOK ∧ liftOK ∧ multiOK ∧ polyOK ∧ bpOK ∧ cptOK ∧ promptOK ∧ gatesOK ∧ nsOK ∧ ntOK ∧ shOK
    where
      parsedRefute : Maybe Submission → Bool
      parsedRefute (just (refuteLift why src)) = (why ==ˢ "unliftable") ∧ (src ==ˢ "module R where")
      parsedRefute _ = false
      parsedMulti : LiftSpec → Bool
      parsedMulti l with endpoints l
      ... | e ∷ [] = (length (baseUnits e) ≡ᵇ 2) ∧ (length (upperUnits e) ≡ᵇ 2)
      ... | _ = false
      caseShape : HomeShape → Bool
      caseShape (node _) = true

  runArgs : List String → IO ⊤
  runArgs ("roundtrip" ∷ f ∷ []) = readFile f >>= λ txt → putStrLn (roundtripText txt)
  runArgs ("units" ∷ f ∷ [])     = readFile f >>= λ txt → putStrLn (unitsText txt)
  runArgs ("order" ∷ f ∷ [])     = readFile f >>= λ txt → putStrLn (orderText txt)
  runArgs ("canonical" ∷ f ∷ []) = readFile f >>= λ txt → putStrLn (canonicalText txt)
  runArgs ("apply" ∷ f ∷ g ∷ []) =
    readFile f >>= λ old → readFile g >>= λ pl → putStrLn (applyTexts old pl)
  runArgs ("check-interface" ∷ f ∷ g ∷ []) =
    readFile f >>= λ sp → readFile g >>= λ ca → putStrLn (checkInterfaceTexts sp ca)
  runArgs ("refute-stub" ∷ f ∷ []) =
    readFile f >>= λ sp → putStrLn (refuteStubText sp)
  runArgs ("check-refute" ∷ spec ∷ f ∷ allowed) =
    readFile f >>= λ c → putStrLn (checkRefuteText spec allowed c)
  runArgs ("check-lift-refute" ∷ spec ∷ f ∷ allowed) =
    readFile f >>= λ txt → putStrLn (maybe′ (checkLiftBundle (NT.moduleQName spec) allowed)
      "REFUTE_GATE_ERROR\ninvalid bundle" (parseSExpr txt))
  runArgs ("check-object" ∷ role ∷ f ∷ allowed) =
    readFile f >>= λ c → putStrLn (checkObjectText role allowed c)
  runArgs ("check-plan" ∷ f ∷ g ∷ []) =
    readFile f >>= λ ctx → readFile g >>= λ req → putStrLn (Preview.planPreview ctx req)
  runArgs ("decode-plan" ∷ f ∷ []) = readFile f >>= λ txt → putStrLn (Preview.decodePlanSource txt)
  runArgs ("plan-deps" ∷ f ∷ []) = readFile f >>= λ ctx → putStrLn (Preview.planDeps ctx "(subspecs)")
  runArgs ("plan-deps" ∷ f ∷ g ∷ []) =
    readFile f >>= λ ctx → readFile g >>= λ subs → putStrLn (Preview.planDeps ctx subs)
  runArgs ("check-object-json" ∷ role ∷ f ∷ allowed) =
    readFile f >>= λ txt → putStrLn (Preview.objectPreview role allowed txt)
  runArgs ("check-interface-json" ∷ f ∷ g ∷ []) =
    readFile f >>= λ sp → readFile g >>= λ ca → putStrLn (Preview.interfacePreview sp ca)
  runArgs ("verify-self" ∷ []) =
    if selfCheckOK then (liftUnit runPrismCatSelfChecks >> putStrLn "HARNESS_ENGINE_OK") else liftUnit exitFailure
  runArgs _ = liftUnit exitFailure

main : Main
main = run (liftUnit enableLineBuffering >> getArgs >>= runArgs)
