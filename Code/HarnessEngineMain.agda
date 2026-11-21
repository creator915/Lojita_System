{-# OPTIONS --guardedness #-}
module Code.HarnessEngineMain where

open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat using (_≡ᵇ_)
open import Data.Product using (_,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
import Data.Unit as Unit
open import Data.Unit.Polymorphic using (⊤; tt)
import IO.Primitive as Prim
open import IO using (IO; Main; run; putStrLn; _>>=_; _>>_; pure; lift) renaming (readFiniteFile to readFile)
open import System.Environment using (getArgs)
open import OwnershipIO.FFI using (exitFailure; enableLineBuffering)

import Context.Blueprint as BP
import Context.PolyTransport as CPT
import Context.Terminal as Term
import Context.Filter as Filter
import Backend.Mode as Mode
open import Code
open import Code.SExpr using (parseSExpr; showSExpr)
open import Code.Shape using (HomeShape; node)
open import Code.Transport
open import Code.Lift using (liftSpec)
open import Code.Protocol
open import Code.Encode using (encodeCanonical)
open import Code.Parse using (parse; parsePlan; parseLift)
open import Code.Render using (render)
import Code.Namespace as NS
import Code.PolyTransport as PT
import Code.NodeTransport as NT
open import Code.Submission using (parseSubmission)
open import Code.SessionProtocol using (parseSessionAction)
open import Code.Prompt using (nodePrompt)
open import Code.HarnessCore
open import Code.PureCLI

private
  liftUnit : Prim.IO Unit.⊤ → IO ⊤
  liftUnit action = lift action >> pure tt

  canonicalText : String → String
  canonicalText txt = maybe′ encodeCanonical "-- parse error" (parse txt)

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
        liftOK     = maybe′ (λ _ → true) false (parseLift "(lift \"A\" \"B\" () ())")
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
    in rtOK ∧ modeOK ∧ termOK ∧ filtOK ∧ actOK ∧ subOK ∧ liftOK ∧ polyOK ∧ bpOK ∧ cptOK ∧ promptOK ∧ gatesOK ∧ nsOK ∧ ntOK ∧ shOK
    where
      caseShape : HomeShape → Bool
      caseShape (node _) = true

  runArgs : List String → IO ⊤
  runArgs ("roundtrip" ∷ f ∷ []) = readFile f >>= λ txt → putStrLn (roundtripText txt)
  runArgs ("units" ∷ f ∷ [])     = readFile f >>= λ txt → putStrLn (unitsText txt)
  runArgs ("order" ∷ f ∷ [])     = readFile f >>= λ txt → putStrLn (orderText txt)
  runArgs ("canonical" ∷ f ∷ []) = readFile f >>= λ txt → putStrLn (canonicalText txt)
  runArgs ("apply" ∷ f ∷ g ∷ []) =
    readFile f >>= λ old → readFile g >>= λ pl → putStrLn (applyTexts old pl)
  runArgs ("verify-self" ∷ []) =
    if selfCheckOK then putStrLn "HARNESS_ENGINE_OK" else liftUnit exitFailure
  runArgs _ = liftUnit exitFailure

main : Main
main = run (liftUnit enableLineBuffering >> getArgs >>= runArgs)
