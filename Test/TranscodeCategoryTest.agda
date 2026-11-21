{-# OPTIONS --guardedness #-}
module Test.TranscodeCategoryTest where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (_≡ᵇ_; _≤_)
open import Data.Product using (_,_)
open import Data.String using (String)
import Data.String.Properties as Stringₚ
open import Level using (0ℓ)
open import IO using (IO; Main; run; putStrLn; _>>_)
open import Data.Unit.Polymorphic using (⊤)
open import System.Exit using (die)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Code
import Code.TranscodeIR as IR
import Context.TranscodeCategory as C

private
  key : Name → Name → QName
  key m n = mkQ (m ∷ n ∷ [])

  dataA : Name → List Decl
  dataA m = dataSig plain "A" [] (set 0) ∷
            dataDef plain "A" [] [ "a" , def (key m "A") ] ∷ []

  constant : Name → Name → Expr → Decl
  constant m n value = fun plain n [ clause (head (key m n) []) (rhs value) [] ]

  demo = "SharedPureHelperSig"
  ref : Name → Expr
  ref n = def (key demo n)

  helper = sig plain "h" (set 0) ∷ constant demo "h" (ref "A") ∷ []
  stream = key demo "Stream"
  fieldQ = mkQ (demo ∷ "Stream" ∷ "out" ∷ [])
  fSig = sig plain "f" (ref "h")
  fFun = constant demo "f" (con (mkQ (demo ∷ "A" ∷ "a" ∷ [])))
  gSig = sig plain "g" (ref "Stream")
  gFun = fun plain "g" [ clause (proj fieldQ (head (key demo "g") []) []) (rhs (ref "f")) [] ]
  mixed = code (mkQ [ demo ]) []
    (dataA demo ++ helper ++ (fSig ∷ fFun ∷ recSig plain "Stream" [] (set 0) ∷
      recDef plain "Stream" [] (recDir true nothing) [ "out" , ref "h" ] ∷
      gSig ∷ gFun ∷ []))

  unitMatches : Code → QName → List Decl → Bool
  unitMatches c name expected with lookupUnit (units c) name
  ... | just u = eqDecls (udecls u) expected
  ... | nothing = false

  helperColor : Bool
  helperColor with IR.classifyCodeUnit mixed (unitOf (key demo "h") helper)
  ... | C.pureSigHelperDecl = true
  ... | _ = false

  sharedPureHelperSig : Bool
  sharedPureHelperSig with IR.splitCodePushout mixed
  ... | nothing = false
  ... | just (base , lean , agda) =
    helperColor ∧ unitMatches base (key demo "h") helper ∧
    unitMatches lean (key demo "h") helper ∧ unitMatches agda (key demo "h") helper ∧
    unitMatches lean (key demo "f") (fSig ∷ fFun ∷ []) ∧
    unitMatches lean (key demo "g") [ gSig ] ∧
    unitMatches agda (key demo "f") [ fSig ] ∧ unitMatches agda (key demo "g") (gSig ∷ gFun ∷ [])

  upA = key "M0" "A"
  upstreamProof = key "M0" "surrogateBound"
  natProps = mkQ ("Data" ∷ "Nat" ∷ "Properties" ∷ [])
  natModule = mkQ ("Data" ∷ "Nat" ∷ [])
  boolModule = mkQ ("Data" ∷ "Bool" ∷ [])
  natPath = "Agda" ∷ "Builtin" ∷ "Nat" ∷ []
  nat = def (qn (natPath ++ [ "Nat" ]) "ℕ")
  ltBool = def (qn (natPath ++ [ "_<_" ]) "_<ᵇ_")
  lt = def (mkQ ("Data" ∷ "Nat" ∷ "Base" ∷ "_<_" ∷ []))
  truth = def (mkQ ("Data" ∷ "Bool" ∷ "Base" ∷ "T" ∷ []))
  lowerBound : Expr → Expr
  lowerBound op = app (app op (vis (lit (natL 56319)))) (vis (var "n"))
  proofSig = sig plain "surrogateBound"
    (pi (bind visible [ "n" ] nat) (fun′ (vis (app truth (vis (lowerBound ltBool)))) (lowerBound lt)))
  proofBody = fun plain "surrogateBound" [ clause (head upstreamProof [ vis (varP "n") ])
    (rhs (lowerBound (def (mkQ (full natProps ++ [ "<ᵇ⇒<" ]))))) [] ]
  usingOnly : List Name → Directive
  usingOnly ns = directive (just ns) [] [] false
  upstream = code (mkQ [ "M0" ]) []
    (import′ natModule true (usingOnly ("ℕ" ∷ "_<_" ∷ "_<ᵇ_" ∷ [])) [] ∷
     import′ natProps true (usingOnly [ "<ᵇ⇒<" ]) [] ∷
     import′ boolModule true (usingOnly [ "T" ]) [] ∷ (dataA "M0" ++ (proofSig ∷ proofBody ∷ [])))
  downstream = code (mkQ [ "M1" ]) []
    (import′ (mkQ [ "M0" ]) false everything (dataA "M0") ∷
     recSig plain "Stream" [] (set 0) ∷ recDef plain "Stream" [] (recDir true nothing) [ "out" , def upA ] ∷ [])

  absent : Code → QName → Bool
  absent c q with lookupUnit (units c) q
  ... | nothing = true
  ... | just _ = false

  crossModBigUpstreamSlowLeaf : Bool
  crossModBigUpstreamSlowLeaf with IR.projectCodeUpstreamShell upstream (refsDecls (decls downstream))
                                 | IR.projectCodeUpstreamShell upstream [ upstreamProof ]
  ... | just fromLeaf | just fromProof =
    unitMatches fromLeaf upA (dataA "M0") ∧ absent fromLeaf upstreamProof ∧
    unitMatches fromProof upstreamProof [ proofSig ] ∧ absent fromProof upA ∧ eqDecls (decls fromLeaf) (dataA "M0")
  ... | _ | _ = false

  -- No type in Up refers to h. Its body is first needed in a downstream field type.
  downstreamOnlyHelper : Bool
  downstreamOnlyHelper with IR.projectCodeUpstreamFor up indexed
    where
    h = sig plain "h" (set 0) ∷ constant "Up" "h" (def (key "Up" "A")) ∷ []
    up = code (mkQ [ "Up" ]) [] (dataA "Up" ++ h)
    indexed = code (mkQ [ "Leaf" ]) []
      (import′ (mkQ [ "Up" ]) false everything [] ∷ recSig plain "R" [] (set 0) ∷
       recDef plain "R" [] (recDir true nothing) [ "out" , def (key "Up" "h") ] ∷ [])
  ... | nothing = false
  ... | just projected = unitMatches projected (key "Up" "h")
    (sig plain "h" (set 0) ∷ constant "Up" "h" (def (key "Up" "A")) ∷ []) ∧
    unitMatches projected (key "Up" "A") (dataA "Up")

  rejectDangling : Bool
  rejectDangling with IR.lowerCode (code (mkQ [ demo ]) [] (fSig ∷ fFun ∷ []))
  ... | nothing = true
  ... | just _ = false

  rejectUnimported : Bool
  rejectUnimported with IR.lowerCode (code (mkQ [ demo ]) [] [ sig plain "x" (def (key "Other" "A")) ])
  ... | nothing = true
  ... | just _ = false

  module Symbols = C.Over Stringₚ._≟_

  incompatibleSpan : Bool
  incompatibleSpan with Symbols.checkPoint [] | Symbols.checkPoint [ C.decl "x" C.sweetBodyDecl [] [] ]
                                             | Symbols.checkPoint [ C.decl "x" C.exoBodyDecl [] [] ]
  ... | just base | just l | just r with Symbols.checkedPushoutGlue base l r
  ...   | nothing = true
  ...   | just _ = false
  incompatibleSpan | _ | _ | _ = false

  open C.Guard Stringₚ._≟_
  hybridDirtyAxiomNeg =
    let allowed = [ "∂g" ] in
    guardAxiomsAssuming allowed [ C.approvedBoundary "∂g" ] ∧
    not (guardAxiomsAssuming allowed [ C.approvedBoundary "stranger" ]) ∧
    not (guardAxiomsAssuming allowed [ C.forbiddenKernelAxiom C.choiceAx ]) ∧
    not (guardAxiomsAssuming allowed [ C.forbiddenKernelAxiom C.trustMeAx ])

  portColors : Bool
  portColors with IR.annotateExprPorts mixed (rec′ [ "field" , lit (natL 3) ])
                | IR.annotateExprPorts mixed (app (ref "f") (arg inst nothing (lit (natL 3))))
                | IR.annotateExprPorts mixed (fun′ (vis (ref "A")) (set 0))
  ... | (_ , C.Thunked) ∷ [] | (_ , C.Ghost) ∷ [] | (_ , C.Ghost) ∷ (_ , C.Ghost) ∷ [] = true
  ... | _ | _ | _ = false

  linear50 : C.evalThunkedCost (C.spineChain 50) ≤ 101
  linear50 = C.thunked-spine-linear 50

  chooseRight : C.evalThunkedVal (C.branch false (C.leaf 7) (C.leaf 23)) ≡ 23
  chooseRight = refl

  assert : String → Bool → IO (⊤ {0ℓ})
  assert name true  = putStrLn name
  assert name false = die name

main : Main
main = run
  (assert "SharedPureHelperSig" sharedPureHelperSig >>
   assert "CrossModBigUpstreamSlowLeaf" crossModBigUpstreamSlowLeaf >>
   assert "Downstream signature helper" downstreamOnlyHelper >>
   assert "DanglingLocal" rejectDangling >>
   assert "UnimportedName" rejectUnimported >>
   assert "Conflicting concrete declarations" incompatibleSpan >>
   assert "HybridDirtyAxiomNeg" hybridDirtyAxiomNeg >>
   assert "Evaluation colors" portColors >>
   assert "spineChain 50" (C.evalThunkedCost (C.spineChain 50) ≡ᵇ 101))
