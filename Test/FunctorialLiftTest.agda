{-# OPTIONS --guardedness #-}
module Test.FunctorialLiftTest where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; [_]; _++_; foldl; take; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList; fromList)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Context.PolyTransport using (PortRel; idPort; Transports₁; cut₁)
open import Code
open import Code.Lift
open import Code.Encode using (encodeLift; encodeCode)
open import Code.Parse using (parseLift)
open import Code.SExpr using (list; sym; showSExpr)
open import Code.Transport using (plan; specΔ)
open import Code.Protocol using (NodeTask; nodeTask; baseModules; maybeLift; allowedAncestors)
open import Code.HarnessCore using (childTask)
open import Code.SessionRunner using (precheckLift; precheckLiftTree)
open import Code.PlanPreview using (planContext; planPreview)
import Code.NodeTransport as NT
import Code.PolyTransport as PT

module Programs where
  convert₀ parse₁ : ℕ → ℕ × ℕ
  convert₀ n = suc (suc n) , n
  parse₁ n = suc n , n

  render₁ pass1₀ pass2₀ fused₁ : ℕ → ℕ
  render₁ = suc
  pass1₀ = suc
  pass2₀ n = n + n
  fused₁ n = suc n + suc n

  port : PortRel ℕ ℕ
  port = idPort ℕ

  splitSquare : Transports₁ port (idPort (ℕ × ℕ)) (λ _ → ⊤) convert₀ (cut₁ parse₁ render₁)
  splitSquare x .x _ refl = refl

  fusionSquare : Transports₁ port port (λ _ → ⊤) (λ x → pass2₀ (pass1₀ x)) fused₁
  fusionSquare x .x _ refl = refl

-- AST fixtures expose the programs and proofs above under their package names.
at : QName → String → QName
at m n = mkQ (full m ++ [ n ])

B U programs poly : QName
B = NT.moduleQName "Gen.T0.Root"
U = NT.moduleQName "Gen.T1.Root"
programs = NT.moduleQName "Test.FunctorialLiftTest.Programs"
poly = NT.moduleQName "Context.PolyTransport"

call : QName → List Expr → Expr
call q = foldl (λ f x → app f (vis x)) (def q)

alias : QName → String → Expr → List Decl
alias m n t = sig plain n t ∷ fun plain n [ clause (head (at m n) []) (rhs (def (at programs n))) [] ] ∷ []

nat pairNat unary stepType : Expr
nat = def (NT.moduleQName "Agda.Builtin.Nat.Nat")
pairNat = call (NT.moduleQName "Data.Product._×_") (nat ∷ nat ∷ [])
unary = fun′ (vis nat) nat
stepType = fun′ (vis nat) pairNat

transportType : Expr → Expr → Expr → Expr
transportType outPort f g = call (at poly "Transports₁")
  (def (at programs "port") ∷ outPort ∷ lam (vis "_") (def (NT.moduleQName "Data.Unit.⊤")) ∷ f ∷ g ∷ [])

convert parseStep renderStep splitProof : QName
convert = at B "convert₀"
parseStep = at U "parse₁"
renderStep = at U "render₁"
splitProof = at U "splitSquare"

splitType : Expr
splitType = transportType (call (at poly "idPort") [ pairNat ]) (def convert)
  (call (at poly "cut₁") (def parseStep ∷ def renderStep ∷ []))

splitEp : EndpointLift
splitEp = polyEndpointLift [ convert ] (parseStep ∷ renderStep ∷ []) splitProof

splitBase splitUpper : Code
splitBase = code B [] (alias B "convert₀" stepType)
splitUpper = code U [] (alias U "parse₁" stepType ++ alias U "render₁" unary)

splitGate : Code → Expr → EndpointLift → List LiftProblem
splitGate c t e = checkLift splitBase (record c { decls = decls c ++ alias U "splitSquare" t }) []
  (liftSpec B U [] [ e ])

unit-split : splitGate splitUpper splitType splitEp ≡ []
unit-split = refl

missing-second-stage : splitGate (code U [] (alias U "parse₁" stepType)) splitType splitEp ≡ [ missingUpperUnit renderStep ]
missing-second-stage = refl

every-stage-in-signature : splitGate splitUpper (transportType (def (at programs "port")) (def convert) (def parseStep))
  splitEp ≡ [ invalidSquare splitProof ]
every-stage-in-signature = refl

-- Put all endpoint and relation references in the domain and require the
-- relation explicitly. Only the nontrivial-codomain check can reject these.
trivialGate : Expr → List LiftProblem
trivialGate result = splitGate splitUpper (let′ [] (fun′ (vis splitType) result))
  (record splitEp { requiredRefs = [ at poly "Transports₁" ] })

unit-result : trivialGate (def (NT.moduleQName "Data.Unit.Base.⊤")) ≡ [ invalidSquare splitProof ]
unit-result = refl

level-polymorphic-unit : trivialGate (app (def (NT.moduleQName "Data.Unit.Polymorphic.⊤")) (vis (var "ℓ")))
  ≡ [ invalidSquare splitProof ]
level-polymorphic-unit = refl

universe-result : trivialGate (set 1) ≡ [ invalidSquare splitProof ]
universe-result = refl

universe-application : trivialGate (app (set 0) (vis (var "ℓ"))) ≡ [ invalidSquare splitProof ]
universe-application = refl

empty-base : splitGate splitUpper splitType (record splitEp { baseUnits = [] }) ≡ [ emptyLiftEndpoints splitProof ]
empty-base = refl

empty-upper : splitGate splitUpper splitType (record splitEp { upperUnits = [] }) ≡ [ emptyLiftEndpoints splitProof ]
empty-upper = refl

childImport : QName → List Decl → Decl
childImport q ds = import′ q false everything ds

parser blockParser inlineParser : QName
parser = at B "Parser₀"
blockParser = at U "BlockParser₁"
inlineParser = at U "InlineParser₁"

parserIface : List Decl
parserIface = [ sig plain "parse₁" stepType ]

parserBase blockOnly : Code
parserBase = code B [] [ childImport parser parserIface ]
blockOnly = code U [] [ childImport blockParser [] ]

parserTargets : List QName
parserTargets = blockParser ∷ inlineParser ∷ []

parserSplit : LiftSpec
parserSplit = liftSpecTree B U (mkChildLift parser blockParser nothing ∷ mkChildLift parser inlineParser nothing ∷ []) []

both-targets-imported : checkLift parserBase blockOnly [ childImport inlineParser [] ] parserSplit ≡ []
both-targets-imported = refl

missing-second-child : checkLift parserBase blockOnly [] parserSplit ≡ [ missingChildImport inlineParser ]
missing-second-child = refl

duplicate-target : checkLift parserBase blockOnly []
  (liftSpecTree B U (mkChildLift parser blockParser nothing ∷ [ moveChildLifts [ parser ] [ blockParser ] [] ]) [])
  ≡ [ duplicateUpperChild blockParser ]
duplicate-target = refl

wrong-nested-target : checkLift parserBase blockOnly []
  (liftSpecTree B U [ mkChildLift parser blockParser (just (liftSpec parser inlineParser [] [])) ] [])
  ≡ [ invalidChildLift inlineParser ]
wrong-nested-target = refl

-- A parent's square relates both imported base functions to one exported
-- upper function. The proof remains local to the parent.
passA passB fusedPkg pass1 pass2 fused fusionProof : QName
passA = at B "Pass1"
passB = at B "Pass2"
fusedPkg = at U "Fused"
pass1 = at passA "pass1₀"
pass2 = at passB "pass2₀"
fused = at fusedPkg "fused₁"
fusionProof = at U "fusionSquare"

sources : List QName
sources = passA ∷ passB ∷ []

fusionSquareDecls : List Decl
fusionSquareDecls = alias U "fusionSquare" (transportType (def (at programs "port"))
  (lam (vis "x") (call pass2 [ call pass1 [ var "x" ] ])) (def fused))

fusedImport : Decl
fusedImport = childImport fusedPkg [ sig plain "fused₁" unary ]

passACode passBCode fusedCode fusionBase fusionUpper : Code
passACode = code passA [] (alias passA "pass1₀" unary)
passBCode = code passB [] (alias passB "pass2₀" unary)
fusedCode = code fusedPkg [] (alias fusedPkg "fused₁" unary)
fusionBase = code B [] (childImport passA [ sig plain "pass1₀" unary ] ∷ childImport passB [ sig plain "pass2₀" unary ] ∷ [])
fusionUpper = code U [] (fusedImport ∷ fusionSquareDecls)

fusion : List LiftSpec → LiftSpec
fusion subs = liftSpecTree B U [ moveChildLifts sources [ fusedPkg ] subs ]
  [ polyEndpointLift (pass1 ∷ pass2 ∷ []) [ fused ] fusionProof ]

unit-and-package-fusion : checkLift fusionBase fusionUpper [] (fusion []) ≡ []
unit-and-package-fusion = refl

spec-import-exports-endpoint : checkLift fusionBase (code U [] fusionSquareDecls) [ fusedImport ] (fusion []) ≡ []
spec-import-exports-endpoint = refl

wrong-root-modules : checkLift fusionBase fusionUpper [] (liftSpec U B [] []) ≡
  wrongBase ∷ wrongUpper ∷ missingChildMap passA ∷ missingChildMap passB ∷ []
wrong-root-modules = refl

wrong-nested-base : checkLift fusionBase fusionUpper [] (fusion [ liftSpec parser fusedPkg [] [] ]) ≡ [ invalidChildLift fusedPkg ]
wrong-nested-base = refl

subB : LiftSpec
subB = liftSpec passB fusedPkg [] [ endpointLift pass2 fused (at fusedPkg "childSquare") ]

fusion-roundtrip : parseLift (showSExpr (encodeLift (fusion [ subB ]))) ≡ just (fusion [ subB ])
fusion-roundtrip = refl

wireSpec : LiftSpec
wireSpec = liftSpecTree (q "B") (q "U")
  [ moveChildLifts (q "a" ∷ [ q "b" ]) [ q "c" ] [ liftSpec (q "b") (q "c") [] [] ] ]
  [ polyEndpointLiftRefs (q "x" ∷ [ q "y" ]) [ q "z" ] (q "s") [ q "r" ] ]
  where q = NT.moduleQName

move-and-endpoint-wire : showSExpr (encodeLift wireSpec) ≡
  "(lift \"B\" \"U\" ((move (\"a\" \"b\") (\"c\") ((lift \"b\" \"c\" () ())))) (((\"x\" \"y\") (\"z\") \"s\" (\"r\"))))"
move-and-endpoint-wire = refl

legacyWire : String
legacyWire = "(lift \"B\" \"U\" ((\"B.C\" \"U.C\")) ((\"x\" \"y\" \"s\") ((q \"B.z\" \"Z\") \"y\" \"s\" (\"r\"))))"

legacySpec : LiftSpec
legacySpec = liftSpec (mkQ [ "B" ]) (mkQ [ "U" ]) [ NT.moduleQName "B.C" , NT.moduleQName "U.C" ]
  (endpointLift (mkQ [ "x" ]) y s ∷ endpointLiftRefs (qn ("B" ∷ "z" ∷ []) "Z") y s [ mkQ [ "r" ] ] ∷ [])
  where
    y = mkQ [ "y" ]
    s = mkQ [ "s" ]

legacy-sub-projection : ∀ b u (s : Maybe LiftSpec) → subLift (mkChildLift b u s) ≡ s
legacy-sub-projection _ _ _ = refl

legacy-bytes : showSExpr (encodeLift legacySpec) ≡ legacyWire
legacy-bytes = refl

legacy-scoped-qname : parseLift legacyWire ≡ just legacySpec
legacy-scoped-qname = refl

mixed-endpoint-syntax : parseLift "(lift \"B\" \"U\" () ((\"x\" (\"y\" \"z\") \"s\") ((\"p\" \"q\") \"r\" \"t\")))"
  ≡ just (liftSpec (mkQ [ "B" ]) (mkQ [ "U" ]) []
    (polyEndpointLift [ mkQ [ "x" ] ] (mkQ [ "y" ] ∷ mkQ [ "z" ] ∷ []) (mkQ [ "s" ]) ∷
     polyEndpointLift (mkQ [ "p" ] ∷ mkQ [ "q" ] ∷ []) [ mkQ [ "r" ] ] (mkQ [ "t" ]) ∷ []))
mixed-endpoint-syntax = refl

bases : List Code
bases = passACode ∷ passBCode ∷ []

fusion-precheck : precheckLift 4 bases fusionBase U (fusion [ subB ]) ≡ []
fusion-precheck = refl

second-base-module-required : precheckLift 4 [ passACode ] fusionBase U (fusion []) ≡ [ missingBaseUnit passB ]
second-base-module-required = refl

second-base-endpoint-required : precheckLift 4 bases (code B [] [ childImport passA [ sig plain "pass1₀" unary ] ]) U
  (fusion []) ≡ [ missingBaseUnit pass2 ]
second-base-endpoint-required = refl

missingName : QName
missingName = at parser "missing"

badParserSub : LiftSpec
badParserSub = liftSpec parser inlineParser [] [ endpointLift missingName (at inlineParser "f") (at inlineParser "sq") ]

precheck-split : List ChildLift → List LiftProblem
precheck-split cs = precheckLift 3 [ code parser [] [] ] parserBase U (liftSpecTree B U cs [])

second-legacy-branch : precheck-split
  (mkChildLift parser blockParser nothing ∷ mkChildLift parser inlineParser (just badParserSub) ∷ []) ≡ [ missingBaseUnit missingName ]
second-legacy-branch = refl

second-move-subspec : precheck-split [ moveChildLifts [ parser ] parserTargets (liftSpec parser blockParser [] [] ∷ [ badParserSub ]) ]
  ≡ [ missingBaseUnit missingName ]
second-move-subspec = refl

blockSub : LiftSpec
blockSub = liftSpec parser blockParser [ passA , at blockParser "Child" ] []

default-prechecked : precheckLift 4 (code parser [] [ childImport passA parserIface ] ∷ bases) parserBase U
  (liftSpecTree B U [ moveChildLifts [ parser ] parserTargets [ blockSub ] ] []) ≡ [ missingChildMap passA ]
default-prechecked = refl

-- Reuse a sealed source through three explicit levels. The number of base
-- modules is smaller than the depth at which the missing endpoint occurs.
reusedBase : LiftSpec
reusedBase = liftSpecTree parser blockParser [ mkChildLift parser U (just middle) ] []
  where
    middle = liftSpecTree parser U [ moveChildLifts [ parser ] [ inlineParser ] [ badParserSub ] ] []

deep-precheck : precheckLiftTree [ code parser [] [] ] (code parser [] []) blockParser reusedBase ≡ [ missingBaseUnit missingName ]
deep-precheck = refl

taskFor : Code → List Code → LiftSpec → NodeTask
taskFor base bs l = record (nodeTask (specΔ U [] []) [] (just (base , l)))
  { baseModules = bs ; allowedAncestors = just [] }

fusedTask : List LiftSpec → NodeTask
fusedTask ss = childTask (taskFor fusionBase bases (fusion ss)) fusionUpper (plan "" [] []) (NT.moduleKey fusedPkg)

both-ancestors : allowedAncestors (fusedTask []) ≡ just sources
both-ancestors = refl

fusion-without-child-spec : maybeLift (fusedTask []) ≡ nothing
fusion-without-child-spec = refl

selected-child-base : maybeLift (fusedTask [ subB ]) ≡ just (passBCode , subB)
selected-child-base = refl

parserCode : Code
parserCode = code parser [] []

default-for-other-target : maybeLift (childTask (taskFor parserBase [ parserCode ]
  (liftSpecTree B U [ moveChildLifts [ parser ] parserTargets [ badParserSub ] ] [])) blockOnly (plan "" [] []) (NT.moduleKey blockParser))
  ≡ just (parserCode , liftSpec parser blockParser [] [])
default-for-other-target = refl

-- A kept root has no child planning turns. Its fused child still owes the
-- explicitly selected square from Pass2.
keptRoot : NT.Frozen
keptRoot = NT.frozen fusionUpper [] [] [ NT.moduleKey fusedPkg , NT.frozen fusedCode [] [] [] ]

keptLifting : LiftSpec
keptLifting = liftSpecTree B U [ moveChildLifts (passA ∷ [ B ]) (blockParser ∷ [ U ]) (unkept ∷ [ retained ]) ] []
  where
    unkept = liftSpec passA blockParser [] []
    retained = fusion (liftSpec passA fusedPkg [] [] ∷ [ subB ])

kept-nested-fusion : NT.checkKeptLifts (fusionBase ∷ bases)
  [ NT.frozen (code B [] []) [] [] [ NT.moduleKey U , keptRoot ] , PT.transportSpecTree B U [ PT.keepChild U U ] [] ]
  keptLifting ≡ [ missingSquare (at fusedPkg "childSquare") ]
kept-nested-fusion = refl

-- The Agda preview and the native check-plan CLI consume the same fixtures.
fusionContext : String
fusionContext = planContext t fusionUpper []
  where
    t = record (nodeTask (specΔ U [] []) [] nothing) { baseModules = [ fusionBase ] }

previewRequest : LiftSpec → String
previewRequest l = showSExpr (list (sym "check-plan" ∷ list [ sym "moves" ] ∷ encodeCode (code U [] []) ∷
  list [ sym "subspecs" ] ∷ list (sym "lift" ∷ encodeLift l ∷ []) ∷ []))

unimportedTarget : LiftSpec
unimportedTarget = liftSpecTree B U [ moveChildLifts sources (fusedPkg ∷ mkQ [ "Missing" ] ∷ []) [] ] []

startsWith : String → String → Bool
startsWith prefix s = prefix ==ˢ fromList (take (length (toList prefix)) (toList s))

preview-accepts-fusion : startsWith "{\"ok\":true,\"diagnostics\":[]," (planPreview fusionContext (previewRequest (fusion [ subB ]))) ≡ true
preview-accepts-fusion = refl

preview-reports-missing-target : startsWith "{\"ok\":false,\"diagnostics\":[\"(missingChildImport \\\"Missing\\\")\"]"
  (planPreview fusionContext (previewRequest unimportedTarget)) ≡ true
preview-reports-missing-target = refl
