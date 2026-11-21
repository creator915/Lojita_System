module Test.PolyTransportTest where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_; map; foldl)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Function using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Context.Blueprint using (PortLift; portLift; project; Commutes₁)
open import Context.PolyTransport
open import Code
open import Code.PolyTransport
open import Code.SExpr using (showSExpr)

Total : {A : Set} → A → Set
Total _ = ⊤

-- An existing request gains a separately wired enable bit and a new callback.
record Request : Set where
  constructor request
  field
    value   : ℕ
    enabled : Bool

OldInput HookedInput : Set
OldInput    = Request × ⊤
HookedInput = (ℕ × Bool) × (ℕ → ℕ)

ports : Request → ℕ × Bool
ports (request n active) = n , active

inputRel : PortRel OldInput HookedInput
inputRel = tensorPort (splitPort ports) (introPort (ℕ → ℕ))

baseline : OldInput → Set
baseline (r , _) = Request.enabled r ≡ false

module Old where
  oldStep : ℕ → ℕ × ℕ
  oldStep n = suc (suc n) , n

  pass1 pass2 : List ℕ → List ℕ
  pass1 = map suc
  pass2 = map (λ n → n + n)

  oldRead : OldInput → ℕ
  oldRead (r , _) = Request.value r

  oldRun : ℕ → ℕ
  oldRun = suc

module New where
  newStage1 : ℕ → ℕ × ℕ
  newStage1 n = suc n , n

  newStage2 : ℕ → ℕ
  newStage2 = suc

  splitSquare : TransportsPoly (idPort ℕ) (idPort (ℕ × ℕ)) Total
                  Old.oldStep (cut₁ newStage1 newStage2)
  splitSquare x .x _ refl = refl

  fusedPass : List ℕ → List ℕ
  fusedPass = map (λ n → suc n + suc n)

  fusionSquare : TransportsPoly (idPort (List ℕ)) (idPort (List ℕ)) Total
                   (Old.pass2 ∘′ Old.pass1) fusedPass
  fusionSquare xs .xs _ refl = fuse xs
    where
      fuse : ∀ ns → Old.pass2 (Old.pass1 ns) ≡ fusedPass ns
      fuse [] = refl
      fuse (n ∷ ns) = cong ((suc n + suc n) ∷_) (fuse ns)

  newDecode : HookedInput → HookedInput
  newDecode ((n , active) , hook) = (suc n , active) , hook

  newRun : HookedInput → ℕ
  newRun ((n , active) , hook) = if active then hook n else n

  rewireSquare : TransportsPoly inputRel (idPort ℕ) baseline
                   (Old.oldRun ∘′ Old.oldRead) (newRun ∘′ newDecode)
  rewireSquare (request n .false , tt) (.(n , false) , hook) refl (refl , _) = refl

split-result : cut₁ New.newStage1 New.newStage2 3 ≡ (5 , 3)
split-result = refl

fused-result : New.fusedPass (0 ∷ 2 ∷ []) ≡ 2 ∷ 6 ∷ []
fused-result = refl

-- The domain matters: enabling this hook changes the observable result.
enabled-hook : (Old.oldRun (Old.oldRead (request 3 true , tt)) ≡ 4) ×
               (New.newRun (New.newDecode ((3 , true) , λ _ → 0)) ≡ 0)
enabled-hook = refl , refl

first-stage : TransportsPoly (idPort ℕ) (tensorPort (graphPort suc) (idPort ℕ)) Total
                New.newStage1 Old.oldStep
first-stage x .x _ refl = refl , refl

second-stage : Transports₁ (graphPort suc) (graphPort suc) Total New.newStage2 Old.oldRun
second-stage x .(suc x) _ refl = refl

cut-square : TransportsPoly (idPort ℕ) (tensorPort (graphPort suc) (idPort ℕ)) Total
               (cut₁ New.newStage1 New.newStage2) (cut₁ Old.oldStep Old.oldRun)
cut-square = composeTransportsCut
  {Rin = idPort ℕ} {Rmid = graphPort suc} {Rc = idPort ℕ} {Rd = graphPort suc}
  {f = New.newStage1} {f′ = Old.oldStep} {g = New.newStage2} {g′ = Old.oldRun}
  first-stage second-stage

cut-preserves-both-ports : cut-square 3 3 tt refl ≡ (refl , refl)
cut-preserves-both-ports = refl

cut-witness : cutRel (λ a b c → (suc a ≡ b) × (a ≡ c)) (λ b d → suc b ≡ d) 3 5 3
cut-witness = 4 , (refl , refl) , refl

split-merge-witness : rel (compPort (splitPort New.newStage1) (mergePort proj₁)) 3 4
split-merge-witness = (4 , 3) , refl , refl

prune-argument : Transports₂ (cographPort suc) (elimPort Bool) (equivPort _≡_) (λ _ _ → ⊤)
                   (λ n _ → n) (λ n _ → suc n)
prune-argument .(suc y) _ y tt _ refl _ = refl

-- These are the original Blueprint types, for arbitrary lifts and domains.
blueprint-cube : {A B U V : Set} (p : PortLift A U) (q : PortLift B V)
  {Dom : U → Set} {b₀ b₀′ : A → B} {u : U → V}
  → TransportsPoly (idPort A) (idPort B) Total b₀ b₀′
  → Commutes₁ p q Dom _≡_ b₀ u → Commutes₁ p q Dom _≡_ b₀′ u
blueprint-cube p q {Dom} {b₀} {b₀′} {u} =
  transportLiftCube (project p) (project q) {Dom} {b₀} {b₀′} {u}

listLift : PortLift (List ℕ) (List ℕ × Bool)
listLift = portLift proj₁

upperPass : List ℕ × Bool → List ℕ × Bool
upperPass (xs , active) = Old.pass2 (Old.pass1 xs) , active

cube-after-fusion : Commutes₁ listLift listLift (λ x → proj₂ x ≡ true) _≡_ New.fusedPass upperPass
cube-after-fusion = blueprint-cube listLift listLift {u = upperPass} New.fusionSquare (λ _ _ → refl)

cube-result : cube-after-fusion (1 ∷ 2 ∷ [] , true) refl ≡ refl
cube-result = refl

-- AST fixtures export aliases of the programs and proofs above. The gate
-- reads the signature at the public name, independently of its proof body.
q : String → QName
q n = mkQ [ n ]

qualify : QName → String → QName
qualify m n = mkQ (full m ++ [ n ])

before after here poly : QName
before = q "Before"
after  = q "After"
here   = mkQ ("Test" ∷ "PolyTransportTest" ∷ [])
poly   = mkQ ("Context" ∷ "PolyTransport" ∷ [])

oldName newName : String → QName
oldName = qualify before
newName = qualify after

call : QName → List Expr → Expr
call f = foldl (λ t a → app t (vis a)) (def f)

arrow : Expr → Expr → Expr
arrow a b = fun′ (vis a) b

nat ns pairNat stepType passType unaryType : Expr
nat = def (mkQ ("Agda" ∷ "Builtin" ∷ "Nat" ∷ "Nat" ∷ []))
ns = call (mkQ ("Agda" ∷ "Builtin" ∷ "List" ∷ "List" ∷ [])) [ nat ]
pairNat = call (mkQ ("Data" ∷ "Product" ∷ "_×_" ∷ [])) (nat ∷ nat ∷ [])
stepType = arrow nat pairNat
passType = arrow ns ns
unaryType = arrow nat nat

definition : QName → String → Expr → Expr → List Decl
definition m n t body = sig plain n t ∷
  fun plain n [ clause (head (qualify m n) []) (rhs body) [] ] ∷ []

oldAlias newAlias : String → Expr → List Decl
oldAlias n t = definition before n t (def (qualify (qualify here "Old") n))
newAlias n t = definition after  n t (def (qualify (qualify here "New") n))

squareType : Expr → Expr → Expr → Expr → Expr → Expr
squareType rin rout dom f g = call (qualify poly "TransportsPoly") (rin ∷ rout ∷ dom ∷ f ∷ g ∷ [])

identity : Expr → Expr
identity a = call (qualify poly "idPort") [ a ]

totalType : Expr
totalType = def (qualify here "Total")

composite : QName → QName → Expr
composite g f = call (mkQ ("Function" ∷ "Base" ∷ "_∘′_" ∷ [])) (def g ∷ def f ∷ [])

splitOld splitNew fusionOld fusionNew rewireOld rewireNew : List Decl
splitOld = oldAlias "oldStep" stepType
splitNew = newAlias "newStage1" stepType ++ newAlias "newStage2" unaryType
fusionOld = oldAlias "pass1" passType ++ oldAlias "pass2" passType
fusionNew = newAlias "fusedPass" passType
rewireOld = oldAlias "oldRead" (arrow (def (qualify here "OldInput")) nat) ++ oldAlias "oldRun" unaryType
rewireNew = newAlias "newDecode" (arrow input input) ++ newAlias "newRun" (arrow input nat)
  where input = def (qualify here "HookedInput")

splitSpec fusionSpec rewireSpec : PolySquareSpec
splitSpec = polySquare [ oldName "oldStep" ] (newName "newStage1" ∷ newName "newStage2" ∷ [])
              (newName "splitSquare")
fusionSpec = polySquare (oldName "pass1" ∷ oldName "pass2" ∷ []) [ newName "fusedPass" ]
               (newName "fusionSquare")
rewireSpec = polySquareRefs (oldName "oldRead" ∷ oldName "oldRun" ∷ [])
               (newName "newDecode" ∷ newName "newRun" ∷ []) (newName "rewireSquare")
               (qualify here "inputRel" ∷ qualify here "baseline" ∷ [])

splitType fusionType rewireType : Expr
splitType = squareType (identity nat) (identity pairNat) totalType (def (oldName "oldStep"))
  (call (qualify poly "cut₁") (def (newName "newStage1") ∷ def (newName "newStage2") ∷ []))
fusionType = squareType (identity ns) (identity ns) totalType
  (composite (oldName "pass2") (oldName "pass1")) (def (newName "fusedPass"))
rewireType = squareType (def (qualify here "inputRel")) (identity nat) (def (qualify here "baseline"))
  (composite (oldName "oldRun") (oldName "oldRead")) (composite (newName "newRun") (newName "newDecode"))

gate : List Decl → List Decl → List Decl → PolySquareSpec → List PolyTransportProblem
gate old new tests s = checkPolyTransport (code before [] old) (code after [] new) tests
                         (transportSpecTree before after [] [ s ])

splitGate : List Decl → List PolyTransportProblem
splitGate proof = gate splitOld (splitNew ++ proof) [] splitSpec

split-valid : splitGate (newAlias "splitSquare" splitType) ≡ []
split-valid = refl

fusion-valid : gate fusionOld (fusionNew ++ newAlias "fusionSquare" fusionType) [] fusionSpec ≡ []
fusion-valid = refl

rewire-valid-in-spec : gate rewireOld rewireNew (newAlias "rewireSquare" rewireType) rewireSpec ≡ []
rewire-valid-in-spec = refl

-- This parent retains one child, installs two and retires two. Its spec
-- supplies the second new import and exposes one endpoint on that import.
stable copied retired₁ retired₂ added₁ added₂ : QName
stable = q "Stable"
copied = q "StableCopy"
retired₁ = q "OldReader"
retired₂ = q "OldCache"
added₁ = q "Parser"
added₂ = q "Renderer"

childImport : QName → List Decl → Decl
childImport m = import′ m false everything

-- Both child interfaces expose the same concrete implementation of run.
runChild : QName → Decl
runChild m = childImport m (definition m "run" unaryType (def (qualify (qualify here "Old") "oldRun")))

oldParent newParent : Code
oldParent = code before [] (runChild stable ∷ runChild retired₁ ∷ runChild retired₂ ∷ childImport (q "ContextLib") [] ∷ [])
newParent = code after [] (runChild copied ∷ childImport added₁ [] ∷ [])

parentMoves : List ChildMove
parentMoves = keepChild stable copied ∷ moveChildren [] (added₁ ∷ added₂ ∷ []) [] ∷
              moveChildren (retired₁ ∷ retired₂ ∷ []) [] [] ∷ []

externalSpec : PolySquareSpec
externalSpec = polySquare [ qualify retired₁ "run" ] [ qualify added₂ "run" ] (newName "externalSquare")

parentTests : List Decl
parentTests = runChild added₂ ∷ definition after "externalSquare" t proof
  where
    t = pi (bind visible [ "x" ] nat) (call (mkQ ("Agda" ∷ "Builtin" ∷ "Equality" ∷ "_≡_" ∷ []))
          (call (qualify retired₁ "run") [ var "x" ] ∷ call (qualify added₂ "run") [ var "x" ] ∷ []))
    proof = lam (vis "x") (con (mkQ ("Agda" ∷ "Builtin" ∷ "Equality" ∷ "refl" ∷ [])))

parentSpec : TransportSpec
parentSpec = transportSpecTree before after parentMoves [ externalSpec ]

children-and-external-endpoints : checkPolyTransport oldParent newParent parentTests parentSpec ≡ []
children-and-external-endpoints = refl

proof-must-be-local : checkPolyTransport oldParent newParent parentTests
  (transportSpecTree before after parentMoves [ record externalSpec { squareUnit = qualify added₂ "run" } ])
  ≡ [ missingPolySquare (qualify added₂ "run") ]
proof-must-be-local = refl

kept-branch : keptPairs parentSpec ≡ [ stable , copied ]
kept-branch = refl

childGate : List ChildMove → List PolyTransportProblem
childGate cs = checkPolyTransport oldParent newParent parentTests (transportSpecTree before after cs [])

omitted-child : childGate (keepChild stable copied ∷ moveChildren [ retired₁ ] [] [] ∷ []) ≡
                  [ unaccountedOldChild retired₂ ]
omitted-child = refl

duplicate-between-branches : childGate (parentMoves ++ [ moveChildren [] [ copied ] [] ]) ≡
                               [ duplicateTargetChild copied ]
duplicate-between-branches = refl

duplicate-inside-move : childGate (keepChild stable copied ∷
  moveChildren (retired₁ ∷ retired₂ ∷ []) (added₂ ∷ added₂ ∷ []) [] ∷ []) ≡ [ duplicateTargetChild added₂ ]
duplicate-inside-move = refl

absent-import : childGate (parentMoves ++ [ moveChildren [] [ q "Lost" ] [] ]) ≡
                  [ missingTargetChildImport (q "Lost") ]
absent-import = refl

wrong-modules : checkPolyTransport (code before [] []) (code after [] []) []
                  (transportSpecTree after before [] []) ≡ wrongOldMod ∷ wrongNewMod ∷ []
wrong-modules = refl

signature-alone : splitGate [ sig plain "splitSquare" splitType ] ≡
                    [ invalidPolySquare (squareUnit splitSpec) ]
signature-alone = refl

absent-proof : splitGate [] ≡ [ missingPolySquare (squareUnit splitSpec) ]
absent-proof = refl

absent-old : gate [] (splitNew ++ newAlias "splitSquare" splitType) [] splitSpec ≡
               [ missingOldEndpoint (oldName "oldStep") ]
absent-old = refl

absent-new : gate splitOld (newAlias "newStage1" stepType ++ newAlias "splitSquare" splitType) [] splitSpec ≡
               [ missingNewEndpoint (newName "newStage2") ]
absent-new = refl

missing-from-signature : splitGate (definition after "splitSquare"
  (squareType (identity nat) (identity pairNat) totalType (def (oldName "oldStep")) (def (newName "newStage1")))
  (def (newName "newStage2"))) ≡ [ invalidPolySquare (squareUnit splitSpec) ]
missing-from-signature = refl

missing-fusion-stage : gate fusionOld (fusionNew ++ newAlias "fusionSquare"
  (squareType (identity ns) (identity ns) totalType (def (oldName "pass1")) (def (newName "fusedPass"))))
  [] fusionSpec ≡ [ invalidPolySquare (squareUnit fusionSpec) ]
missing-fusion-stage = refl

-- All endpoints occur in the premise. Only the final codomain varies.
withPremise : Expr → Expr
withPremise result = pi (bind visible [ "premise" ] splitType) (arrow nat result)

declaredRefs : PolySquareSpec
declaredRefs = record splitSpec { requiredRefs = [ qualify here "Total" ] }

unit-codomain : gate splitOld (splitNew ++ newAlias "splitSquare" (withPremise
  (def (mkQ ("Agda" ∷ "Builtin" ∷ "Unit" ∷ "⊤" ∷ []))))) [] declaredRefs ≡
  [ invalidPolySquare (squareUnit splitSpec) ]
unit-codomain = refl

relation-only-in-premise : splitGate (newAlias "splitSquare" (withPremise nat)) ≡
                             [ invalidPolySquare (squareUnit splitSpec) ]
relation-only-in-premise = refl

sort-with-level : gate splitOld (splitNew ++ newAlias "splitSquare"
  (withPremise (app (Code.set 0) (vis (var "ℓ"))))) [] declaredRefs ≡
  [ invalidPolySquare (squareUnit splitSpec) ]
sort-with-level = refl

absent-required-ref : gate splitOld (splitNew ++ newAlias "splitSquare" splitType) []
  (record splitSpec { requiredRefs = [ q "otherProjection" ] }) ≡ [ invalidPolySquare (squareUnit splitSpec) ]
absent-required-ref = refl

Observed : (ℕ → ℕ × ℕ) → (ℕ → ℕ × ℕ) → (ℕ → ℕ) → Set
Observed step stage finish = ∀ n → step n ≡ cut₁ stage finish n

observed : Observed Old.oldStep New.newStage1 New.newStage2
observed n = refl

custom-relation : gate splitOld (splitNew ++ definition after "splitSquare"
  (call (qualify here "Observed")
    (def (oldName "oldStep") ∷ def (newName "newStage1") ∷ def (newName "newStage2") ∷ []))
  (def (qualify here "observed"))) [] (record splitSpec { requiredRefs = [ qualify here "Observed" ] }) ≡ []
custom-relation = refl

hole-in-proof : splitGate (definition after "splitSquare" splitType hole) ≡
                  [ invalidPolySquare (squareUnit splitSpec) ]
hole-in-proof = refl

flag-envelope : gate splitOld (pragma "OPTIONS --safe" ∷ (splitNew ++ newAlias "splitSquare" splitType)) []
                  splitSpec ≡ [ invalidPolySquare (squareUnit splitSpec) ]
flag-envelope = refl

empty-old : gate splitOld (splitNew ++ newAlias "splitSquare" splitType) []
  (record splitSpec { oldUnits = [] }) ≡ [ emptySquareEndpoints (squareUnit splitSpec) ]
empty-old = refl

empty-new : gate splitOld (splitNew ++ newAlias "splitSquare" splitType) []
  (record splitSpec { newUnits = [] }) ≡ [ emptySquareEndpoints (squareUnit splitSpec) ]
empty-new = refl

-- Two sibling subspecs, another level below the first, and a displayed
-- alias exercise all list boundaries and both QName encodings.
nestedSpec : TransportSpec → TransportSpec
nestedSpec leaf = transportSpecTree (q "Root") (q "Root′")
  [ moveChildren (before ∷ stable ∷ []) (after ∷ copied ∷ [])
    (transportSpecTree before after [ moveChildren [ stable ] [ copied ] [ leaf ] ]
       (splitSpec ∷ fusionSpec ∷ rewireSpec ∷ []) ∷ transportSpecTree stable copied [] [] ∷ []) ] []

aliasedLeaf complex : TransportSpec
aliasedLeaf = transportSpecTree (qn (full stable) "S") copied parentMoves [ externalSpec ]
complex = nestedSpec aliasedLeaf

codec-roundtrip : decodePolyTransport (encodePolyTransport complex) ≡ just complex
codec-roundtrip = refl

text-roundtrip : parsePolyTransport (showSExpr (encodePolyTransport complex)) ≡ just complex
text-roundtrip = refl

nested-keep : keptPairs complex ≡ [ stable , copied ]
nested-keep = refl

segmentSpec : TransportSpec
segmentSpec = transportSpecTree (mkQ []) (qn ("A.B" ∷ "C" ∷ []) "C") [] []

segment-roundtrip : parsePolyTransport (showSExpr (encodePolyTransport segmentSpec)) ≡ just segmentSpec
segment-roundtrip = refl

bad-nested-tag : parsePolyTransport "(poly-transport \"A\" \"B\" ((move () () ((bad)))) ())" ≡ nothing
bad-nested-tag = refl

equality-uses-full-names : eqTransportSpec complex
  (nestedSpec (transportSpecTree stable copied parentMoves [ externalSpec ])) ≡ true
equality-uses-full-names = refl

nested-difference : eqTransportSpec complex
  (nestedSpec (transportSpecTree stable copied parentMoves [])) ≡ false
nested-difference = refl

diagnostic : showPolyTransportProblem (missingOldEndpoint (oldName "oldStep")) ≡
               "(missingOldEndpoint \"Before.oldStep\")"
diagnostic = refl
