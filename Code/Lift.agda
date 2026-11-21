module Code.Lift where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Char using (Char; isSpace; toℕ)
open import Agda.Builtin.Char using (primCharEquality)
open import Data.Nat using (_<ᵇ_)
open import Code
open import Code.Transport using (withTests; nullᵇ)
open import Code.Namespace using (moduleImports; isMetaModule)

record EndpointLift : Set where
  constructor polyEndpointLiftRefs
  field
    baseUnits upperUnits : List QName
    squareUnit : QName
    requiredRefs : List QName
open EndpointLift public

polyEndpointLift : List QName → List QName → QName → EndpointLift
polyEndpointLift bs us s = polyEndpointLiftRefs bs us s []

endpointLiftRefs : QName → QName → QName → List QName → EndpointLift
endpointLiftRefs b u s = polyEndpointLiftRefs [ b ] [ u ] s

endpointLift : QName → QName → QName → EndpointLift
endpointLift b u s = endpointLiftRefs b u s []

mutual
  data LiftSpec : Set where
    liftSpecTree : QName → QName → List ChildLift → List EndpointLift → LiftSpec

  data ChildLift : Set where
    mkChildLift : QName → QName → Maybe LiftSpec → ChildLift
    moveChildLifts : List QName → List QName → List LiftSpec → ChildLift

baseMod : LiftSpec → QName
baseMod (liftSpecTree b _ _ _) = b

upperMod : LiftSpec → QName
upperMod (liftSpecTree _ u _ _) = u

childLifts : LiftSpec → List ChildLift
childLifts (liftSpecTree _ _ cs _) = cs

endpoints : LiftSpec → List EndpointLift
endpoints (liftSpecTree _ _ _ es) = es

baseChildrenOf upperChildrenOf : ChildLift → List QName
baseChildrenOf (mkChildLift b _ _) = [ b ]
baseChildrenOf (moveChildLifts bs _ _) = bs
upperChildrenOf (mkChildLift _ u _) = [ u ]
upperChildrenOf (moveChildLifts _ us _) = us

subLiftsOf : ChildLift → List LiftSpec
subLiftsOf (mkChildLift _ _ nothing) = []
subLiftsOf (mkChildLift _ _ (just s)) = [ s ]
subLiftsOf (moveChildLifts _ _ ss) = ss

-- Legacy scalar projections select the first member, or the empty name.
private
  firstName : List QName → QName
  firstName [] = mkQ []
  firstName (q ∷ _) = q

baseUnit upperUnit : EndpointLift → QName
baseUnit e = firstName (baseUnits e)
upperUnit e = firstName (upperUnits e)

baseChild upperChild : ChildLift → QName
baseChild c = firstName (baseChildrenOf c)
upperChild c = firstName (upperChildrenOf c)

subLift : ChildLift → Maybe LiftSpec
subLift (mkChildLift _ _ s) = s
subLift (moveChildLifts _ _ []) = nothing
subLift (moveChildLifts _ _ (s ∷ _)) = just s

childMap : LiftSpec → List (QName × QName)
childMap l = concatMap pairs (childLifts l)
  where
    pairs : ChildLift → List (QName × QName)
    pairs c = concatMap (λ b → map (b ,_) (upperChildrenOf c)) (baseChildrenOf c)

liftSpec : QName → QName → List (QName × QName) → List EndpointLift → LiftSpec
liftSpec b u cs es = liftSpecTree b u (map (λ c → mkChildLift (proj₁ c) (proj₂ c) nothing) cs) es

-- A child task can carry one base module. With a single source, each
-- target lacking an explicit spec inherits the usual empty leaf spec.
childSpecs : ChildLift → List LiftSpec
childSpecs c with baseChildrenOf c | subLiftsOf c
... | b ∷ [] | ss = ss ++ map (λ u → liftSpec b u [] []) (filterᵇ needsDefault (upperChildrenOf c))
  where
    needsDefault : QName → Bool
    needsDefault u = not (anyᵇ (λ s → upperMod s ==ᴺ u) ss)
... | _ | ss = ss

data LiftProblem : Set where
  wrongBase wrongUpper : LiftProblem
  missingChildMap missingChildImport duplicateUpperChild invalidChildLift : QName → LiftProblem
  emptyLiftEndpoints missingBaseUnit missingUpperUnit missingSquare invalidSquare : QName → LiftProblem

missingLiftNames : (QName → LiftProblem) → List QName → List QName → List LiftProblem
missingLiftNames problem expected available =
  map problem (filterᵇ (λ q → not (elemᵇ _==ᴺ_ q available)) expected)

requiredBaseChildren : Code → List ChildLift → List QName
requiredBaseChildren base cs = nubᵇ _==ᴺ_
  (map imod (filterᵇ (λ i → not (nullᵇ (assumes i))) (imports base)) ++ concatMap baseChildrenOf cs)

childMapProblems : Code → List ChildLift → List LiftProblem
childMapProblems base cs =
     missingLiftNames missingChildMap (requiredBaseChildren base cs) (concatMap baseChildrenOf cs)
  ++ map duplicateUpperChild (nubᵇ _==ᴺ_ (repeated (concatMap upperChildrenOf cs)))
  ++ concatMap invalidSubs cs
  where
    repeated : List QName → List QName
    repeated [] = []
    repeated (q ∷ qs) with elemᵇ _==ᴺ_ q qs
    ... | true = q ∷ repeated qs
    ... | false = repeated qs

    invalidSubs : ChildLift → List LiftProblem
    invalidSubs c = map (λ s → invalidChildLift (upperMod s)) (filterᵇ outside (subLiftsOf c))
      where
        outside : LiftSpec → Bool
        outside s = not (elemᵇ _==ᴺ_ (baseMod s) (baseChildrenOf c) ∧ elemᵇ _==ᴺ_ (upperMod s) (upperChildrenOf c))

baseEndpointProblems : List QName → EndpointLift → List LiftProblem
baseEndpointProblems available e =
     (if nullᵇ (baseUnits e) ∨ nullᵇ (upperUnits e) then [ emptyLiftEndpoints (squareUnit e) ] else [])
  ++ missingLiftNames missingBaseUnit (baseUnits e) available

private
  codomain : Expr → Expr
  codomain (pi _ t) = codomain t
  codomain (fun′ _ t) = codomain t
  codomain (let′ bs t) = let′ bs (codomain t)
  codomain t = t

  unitType : List Name → Bool
  unitType ("⊤" ∷ []) = true
  unitType ("Agda" ∷ "Builtin" ∷ "Unit" ∷ "⊤" ∷ []) = true
  unitType ("Data" ∷ "Unit" ∷ "⊤" ∷ []) = true
  unitType ("Data" ∷ "Unit" ∷ "Base" ∷ "⊤" ∷ []) = true
  unitType ("Data" ∷ "Unit" ∷ "Polymorphic" ∷ "⊤" ∷ []) = true
  unitType ("Data" ∷ "Unit" ∷ "Polymorphic" ∷ "Base" ∷ "⊤" ∷ []) = true
  unitType _ = false

  trivial : Expr → Bool
  trivial (set _) = true
  trivial (def q) = unitType (full q)
  trivial (app f _) = trivial f
  trivial (let′ _ t) = trivial t
  trivial _ = false

  relation : QName → Bool
  relation q = (q ==ᴺ mkQ [ "_≡_" ])
             ∨ (q ==ᴺ mkQ ("Agda" ∷ "Builtin" ∷ "Equality" ∷ "_≡_" ∷ []))
             ∨ (q ==ᴺ mkQ ("Relation" ∷ "Binary" ∷ "PropositionalEquality" ∷ "_≡_" ∷ []))
             ∨ isPrefix ("Context" ∷ "Blueprint" ∷ []) (full q)
             ∨ isPrefix ("Context" ∷ "PolyTransport" ∷ []) (full q)

  signatureOK : EndpointLift → Decl → Bool
  signatureOK e (sig _ _ t) with refsExpr t | codomain t
  ... | refs | result =
    allᵇ (λ q → elemᵇ _==ᴺ_ q refs) (baseUnits e ++ upperUnits e ++ requiredRefs e)
    ∧ not (trivial result)
    ∧ (anyᵇ relation (refsExpr result) ∨ not (nullᵇ (requiredRefs e)))
  signatureOK _ _ = false

checkLift : Code → Code → List Decl → LiftSpec → List LiftProblem
checkLift base upper upperSpec l with withTests upper upperSpec
... | checked with units checked | map uname (units base ++ extUnits base)
... | locals | baseNames with map uname (locals ++ extUnits checked)
... | upperNames =
     (if modName base ==ᴺ baseMod l then [] else [ wrongBase ])
  ++ (if modName upper ==ᴺ upperMod l then [] else [ wrongUpper ])
  ++ childMapProblems base (childLifts l)
  ++ missingLiftNames missingChildImport (nubᵇ _==ᴺ_ (concatMap upperChildrenOf (childLifts l))) (map imod (imports checked))
  ++ concatMap checkEndpoint (endpoints l)
  where
    checkSquare : EndpointLift → List LiftProblem
    checkSquare e with lookupUnit locals (squareUnit e)
    ... | nothing = [ missingSquare (squareUnit e) ]
    ... | just u = if not (isPostulate (udecls u))
                      ∧ nullᵇ (closedImplOK (flagsOf upper) (code (modName upper) [] (udecls u)))
                      ∧ anyᵇ (signatureOK e) (udecls u)
                   then [] else [ invalidSquare (squareUnit e) ]

    checkEndpoint : EndpointLift → List LiftProblem
    checkEndpoint e = baseEndpointProblems baseNames e
                   ++ missingLiftNames missingUpperUnit (upperUnits e) upperNames
                   ++ checkSquare e

-- Resolve the module first. A witness or specification nested below a base
-- has its own declarations, and a witness may import a base below itself.
extractCulpritBaseUnits : List Code → Code → List QName
extractCulpritBaseUnits bases c = nubᵇ _==ᴺ_ (concatMap owner (refsDecls (decls c)))
  where
    baseNames = map modName bases
    localNames = modName c ∷ map uname (units c)
    modules = map (λ m → unitOf m []) (modName c ∷ moduleImports c ++ baseNames)
    candidates = concatMap units bases

    owns : QName → Unit → Bool
    owns q u = unitOwns u q ∨ anyᵇ flatConstructor (udecls u)
      where
        flatConstructor : Decl → Bool
        flatConstructor (dataDef _ _ _ cs) = anyᵇ (λ d → inUnitScope u (proj₁ d) q) cs
        flatConstructor _ = false

    owner : QName → List QName
    owner q with longestUnit (filterᵇ (λ m → isPrefix (full (uname m)) (full q)) modules)
    ... | nothing = []
    ... | just m with elemᵇ _==ᴺ_ (uname m) baseNames ∧ not (elemᵇ _==ᴺ_ (uname m) localNames)
    ...   | false = []
    ...   | true with longestUnit (filterᵇ (λ u → isPrefix (full (uname m)) (full (uname u)) ∧ owns q u) candidates)
    ...     | nothing = [ uname m ]
    ...     | just u = [ uname u ]

private
  -- The native gate uses the same path grammar as Meta.Boundary.objectNamespace false.
  witnessPathOK : QName → Bool
  witnessPathOK q with full q
  ... | [] = false
  ... | root ∷ rest = not (isMetaModule (mkQ [ root ])) ∧ safeQName q ∧ allᵇ partOK (root ∷ rest)
    where
      charOK : Char → Bool
      charOK c = not (isSpace c ∨ (toℕ c <ᵇ 32) ∨ primCharEquality c '.' ∨ primCharEquality c '/' ∨ primCharEquality c '\\')
      partOK : String → Bool
      partOK s = not (s ==ˢ "") ∧ allᵇ charOK (toList s)

validLiftRefutation : QName → List Code → List String → Code → List RefuteProblem
validLiftRefutation spec bases allowed c = witnessNamespaceProblems spec c
  ++ map unauthorizedImport (filterᵇ (λ q → not (witnessPathOK q)) (modName c ∷ imported))
  ++ (if elemᵇ _==ᴺ_ (modName c) baseNames then [ unauthorizedImport (modName c) ] else [])
  ++ checkWitnessIn (λ n e → not (n ==ˢ "_") ∧ bottomExpr e) missingBottomProof
       (modName c ∷ spec ∷ baseNames) imported allowed c
  ++ (if nullᵇ (extractCulpritBaseUnits bases c) then [ missingBaseReference ] else [])
  where
    baseNames = map modName bases
    imported = moduleImports c
