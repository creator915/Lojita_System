module Code.Lift where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Code
open import Code.Transport using (withTests; nullᵇ)

record EndpointLift : Set where
  constructor endpointLiftRefs
  field
    baseUnit upperUnit squareUnit : QName
    requiredRefs : List QName
open EndpointLift public

endpointLift : QName → QName → QName → EndpointLift
endpointLift b u s = endpointLiftRefs b u s []

mutual
  data LiftSpec : Set where
    liftSpecTree : QName → QName → List ChildLift → List EndpointLift → LiftSpec

  data ChildLift : Set where
    mkChildLift : QName → QName → Maybe LiftSpec → ChildLift

baseMod : LiftSpec → QName
baseMod (liftSpecTree b _ _ _) = b

upperMod : LiftSpec → QName
upperMod (liftSpecTree _ u _ _) = u

childLifts : LiftSpec → List ChildLift
childLifts (liftSpecTree _ _ cs _) = cs

endpoints : LiftSpec → List EndpointLift
endpoints (liftSpecTree _ _ _ es) = es

baseChild : ChildLift → QName
baseChild (mkChildLift b _ _) = b

upperChild : ChildLift → QName
upperChild (mkChildLift _ u _) = u

subLift : ChildLift → Maybe LiftSpec
subLift (mkChildLift _ _ l) = l

-- Preserve the flat API while exposing recursive specifications separately.
childMap : LiftSpec → List (QName × QName)
childMap l = map (λ c → baseChild c , upperChild c) (childLifts l)

liftSpec : QName → QName → List (QName × QName) → List EndpointLift → LiftSpec
liftSpec b u cs es = liftSpecTree b u (map (λ c → mkChildLift (proj₁ c) (proj₂ c) nothing) cs) es

data LiftProblem : Set where
  wrongBase wrongUpper : LiftProblem
  missingChildMap missingChildImport missingBaseUnit missingUpperUnit missingSquare invalidSquare : QName → LiftProblem

checkLift : Code → Code → List Decl → LiftSpec → List LiftProblem
checkLift base upper upperSpec l with units (withTests upper upperSpec)
... | checkedUnits =
  (if modName base ==ᴺ baseMod l then [] else wrongBase ∷ [])
  ++ (if modName upper ==ᴺ upperMod l then [] else wrongUpper ∷ [])
  ++ concatMap checkChild required
  ++ concatMap checkEndpoint (endpoints l)
  where
    required = nubᵇ _==ᴺ_ (map imod (filterᵇ (λ i → not (nullᵇ (assumes i))) (imports base)) ++ map proj₁ (childMap l))
    checkChild : QName → List LiftProblem
    checkChild q with filterᵇ (λ e → proj₁ e ==ᴺ q) (childMap l)
    ... | [] = missingChildMap q ∷ []
    ... | (_ , u) ∷ _ = if anyᵇ (λ i → imod i ==ᴺ u) (imports upper) then [] else missingChildImport u ∷ []
    present : QName → List Unit → Bool
    present q us = anyᵇ (λ u → uname u ==ᴺ q) us
    codomain : Expr → Expr
    codomain (pi _ t) = codomain t
    codomain (fun′ _ t) = codomain t
    codomain t = t
    trivial : Expr → Bool
    trivial (set _) = true
    trivial (def q) = (q ==ᴺ mkQ ("⊤" ∷ []))
                    ∨ (q ==ᴺ mkQ ("Agda" ∷ "Builtin" ∷ "Unit" ∷ "⊤" ∷ []))
                    ∨ (q ==ᴺ mkQ ("Data" ∷ "Unit" ∷ "⊤" ∷ []))
    trivial _ = false
    relation : QName → Bool
    relation q = (q ==ᴺ mkQ ("_≡_" ∷ []))
               ∨ (q ==ᴺ mkQ ("Agda" ∷ "Builtin" ∷ "Equality" ∷ "_≡_" ∷ []))
               ∨ (q ==ᴺ mkQ ("Relation" ∷ "Binary" ∷ "PropositionalEquality" ∷ "_≡_" ∷ []))
               ∨ isPrefix ("Context" ∷ "Blueprint" ∷ []) (full q)
    square : EndpointLift → Unit → Bool
    square e u = not (isPostulate (udecls u)) ∧ nullᵇ (closedImplOK (flagsOf upper) (code (modName upper) [] (udecls u)))
               ∧ anyᵇ signature (udecls u)
      where
        signature : Decl → Bool
        signature (sig _ _ t) = elemᵇ _==ᴺ_ (baseUnit e) (refsExpr t)
                             ∧ elemᵇ _==ᴺ_ (upperUnit e) (refsExpr t)
                             ∧ allᵇ (λ r → elemᵇ _==ᴺ_ r (refsExpr t)) (requiredRefs e)
                             ∧ not (trivial (codomain t))
                             ∧ (anyᵇ relation (refsExpr (codomain t)) ∨ not (nullᵇ (requiredRefs e)))
        signature _ = false
    checkSquare : EndpointLift → List LiftProblem
    checkSquare e with lookupUnit checkedUnits (squareUnit e)
    ... | nothing = missingSquare (squareUnit e) ∷ []
    ... | just u = if square e u then [] else invalidSquare (squareUnit e) ∷ []
    checkEndpoint : EndpointLift → List LiftProblem
    checkEndpoint e =
      (if present (baseUnit e) (units base ++ extUnits base) then [] else missingBaseUnit (baseUnit e) ∷ [])
      ++ (if present (upperUnit e) checkedUnits then [] else missingUpperUnit (upperUnit e) ∷ [])
      ++ checkSquare e
