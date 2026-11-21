{-# OPTIONS --guardedness #-}
module Test.BlueprintLift where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context.Blueprint
open import Code
open import Code.Transport using (nullᵇ; specΔ; plan)
open import Code.Lift
open import Code.Encode using (encodeLift)
open import Code.Parse using (parseLift)
open import Code.SExpr using (showSExpr)
open import Code.Protocol using (NodeTask; nodeTask; maybeLift; baseModules)
import Code.Harness as Harness

baseMatch : Bool → Bool → Bool
baseMatch flag tag = if flag then tag else true

internalCounter : ℕ
internalCounter = 17

upperMatch : Bool → (Bool × String) → Bool × String
upperMatch flag (tag , body) = baseMatch flag tag , body

wordPort : PortLift Bool (Bool × String)
wordPort = portLift proj₁

square : Commutes₂ (keepPort Bool) wordPort wordPort (λ _ _ → ⊤) _≡_ baseMatch upperMatch
square flag (tag , body) _ = refl

body-preserved : ∀ flag word → proj₂ (upperMatch flag word) ≡ proj₂ word
body-preserved flag (tag , body) = refl

concrete : upperMatch true (true , "abc") ≡ (true , "abc")
concrete = refl

q : String → QName
q n = mkQ (n ∷ [])

B U : QName
B = q "BaseLift"
U = q "UpperLift"

local : String → String → QName
local m n = mkQ (m ∷ n ∷ [])

constant : String → String → List Decl
constant m n = sig plain n (Code.set 0) ∷ fun plain n (clause (head (local m n) []) (rhs (Code.set 0)) [] ∷ []) ∷ []

baseAST : Code
baseAST = code B [] (import′ (q "LowerChild") false everything (sig plain "x" (Code.set 0) ∷ []) ∷
  Data.List._++_ (constant "BaseLift" "baseMatch") (constant "BaseLift" "internalCounter"))

upperAST : Code
upperAST = code U [] (import′ (q "UpperChild") false everything [] ∷ import′ (q "ExtraChild") false everything [] ∷
  Data.List._++_ (constant "UpperLift" "upperMatch")
    (sig plain "square" (app (app (def (mkQ ("Context" ∷ "Blueprint" ∷ "Commutes₂" ∷ [])))
      (vis (def (local "BaseLift" "baseMatch")))) (vis (def (local "UpperLift" "upperMatch"))))
     ∷ fun plain "square" (clause (head (local "UpperLift" "square") []) (rhs (var "refl")) [] ∷ []) ∷ []))

lifting : LiftSpec
lifting = liftSpec B U ((q "LowerChild" , q "UpperChild") ∷ [])
  (endpointLift (local "BaseLift" "baseMatch") (local "UpperLift" "upperMatch") (local "UpperLift" "square") ∷ [])

partial-lift : checkLift baseAST upperAST [] lifting ≡ []
partial-lift = refl

-- The counter is deliberately absent, and the extra child is deliberately new.
no-counter-required : nullᵇ (checkLift baseAST upperAST [] lifting) ≡ true
no-counter-required = refl

missing-square : nullᵇ (checkLift baseAST (code U [] (import′ (q "UpperChild") false everything [] ∷ constant "UpperLift" "upperMatch")) [] lifting) ≡ false
missing-square = refl

-- A user projection on a four-argument function needs no Blueprint wrapper
-- and none of the names from the former projection whitelist.
boolExpr pairExpr : Expr
boolExpr = def (mkQ ("Agda" ∷ "Builtin" ∷ "Bool" ∷ "Bool" ∷ []))
pairExpr = app (app (def (mkQ ("Data" ∷ "Product" ∷ "_×_" ∷ []))) (vis boolExpr))
  (vis (def (mkQ ("Agda" ∷ "Builtin" ∷ "String" ∷ "String" ∷ []))))

fourType : Expr → Expr
fourType t = pi (bind visible ("a" ∷ "b" ∷ "c" ∷ "d" ∷ []) boolExpr) t

fourApply : QName → Expr
fourApply f = app (app (app (app (def f) (vis (var "a"))) (vis (var "b"))) (vis (var "c"))) (vis (var "d"))

fourPatterns : List (Arg Pat)
fourPatterns = vis (varP "a") ∷ vis (varP "b") ∷ vis (varP "c") ∷ vis (varP "d") ∷ []

fourBase : Code
fourBase = code (q "LowerChild") []
  (sig plain "f" (fourType boolExpr)
   ∷ fun plain "f" (clause (head (local "LowerChild" "f") fourPatterns) (rhs (var "a")) [] ∷ []) ∷ [])

customSquareType : Expr
customSquareType = fourType
  (app (app (def (mkQ ("Agda" ∷ "Builtin" ∷ "Equality" ∷ "_≡_" ∷ [])))
    (vis (app (def (local "UpperChild" "myCustomProj")) (vis (fourApply (local "UpperChild" "f"))))))
    (vis (fourApply (local "LowerChild" "f"))))

fourUpper : Code
fourUpper = code (q "UpperChild") []
  (sig plain "f" (fourType pairExpr)
   ∷ fun plain "f" (clause (head (local "UpperChild" "f") fourPatterns)
       (rhs (app (app (con (mkQ ("Data" ∷ "Product" ∷ "_,_" ∷ [])))
         (vis (fourApply (local "LowerChild" "f")))) (vis (lit (strL "body"))))) [] ∷ [])
   ∷ sig plain "myCustomProj" (fun′ (vis pairExpr) boolExpr)
   ∷ fun plain "myCustomProj" (clause (head (local "UpperChild" "myCustomProj")
       (vis (conP (mkQ ("Data" ∷ "Product" ∷ "_,_" ∷ [])) (vis (varP "tag") ∷ vis wildP ∷ [])) ∷ []))
       (rhs (var "tag")) [] ∷ [])
   ∷ sig plain "square" customSquareType
   ∷ fun plain "square" (clause (head (local "UpperChild" "square") fourPatterns) (rhs (var "refl")) [] ∷ []) ∷ [])

customEndpoint : EndpointLift
customEndpoint = endpointLiftRefs (local "LowerChild" "f") (local "UpperChild" "f") (local "UpperChild" "square")
  (local "UpperChild" "myCustomProj" ∷ [])

grandchildLift : LiftSpec
grandchildLift = liftSpecTree (q "LowerChild") (q "UpperChild") [] (customEndpoint ∷ [])

custom-projection-four-arguments : checkLift fourBase fourUpper [] grandchildLift ≡ []
custom-projection-four-arguments = refl

custom-projection-without-required-refs : checkLift fourBase fourUpper []
  (liftSpec (q "LowerChild") (q "UpperChild") []
    (endpointLift (local "LowerChild" "f") (local "UpperChild" "f") (local "UpperChild" "square") ∷ [])) ≡ []
custom-projection-without-required-refs = refl

-- Root -> Child -> Grandchild: both lower levels have selected endpoints.
recursiveChildLift recursiveLift : LiftSpec
recursiveChildLift = liftSpecTree B U
  (mkChildLift (q "LowerChild") (q "UpperChild") (just grandchildLift) ∷ []) (endpoints lifting)
recursiveLift = liftSpecTree (q "RootBase") (q "RootUpper")
  (mkChildLift B U (just recursiveChildLift) ∷ []) []

recursive-lift-roundtrip : parseLift (showSExpr (encodeLift recursiveLift)) ≡ just recursiveLift
recursive-lift-roundtrip = refl

rootBase rootUpper : Code
rootBase = code (q "RootBase") [] (import′ B false everything (sig plain "baseMatch" (Code.set 0) ∷ []) ∷ [])
rootUpper = code (q "RootUpper") [] (import′ U false everything (sig plain "upperMatch" (Code.set 0) ∷ []) ∷ [])

rootTask : LiftSpec → NodeTask
rootTask l = record (nodeTask (specΔ (q "RootUpper") [] []) [] (just (rootBase , l)))
  { baseModules = baseAST ∷ fourBase ∷ [] }

recursiveChildTask recursiveGrandchildTask : NodeTask
recursiveChildTask = Harness.childTask (rootTask recursiveLift) rootUpper (plan "" [] []) "UpperLift"
recursiveGrandchildTask = Harness.childTask recursiveChildTask upperAST (plan "" [] []) "UpperChild"

recursive-child-propagation : maybeLift recursiveChildTask ≡ just (baseAST , recursiveChildLift)
recursive-child-propagation = refl

recursive-grandchild-propagation : maybeLift recursiveGrandchildTask ≡ just (fourBase , grandchildLift)
recursive-grandchild-propagation = refl

recursive-child-valid : Harness.liftProblems recursiveChildTask upperAST ≡ []
recursive-child-valid = refl

recursive-grandchild-valid : Harness.liftProblems recursiveGrandchildTask fourUpper ≡ []
recursive-grandchild-valid = refl

-- Legacy leaf mappings still work, but omitting a non-leaf's subLift fails
-- when that child's own gate discovers the unmapped grandchild.
flatChildTask flatLeafTask : NodeTask
flatChildTask = Harness.childTask (rootTask (liftSpec (q "RootBase") (q "RootUpper") ((B , U) ∷ []) []))
  rootUpper (plan "" [] []) "UpperLift"
flatLeafTask = Harness.childTask
  (Harness.childTask (rootTask (liftSpecTree (q "RootBase") (q "RootUpper") (mkChildLift B U (just lifting) ∷ []) []))
    rootUpper (plan "" [] []) "UpperLift") upperAST (plan "" [] []) "UpperChild"

omitted-subLift-is-empty : maybeLift flatChildTask ≡ just (baseAST , liftSpec B U [] [])
omitted-subLift-is-empty = refl

omitted-subLift-requires-grandchild-map : Harness.liftProblems flatChildTask upperAST ≡ missingChildMap (q "LowerChild") ∷ []
omitted-subLift-requires-grandchild-map = refl

leaf-without-subLift : maybeLift flatLeafTask ≡ just (fourBase , liftSpec (q "LowerChild") (q "UpperChild") [] [])
leaf-without-subLift = refl

leaf-without-subLift-valid : Harness.liftProblems flatLeafTask fourUpper ≡ []
leaf-without-subLift-valid = refl
