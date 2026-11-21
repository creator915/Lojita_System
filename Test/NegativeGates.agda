module Test.NegativeGates where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Code
open import Code.Transport
open import Code.Lift
open import Test.TransportTest using (C₀; C₂; P₂; C·)

bad : Code
bad = code (mkQ ("Bad" ∷ [])) [] (sig plain "lie" (def (mkQ ("Data" ∷ "Empty" ∷ "⊥" ∷ []))) ∷ [])

N1-stub : closedImplOK [] bad ≡ unimplementedPostulate (mkQ ("Bad" ∷ "lie" ∷ [])) ∷ []
N1-stub = refl

holeCode : Code
holeCode = code (mkQ ("Bad" ∷ [])) []
  (sig plain "x" (set 0) ∷ fun plain "x" (clause (head (mkQ ("Bad" ∷ "x" ∷ [])) []) (rhs hole) [] ∷ []) ∷ [])

N1-hole : nullᵇ (closedImplOK [] holeCode) ≡ false
N1-hole = refl

N2-frontier : frontier C₀ C₂ P₂ ≡ unit (C· "two") ∷ []
N2-frontier = refl

seed : SpecΔ
seed = specΔ (mkQ ("C" ∷ [])) [] (keep (ext (C· "one")) ∷ [])

N2-seed : extendsSeed seed (plan "" [] []) ≡ false
N2-seed = refl

base : Code
base = code (mkQ ("Base" ∷ [])) [] (import′ (mkQ ("Kid" ∷ [])) false everything (sig plain "x" (set 0) ∷ []) ∷ [])

N4-child : checkLift base (code (mkQ ("Upper" ∷ [])) [] []) []
  (liftSpec (mkQ ("Base" ∷ [])) (mkQ ("Upper" ∷ [])) [] []) ≡ missingChildMap (mkQ ("Kid" ∷ [])) ∷ []
N4-child = refl

N7-forgery : nullᵇ (validRefutation (mkQ ("Spec" ∷ [])) [] bad) ≡ false
N7-forgery = refl

-- N3/N5/N6 require the real compiler. SessionIO dumps these source fixtures
-- and verifies a nonzero type-check result; these are not mocked verdicts.
N3-source : String
N3-source = "module GateGlue where\nopen import Agda.Builtin.Equality\nopen import Agda.Builtin.Nat\nimport ChildGate\nproof : ChildGate.x ≡ zero\nproof = ChildGate.missingLemma\n"

N3-child : String
N3-child = "module ChildGate where\nopen import Agda.Builtin.Nat\npostulate x : Nat\n"

N5-source : String
N5-source = "module GateLabel where\nopen import Agda.Builtin.Bool\nopen import Agda.Builtin.Equality\nopen import Data.Unit using (⊤)\nopen import Context.Blueprint\nf : Bool → Bool\nf x = false\nsquare : Commutes₁ (keepPort Bool) (keepPort Bool) (λ _ → ⊤) _≡_ (λ b → b) f\nsquare b _ = refl\n"

N6-source : String
N6-source = "module GateBody where\nopen import Agda.Builtin.String\nopen import Agda.Builtin.Bool\nopen import Agda.Builtin.Equality\nopen import Data.Unit using (⊤)\nopen import Data.Product using (_×_; _,_; proj₁; proj₂)\nopen import Context.Blueprint\nf : Bool × String → Bool × String\nf (tag , body) = tag , \"\"\nword : PortLift Bool (Bool × String)\nword = portLift proj₁\nsquare : Commutes₁ word word (λ _ → ⊤) _≡_ (λ b → b) f\nsquare (tag , body) _ = refl\nscatter : proj₂ (f (true , \"hello\")) ≡ \"hello\"\nscatter = refl\n"


-- Nested parameterized modules cannot masquerade as a closed exported bottom.
parameterizedForgery : Code
parameterizedForgery = code (mkQ ("Nested" ∷ [])) []
  (module′ "M" (bind visible ("assumption" ∷ []) (def (mkQ ("Data" ∷ "Empty" ∷ "⊥" ∷ []))) ∷ [])
    (sig plain "absurd" (def (mkQ ("Data" ∷ "Empty" ∷ "⊥" ∷ [])))
     ∷ fun plain "absurd" (clause (head (mkQ ("Nested" ∷ "M" ∷ "absurd" ∷ [])) []) (rhs (var "assumption")) [] ∷ []) ∷ []) ∷ [])

N7-parameterized : nullᵇ (validRefutation (mkQ ("Spec" ∷ [])) [] parameterizedForgery) ≡ false
N7-parameterized = refl

N1-unsafe-primitive : nullᵇ (closedImplOK [] (code (mkQ ("Unsafe" ∷ [])) []
  (import′ (mkQ ("Agda" ∷ "Builtin" ∷ "TrustMe" ∷ [])) true everything [] ∷ []))) ≡ false
N1-unsafe-primitive = refl

N4-import : checkLift base (code (mkQ ("Upper" ∷ [])) [] []) []
  (liftSpec (mkQ ("Base" ∷ [])) (mkQ ("Upper" ∷ [])) ((mkQ ("Kid" ∷ []) , mkQ ("UpperKid" ∷ [])) ∷ []) [])
  ≡ missingChildImport (mkQ ("UpperKid" ∷ [])) ∷ []
N4-import = refl

squareName : String → String → QName
squareName m n = mkQ (m ∷ n ∷ [])

equality : Expr → Expr → Expr
equality a b = app (app (def (mkQ ("Agda" ∷ "Builtin" ∷ "Equality" ∷ "_≡_" ∷ []))) (vis a)) (vis b)

endpointFunction : String → List Decl
endpointFunction m = sig plain "f" (def (mkQ ("Agda" ∷ "Builtin" ∷ "Bool" ∷ "Bool" ∷ [])))
  ∷ fun plain "f" (clause (head (squareName m "f") []) (rhs (con (mkQ ("Agda" ∷ "Builtin" ∷ "Bool" ∷ "true" ∷ [])))) [] ∷ []) ∷ []

squareBase : Code
squareBase = code (mkQ ("Base" ∷ [])) [] (endpointFunction "Base")

squareUpper : Expr → List (Arg Pat) → Expr → Code
squareUpper t ps body = code (mkQ ("Upper" ∷ [])) [] (Data.List._++_ (endpointFunction "Upper")
  (sig plain "square" t ∷ fun plain "square" (clause (head (squareName "Upper" "square") ps) (rhs body) [] ∷ []) ∷ []))

squareLift : List QName → LiftSpec
squareLift rs = liftSpec (mkQ ("Base" ∷ [])) (mkQ ("Upper" ∷ [])) []
  (endpointLiftRefs (squareName "Base" "f") (squareName "Upper" "f") (squareName "Upper" "square") rs ∷ [])

-- Base.f ≡ Base.f → Upper.f ≡ Upper.f → ⊤ mentions both endpoints
-- and equality, but its codomain proves no commuting relation.
fakeSquare : Code
fakeSquare = squareUpper
  (fun′ (vis (equality (def (squareName "Base" "f")) (def (squareName "Base" "f"))))
    (fun′ (vis (equality (def (squareName "Upper" "f")) (def (squareName "Upper" "f"))))
      (def (mkQ ("Data" ∷ "Unit" ∷ "⊤" ∷ [])))))
  (vis wildP ∷ vis wildP ∷ []) (con (mkQ ("Data" ∷ "Unit" ∷ "tt" ∷ [])))

N4-trivial-square : checkLift squareBase fakeSquare [] (squareLift []) ≡ invalidSquare (squareName "Upper" "square") ∷ []
N4-trivial-square = refl

N4-trivial-square-with-refs : checkLift squareBase fakeSquare [] (squareLift (squareName "Base" "f" ∷ []))
  ≡ invalidSquare (squareName "Upper" "square") ∷ []
N4-trivial-square-with-refs = refl

-- A genuine equality still cannot omit a reference declared by the lift.
N4-missing-required-ref : checkLift squareBase
  (squareUpper (equality (def (squareName "Base" "f")) (def (squareName "Upper" "f"))) [] (var "refl")) []
  (squareLift (squareName "Upper" "myCustomProj" ∷ [])) ≡ invalidSquare (squareName "Upper" "square") ∷ []
N4-missing-required-ref = refl
