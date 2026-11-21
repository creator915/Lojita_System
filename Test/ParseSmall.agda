module Test.ParseSmall where

open import Data.Bool using (Bool; true)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Code
open import Code.Parse

A-sexp : String
A-sexp = "(module \"A\" (params)\n  (datasig (mods) \"ℕ\" (params) (set 0))\n  (datadef (mods) \"ℕ\" () (con \"zero\" (def \"A.ℕ\")) (con \"suc\" (fun (arg vis _ (def \"A.ℕ\")) (def \"A.ℕ\"))))\n)\n"

C-sexp : String
C-sexp = "(module \"C\" (params)\n  (import \"A\" noopen (dir everything (hiding) (renaming) private) (assumes))\n  (sig (mods) \"one\" (def (q \"A.ℕ\" \"A.ℕ\")))\n  (fun (mods) \"one\" (clause (head \"C.one\") (rhs (app (con (q \"A.ℕ.suc\" \"A.suc\")) (arg vis _ (con (q \"A.ℕ.zero\" \"A.zero\"))))) (where)))\n  (sig (mods) \"two\" (def (q \"A.ℕ\" \"A.ℕ\")))\n  (fun (mods) \"two\" (clause (head \"C.two\") (rhs (app (con (q \"A.ℕ.suc\" \"A.suc\")) (arg vis _ (def \"C.one\")))) (where)))\n  (sig (mods) \"double\" (fun (arg vis _ (def (q \"A.ℕ\" \"A.ℕ\"))) (def (q \"A.ℕ\" \"A.ℕ\"))))\n  (fun (mods) \"double\" (clause (head \"C.double\" (arg vis _ (conp (q \"A.ℕ.zero\" \"A.zero\")))) (rhs (con (q \"A.ℕ.zero\" \"A.zero\"))) (where)) (clause (head \"C.double\" (arg vis _ (conp (q \"A.ℕ.suc\" \"A.suc\") (arg vis _ (varp \"n\"))))) (rhs (app (con (q \"A.ℕ.suc\" \"A.suc\")) (arg vis _ (app (con (q \"A.ℕ.suc\" \"A.suc\")) (arg vis _ (app (def \"C.double\") (arg vis _ (var \"n\")))))))) (where)))\n  (sig (mods) \"f\" (fun (arg vis _ (def (q \"A.ℕ\" \"A.ℕ\"))) (def (q \"A.ℕ\" \"A.ℕ\"))))\n  (fun (mods) \"f\" (clause (head \"C.f\" (arg vis _ (varp \"n\"))) (rhs (app (def \"C._.helper\") (arg vis _ (var \"n\")))) (where (sig (mods private) \"helper\" (fun (arg vis _ (def (q \"A.ℕ\" \"A.ℕ\"))) (def (q \"A.ℕ\" \"A.ℕ\")))) (fun (mods) \"helper\" (clause (head \"C._.helper\" (arg vis _ (varp \"m\"))) (rhs (app (con (q \"A.ℕ.suc\" \"A.suc\")) (arg vis _ (var \"m\")))) (where))))))\n)\n"

_ : is-just (parse A-sexp) ≡ true
_ = refl

_ : is-just (parse C-sexp) ≡ true
_ = refl

unitNames : Maybe Code → List QName
unitNames nothing  = []
unitNames (just c) = map uname (units c)

-- A 有一个单元 ℕ；C 有 one two double f
_ : map shown (unitNames (parse A-sexp)) ≡ ("ℕ" ∷ [])
_ = refl

_ : map shown (unitNames (parse C-sexp)) ≡ ("one" ∷ "two" ∷ "double" ∷ "f" ∷ [])
_ = refl

-- A scope-level overload survives the backend wire round trip. Object identity
-- and the presentation-independent hash keep their existing primary path.
open import Code.Encode using (encQ; canonical)
open import Code.SExpr using (str)

overloadedCons : QName
overloadedCons = scopedQName ("List" ∷ "_∷_" ∷ []) "_∷_" ("All._∷_" ∷ [])

_ : decodeQ (encQ overloadedCons) ≡ just overloadedCons
_ = refl

_ : canonical (encQ overloadedCons) ≡ str "List._∷_"
_ = refl
