module Test.SubmissionTest where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; lines; unlines; words)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Code.SExpr
open import Code.Submission
open import Code.Prompt using (closedWorldTemplate)

unterminated : parseSExpr "\"unterminated" ≡ nothing
unterminated = refl

escapes : parseSExpr "\"a\\tb\\r\\nc\"" ≡ just (str "a\tb\r\nc")
escapes = refl

fenced : parseSubmission "```sexp\n(submission (kind plan) (why \"constant\") (main @main) (subspecs) (moves))\n```\n```agda main\nmodule X where\n```\n"
       ≡ just (submitPlan "constant" "module X where" [] [])
fenced = refl

duplicates : parseSubmission "(submission (kind plan) (kind contradiction) (why \"x\") (main \"x\") (subspecs) (moves))" ≡ nothing
duplicates = refl

omitted-subspecs : parseSubmission "(submission (kind plan) (why \"leaf\") (main \"module X where\") (moves))"
                ≡ just (submitPlan "leaf" "module X where" [] [])
omitted-subspecs = refl

invalid-subspecs : parseSubmission "(submission (kind plan) (why \"leaf\") (main \"module X where\") (subspecs invalid) (moves))" ≡ nothing
invalid-subspecs = refl

invalid-subspec-entry : parseSubmission "(submission (kind plan) (why \"leaf\") (main \"module X where\") (subspecs (\"Child\")) (moves))" ≡ nothing
invalid-subspec-entry = refl

add-moves-without-why : parseSubmission "(submission (kind add-moves) (moves))" ≡ just (addMoves [] nothing)
add-moves-without-why = refl

add-moves-with-why : parseSubmission "(submission (kind add-moves) (why \"reviewed dependents\") (moves))"
                   ≡ just (addMoves [] nothing)
add-moves-with-why = refl

add-moves-with-why-and-main : parseSubmission "(submission (kind add-moves) (why \"revised\") (main \"module X where\") (moves))"
                            ≡ just (addMoves [] (just "module X where"))
add-moves-with-why-and-main = refl

add-moves-invalid-why : parseSubmission "(submission (kind add-moves) (why revised) (moves))" ≡ nothing
add-moves-invalid-why = refl

add-moves-empty-why : parseSubmission "(submission (kind add-moves) (why) (moves))" ≡ nothing
add-moves-empty-why = refl

add-moves-many-why : parseSubmission "(submission (kind add-moves) (why \"a\" \"b\") (moves))" ≡ nothing
add-moves-many-why = refl

add-moves-duplicate-why : parseSubmission "(submission (kind add-moves) (why \"a\") (why \"b\") (moves))" ≡ nothing
add-moves-duplicate-why = refl

-- Each sexp fence starts a submission. Only adjacent named Agda blocks
-- (possibly separated by blank lines) belong to that envelope.
examples : List String → List String
examples = collect false []
  where
    emit : List String → List String → List String
    emit [] rest = rest
    emit acc rest = unlines (reverse acc) ∷ rest

    collect : Bool → List String → List String → List String
    collect _ acc [] = emit acc []
    collect true acc ("```" ∷ ls) = collect false ("```" ∷ acc) ls
    collect true acc (l ∷ ls) = collect true (l ∷ acc) ls
    collect false acc ("```sexp" ∷ ls) = emit acc (collect true ("```sexp" ∷ []) ls)
    collect false [] (_ ∷ ls) = collect false [] ls
    collect false acc (l ∷ ls) with words l
    ... | "```agda" ∷ name ∷ [] = collect true (l ∷ acc) ls
    ... | [] = collect false acc ls
    ... | _ = emit acc (collect false [] ls)

parses : List String → Bool
parses [] = true
parses (s ∷ ss) with parseSubmission s
... | nothing = false
... | just _ = parses ss

authoritative-examples : parses (examples (lines closedWorldTemplate)) ≡ true
authoritative-examples = refl
