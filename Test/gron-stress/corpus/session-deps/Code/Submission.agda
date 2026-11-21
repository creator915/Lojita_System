module Code.Submission where

open import Agda.Builtin.Char using (primCharEquality)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; reverse; map; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList; lines; unlines; words; intersperse) renaming (_++_ to _++ˢ_)
open import Code using (Name; _==ˢ_; elemᵇ)
open import Code.Transport using (Proarrow)
open import Code.SExpr
open import Code.Parse using (decodeMoves)

data Submission : Set where
  submitPlan : String → String → List (Name × String) → List Proarrow → Submission
  addMoves : List Proarrow → Maybe String → Submission
  refute : String → Submission
  independent : String → String → Submission

private
  infixl 1 _>>=_
  _>>=_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  nothing >>= f = nothing
  just a >>= f = f a

-- A fenced envelope may refer to separate verbatim source blocks:
-- (main @main), followed by ```agda main ... ```. Standard escaped strings
-- and multiline S-expression strings use exactly the same decoder.
record Blocks : Set where
  constructor blocks
  field
    envelope : List String
    sources : List (Name × String)
open Blocks

extract : List String → Blocks
extract ls = go ls nothing [] [] []
  where
    go : List String → Maybe String → List String → List String → List (Name × String) → Blocks
    go [] nothing _ env srcs = blocks (reverse env) srcs
    go [] (just _) _ _ _ = blocks [] []
    go (l ∷ ls) nothing cur env srcs with words l
    ... | "```sexp" ∷ [] = go ls (just "sexp") [] env srcs
    ... | "```agda" ∷ n ∷ [] = go ls (just n) [] env srcs
    ... | _ = go ls nothing [] (l ∷ env) srcs
    go (l ∷ ls) (just n) cur env srcs =
      if l ==ˢ "```" then
        (if n ==ˢ "sexp" then go ls nothing [] (cur ++ env) srcs
         else go ls nothing [] env (("@" ++ˢ n , unlines (reverse cur)) ∷ srcs))
      else go ls (just n) (l ∷ cur) env srcs

resolveBlocks : List (Name × String) → SExpr → Maybe SExpr
resolveBlocks bs (sym s) = just (lookup bs)
  where
    lookup : List (Name × String) → SExpr
    lookup [] = sym s
    lookup ((n , txt) ∷ xs) = if n ==ˢ s then str txt else lookup xs
resolveBlocks bs (list xs) = walk xs >>= λ ys → just (list ys)
  where
    walk : List SExpr → Maybe (List SExpr)
    walk [] = just []
    walk (x ∷ xs) = resolveBlocks bs x >>= λ y → walk xs >>= λ ys → just (y ∷ ys)
resolveBlocks bs s = just s

getField : String → List SExpr → Maybe (List SExpr)
getField name [] = nothing
getField name (list (sym key ∷ xs) ∷ fs) = if name ==ˢ key then just xs else getField name fs
getField name (_ ∷ fs) = getField name fs

textField : String → List SExpr → Maybe String
textField k fs with getField k fs
... | just (str s ∷ []) = just s
... | _ = nothing

uniqueFields : List String → List SExpr → Bool
uniqueFields seen [] = true
uniqueFields seen (list (sym k ∷ _) ∷ fs) = if elemᵇ _==ˢ_ k seen then false else uniqueFields (k ∷ seen) fs
uniqueFields seen _ = false

allowedFields : List String → List SExpr → Bool
allowedFields allowed [] = true
allowedFields allowed (list (sym k ∷ _) ∷ fs) = if elemᵇ _==ˢ_ k allowed then allowedFields allowed fs else false
allowedFields allowed _ = false

decodeSubspecs : List SExpr → Maybe (List (Name × String))
decodeSubspecs [] = just []
decodeSubspecs (list (str n ∷ str s ∷ []) ∷ xs) = decodeSubspecs xs >>= λ ys → just ((n , s) ∷ ys)
decodeSubspecs _ = nothing

decodeSubmission : SExpr → Maybe Submission
decodeSubmission (list (sym "submission" ∷ fs)) = if uniqueFields [] fs then kind (getField "kind" fs) else nothing
  where
    subspecs : Maybe (List (Name × String))
    subspecs with getField "subspecs" fs
    ... | nothing = just []
    ... | just xs = decodeSubspecs xs

    reason : Maybe String
    reason with getField "why" fs
    ... | nothing = just ""
    ... | just _ = textField "why" fs

    witnessSource : Maybe String
    witnessSource with getField "refute" fs | getField "witness" fs
    ... | just (str src ∷ []) | nothing = just src
    ... | nothing | just (str src ∷ []) = just src
    ... | _ | _ = nothing

    kind : Maybe (List SExpr) → Maybe Submission
    kind (just (sym "plan" ∷ [])) =
      if allowedFields ("kind" ∷ "why" ∷ "main" ∷ "subspecs" ∷ "moves" ∷ []) fs then
      (textField "why" fs >>= λ why → textField "main" fs >>= λ src →
      subspecs >>= λ subs → getField "moves" fs >>= decodeMoves >>= λ ms →
      just (submitPlan why src subs ms)) else nothing
    kind (just (sym "add-moves" ∷ [])) =
      if allowedFields ("kind" ∷ "why" ∷ "main" ∷ "moves" ∷ []) fs then
      (reason >>= λ _ → getField "moves" fs >>= decodeMoves >>= extra) else nothing
      where
        extra : List Proarrow → Maybe Submission
        extra ms with getField "main" fs
        ... | nothing = just (addMoves ms nothing)
        ... | just (str src ∷ []) = just (addMoves ms (just src))
        ... | _ = nothing
    kind (just (sym "contradiction" ∷ [])) =
      if allowedFields ("kind" ∷ "refute" ∷ []) fs then (textField "refute" fs >>= λ src → just (refute src)) else nothing
    kind (just (sym "independent" ∷ [])) =
      if allowedFields ("kind" ∷ "why" ∷ "refute" ∷ "witness" ∷ []) fs then
        (reason >>= λ why → witnessSource >>= λ src → just (independent why src)) else nothing
    kind _ = nothing
decodeSubmission _ = nothing

parseSubmission : String → Maybe Submission
parseSubmission s = let b = extract (lines s) in
  parseSExpr (unlines (envelope b)) >>= resolveBlocks (sources b) >>= decodeSubmission

unresolvedAtRefs : SExpr → List String
unresolvedAtRefs (sym s) with toList s
... | '@' ∷ _ = s ∷ []
... | _       = []
unresolvedAtRefs (list xs) = go xs
  where
    go : List SExpr → List String
    go [] = []
    go (y ∷ ys) = unresolvedAtRefs y ++ go ys
unresolvedAtRefs _ = []

quotedAtRefs : SExpr → List String
quotedAtRefs (str s) with toList s
... | '@' ∷ _ = s ∷ []
... | _       = []
quotedAtRefs (list xs) = go xs
  where
    go : List SExpr → List String
    go [] = []
    go (y ∷ ys) = quotedAtRefs y ++ go ys
quotedAtRefs _ = []

explainSubmissionFailure : String → String
explainSubmissionFailure s with s ==ˢ ""
... | true = "submission: empty AI reply"
... | false =
  let b   = extract (lines s)
      env = unlines (envelope b)
      avail = intersperse ", " (map proj₁ (sources b))
      availNote = if avail ==ˢ "" then "(none attached or saved)" else avail
  in if env ==ˢ "" then
       "submission: missing envelope or unclosed ```agda / ```sexp code fence (ensure every ``` fence has a matching closing ``` line)"
     else inspectEnv (parseSExpr env)
  where
    b = extract (lines s)
    env = unlines (envelope b)
    avail = intersperse ", " (map proj₁ (sources b))
    availNote = if avail ==ˢ "" then "(none attached or saved)" else avail
    inspectResolved : SExpr → String
    inspectResolved r with unresolvedAtRefs r | quotedAtRefs r
    ... | u@(_ ∷ _) | _ =
      "submission: unresolved @block reference(s) " ++ˢ intersperse ", " u
      ++ˢ " (available blocks: " ++ˢ availNote ++ˢ "; save draft via write_draft first or attach ```agda <name> fence)"
    ... | [] | q@(_ ∷ _) =
      "submission: malformed envelope fields or moves (note: found quoted string " ++ˢ intersperse ", " q
      ++ˢ " — write bare @name WITHOUT double quotes to reference a draft/fence block!)"
    ... | [] | [] =
      "submission: envelope parsed as S-expression, but failed schema check (expected `(submission (kind plan|add-moves|contradiction|independent) ...)` with unique valid fields: `plan` requires `why`, `main`, `moves`, optional `subspecs`; `independent` accepts (submission (kind independent) (why \"...\") (refute @unprovable)); `moves` entries must be `(move SRC TGT)` where SRC/TGT are `bot`, `flags`, `(unit \"...\")`, or `(ext \"...\")`)"
    inspectEnv : Maybe SExpr → String
    inspectEnv nothing =
      "submission: top-level text outside ```agda fences is not a single valid S-expression (output ONLY the `(submission ...)` S-expression without narrative prose!). Prefix seen:\n"
      ++ˢ fromList (take 240 (toList env))
    inspectEnv (just raw) with resolveBlocks (sources b) raw
    ... | nothing = "submission: failed resolving @block references"
    ... | just r  = inspectResolved r
