module Code.SessionProtocol where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁)
open import Data.String using (String; toList; fromList; lines; unlines; intersperse) renaming (_++_ to _++ˢ_)
open import Code using (_==ˢ_)
open import Code.SExpr
open import Code.Submission using (extract; Blocks; resolveBlocks; getField; textField; uniqueFields; allowedFields; unresolvedAtRefs; quotedAtRefs)

data SessionAction : Set where
  run-script build-exe : String → String → SessionAction
  drive-tree-with : String → String → String → List String → Maybe String → Maybe String → SessionAction
  finish : String → SessionAction

pattern drive-tree name why src bases lift = drive-tree-with name why src bases lift nothing

private
  infixl 1 _>>=_
  _>>=_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  nothing >>= f = nothing
  just x >>= f = f x

strings : List SExpr → Maybe (List String)
strings [] = just []
strings (str s ∷ ss) = strings ss >>= λ rest → just (s ∷ rest)
strings _ = nothing

optionalSource : List SExpr → Maybe (Maybe String)
optionalSource (sym "nothing" ∷ []) = just nothing
optionalSource (list (sym "just" ∷ str s ∷ []) ∷ []) = just (just s)
optionalSource _ = nothing

optionalTransport : Maybe (List SExpr) → Maybe (Maybe String)
optionalTransport nothing = just nothing
optionalTransport (just xs) = optionalSource xs

decodeSessionAction : SExpr → Maybe SessionAction
decodeSessionAction (list (sym "session-action" ∷ fs)) =
  if uniqueFields [] fs then kind (getField "kind" fs) else nothing
  where
    sourceAction : (String → String → SessionAction) → Maybe SessionAction
    sourceAction k = if allowedFields ("kind" ∷ "why" ∷ "source" ∷ []) fs then
      (textField "why" fs >>= λ why → textField "source" fs >>= λ src → just (k why src)) else nothing
    kind : Maybe (List SExpr) → Maybe SessionAction
    kind (just (sym "run-script" ∷ [])) = sourceAction run-script
    kind (just (sym "build-exe" ∷ [])) = sourceAction build-exe
    kind (just (sym "drive-tree" ∷ [])) =
      if allowedFields ("kind" ∷ "treeName" ∷ "why" ∷ "specSrc" ∷ "baseTrees" ∷ "maybeLiftSrc" ∷ "maybeTransportSrc" ∷ []) fs then
      (textField "treeName" fs >>= λ name → textField "why" fs >>= λ why → textField "specSrc" fs >>= λ src →
       getField "baseTrees" fs >>= strings >>= λ bases → getField "maybeLiftSrc" fs >>= optionalSource >>= λ lift →
       optionalTransport (getField "maybeTransportSrc" fs) >>= λ trans →
       just (drive-tree-with name why src bases lift trans)) else nothing
    kind (just (sym "finish" ∷ [])) = if allowedFields ("kind" ∷ "summary" ∷ []) fs then
      (textField "summary" fs >>= λ summary → just (finish summary)) else nothing
    kind _ = nothing
decodeSessionAction _ = nothing

parseSessionAction : String → Maybe SessionAction
parseSessionAction txt = let b = extract (lines txt) in
  parseSExpr (unlines (Blocks.envelope b)) >>= resolveBlocks (Blocks.sources b) >>= decodeSessionAction

explainSessionActionFailure : String → String
explainSessionActionFailure txt with txt ==ˢ ""
... | true = "session-action: empty AI reply"
... | false =
  let b   = extract (lines txt)
      env = unlines (Blocks.envelope b)
  in if env ==ˢ "" then
       "session-action: missing envelope or unclosed ```agda / ```sexp fence (ensure every ``` fence has a matching closing ``` line)"
     else inspectEnv (parseSExpr env)
  where
    b = extract (lines txt)
    env = unlines (Blocks.envelope b)
    avail = intersperse ", " (map proj₁ (Blocks.sources b))
    availNote = if avail ==ˢ "" then "(none attached or saved)" else avail
    inspectResolved : SExpr → String
    inspectResolved r with unresolvedAtRefs r | quotedAtRefs r
    ... | u@(_ ∷ _) | _ =
      "session-action: unresolved @block reference(s) " ++ˢ intersperse ", " u
      ++ˢ " (available blocks: " ++ˢ availNote ++ˢ "; save draft via write_draft first or attach ```agda <name> fence)"
    ... | [] | q@(_ ∷ _) =
      "session-action: malformed field value (found quoted string " ++ˢ intersperse ", " q
      ++ˢ " — write bare @name WITHOUT double quotes to reference a draft/fence block!)"
    ... | [] | [] =
      "session-action: envelope parsed as S-expression, but failed schema check (expected `(session-action (kind run-script|drive-tree|build-exe|finish) ...)` with unique valid fields; note `maybeLiftSrc` must be `nothing` or `(just \"(lift ...)\")`)"
    inspectEnv : Maybe SExpr → String
    inspectEnv nothing =
      "session-action: top-level text outside ```agda fences is not a single valid S-expression (output ONLY the `(session-action ...)` S-expression without narrative prose!). Prefix seen:\n"
      ++ˢ fromList (take 240 (toList env))
    inspectEnv (just raw) with resolveBlocks (Blocks.sources b) raw
    ... | nothing = "session-action: failed resolving @block references"
    ... | just r  = inspectResolved r

-- Ref configuration is data, never a shell command. Optional args precede the
-- arguments of each request; timeoutMs bounds every batch invocation.
data RefTarget : Set where
  local : String → RefTarget
  docker : String → String → RefTarget

record RefSpec : Set where
  constructor refSpec
  field
    target : RefTarget
    arguments : List String
    timeoutMs : ℕ
open RefSpec public

decodeRefSpec : SExpr → Maybe RefSpec
decodeRefSpec (list (sym "ref-target" ∷ t ∷ fs)) =
  if uniqueFields [] fs then
    (if allowedFields ("args" ∷ "timeoutMs" ∷ []) fs then
      (targetOf t >>= λ ref → args (getField "args" fs) >>= λ as →
       timeout (getField "timeoutMs" fs) >>= λ ms → just (refSpec ref as ms)) else nothing)
  else nothing
  where
    targetOf : SExpr → Maybe RefTarget
    targetOf (list (sym "local" ∷ str exe ∷ [])) = just (local exe)
    targetOf (list (sym "docker" ∷ str image ∷ str exe ∷ [])) = just (docker image exe)
    targetOf _ = nothing
    args : Maybe (List SExpr) → Maybe (List String)
    args nothing = just []
    args (just xs) = strings xs
    timeout : Maybe (List SExpr) → Maybe ℕ
    timeout nothing = just 30000
    timeout (just (num ms ∷ [])) = just ms
    timeout _ = nothing
decodeRefSpec _ = nothing

parseRefSpec : String → Maybe RefSpec
parseRefSpec txt = parseSExpr txt >>= decodeRefSpec

encodeRefSpec : RefSpec → SExpr
encodeRefSpec (refSpec t as ms) = list (sym "ref-target" ∷ encodeTarget t
  ∷ list (sym "args" ∷ Data.List.map str as) ∷ list (sym "timeoutMs" ∷ num ms ∷ []) ∷ [])
  where
    encodeTarget : RefTarget → SExpr
    encodeTarget (local exe) = list (sym "local" ∷ str exe ∷ [])
    encodeTarget (docker image exe) = list (sym "docker" ∷ str image ∷ str exe ∷ [])
