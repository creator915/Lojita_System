{-# OPTIONS --guardedness #-}
module Test.PromptExamplesCheck where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; unlines) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import IO.Primitive using (IO; return; _>>=_)
import IO.Primitive.Finite as F
open import System.Environment.Primitive using (getArgs)
open import OwnershipIO.FFI using (failIO)
open import Code using (Code; modName; decls; _==ˢ_; _==ᴺ_; closedImplOK; validRefutation)
open import Code.Transport using (nullᵇ; specProblem; satisfies; specΔ)
open import Code.Parse using (parse; parseLift)
import Code.Lift as L
import Code.PolyTransport as P
open import Code.SessionProtocol
open import Code.SessionRunner using (sessionEnvSource)
open import Code.Submission using (parseSubmission; submitPlan; addMoves; refute)
open import Code.Prompt public using
  ( PromptHeader; nativeHeader; closedWorldTemplate; sessionTemplate; sessionTransportHelp
  ; refuteExtraText; nodePrompt; showProblem; showImplProblem; showLiftProblem; showRefuteProblem )

private
  assert : Bool → String → IO ⊤
  assert true  _ = return tt
  assert false e = failIO e

  readCode : String → IO Code
  readCode file = F.readFile file >>= λ src → fromDump (parse src)
    where
      fromDump : Maybe Code → IO Code
      fromDump nothing  = failIO ("invalid dump: " ++ˢ file)
      fromDump (just c) = return c

  -- The envelope parser has resolved @fences. Return every source field to the
  -- extractor, including literal sources, for the same checks as standalone blocks.
  save : String → String → String → IO ⊤
  save dir part = F.writeFile (dir ++ˢ "/" ++ˢ part)

  node : String → String → IO ⊤
  node dir txt with parseSubmission txt
  ... | nothing = failIO "invalid submission"
  ... | just (submitPlan _ src subs _) = save dir "main" src >>= λ _ → children 0 subs
    where
      children : ℕ → List (String × String) → IO ⊤
      children _ [] = return tt
      children n ((_ , code) ∷ rest) =
        save dir ("subspec-" ++ˢ show n) code >>= λ _ → children (suc n) rest
  ... | just (refute src) = save dir "refute" src
  ... | just (addMoves _ nothing) = return tt
  ... | just (addMoves _ (just src)) = save dir "main" src

  descriptor : ∀ {A : Set} → (String → Maybe A) → Maybe String → Bool
  descriptor decode nothing    = true
  descriptor decode (just txt) = is-just (decode txt)

  session : String → String → IO ⊤
  session dir txt with parseSessionAction txt
  ... | nothing = failIO "invalid session-action"
  ... | just (run-script _ src) = save dir "source" src
  ... | just (build-exe-mode _ _ _) = return tt
  ... | just (finish _) = return tt
  ... | just (drive-tree-with _ _ src _ lift poly) =
    assert (descriptor parseLift lift ∧ descriptor P.parsePolyTransport poly) "invalid transport/lift descriptor" >>= λ _ →
    save dir "specSrc" src

  checkDump : String → String → IO ⊤
  checkDump "spec" path = readCode path >>= λ c → assert (is-nothing (specProblem (decls c))) path
  checkDump role path = readCode path >>= λ c →
    let allowed = if role ==ˢ "io" then "--guardedness" ∷ [] else []
        errors = closedImplOK allowed c
    in assert (nullᵇ errors) (path ++ˢ "\n" ++ˢ unlines (map showImplProblem errors))

  -- Apply the actual vertical/horizontal gates to the example implementations.
  squares : String → Code → Code → Code → IO ⊤
  squares txt old impl spec with parseSessionAction txt
  ... | just (drive-tree-with _ _ _ _ lift poly) =
    assert (modName impl ==ᴺ modName spec ∧ satisfies (specΔ (modName spec) (decls spec) []) impl)
           "implementation differs from specSrc" >>= λ _ →
    assert (vertical lift ∧ horizontal poly) "example fails its commuting-square descriptor"
    where
      vertical : Maybe String → Bool
      vertical nothing = true
      vertical (just s) with parseLift s
      ... | nothing = false
      ... | just l = nullᵇ (L.checkLift old impl (decls spec) l)

      horizontal : Maybe String → Bool
      horizontal nothing = true
      horizontal (just s) with P.parsePolyTransport s
      ... | nothing = false
      ... | just p = nullᵇ (P.checkPolyTransport old impl (decls spec) p)
  ... | _ = failIO "expected a drive-tree example"

  cli : List String → IO ⊤
  cli ("env" ∷ cand ∷ relay ∷ scratch ∷ []) =
    F.putStr (sessionEnvSource (refSpec (local "/bin/cat") [] 30000) cand relay scratch)
  cli ("node" ∷ dir ∷ file ∷ []) = F.readFile file >>= node dir
  cli ("session" ∷ dir ∷ file ∷ []) = F.readFile file >>= session dir
  cli ("dump" ∷ role ∷ file ∷ []) = checkDump role file
  cli ("refutation" ∷ spec ∷ proof ∷ []) =
    readCode spec >>= λ s → readCode proof >>= λ p →
    assert (nullᵇ (validRefutation (modName s) [] p)) "invalid refutation"
  cli ("squares" ∷ envelope ∷ old ∷ impl ∷ spec ∷ []) =
    F.readFile envelope >>= λ txt → readCode old >>= λ o → readCode impl >>= λ i →
    readCode spec >>= squares txt o i
  cli _ = failIO "expected env, node, session, dump, refutation or squares"

main : IO ⊤
main = getArgs >>= cli
