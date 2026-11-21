{-# OPTIONS --guardedness #-}
module Test.MetaBoundary where

open import Agda.Builtin.Char using (primCharEquality)
open import Data.Bool.Base using (Bool; true; false; not; _∧_)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List; []; _∷_; _++_; all; any; concatMap; tails)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (zero; suc)
open import Data.Product using (_,_)
open import Data.String.Base using (String; toList) renaming (_++_ to _++ˢ_)
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecPropositional _≟_ using (_∉_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import IO.Primitive using (IO; return; _>>=_)
open import IO.Primitive.Finite using (putStrLn)
open import System.Environment.Primitive using (getArgs)
open import OwnershipIO.FFI using (currentDirectory; mkdirP; listDirectory; fileExists; dirExists;
                                 readProcessAt; procResult; failIO)
open import OwnershipIO.MetaFFI using (_>>_; withPrivateTemp; writeUTF8; catchIO)
open import Code using (Code; Decl; code; mkQ; qn; modName; full; import′; module′; everything; _==ˢ_; eqList)
open import Code.Protocol using (agdaCheck; dumpReq; dumped; dumpFailed; DumpResult)
open import Code.Transport using (CheckResult; pass; fail)
open import Meta.Sandbox

private
  simple : ModulePath → List Decl → Code
  simple path = code (mkQ path) []

  useMod : ModulePath → Decl
  useMod path = import′ (mkQ path) true everything []

  harness = useMod ("Code" ∷ "Harness" ∷ [])
  badImport = simple ("Object" ∷ []) (harness ∷ [])
  shadow = simple ("Ownership" ∷ []) []
  legal = simple ("Object" ∷ "Good" ∷ [])
    (useMod ("Context" ∷ "Blueprint" ∷ []) ∷ useMod ("Data" ∷ "Nat" ∷ []) ∷ [])

  -- Instantiate the safe theorem with the repository's actual Code type.
  prefix-proof : (c : Code) → checkObjectModuleSafe false c ≡ true →
                 firstSegment (full (modName c)) ∉ reservedPrefixes
  prefix-proof = ordinary-prefix-safe

  _ : all (λ p → not (checkObjectModuleSafe false (simple (p ∷ "Sub" ∷ []) []))) reservedPrefixes ≡ true
  _ = refl
  _ : checkObjectModuleSafe false (simple ("Main" ∷ []) []) ≡ false
  _ = refl
  _ : checkObjectModuleSafe true (simple ("Main" ∷ []) []) ≡ true
  _ = refl
  _ : checkObjectModuleSafe true (simple ("Main" ∷ "Sub" ∷ []) []) ≡ false
  _ = refl
  _ : checkObjectModuleSafe true (simple ("Main" ∷ []) (harness ∷ [])) ≡ false
  _ = refl
  _ : checkObjectModuleSafe false (simple ("Good" ∷ []) (module′ "Local" [] (harness ∷ []) ∷ [])) ≡ false
  _ = refl
  _ : checkObjectModuleSafe false (simple ("Code.Harness" ∷ []) []) ≡ false
  _ = refl
  _ : checkObjectModuleSafe false (simple ("../Bad" ∷ []) []) ≡ false
  _ = refl
  _ : checkObjectModuleSafe false legal ≡ true
  _ = refl

  assert : String → Bool → IO ⊤
  assert label true = return tt
  assert label false = failIO ("MetaBoundary: " ++ˢ label)

  contains : String → String → Bool
  contains needle haystack = any (prefix (toList needle)) (tails (toList haystack))
    where
    prefix : List Char → List Char → Bool
    prefix [] _ = true
    prefix (c ∷ cs) (d ∷ ds) = primCharEquality c d ∧ prefix cs ds
    prefix (_ ∷ _) [] = false

  gateFailed : CheckResult → IO ⊤
  gateFailed pass = failIO "MetaBoundary: expected a static rejection"
  gateFailed (fail msg) = assert msg (contains "forbidden module name or import" msg)

  dumpGateFailed : DumpResult → IO ⊤
  dumpGateFailed (dumped _) = failIO "MetaBoundary: dump accepted forbidden source"
  dumpGateFailed (dumpFailed msg) = assert msg (contains "forbidden module name or import" msg)

  checked : CheckResult → IO ⊤
  checked pass = return tt
  checked (fail msg) = failIO msg

  emptyScratch : String → IO ⊤
  emptyScratch scratch = listDirectory scratch >>= λ where
    [] → return tt
    (p ∷ _) → failIO ("MetaBoundary: leftover sandbox path " ++ˢ p)

  mode : String → IO String
  mode path = readProcessAt "" 5000 "stat" ("-c" ∷ "%a" ∷ "--" ∷ path ∷ []) "" >>= λ where
    (procResult zero out _) → return out
    (procResult (suc _) _ err) → failIO err

  -- Direct invocation deliberately skips the static gate. Require an Agda
  -- module-resolution diagnostic naming Code.Harness, not just a nonzero exit.
  probe : String → List String → IO ⊤
  probe work paths@(view ∷ stdlib ∷ ancestor ∷ []) = do
    assert "installed stdlib" (stdlib ==ˢ "/usr/share/agda-stdlib")
    fileExists (view ++ˢ "/Context/Blueprint.agda") >>= assert "Context present"
    dirExists (view ++ˢ "/Code") >>= λ b → assert "Code absent" (not b)
    fileExists (view ++ˢ "/Ownership.agda") >>= λ b → assert "Ownership absent" (not b)
    dirExists (view ++ˢ "/Store") >>= λ b → assert "Store absent" (not b)
    dirExists (view ++ˢ "/Meta") >>= λ b → assert "Meta absent" (not b)
    dirExists (ancestor ++ˢ "/Code") >>= λ b → assert "reserved ancestor subtree hidden" (not b)
    fileExists (ancestor ++ˢ "/Ancestor/Base.agda") >>= assert "ancestor present"
    mode view >>= λ m → assert "read-only view root" (m ==ˢ "555\n")
    mode (view ++ˢ "/Context/Blueprint.agda") >>= λ m → assert "read-only Context source" (m ==ˢ "444\n")
    mode (ancestor ++ˢ "/Ancestor/Base.agda") >>= λ m → assert "read-only ancestor" (m ==ˢ "444\n")
    writeUTF8 (work ++ˢ "/Probe.agda") "module Probe where\nopen import Code.Harness\n"
    let args = concatMap (λ i → "-i" ∷ i ∷ []) (work ∷ paths)
    readProcessAt work 120000 "agda" ("--no-libraries" ∷ args ++ ("Probe.agda" ∷ [])) "" >>= λ where
      (procResult zero _ _) → failIO "MetaBoundary: Code.Harness was visible"
      (procResult (suc _) out err) → let msg = out ++ˢ err in
        assert msg (contains "Failed to find source of module Code.Harness" msg)
  probe _ _ = failIO "MetaBoundary: unexpected whitelist"

  liveDump : String → String → String → IO ⊤
  liveDump bin repo scratch = do
    let src = "module Object.FromText where\nimport Context.Blueprint\nimport Typed\nimport Aux\n"
        aux = "module Aux where\n-- import Code.Harness is a comment\nimport Data.Nat\n"
    sandboxDump bin repo scratch [] (dumpReq src (("Aux" , aux) ∷ []) (simple ("Typed" ∷ []) [] ∷ [])) >>= λ where
      (dumpFailed msg) → failIO msg
      (dumped c) → assert "decoded real dump"
        (eqList _==ˢ_ (full (modName c)) ("Object" ∷ "FromText" ∷ []) ∧ checkObjectModuleSafe false c)
    let badLitSrc = "module Object.BadLit where\nimport Context.Blueprint\nimport Data.List.Membership.Propositional.Properties\nopen import Data.Nat\nbad : ℕ → ℕ\nbad 39 = 0\nbad n = n\n"
    sandboxDump bin repo scratch [] (dumpReq badLitSrc [] []) >>= λ where
      (dumpFailed msg) → failIO ("MetaBoundary: unexpected dump failure on BadLit: " ++ˢ msg)
      (dumped badLitCode) → sandboxAgdaCheck repo scratch [] (agdaCheck badLitCode []) >>= λ where
        pass → failIO "MetaBoundary: expected Agda pattern literal rejection"
        (fail msg) → assert msg (contains "when checking that the pattern 39 has type ℕ" msg
                               ∧ not (contains "supported by Cubical Agda" msg))
    let bad = "module Raw where\nmodule Local where\n  open import {- comment -}\n    Code.Harness\n"
        absent = scratch ++ˢ "/unused-dump"
    sandboxDump absent repo scratch [] (dumpReq bad [] []) >>= dumpGateFailed
    sandboxDump absent repo scratch [] (dumpReq src (("label" , "module Meta.Helper where\n") ∷ []) []) >>= dumpGateFailed
    sandboxDump absent repo scratch [] (dumpReq src [] (shadow ∷ [])) >>= dumpGateFailed
    emptyScratch scratch

  runTests : String → String → String → IO ⊤
  runTests repo bin tmp = do
    let scratch = tmp ++ˢ "/scratch"
        ancestor = tmp ++ˢ "/sealed"
        work = tmp ++ˢ "/probe"
    mkdirP scratch
    mkdirP work
    mkdirP (ancestor ++ˢ "/Ancestor")
    mkdirP (ancestor ++ˢ "/Code")
    writeUTF8 (ancestor ++ˢ "/Ancestor/Base.agda") "module Ancestor.Base where\n"
    writeUTF8 (ancestor ++ˢ "/Code/Harness.agda") "module Code.Harness where\n"
    sandboxAgdaCheck repo scratch [] (agdaCheck badImport []) >>= gateFailed
    sandboxAgdaCheck repo scratch [] (agdaCheck shadow []) >>= gateFailed
    sandboxAgdaCheck repo scratch [] (agdaCheck legal (shadow ∷ [])) >>= gateFailed
    emptyScratch scratch
    putStrLn "PASS  safe prefix theorem, entry Main and static gates"

    original ← mode (repo ++ˢ "/Context/Blueprint.agda")
    fileExists (repo ++ˢ "/Code/Harness.agda") >>= assert "harness present in the actual repository"
    withWhitelistView repo scratch (ancestor ∷ []) (probe work)
    emptyScratch scratch
    mode (repo ++ˢ "/Context/Blueprint.agda") >>= λ m → assert "source permissions preserved" (original ==ˢ m)
    sandboxAgdaCheck repo scratch [] (agdaCheck legal []) >>= checked
    let fromAncestor = simple ("Consumer" ∷ []) (useMod ("Ancestor" ∷ "Base" ∷ []) ∷ [])
    sandboxAgdaCheck repo scratch (ancestor ∷ []) (agdaCheck fromAncestor []) >>= checked
    putStrLn "PASS  physical isolation, read-only Context, stdlib and ancestor imports"

    sandboxAgdaCheck repo scratch [] (agdaCheck fromAncestor []) >>= λ where
      pass → failIO "MetaBoundary: previous ancestor leaked into a fresh view"
      (fail msg) → assert msg (contains "Failed to find source of module Ancestor.Base" msg)
    aborted ← catchIO (withWhitelistView repo scratch [] (λ _ → failIO {A = Bool} "probe aborted"))
                      (λ msg → return (contains "probe aborted" msg))
    assert "exception from callback" aborted
    emptyScratch scratch
    liveDump bin repo scratch
    putStrLn "PASS  real dump, source and dependency gates, cleanup on success and failure"

main : IO ⊤
main = do
  repo ← currentDirectory
  args ← getArgs
  let bin = binary repo args
  withPrivateTemp "/tmp" (runTests repo bin)
  where
  binary : String → List String → String
  binary repo [] = repo ++ˢ "/dump/dump"
  binary _ (bin ∷ _) = bin
