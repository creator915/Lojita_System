module Test.SessionProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just; nothing)
open import Data.String using (String; lines)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Code.Prompt using (sessionTemplate)
open import Code.SessionProtocol
open import Test.SubmissionTest using (examples)

literal : parseSessionAction "(session-action (kind run-script) (why \"observe\") (source \"module Probe where\\n\"))"
  ≡ just (run-script "observe" "module Probe where\n")
literal = refl

fenced : parseSessionAction "```sexp\n(session-action (kind run-script) (why \"observe\") (source @probe))\n```\n```agda probe\nmodule Probe where\n```\n"
  ≡ just (run-script "observe" "module Probe where")
fenced = refl

removedContext : parseSessionAction "(session-action (kind put-context) (why \"finite tags\") (source \"module Tags where\"))" ≡ nothing
removedContext = refl

removedContextFenced : parseSessionAction "```sexp\n(session-action (kind put-context) (why \"finite tags\") (source @ctx))\n```\n```agda ctx\nmodule Tags where\n```\n" ≡ nothing
removedContextFenced = refl

base : parseSessionAction "(session-action (kind drive-tree) (treeName \"T0\") (why \"classify\") (specSrc \"spec\") (baseTrees) (maybeLiftSrc nothing))"
  ≡ just (drive-tree "T0" "classify" "spec" [] nothing)
base = refl

lifted : parseSessionAction "(session-action (kind drive-tree) (treeName \"T2\") (why \"refine\") (specSrc \"spec\") (baseTrees \"T0\" \"T1\") (maybeLiftSrc (just \"lift\")))"
  ≡ just (drive-tree "T2" "refine" "spec" ("T0" ∷ "T1" ∷ []) (just "lift"))
lifted = refl

build : parseSessionAction "(session-action (kind build-exe) (why \"link\") (entry \"Gen.T1.Emph.app\"))"
  ≡ just (build-exe "link" "Gen.T1.Emph.app")
build = refl

buildCliSym : parseSessionAction "(session-action (kind build-exe) (why \"link\") (entry \"Gen.T1.Emph.app\") (mode cli))"
  ≡ just (build-exe-mode cliMode "link" "Gen.T1.Emph.app")
buildCliSym = refl

buildCliStr : parseSessionAction "(session-action (kind build-exe) (why \"link\") (entry \"Gen.T1.Emph.app\") (mode \"cli\"))"
  ≡ just (build-exe-mode cliMode "link" "Gen.T1.Emph.app")
buildCliStr = refl

buildReactiveSym : parseSessionAction "(session-action (kind build-exe) (why \"tui\") (entry \"Gen.T1.Tui.app\") (mode reactive))"
  ≡ just (build-exe-mode reactiveMode "tui" "Gen.T1.Tui.app")
buildReactiveSym = refl

buildReactiveStr : parseSessionAction "(session-action (kind build-exe) (why \"tui\") (entry \"Gen.T1.Tui.app\") (mode \"reactive\"))"
  ≡ just (build-exe-mode reactiveMode "tui" "Gen.T1.Tui.app")
buildReactiveStr = refl

removedBuildSource : parseSessionAction "(session-action (kind build-exe) (why \"link\") (source \"module Main where\"))" ≡ nothing
removedBuildSource = refl

removedBuildSourceFenced : parseSessionAction "```sexp\n(session-action (kind build-exe) (why \"link\") (source @entry))\n```\n```agda entry\nmodule Main where\n```\n" ≡ nothing
removedBuildSourceFenced = refl

removedBuildSourceAndEntry : parseSessionAction "(session-action (kind build-exe) (why \"link\") (entry \"Gen.T1.Emph.app\") (source \"module Main where\"))" ≡ nothing
removedBuildSourceAndEntry = refl

badBuildMode : parseSessionAction "(session-action (kind build-exe) (why \"link\") (entry \"Gen.T1.Emph.app\") (mode daemon))" ≡ nothing
badBuildMode = refl

done : parseSessionAction "(session-action (kind finish) (summary \"replayed\"))" ≡ just (finish "replayed")
done = refl

duplicate : parseSessionAction "(session-action (kind finish) (summary \"a\") (summary \"b\"))" ≡ nothing
duplicate = refl

unknown : parseSessionAction "(session-action (kind finish) (summary \"a\") (extra \"b\"))" ≡ nothing
unknown = refl

unresolved : parseSessionAction "(session-action (kind run-script) (why \"a\") (source @missing))" ≡ nothing
unresolved = refl

unterminated : parseSessionAction "(session-action (kind run-script) (why \"a\") (source @p))\n```agda p\nmodule Probe where\n" ≡ nothing
unterminated = refl

missing : parseSessionAction "(session-action (kind build-exe) (entry \"Gen.T1.Emph.app\"))" ≡ nothing
missing = refl

missingEntry : parseSessionAction "(session-action (kind build-exe) (why \"link\"))" ≡ nothing
missingEntry = refl

badMaybe : parseSessionAction "(session-action (kind drive-tree) (treeName \"T1\") (why \"x\") (specSrc \"s\") (baseTrees) (maybeLiftSrc (just 3)))" ≡ nothing
badMaybe = refl

sessionExamples : List String
sessionExamples = examples (lines sessionTemplate)

exampleCount : length sessionExamples ≡ 10
exampleCount = refl

examplesParse : List String → Bool
examplesParse [] = true
examplesParse (example ∷ rest) with parseSessionAction example
... | nothing = false
... | just _ = examplesParse rest

templateExamplesParse : examplesParse sessionExamples ≡ true
templateExamplesParse = refl

refLocal : parseRefSpec "(ref-target (local \"/bin/cat\"))" ≡ just (refSpec (local "/bin/cat") [] 30000)
refLocal = refl

refDocker : parseRefSpec "(ref-target (docker \"image\" \"/exe\") (args \"--flag\") (timeoutMs 5000))"
  ≡ just (refSpec (docker "image" "/exe") ("--flag" ∷ []) 5000)
refDocker = refl

badRef : parseRefSpec "(ref-target (local \"/bin/cat\") (shell \"ignored\"))" ≡ nothing
badRef = refl
