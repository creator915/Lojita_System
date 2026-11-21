{-# OPTIONS --guardedness #-}
module Test.TermIO where

open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; foldl; length)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership using (St; Dir; Chan; Srv; Prog; done; openAs; call; stop; _>>=_; _>>_; ⊤-inst; ×-inst; ≡-inst)
open import OwnershipIO using (ModelsIO; evalIO)
open import OwnershipIO.FFI using (currentDirectory; exitFailure)
open import Context.Terminal
open import Code.TermTool
open import Test.TermConformance

Home Live : TermConfig → St
Home cfg = Dir (("slot" , Dir (TermFiles cfg)) ∷ [])
Live cfg = Dir (("slot" , Chan (Srv TermStep RawTermObs (Dir (TermFiles cfg)))) ∷ [])

-- Trace observations are at explicit drain/quiescence checkpoints, not kernel
-- read boundaries. Nothing is discarded: all bytes from each action and its
-- drains are concatenated in channel order and compared exactly with Agda.
-- Repeated drains allow startup/exit acknowledgements to arrive under load.
settle : (cfg : TermConfig) → ℕ → RawTermObs → RawTermObs → Prog (ptySpec ∷ []) (Live cfg) (Live cfg) RawTermObs
settle cfg zero expected got = done got
settle cfg (suc fuel) expected got = call "slot" drainRaw >>= λ more →
  let all = appendObs got more in
  if eqObs expected all then done all else settle cfg fuel expected all

calls : (cfg : TermConfig) → List TermStep → List RawTermObs → Prog (ptySpec ∷ []) (Live cfg) (Live cfg) (List RawTermObs)
calls cfg (q ∷ qs) (expected ∷ rest) = call "slot" q >>= λ got →
  settle cfg 60 expected got >>= λ observed →
  if eqObs expected observed then
    (calls cfg qs rest >>= λ observations → done (observed ∷ observations))
  else done (observed ∷ [])
calls cfg _ _ = done []

session : (cfg : TermConfig) → List TermStep → List RawTermObs → Prog (ptySpec ∷ []) (Home cfg) (Home cfg) (List RawTermObs)
session cfg qs expected = openAs "slot" "pty" cfg >> calls cfg qs expected >>= λ trace → stop "slot" >> done trace

showExit : Maybe ℕ → String
showExit nothing = "running"
showExit (just n) = show n

showObs : RawTermObs → String
showObs o = "tty=" ++ˢ hexBytes (ttyOut o) ++ˢ " stdout=" ++ˢ hexBytes (stdoutOut o)
  ++ˢ " stderr=" ++ˢ hexBytes (stderrOut o) ++ˢ " exit=" ++ˢ showExit (exitStatus o)

report : String → Bool → IO.IO Bool
report label b = F.putStrLn ((if b then "PASS " else "FAIL ") ++ˢ label) IO.>>= λ _ → IO.return b

compareTrace : ℕ → List RawTermObs → List RawTermObs → IO.IO Bool
compareTrace n [] [] = IO.return true
compareTrace n (e ∷ es) (a ∷ as) =
  (if eqObs e a then IO.return true else
    F.putStrLn ("FAIL checkpoint " ++ˢ show n ++ˢ "\n  expected " ++ˢ showObs e ++ˢ "\n  observed " ++ˢ showObs a) IO.>>= λ _ → IO.return false)
  IO.>>= λ b → compareTrace (suc n) es as IO.>>= λ rest → IO.return (b ∧ rest)
compareTrace n _ _ = report "trace length" false

eqLines : List String → List String → Bool
eqLines [] [] = true
eqLines (a ∷ as) (b ∷ bs) = primStringEquality a b ∧ eqLines as bs
eqLines _ _ = false

env : List (String × String)
env = ("TERM" , "xterm-256color") ∷ ("LC_ALL" , "C.UTF-8") ∷ ("DECLARED" , "visible") ∷ []

fixtureConfig : SandboxTarget → String → TermTopology → ℕ → ℕ → TermConfig
fixtureConfig target name topo r c = termConfig target topo "/usr/bin/python3"
  ("-I" ∷ "-S" ∷ "-u" ∷ "probe.py" ∷ name ∷ []) env r c ("probe.py" ∷ "nested/note.txt" ∷ [])

runFixture : ∀ {S E} → String → String → SandboxTarget → String → TermTopology → ℕ → ℕ
  → Handler S E → TimedMachine S E → List TermStep → String → (List RawTermObs → Bool) → IO.IO Bool
runFixture cwd source target name topo r c handler model qs note extra =
  evalIO (ptyTool (cwd ++ˢ "/tmp/term-build/term-relay") (cwd ++ˢ "/tmp/term-sandboxes") ∷ [])
    (session cfg qs expected) ((source , "original" , tt) , tt) IO.>>= λ result →
  compareTrace 0 expected (proj₂ result) IO.>>= λ traceOK →
  report name (traceOK ∧ extra (proj₂ result)
    ∧ primStringEquality (proj₁ (proj₁ (proj₁ result))) source
    ∧ primStringEquality (proj₁ (proj₂ (proj₁ (proj₁ result)))) note)
  where
    cfg = fixtureConfig target name topo r c
    expected = traceTimed handler qs model

projected : List RawTermObs → Bool
projected trace = eqLines (screenLines (foldl (λ s o → stepANSI s (ttyOut o)) (blankScreen 3 12) trace))
  ("OK    #     " ∷ ">ow?        " ∷ "            " ∷ [])

suite : String → String → SandboxTarget → IO.IO Bool
suite cwd source target =
  runFixture cwd source target "pipe" pipeStdioWithTTY 24 80 pipeHandler pipeInitial pipeSteps "original" (λ _ → true) IO.>>= λ a →
  runFixture cwd source target "timer" pipeStdioWithTTY 24 80 timing timerInitial beforeSteps "original" (λ _ → true) IO.>>= λ b →
  runFixture cwd source target "timer" pipeStdioWithTTY 24 80 timing timerInitial afterSteps "original" (λ _ → true) IO.>>= λ c →
  runFixture cwd source target "ansi" pipeStdioWithTTY 3 12 ansiHandler ansiInitial ansiSteps "original" projected IO.>>= λ d →
  runFixture cwd source target "signals" pipeStdioWithTTY 24 80 signalHandler signalInitial signalSteps "original" (λ _ → true) IO.>>= λ e →
  runFixture cwd source target "files" pipeStdioWithTTY 24 80 fileHandler fileInitial (drainRaw ∷ []) "original|updated\n" (λ _ → true) IO.>>= λ f →
  runFixture cwd source target "binary" pipeStdioWithTTY 24 80 binaryHandler ansiInitial binarySteps "original" (λ _ → true) IO.>>= λ g →
  runFixture cwd source target "alltty" allTTY 24 80 allTTYHandler allTTYInitial (drainRaw ∷ writeStdin (bytes "x") ∷ drainRaw ∷ []) "original" (λ _ → true) IO.>>= λ h →
  IO.return (a ∧ b ∧ c ∧ d ∧ e ∧ f ∧ g ∧ h)

fzfImage : String
fzfImage = "programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6"

fzfConfig : TermConfig
fzfConfig = termConfig (dockerSandbox fzfImage) pipeStdioWithTTY "/workspace/executable"
  ("--no-sort" ∷ "--no-mouse" ∷ []) env 24 80 []

rawCalls : (cfg : TermConfig) → List TermStep → RawTermObs → Prog (ptySpec ∷ []) (Live cfg) (Live cfg) RawTermObs
rawCalls cfg [] acc = done acc
rawCalls cfg (q ∷ qs) acc = call "slot" q >>= λ o → rawCalls cfg qs (appendObs acc o)

waitExit : (cfg : TermConfig) → ℕ → RawTermObs → Prog (ptySpec ∷ []) (Live cfg) (Live cfg) RawTermObs
waitExit cfg zero acc = done acc
waitExit cfg (suc fuel) acc = call "slot" drainRaw >>= λ o → next (appendObs acc o)
  where
    next : RawTermObs → Prog (ptySpec ∷ []) (Live cfg) (Live cfg) RawTermObs
    next all with exitStatus all
    ... | just _ = done all
    ... | nothing = waitExit cfg fuel all

fzfSession : Prog (ptySpec ∷ []) (Home fzfConfig) (Home fzfConfig) RawTermObs
fzfSession = openAs "slot" "pty" fzfConfig >> rawCalls fzfConfig
  (writeStdin (bytes "alpha\nbeta\ngamma\n") ∷ closeStdin ∷ sleepMs 300
  ∷ writeTTY (encodeKey (textKey "beta")) ∷ sleepMs 150 ∷ writeTTY (encodeKey enter) ∷ []) emptyObs
  >>= λ o → waitExit fzfConfig 100 o >>= λ final → stop "slot" >> done final

hasEscape : Bytes → Bool
hasEscape [] = false
hasEscape (b ∷ bs) = (toℕ b ≡ᵇ 27) ∨ hasEscape bs

fzfSmoke : String → IO.IO Bool
fzfSmoke cwd = evalIO (ptyTool (cwd ++ˢ "/tmp/term-build/term-relay") (cwd ++ˢ "/tmp/term-sandboxes") ∷ [])
  fzfSession (tt , tt) IO.>>= λ result →
  let o = proj₂ result in
  F.putStrLn ("fzf tty-bytes=" ++ˢ show (length (ttyOut o)) ++ˢ " stdout=" ++ˢ hexBytes (stdoutOut o)
    ++ˢ " stderr=" ++ˢ hexBytes (stderrOut o) ++ˢ " exit=" ++ˢ showExit (exitStatus o)) IO.>>= λ _ →
  report "real fzf /dev/tty UI, stdout beta only, exit 0"
    (hasEscape (ttyOut o) ∧ eqBytes (stdoutOut o) (bytes "beta\n") ∧ eqBytes (stderrOut o) [] ∧ eqExit (exitStatus o) (just 0))

main : IO.IO ⊤
main = currentDirectory IO.>>= λ cwd → F.readFile "runtime/term-fixture.py" IO.>>= λ source →
  F.putStrLn "Local env -i conformance" IO.>>= λ _ → suite cwd source localSandbox IO.>>= λ localOK →
  F.putStrLn "Docker cleanroom conformance" IO.>>= λ _ → suite cwd source (dockerSandbox fzfImage) IO.>>= λ dockerOK →
  fzfSmoke cwd IO.>>= λ fzfOK →
  if localOK ∧ dockerOK ∧ fzfOK then F.putStrLn "ALL TERMINAL TESTS PASS" else exitFailure
