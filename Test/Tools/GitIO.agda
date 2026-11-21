{-# OPTIONS --guardedness #-}
module Test.Tools.GitIO where

open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership using (St; Dir; Chan; Srv; Prog; done; openAs; call; stop;
  _>>=_; _>>_; ⊤-inst; ×-inst; ≡-inst)
open import OwnershipIO using (evalIO)
open import OwnershipIO.FFI using (currentDirectory; exitFailure)
open import OwnershipIO.Tools.GitFFI using (localOnly)
open import Context.Terminal using (Byte; Bytes; byte; bytes; SandboxTarget; localSandbox; dockerSandbox)
open import Context.Tools.FsSandbox using (eqBytes; all)
open import Context.Tools.GitSandbox
open import Code.Tools.GitTool
open import Code.Driver using (Registry; Pick; SubT; select; all-nil; all-cons)

Home Live : GitConfig → St
Home cfg = Dir (("slot" , Dir (GitOwnedCtx cfg)) ∷ [])
Live cfg = Dir (("slot" , Chan (Srv GitStep RawGitObs (Dir (GitOwnedCtx cfg)))) ∷ [])

calls : (cfg : GitConfig) → List GitStep → Prog (gitSpec ∷ []) (Live cfg) (Live cfg) (List RawGitObs)
calls cfg [] = done []
calls cfg (q ∷ qs) = call "slot" q >>= λ o → calls cfg qs >>= λ os → done (o ∷ os)

session : (cfg : GitConfig) → List GitStep → Prog (gitSpec ∷ []) (Home cfg) (Home cfg) (List RawGitObs)
session cfg qs = openAs "slot" "gitbox" cfg >> calls cfg qs >>= λ os → stop "slot" >> done os

registry : String → Registry (gitSpec ∷ [])
registry cwd = gitTool (cwd ++ˢ "/tmp/ext-tools-build/git-relay") (cwd ++ˢ "/tmp/git-sandboxes") ∷ []

fixtureConfig : SandboxTarget → GitConfig
fixtureConfig destination = gitConfig destination "main" "Probe Author" "probe@example.invalid"
  1700000000 (("DECLARED" , "visible") ∷ ("LC_ALL" , "C.UTF-8") ∷ []) ("README.md" ∷ [])

initialBytes finalBytes : Bytes
initialBytes = bytes "initial\n"
finalBytes = bytes "modified after staging\n"

-- Every observation is paired with the pure transition, including the unborn
-- repository, staged deletion, nested paths, newline names and branch checkout.
scenario : List GitStep
scenario = gitStatus ∷ gitStageAll ∷ gitStatus ∷ gitCommit "initial" 0 ∷ gitStatus ∷
  gitWriteFile "README.md" (bytes "staged\n") ∷ gitStagePaths ("README.md" ∷ []) ∷
  gitWriteFile "README.md" finalBytes ∷ gitWriteFile "notes space\nline.txt" (bytes "notes\n") ∷
  gitWriteFile "nested/new file.txt" (bytes "nested\n") ∷ gitStatus ∷
  gitStageAll ∷ gitCommit "second" 1 ∷ gitStatus ∷
  gitSwitchBranch "feat" true ∷ gitStatus ∷ gitWriteFile "README.md" (bytes "feature\n") ∷
  gitRemoveFile "notes space\nline.txt" ∷ gitStageAll ∷ gitStatus ∷ gitCommit "feature" 2 ∷
  gitCreateTag "v1.0" ∷ gitStatus ∷ gitSwitchBranch "main" false ∷ gitStatus ∷
  gitRemoveFile "notes space\nline.txt" ∷ gitStagePaths ("notes space\nline.txt" ∷ []) ∷ gitStatus ∷
  gitWriteFile "notes space\nline.txt" (bytes "notes\n") ∷
  gitStagePaths ("notes space\nline.txt" ∷ []) ∷ gitStatus ∷ []

report : String → Bool → IO.IO Bool
report label b = F.putStrLn ((if b then "PASS " else "FAIL ") ++ˢ label) IO.>>= λ _ → IO.return b

eqMaybeSummary : Maybe GitRepoSummary → Maybe GitRepoSummary → Bool
eqMaybeSummary nothing nothing = true
eqMaybeSummary (just a) (just b) = eqGitSummary a b
eqMaybeSummary _ _ = false

successful : RawGitObs → Bool
successful o with exitStatus o
... | nothing = not (timedOut o)
... | just n = (n ≡ᵇ 0) ∧ not (timedOut o)

isHex : Char → Bool
isHex c = ((48 ≤ᵇ toℕ c) ∧ (toℕ c ≤ᵇ 57)) ∨ ((97 ≤ᵇ toℕ c) ∧ (toℕ c ≤ᵇ 102))

validOid : String → Bool
validOid oid = (length (toList oid) ≡ᵇ 40) ∧ all isHex (toList oid)

checkOid : GitStep → PureGitRepo → RawGitObs → Bool
checkOid (gitCommit _ _) repo o = validOid (commitHash o)
checkOid gitStatus repo o = if commitCount (projectSummary repo) ≡ᵇ 0
  then primStringEquality (commitHash o) "" else validOid (commitHash o)
checkOid _ repo o = primStringEquality (commitHash o) ""

compareModel : ℕ → List GitStep → PureGitRepo → List RawGitObs → IO.IO Bool
compareModel n [] repo [] = IO.return true
compareModel n (q ∷ qs) repo (o ∷ os) with stepPureGit q repo
... | next , expected =
  (if eqMaybeSummary expected (summary o) ∧ successful o ∧ checkOid q next o then IO.return true
   else report ("pure/real observation " ++ˢ show n) false) IO.>>= λ agrees →
  compareModel (suc n) qs next os IO.>>= λ rest → IO.return (agrees ∧ rest)
compareModel n _ repo _ = report "observation count" false

hashes : List RawGitObs → List String
hashes [] = []
hashes (o ∷ os) = if primStringEquality (commitHash o) "" then hashes os else commitHash o ∷ hashes os

sameHashes : List String → List String → Bool
sameHashes [] [] = true
sameHashes (a ∷ as) (b ∷ bs) = validOid a ∧ primStringEquality a b ∧ sameHashes as bs
sameHashes _ _ = false

nonemptyHashes : List String → Bool
nonemptyHashes [] = false
nonemptyHashes (_ ∷ _) = true

modelRun : String → SandboxTarget → IO.IO (Bool × List String)
modelRun cwd destination =
  evalIO (select (gitSpec ∷ []) (registry cwd)) (session cfg scenario)
    ((initialBytes , tt) , tt) IO.>>= λ result →
  compareModel 0 scenario (initPureGit cfg (initialBytes ∷ [])) (proj₂ result) IO.>>= λ agrees →
  report "exact pure/real summaries and owned file after checkout"
    (agrees ∧ eqBytes (proj₁ (proj₁ (proj₁ result))) finalBytes) IO.>>= λ ok →
  IO.return (ok , hashes (proj₂ result))
  where
    cfg = fixtureConfig destination

octets : ℕ → ℕ → Bytes
octets zero start = []
octets (suc n) start = byte start ∷ octets n (suc start)

allOctets : Bytes
allOctets = octets 256 0

pythonCode : String
pythonCode = "import os,sys; assert os.getcwd().endswith('/work'); "
  ++ˢ "assert set(os.environ)=={'DECLARED','LC_ALL'}; assert os.environ['DECLARED']=='visible'; "
  ++ˢ "assert 'HOST_SECRET_LEAK' not in os.environ; "
  ++ˢ "assert open('README.md','rb').read()==b'initial\\n'; "
  ++ˢ "b=sys.stdin.buffer.read(); assert b==bytes(range(256)); "
  ++ˢ "open('README.md','wb').write(b[::-1]); sys.stdout.buffer.write(b); sys.stderr.buffer.write(b[::-1])"

filterStep : SandboxTarget → Bytes → GitStep
filterStep localSandbox input = gitRunTarget "/usr/bin/grep" ("-F" ∷ "README" ∷ []) input 5000
filterStep (dockerSandbox _) input = gitRunTarget "/workspace/executable"
  ("--filter=README" ∷ "--no-sort" ∷ []) input 5000

targetProgram : (cfg : GitConfig) → Prog (gitSpec ∷ []) (Home cfg) (Home cfg) (List RawGitObs)
targetProgram cfg = openAs "slot" "gitbox" cfg >>
  call "slot" gitStageAll >> call "slot" (gitCommit "initial" 0) >>
  call "slot" (gitRunTarget "/usr/bin/git" ("log" ∷ "--format=%s" ∷ []) [] 5000) >>= λ log →
  call "slot" (gitRunTarget "/usr/bin/git" ("ls-files" ∷ []) [] 5000) >>= λ files →
  call "slot" (filterStep (target cfg) (stdoutOut files)) >>= λ filtered →
  call "slot" (gitRunTarget "/usr/bin/python3" ("-I" ∷ "-S" ∷ "-c" ∷ pythonCode ∷ []) allOctets 5000) >>= λ binary →
  call "slot" (gitRunTarget "/usr/bin/python3"
    ("-I" ∷ "-S" ∷ "-c" ∷ "import time; time.sleep(5)" ∷ []) [] 200) >>= λ timeout →
  stop "slot" >> done (log ∷ files ∷ filtered ∷ binary ∷ timeout ∷ [])

targetObservations : List RawGitObs → Bool
targetObservations (log ∷ files ∷ filtered ∷ binary ∷ timeout ∷ []) =
  successful log ∧ eqBytes (stdoutOut log) (bytes "initial\n") ∧
  successful files ∧ eqBytes (stdoutOut files) (bytes "README.md\n") ∧
  successful filtered ∧ eqBytes (stdoutOut filtered) (bytes "README.md\n") ∧
  successful binary ∧ eqBytes (stdoutOut binary) allOctets ∧ eqBytes (stderrOut binary) (reverse allOctets) ∧
  timedOut timeout ∧ timeoutExit (exitStatus timeout)
  where
    timeoutExit : Maybe ℕ → Bool
    timeoutExit (just n) = n ≡ᵇ 124
    timeoutExit _ = false
targetObservations _ = false

targetRun : String → SandboxTarget → IO.IO Bool
targetRun cwd destination = evalIO (select (gitSpec ∷ []) (registry cwd))
  (targetProgram (fixtureConfig destination)) ((initialBytes , tt) , tt) IO.>>= λ result →
  report "git log/ls-files, target filter, exact environment, binary readback, timeout"
    (targetObservations (proj₂ result) ∧ eqBytes (proj₁ (proj₁ (proj₁ result))) (reverse allOctets))

suite : String → SandboxTarget → IO.IO (Bool × List String)
suite cwd destination = modelRun cwd destination IO.>>= λ first →
  modelRun cwd destination IO.>>= λ second →
  report "two runs produce identical nonempty SHA-1 commit/status OIDs"
    (nonemptyHashes (proj₂ first) ∧ sameHashes (proj₂ first) (proj₂ second)) IO.>>= λ deterministic →
  targetRun cwd destination IO.>>= λ targetOK →
  IO.return (proj₁ first ∧ proj₁ second ∧ deterministic ∧ targetOK , proj₂ first)

fzfImage : String
fzfImage = "programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6"

dockerSuite : String → Bool → List String → IO.IO Bool
dockerSuite cwd true localHashes = F.putStrLn "Docker omitted by explicit --local-only" IO.>>= λ _ → IO.return true
dockerSuite cwd false localHashes = F.putStrLn "Docker Git conformance" IO.>>= λ _ →
  suite cwd (dockerSandbox fzfImage) IO.>>= λ remote →
  report "local and Docker SHA-1 OIDs are identical"
    (proj₁ remote ∧ nonemptyHashes localHashes ∧ sameHashes localHashes (proj₂ remote))

main : IO.IO ⊤
main = currentDirectory IO.>>= λ cwd → localOnly IO.>>= λ onlyLocal →
  F.putStrLn "Local Git conformance" IO.>>= λ _ → suite cwd localSandbox IO.>>= λ local →
  dockerSuite cwd onlyLocal (proj₂ local) IO.>>= λ dockerOK →
  if proj₁ local ∧ dockerOK then F.putStrLn "ALL GIT TESTS PASS" else exitFailure
