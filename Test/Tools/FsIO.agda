{-# OPTIONS --guardedness #-}
module Test.Tools.FsIO where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership using (St; Dir; File; Chan; Srv; Prog; done; openAs; call; stop;
  mkdir; rmdir; withEphemeral; _>>=_; _>>_; ⊤-inst; ×-inst; ≡-inst)
open import OwnershipIO using (ModelsIO; evalIO; RunningIO)
open import OwnershipIO.FFI using (currentDirectory; exitFailure; IORef; newIORef; writeIORef; readIORef)
open import OwnershipIO.Tools.FsFFI using (localOnly; clockMs)
open import Context.Terminal using (Byte; Bytes; byte; bytes; SandboxTarget; localSandbox; dockerSandbox)
open import Context.Tools.FsSandbox
open import Code.Tools.FsTool
open import Code.Driver using (Registry; Pick; SubT; select; all-nil; all-cons)
open import Test.Tools.FsConformance

Home Live : FsConfig → St
Home cfg = Dir (("slot" , Dir (FsOwnedCtx cfg)) ∷ [])
Live cfg = Dir (("slot" , Chan (Srv FsStep RawFsObs (Dir (FsOwnedCtx cfg)))) ∷ [])

calls : (cfg : FsConfig) → List FsStep → Prog (fsSpec ∷ []) (Live cfg) (Live cfg) (List RawFsObs)
calls cfg [] = done []
calls cfg (q ∷ qs) = call "slot" q >>= λ o → calls cfg qs >>= λ os → done (o ∷ os)

session : (cfg : FsConfig) → List FsStep → Prog (fsSpec ∷ []) (Home cfg) (Home cfg) (List RawFsObs)
session cfg qs = openAs "slot" "fsbox" cfg >> calls cfg qs >>= λ observations →
  stop "slot" >> done observations

registry : String → Registry (fsSpec ∷ [])
registry cwd = fsTool (cwd ++ˢ "/tmp/ext-tools-build/fs-relay") (cwd ++ˢ "/tmp/fs-sandboxes") ∷ []

report : String → Bool → IO.IO Bool
report label b = F.putStrLn ((if b then "PASS " else "FAIL ") ++ˢ label) IO.>>= λ _ → IO.return b

compareTrace : ℕ → List RawFsObs → List RawFsObs → IO.IO Bool
compareTrace n [] [] = IO.return true
compareTrace n (e ∷ es) (a ∷ as) =
  (if eqObs e a then IO.return true else report ("observation " ++ˢ show n) false)
  IO.>>= λ b → compareTrace (suc n) es as IO.>>= λ rest → IO.return (b ∧ rest)
compareTrace n _ _ = report "trace length" false

modelConformance : String → SandboxTarget → IO.IO Bool
modelConformance cwd destination =
  evalIO (select (fsSpec ∷ []) (registry cwd)) (session cfg conformanceSteps)
    ((initialBytes , tt) , tt) IO.>>= λ result →
  compareTrace 0 (traceVirtualFs noopCmd conformanceSteps (initVirtualFs cfg (initialBytes ∷ [])))
    (proj₂ result) IO.>>= λ agrees →
  report "exact model trace, binary contents, kinds, modes and UTF-8 ordering"
    (agrees ∧ eqBytes (proj₁ (proj₁ (proj₁ result))) finalOwnedBytes)
  where
    cfg = fsConfigFor destination

octetsFrom : ℕ → ℕ → Bytes
octetsFrom zero start = []
octetsFrom (suc count) start = byte start ∷ octetsFrom count (suc start)

allOctets : Bytes
allOctets = octetsFrom 256 0

env : List (String × String)
env = ("DECLARED" , "visible") ∷ ("LC_ALL" , "C.UTF-8") ∷ []

binaryConfig : SandboxTarget → FsConfig
binaryConfig destination = fsConfig destination env ("binary.bin" ∷ []) []

-- Bytes cross all four boundaries: stdin, stdout, stderr and linear file return.
binaryCode : String
binaryCode = "import os,sys; a=open('binary.bin','rb').read(); b=sys.stdin.buffer.read(); "
  ++ˢ "assert a==bytes(range(256)); assert b==bytes(reversed(range(256))); "
  ++ˢ "assert 'HOST_SECRET_LEAK' not in os.environ; assert os.environ['DECLARED']=='visible'; "
  ++ˢ "assert set(os.environ)=={'DECLARED','LC_ALL'}; "
  ++ˢ "sys.stdout.buffer.write(a+b); sys.stderr.buffer.write(b+a); open('binary.bin','wb').write(b+a+b)"

python : String → Bytes → ℕ → FsStep
python source input timeout = runCmd "/usr/bin/python3" ("-I" ∷ "-S" ∷ "-c" ∷ source ∷ []) input timeout

binaryConformance : String → SandboxTarget → IO.IO Bool
binaryConformance cwd destination =
  evalIO (select (fsSpec ∷ []) (registry cwd))
    (session cfg (python binaryCode reversed 5000 ∷ [])) ((allOctets , tt) , tt) IO.>>= λ result →
  compareTrace 0 (rawFsObs (allOctets ++ reversed) (reversed ++ allOctets) (just 0) false [] ∷ [])
    (proj₂ result) IO.>>= λ agrees →
  report "all 256 octets, exact env -i and returned File Bytes"
    (agrees ∧ eqBytes (proj₁ (proj₁ (proj₁ result))) (reversed ++ allOctets ++ reversed))
  where
    cfg = binaryConfig destination
    reversed = reverse allOctets

emptyConfig : SandboxTarget → FsConfig
emptyConfig destination = fsConfig destination env [] []

-- Measure the call itself so Docker startup/teardown latency cannot obscure the
-- command deadline. The wrapper still runs through Registry and Ownership.
timedRegistry : String → IORef ℕ → Registry (fsSpec ∷ [])
timedRegistry cwd elapsed = (λ cfg owned →
  fsTool (cwd ++ˢ "/tmp/ext-tools-build/fs-relay") (cwd ++ˢ "/tmp/fs-sandboxes") cfg owned IO.>>= λ h →
  IO.return (record
    { onCall = λ q → clockMs IO.>>= λ start → RunningIO.onCall h q IO.>>= λ o →
        clockMs IO.>>= λ end → writeIORef elapsed (end ∸ start) IO.>>= λ _ → IO.return o
    ; onStop = RunningIO.onStop h })) ∷ []

timeoutConformance : String → SandboxTarget → IO.IO Bool
timeoutConformance cwd destination = newIORef 0 IO.>>= λ elapsed →
  evalIO (select (fsSpec ∷ []) (timedRegistry cwd elapsed))
    (session (emptyConfig destination) (python "import time; time.sleep(5)" [] 200 ∷ []))
    (tt , tt) IO.>>= λ result → readIORef elapsed IO.>>= λ duration →
  compareTrace 0 (rawFsObs [] [] (just 124) true [] ∷ []) (proj₂ result) IO.>>= λ agrees →
  report ("200ms monotonic timeout (call: " ++ˢ show duration ++ˢ "ms)")
    (agrees ∧ (150 ≤ᵇ duration) ∧ (duration ≤ᵇ 2500))

ephemeralInner : SandboxTarget → Prog (fsSpec ∷ []) (Dir []) (Dir []) (List RawFsObs)
ephemeralInner destination = mkdir "slot" >>
  session (emptyConfig destination) (writeFileStep "temporary/note" (bytes "ephemeral") ∷ snapshotStep ∷ [])
  >>= λ observations → rmdir "slot" >> done observations

outer : St
outer = Dir (("kept" , File Bytes) ∷ [])

ephemeralProgram : SandboxTarget → Prog (fsSpec ∷ []) outer outer (List RawFsObs)
ephemeralProgram destination = withEphemeral "scratch" (ephemeralInner destination)

ephemeralConformance : String → SandboxTarget → IO.IO Bool
ephemeralConformance cwd destination =
  evalIO (select (fsSpec ∷ []) (registry cwd)) (ephemeralProgram destination)
    (allOctets , tt) IO.>>= λ result →
  report "Registry/select and withEphemeral preserve outer state"
    (eqBytes (proj₁ (proj₁ result)) allOctets ∧ eqTrace (proj₂ result)
      (traceVirtualFs noopCmd (writeFileStep "temporary/note" (bytes "ephemeral") ∷ snapshotStep ∷ [])
        (initVirtualFs (emptyConfig destination) [])))

suite : String → SandboxTarget → IO.IO Bool
suite cwd destination = modelConformance cwd destination IO.>>= λ a →
  binaryConformance cwd destination IO.>>= λ b →
  timeoutConformance cwd destination IO.>>= λ c →
  ephemeralConformance cwd destination IO.>>= λ d → IO.return (a ∧ b ∧ c ∧ d)

fzfImage : String
fzfImage = "programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6"

fzfProbe : String → IO.IO Bool
fzfProbe cwd = evalIO (select (fsSpec ∷ []) (registry cwd))
  (session (emptyConfig (dockerSandbox fzfImage))
    (runCmd "/workspace/executable" ("--read0" ∷ "--print0" ∷ "--filter=beta" ∷ "--no-sort" ∷ [])
      (bytes "alpha\0beta\0gamma\0") 5000 ∷ [])) (tt , tt) IO.>>= λ result →
  report "cleanroom fzf --read0 --print0 --filter exact NUL output"
    (eqTrace (proj₂ result) (rawFsObs (bytes "beta\0") [] (just 0) false [] ∷ []))

dockerSuite : String → Bool → IO.IO Bool
dockerSuite cwd true = F.putStrLn "Docker omitted by explicit --local-only" IO.>>= λ _ → IO.return true
dockerSuite cwd false = F.putStrLn "Docker cleanroom filesystem conformance" IO.>>= λ _ →
  suite cwd (dockerSandbox fzfImage) IO.>>= λ dockerOK →
  fzfProbe cwd IO.>>= λ fzfOK → IO.return (dockerOK ∧ fzfOK)

main : IO.IO ⊤
main = currentDirectory IO.>>= λ cwd → localOnly IO.>>= λ onlyLocal →
  F.putStrLn "Local filesystem conformance" IO.>>= λ _ → suite cwd localSandbox IO.>>= λ localOK →
  dockerSuite cwd onlyLocal IO.>>= λ remoteOK →
  if localOK ∧ remoteOK then F.putStrLn "ALL FILESYSTEM TESTS PASS" else exitFailure
