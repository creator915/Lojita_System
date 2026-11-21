{-# OPTIONS --guardedness #-}
module Test.Tools.ExtToolsIO where

open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; reverse)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership using (St; Dir; File; Chan; Srv; Prog; done; openAs; call; stop;
  mkdir; rmdir; create; unlink; inside; read; withEphemeral; _>>=_; _>>_;
  ⊤-inst; ×-inst; ≡-inst)
open import OwnershipIO using (evalIO)
open import OwnershipIO.FFI using (currentDirectory; exitFailure)
open import OwnershipIO.Tools.GitFFI using (localOnly)
open import Context.Terminal using (Bytes; byte; bytes; SandboxTarget; localSandbox; dockerSandbox)
import Context.Tools.FuzzGen as Gen
import Context.Tools.FsSandbox as Fs
import Context.Tools.NetSandbox as Net
import Context.Tools.GitSandbox as Git
open import Code.Tools.AllTools
open import Code.Driver using (Registry; Pick; SubT; select; all-nil; all-cons)

-- Every generated path has a distinct index. Git's byte ordering is therefore
-- independent of the sampled suffix, and the expected filter output is exact.
numbered : ℕ → List (ℕ × Bytes) → List (String × Bytes)
numbered n [] = []
numbered n ((suffix , body) ∷ rest) =
  ("candidate-" ++ˢ show n ++ˢ "-" ++ˢ show suffix ++ˢ ".bin" , body) ∷ numbered (suc n) rest

candidates : List (String × Bytes)
candidates = numbered 0 (Gen.sampleMany 3
  (Gen.genPair (Gen.genBounded 999) (Gen.genList 16 Gen.genByte)) (Gen.mkSeed 2026))

selectedPaths payload artifact sentinel : Bytes
selectedPaths = concatMap (λ p → bytes (proj₁ p ++ˢ "\n")) candidates
payload = byte 0 ∷ byte 255 ∷ byte 128 ∷ proj₁ (Gen.runGen (Gen.genList 32 Gen.genByte) (Gen.mkSeed 42))
artifact = selectedPaths ++ reverse payload
sentinel = bytes "outer ownership must remain exact\0" ++ payload

environment : List (String × String)
environment = ("DECLARED" , "visible") ∷ ("LC_ALL" , "C.UTF-8") ∷ []

gitConfig : SandboxTarget → Git.GitConfig
gitConfig destination = Git.gitConfig destination "main" "Integration Author"
  "integration@example.invalid" 1700000000 environment ("artifact.bin" ∷ [])

fsConfig : SandboxTarget → Fs.FsConfig
fsConfig destination = Fs.fsConfig destination environment ("artifact.bin" ∷ []) []

httpMode : Bytes → Net.NetTopology
httpMode body = Net.httpStubMode
  (Net.httpRoute "POST" "/artifact" 200 "OK" [] body ∷ [])

netConfig : SandboxTarget → Bytes → Net.NetConfig
netConfig destination body = Net.netConfig destination (httpMode body) environment ("artifact.bin" ∷ [])

request response : Bytes
request = Net.encodeHttpReq "POST" "/artifact" [] payload
response = Net.encodeHttpResp 200 "OK" [] artifact

cleanEnvironment : String
cleanEnvironment = "assert set(os.environ)=={'DECLARED','LC_ALL'}; "
  ++ˢ "assert os.environ['DECLARED']=='visible'; assert 'HOST_SECRET_LEAK' not in os.environ; "

pythonGit : String → Bytes → Git.GitStep
pythonGit source input = Git.gitRunTarget "/usr/bin/python3"
  ("-I" ∷ "-S" ∷ "-c" ∷ source ∷ []) input 5000

filterPaths : SandboxTarget → Bytes → Git.GitStep
filterPaths localSandbox input = pythonGit
  ("import os,sys; " ++ˢ cleanEnvironment
    ++ˢ "sys.stdout.buffer.write(b''.join(p for p in sys.stdin.buffer.readlines() if b'candidate-' in p))") input
filterPaths (dockerSandbox _) input = Git.gitRunTarget "/workspace/executable"
  ("--filter=candidate-" ∷ "--no-sort" ∷ []) input 5000

saveSelected : Bytes → Git.GitStep
saveSelected input = pythonGit
  ("import os,sys; " ++ˢ cleanEnvironment
    ++ˢ "b=sys.stdin.buffer.read(); open('artifact.bin','wb').write(b); sys.stdout.buffer.write(b)") input

transform : Fs.FsStep
transform = Fs.runCmd "/usr/bin/python3"
  ("-I" ∷ "-S" ∷ "-c" ∷
    ("import os,sys; " ++ˢ cleanEnvironment
      ++ˢ "a=open('artifact.bin','rb').read(); b=sys.stdin.buffer.read(); "
      ++ˢ "assert b[:3]==bytes([0,255,128]); out=a+b[::-1]; "
      ++ˢ "open('artifact.bin','wb').write(out); sys.stdout.buffer.write(out); sys.stderr.buffer.write(b)") ∷ [])
  payload 5000

-- The client sends the exact pure request in fragments, reads to EOF, checks
-- the body against its owned artifact, and writes the received body back.
client : Net.NetStep
client = Net.runClient "/usr/bin/python3"
  ("-I" ∷ "-S" ∷ "-c" ∷
    ("import os,socket,sys; " ++ˢ cleanEnvironment
      ++ˢ "a=open('artifact.bin','rb').read(); q=sys.stdin.buffer.read(); "
      ++ˢ "s=socket.create_connection(('127.0.0.1',int(sys.argv[1])),2); "
      ++ˢ "s.sendall(q[:7]); s.sendall(q[7:]); r=b''\n"
      ++ˢ "while True:\n b=s.recv(65536)\n if not b: break\n r+=b\n"
      ++ˢ "s.close(); body=r.split(b'\\r\\n\\r\\n',1)[1]; assert body==a; "
      ++ˢ "open('artifact.bin','wb').write(body); sys.stdout.buffer.write(r)") ∷ "{{PORT}}" ∷ [])
  request 5000

GitLive : St
GitLive = Dir (("slot" , Chan (Srv Git.GitStep Git.RawGitObs
  (Dir (("artifact.bin" , File Bytes) ∷ [])))) ∷ [])

gitCalls : List Git.GitStep → Prog FullExtΨ GitLive GitLive (List Git.RawGitObs)
gitCalls [] = done []
gitCalls (q ∷ qs) = call "slot" q >>= λ o → gitCalls qs >>= λ os → done (o ∷ os)

setup : List Git.GitStep
setup = map (λ p → Git.gitWriteFile (proj₁ p) (proj₂ p)) candidates ++
  (Git.gitWriteFile "notes.txt" (bytes "not a candidate\n") ∷
   Git.gitStageAll ∷ Git.gitCommit "deterministic candidates" 0 ∷ [])

gitOK : Git.RawGitObs → Bool
gitOK o = not (Git.timedOut o) ∧ Fs.eqBytes (Git.stderrOut o) [] ∧ statusOK (Git.exitStatus o)
  where
    statusOK : Data.Maybe.Maybe ℕ → Bool
    statusOK nothing = true
    statusOK (just n) = Fs.eqExit (just n) (just 0)

committed : Git.RawGitObs → Bool
committed o with Git.summary o
... | nothing = false
... | just s = Git.eqGitSummary s (Git.gitSummary "main" 1 ("main" ∷ []) [] [] [] [])

oneModification : List Fs.FsDiff → Bool
oneModification (Fs.modified p ∷ []) = primStringEquality p "artifact.bin"
oneModification _ = false

Check : Set
Check = String × Bool

-- One linear directory is transferred, restored and transferred again across
-- all three services. It contains the same File Bytes throughout the pipeline.
pipeline : SandboxTarget → Prog FullExtΨ (Dir []) (Dir []) (List Check)
pipeline destination =
  mkdir "slot" >> inside "slot" (create "artifact.bin" ([] {A = Context.Terminal.Byte})) >>
  openAs "slot" "gitbox" (gitConfig destination) >>
  gitCalls setup >>= λ initialized →
  call "slot" Git.gitStatus >>= λ status →
  call "slot" (Git.gitRunTarget "/usr/bin/git" ("ls-files" ∷ []) [] 5000) >>= λ tracked →
  call "slot" (filterPaths destination (Git.stdoutOut tracked)) >>= λ filtered →
  call "slot" (saveSelected (Git.stdoutOut filtered)) >>= λ saved →
  stop "slot" >> inside "slot" (inside "artifact.bin" read) >>= λ gitFile →
  openAs "slot" "fsbox" (fsConfig destination) >>
  call "slot" Fs.snapshotStep >>= λ before →
  call "slot" transform >>= λ transformed →
  call "slot" Fs.snapshotStep >>= λ after →
  stop "slot" >> inside "slot" (inside "artifact.bin" read) >>= λ fsFile →
  openAs "slot" "netbox" (netConfig destination fsFile) >>
  call "slot" client >>= λ exchange →
  stop "slot" >> inside "slot" (inside "artifact.bin" read) >>= λ netFile →
  inside "slot" (unlink "artifact.bin") >> rmdir "slot" >>
  done
    (("generated candidates committed with clean deterministic Git summary" ,
       Fs.all gitOK initialized ∧ gitOK status ∧ committed status) ∷
     ("tracked paths filtered by target and restored as owned File Bytes" ,
       gitOK tracked ∧ Fs.eqBytes (Git.stdoutOut tracked)
         (bytes "artifact.bin\n" ++ selectedPaths ++ bytes "notes.txt\n") ∧
       gitOK filtered ∧ Fs.eqBytes (Git.stdoutOut filtered) selectedPaths ∧
       gitOK saved ∧ Fs.eqBytes (Git.stdoutOut saved) selectedPaths ∧ Fs.eqBytes gitFile selectedPaths) ∷
     ("binary filesystem transform, exact snapshots and one diffSnapshot modification" ,
       Fs.eqObs before (Fs.rawFsObs [] [] nothing false
         (Fs.fsEntries (Fs.initVirtualFs (fsConfig destination) (selectedPaths ∷ [])))) ∧
       Fs.eqObs transformed (Fs.rawFsObs artifact payload (just 0) false []) ∧
       Fs.eqObs after (Fs.rawFsObs [] [] nothing false
         (Fs.fsEntries (Fs.initVirtualFs (fsConfig destination) (artifact ∷ [])))) ∧
       oneModification (Fs.diffSnapshot (Fs.entries before) (Fs.entries after)) ∧ Fs.eqBytes fsFile artifact) ∷
     ("loopback HTTP client response and capturedReqs match exact pure framing" ,
       Net.eqObs exchange (Net.rawNetObs response [] [] (request ∷ []) (just 0) false) ∧
       Net.eqReqViews (map Net.parseHttpReq (Net.capturedReqs exchange))
         (just (Net.httpReqView "POST" "/artifact" payload) ∷ []) ∧
       Fs.eqBytes netFile artifact) ∷ [])

Outer : St
Outer = Dir (("kept" , File Bytes) ∷ [])

-- The type requires every temporary slot to be stopped and removed. The
-- interpreter result below also verifies the outer bytes, including NUL/0xff.
session : SandboxTarget → Prog FullExtΨ Outer Outer (List Check)
session destination = withEphemeral "integration" (pipeline destination)

registry : String → Registry FullExtΨ
registry cwd = fullExtRegistry
  (extRelayPaths (cwd ++ˢ "/tmp/ext-tools-build/fs-relay")
    (cwd ++ˢ "/tmp/ext-tools-build/net-relay")
    (cwd ++ˢ "/tmp/ext-tools-build/git-relay")
    (cwd ++ˢ "/tmp/ext-tools-build/term-relay")) (cwd ++ˢ "/tmp/ext-sandboxes")

report : String → Bool → IO.IO Bool
report label ok = F.putStrLn ((if ok then "PASS " else "FAIL ") ++ˢ label)
  IO.>>= λ _ → IO.return ok

reportAll : List Check → IO.IO Bool
reportAll [] = IO.return true
reportAll ((label , ok) ∷ rest) = report label ok IO.>>= λ first →
  reportAll rest IO.>>= λ remaining → IO.return (first ∧ remaining)

suite : String → SandboxTarget → IO.IO Bool
suite cwd destination = evalIO (select FullExtΨ (registry cwd))
  (session destination) (sentinel , tt) IO.>>= λ result →
  reportAll (proj₂ result) IO.>>= λ checks →
  report "withEphemeral tears down every slot and preserves exact outer linear state"
    (Fs.eqBytes (proj₁ (proj₁ result)) sentinel) IO.>>= λ outerOK →
  IO.return (checks ∧ outerOK)

fzfImage : String
fzfImage = "programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6"

dockerSuite : String → Bool → IO.IO Bool
dockerSuite cwd true = F.putStrLn "Docker omitted by explicit --local-only" IO.>>= λ _ → IO.return true
dockerSuite cwd false = F.putStrLn "Docker unified external tools conformance" IO.>>= λ _ →
  suite cwd (dockerSandbox fzfImage)

main : IO.IO ⊤
main = currentDirectory IO.>>= λ cwd → localOnly IO.>>= λ onlyLocal →
  F.putStrLn "Local unified external tools conformance" IO.>>= λ _ →
  suite cwd localSandbox IO.>>= λ localOK → dockerSuite cwd onlyLocal IO.>>= λ dockerOK →
  if localOK ∧ dockerOK then F.putStrLn "ALL UNIFIED EXTERNAL TOOL TESTS PASS" else exitFailure
