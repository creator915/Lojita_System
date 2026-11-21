{-# OPTIONS --guardedness #-}
module Test.ReplayGateTest where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; [_])
open import Data.Maybe using (nothing)
open import Data.Nat using (_≡ᵇ_)
open import Data.String using (String; unlines; lines; toList) renaming (_++_ to _++ˢ_; show to quoteText)
open import Agda.Builtin.Char using (primCharEquality)
open import Data.Unit using (⊤; tt)
open import IO.Primitive using (IO; return; _>>=_)
import IO.Primitive.Finite as F
open import OwnershipIO.FFI using (procResult; currentDirectory; failIO; fileExists; listDirectory)
open import OwnershipIO.MetaFFI using (_>>_; withPrivateTemp)
open import Code using (_==ˢ_; elemᵇ; eqList; filterᵇ; mkQ; unit; ⊥)
open import Code.Transport using (_⇝_)
open import Code.AI using (ScriptedBackend)
open import Code.SessionProtocol
open import Code.SessionRunner using (SessionConfig; sessionConfig; workspace; ActionResult; accepted; rejected; finished; executeAction; runSessionScript)
open import Code.SessionWorkspace using (filesBelow; fingerprint; shaFile)
open import Test.HarnessPure using (submission)
open import Test.SessionFixtures using (probeSource; replaySource)

replayBaseSpec : String
replayBaseSpec = unlines
  ("module Base where"
  ∷ "open import Data.Char using (Char)"
  ∷ "open import Data.List using (List; []; _∷_)"
  ∷ "open import Data.Nat using (ℕ)"
  ∷ "open import Data.String using (fromList; toList)"
  ∷ "open import Context.World using (CliApp; CliCaps; env∈Cli; tty∈Cli; readStdinAllW; writeStdoutW; writeStdoutStrW; decodeUtf8Lossy; _>>=w_; _>>w_; pure)"
  ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl)"
  ∷ "data Tag : Set where"
  ∷ "  item : Tag"
  ∷ "postulate"
  ∷ "  idTag : Tag → Tag"
  ∷ "  buggyApp : CliApp CliCaps"
  ∷ "  echoApp : CliApp CliCaps"
  ∷ "_ : idTag item ≡ item"
  ∷ "_ = refl"
  ∷ [])

replayBaseSource : String
replayBaseSource = unlines
  ("module Base where"
  ∷ "open import Data.Char using (Char)"
  ∷ "open import Data.List using (List; []; _∷_)"
  ∷ "open import Data.Nat using (ℕ)"
  ∷ "open import Data.String using (fromList; toList)"
  ∷ "open import Context.World using (CliApp; CliCaps; env∈Cli; tty∈Cli; readStdinAllW; writeStdoutW; writeStdoutStrW; decodeUtf8Lossy; _>>=w_; _>>w_; pure)"
  ∷ "data Tag : Set where"
  ∷ "  item : Tag"
  ∷ "idTag : Tag → Tag"
  ∷ "idTag item = item"
  ∷ "dropBang : List Char → List Char"
  ∷ "dropBang [] = []"
  ∷ "dropBang ('!' ∷ cs) = dropBang cs"
  ∷ "dropBang (c ∷ cs) = c ∷ dropBang cs"
  ∷ "buggyApp : CliApp CliCaps"
  ∷ "buggyApp = readStdinAllW env∈Cli >>=w λ bs → writeStdoutStrW tty∈Cli (fromList (dropBang (toList (decodeUtf8Lossy bs)))) >>w pure 0"
  ∷ "echoApp : CliApp CliCaps"
  ∷ "echoApp = readStdinAllW env∈Cli >>=w writeStdoutW tty∈Cli >>w pure 0"
  ∷ [])

candProbe : String
candProbe = unlines
  ("{-# OPTIONS --guardedness #-}"
  ∷ "module CandidateProbe where"
  ∷ "open import Data.List using ([])"
  ∷ "open import Data.Product using (_,_)"
  ∷ "open import Data.Unit using (⊤; tt)"
  ∷ "import IO.Primitive as IO"
  ∷ "import IO.Primitive.Finite as F"
  ∷ "open import Ownership"
  ∷ "open import OwnershipIO.FFI using (procResult; exitFailure)"
  ∷ "open import SessionEnv"
  ∷ "probe : Prog SessionΨ (Dir []) (Dir []) ProcOut"
  ∷ "probe = mkdir \"procExec\" >> open′ \"procExec\" >> call \"procExec\" (procReq \"cand\" [] \"abc\") >>= λ out →"
  ∷ "  stop \"procExec\" >> rmdir \"procExec\" >> done out"
  ∷ "main : IO.IO ⊤"
  ∷ "main = evalIO sessionEnv probe tt IO.>>= λ where"
  ∷ "  (_ , procResult 0 \"abc\" \"\") → F.putStrLn \"cand only\""
  ∷ "  _ → exitFailure"
  ∷ [])

-- A script-local seed service drives the corpus. Every attempted deletion runs both binaries.
fuzzSource : String
fuzzSource = unlines
  ("{-# OPTIONS --guardedness #-}"
  ∷ "module FuzzReplay where"
  ∷ "open import Agda.Builtin.String using (primStringEquality)"
  ∷ "open import Data.Bool using (Bool; not; _∧_; if_then_else_)"
  ∷ "open import Data.Char using (Char)"
  ∷ "open import Data.List using (List; []; _∷_; [_]; _++_; length)"
  ∷ "open import Data.List.Relation.Unary.All using ([]; _∷_)"
  ∷ "open import Data.Maybe using (Maybe; just; nothing)"
  ∷ "open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≡ᵇ_)"
  ∷ "open import Data.Nat.DivMod using (_/_; _%_)"
  ∷ "open import Data.Nat.Show using (show)"
  ∷ "open import Data.Product using (_×_; _,_)"
  ∷ "open import Data.String using (String; fromList) renaming (_++_ to _++ˢ_; show to quoteText)"
  ∷ "open import Data.Unit using (⊤; tt)"
  ∷ "import IO.Primitive as IO"
  ∷ "import IO.Primitive.Finite as F"
  ∷ "open import Ownership hiding (withEphemeral)"
  ∷ "open import OwnershipIO.FFI using (procResult; failIO; exitFailure)"
  ∷ "open import SessionEnv using (SessionΨ; sessionEnv; ProcOut; procReq; EnvIO; OfferIO; RunningIO; provideIO; evalIO; withEphemeral)"
  ∷ ""
  ∷ "nextSeed : ℕ → ℕ"
  ∷ "nextSeed n = (5 * n + 1) % 256"
  ∷ ""
  ∷ "seeds : ℕ → Server [] ⊤ ℕ [] (File ℕ)"
  ∷ "ServerI.call (seeds n) = ask λ _ → let k = nextSeed n in tell k (daemon (seeds k))"
  ∷ "ServerI.stop (seeds n) = run (create \"last\" n) λ _ → give∃ tt \"last\" end"
  ∷ ""
  ∷ "SeedS : Session"
  ∷ "SeedS = Srv ⊤ ℕ (File ℕ)"
  ∷ "LocalΨ : List Spec"
  ∷ "LocalΨ = mkSpec \"rng\" [] SeedS ∷ SessionΨ"
  ∷ "startSeeds : ⊤ → IO.IO (OfferIO SeedS)"
  ∷ "startSeeds = provideIO [] (daemon (seeds 7))"
  ∷ "localEnv : EnvIO LocalΨ"
  ∷ "localEnv = (λ _ → startSeeds) ∷ sessionEnv"
  ∷ ""
  ∷ "symbol : ℕ → Char"
  ∷ "symbol 0 = '\\n'"
  ∷ "symbol 1 = '\\t'"
  ∷ "symbol 2 = 'λ'"
  ∷ "symbol 3 = '!'"
  ∷ "symbol 4 = ' '"
  ∷ "symbol 5 = 'a'"
  ∷ "symbol 6 = 'b'"
  ∷ "symbol _ = 'c'"
  ∷ ""
  ∷ "word : ℕ → ℕ → List Char"
  ∷ "word zero n = []"
  ∷ "word (suc k) n = symbol ((n / 16) % 8) ∷ word k (nextSeed n)"
  ∷ ""
  ∷ "RngLive : St"
  ∷ "RngLive = Dir ((\"rng\" , Chan SeedS) ∷ [])"
  ∷ "generate : ℕ → Prog LocalΨ RngLive RngLive (List (List Char))"
  ∷ "generate zero = done []"
  ∷ "generate (suc k) = call \"rng\" tt >>= λ n → generate k >>= λ rest →"
  ∷ "  done (word (3 + n % 9) n ∷ rest)"
  ∷ ""
  ∷ "corpus : Prog LocalΨ (Dir []) (Dir []) (List (List Char) × ℕ)"
  ∷ "corpus = withEphemeral \"fuzz\" (mkdir \"rng\" >> open′ \"rng\" >> generate 32 >>= λ xs →"
  ∷ "  stop \"rng\" >> inside \"rng\" read >>= λ lastSeed → unlink \"rng\" >> done (xs , lastSeed))"
  ∷ ""
  ∷ "pair : String → Prog LocalΨ (Dir []) (Dir []) (ProcOut × ProcOut)"
  ∷ "pair s = mkdir \"procExec\" >> open′ \"procExec\" >> call \"procExec\" (procReq \"ref\" [] s) >>= λ ref →"
  ∷ "  call \"procExec\" (procReq \"cand\" [] s) >>= λ cand → stop \"procExec\" >> rmdir \"procExec\" >> done (ref , cand)"
  ∷ ""
  ∷ "differs : List Char → IO.IO Bool"
  ∷ "differs xs = evalIO localEnv (pair (fromList xs)) tt IO.>>= λ where"
  ∷ "  (_ , procResult 0 ref \"\" , procResult 0 cand \"\") →"
  ∷ "    if primStringEquality ref (fromList xs) then IO.return (not (primStringEquality ref cand))"
  ∷ "    else failIO \"unexpected reference output\""
  ∷ "  _ → failIO \"batch process failed\""
  ∷ ""
  ∷ "scan : List (List Char) → IO.IO (ℕ × Maybe (List Char))"
  ∷ "scan [] = IO.return (0 , nothing)"
  ∷ "scan (x ∷ xs) = differs x IO.>>= λ bad → scan xs IO.>>= λ { (count , witness) →"
  ∷ "  IO.return (suc count , (if bad then just x else witness)) }"
  ∷ ""
  ∷ "shrink : List Char → List Char → IO.IO (List Char)"
  ∷ "shrink kept [] = IO.return kept"
  ∷ "shrink kept (c ∷ rest) = differs (kept ++ rest) IO.>>= λ bad →"
  ∷ "  shrink (if bad then kept else kept ++ [ c ]) rest"
  ∷ ""
  ∷ "report : ℕ × Maybe (List Char) → IO.IO ⊤"
  ∷ "report (count , nothing) = F.putStrLn (\"all cases agree: \" ++ˢ show count)"
  ∷ "report (count , just first) = shrink [] first IO.>>= λ small →"
  ∷ "  differs small IO.>>= λ stillBad → differs [] IO.>>= λ emptyBad →"
  ∷ "  if stillBad ∧ not emptyBad ∧ (length small ≡ᵇ 1) then"
  ∷ "    (F.putStrLn (\"cases=\" ++ˢ show count ++ˢ \" first=\" ++ˢ quoteText (fromList first) ++ˢ"
  ∷ "      \" minimal=\" ++ˢ quoteText (fromList small)) IO.>>= λ _ → exitFailure)"
  ∷ "  else failIO \"shrinking did not find a shortest counterexample\""
  ∷ ""
  ∷ "main : IO.IO ⊤"
  ∷ "main = evalIO localEnv corpus tt IO.>>= λ { (_ , xs , lastSeed) →"
  ∷ "  if lastSeed ≡ᵇ 103 then (scan xs IO.>>= report) else failIO \"unexpected seed at stop\" }"
  ∷ [])

ptyReplay : String
ptyReplay = unlines
  ("{-# OPTIONS --guardedness #-}"
  ∷ "module TerminalReplay where"
  ∷ "open import Agda.Builtin.String using (primStringEquality)"
  ∷ "open import Data.Bool using (Bool; false; _∧_; if_then_else_)"
  ∷ "open import Data.List using ([]; _∷_)"
  ∷ "open import Data.Maybe using (nothing; just)"
  ∷ "open import Data.Nat using (ℕ; zero; suc)"
  ∷ "open import Data.Product using (_,_; proj₂)"
  ∷ "open import Data.String using (String)"
  ∷ "open import Data.Unit using (⊤; tt)"
  ∷ "import IO.Primitive as IO"
  ∷ "import IO.Primitive.Finite as F"
  ∷ "open import Ownership hiding (withEphemeral)"
  ∷ "open import OwnershipIO.FFI using (exitFailure)"
  ∷ "open import Code.TermTool using (hexBytes)"
  ∷ "open import SessionEnv"
  ∷ ""
  ∷ "payload : Bytes"
  ∷ "payload = bytes \"λ!\\nterminal\\n\""
  ∷ "Live : St"
  ∷ "Live = Dir ((\"term\" , Chan (Srv TermStep RawTermObs (Dir []))) ∷ [])"
  ∷ "settle : ℕ → RawTermObs → Prog SessionΨ Live Live RawTermObs"
  ∷ "settle zero obs = done obs"
  ∷ "settle (suc n) obs with exitStatus obs"
  ∷ "... | just _ = done obs"
  ∷ "... | nothing = call \"term\" drainRaw >>= λ more → settle n (appendObs obs more)"
  ∷ ""
  ∷ "observeAlias : String → Prog SessionΨ (Dir []) (Dir []) RawTermObs"
  ∷ "observeAlias alias = mkdir \"term\" >>"
  ∷ "  openAs \"term\" \"pty\" (termConfig localSandbox pipeStdioWithTTY alias [] ((\"LC_ALL\" , \"C.UTF-8\") ∷ []) 24 80 []) >>"
  ∷ "  call \"term\" (writeStdin payload) >>= λ sent → call \"term\" closeStdin >>= λ closed →"
  ∷ "  settle 100 (appendObs sent closed) >>= λ obs → stop \"term\" >> rmdir \"term\" >> done obs"
  ∷ ""
  ∷ "agrees : RawTermObs → RawTermObs → Bool"
  ∷ "agrees (rawObs [] ref [] (just 0)) (rawObs [] cand [] (just 0)) ="
  ∷ "  primStringEquality (hexBytes ref) (hexBytes payload) ∧ primStringEquality (hexBytes cand) (hexBytes ref)"
  ∷ "agrees _ _ = false"
  ∷ "replay : Prog SessionΨ (Dir []) (Dir []) Bool"
  ∷ "replay = observeAlias \"ref\" >>= λ ref → observeAlias \"cand\" >>= λ cand → done (agrees ref cand)"
  ∷ "main : IO.IO ⊤"
  ∷ "main = evalIO sessionEnv replay tt IO.>>= λ r → if proj₂ r then F.putStrLn \"PTY replay passed\" else exitFailure"
  ∷ [])

assert : String → Bool → IO ⊤
assert label true = return tt
assert label false = failIO label

perform : SessionConfig → SessionAction → IO String
perform cfg action = executeAction cfg action >>= λ where
  (accepted msg) → return msg
  (rejected e) → failIO e
  (finished _) → failIO "unexpected finish"

passingScript : SessionConfig → String → String → IO ⊤
passingScript cfg src expected = do
  msg ← perform cfg (run-script expected src)
  assert msg (msg ==ˢ ("observation:\n" ++ˢ expected ++ˢ "\n"))

refused : SessionConfig → String → IO ⊤
refused cfg label = executeAction cfg (finish label) >>= λ where
  (rejected e) → assert (label ++ˢ "\n" ++ˢ e) (e ==ˢ "finish: mandatory real replay missing or stale for current bin/candidate; run a passing run-script that compares both \"ref\" and \"cand\" after the latest build-exe")
  _ → failIO ("finish allowed " ++ˢ label)

unstamped : SessionConfig → String → IO ⊤
unstamped cfg label = do
  exists ← fileExists (workspace cfg ++ˢ "/bin/replayed.sha256")
  assert ("found replay stamp after " ++ˢ label) (not exists)
  refused cfg label
  F.putStrLn ("PASS finish refused " ++ˢ label)

checkFuzz : SessionConfig → IO ⊤
checkFuzz cfg = do
  before ← nonCacheFiles
  procResult status out err ← runSessionScript cfg fuzzSource
  let expected = "cases=32 first=" ++ˢ quoteText "λ!\n" ++ˢ " minimal=" ++ˢ quoteText "!" ++ˢ "\n"
  assert ("fuzz replay\n" ++ˢ out ++ˢ err) ((status ≡ᵇ 1) ∧ (out ==ˢ expected) ∧ (err ==ˢ ""))
  after ← nonCacheFiles
  dirs ← listDirectory (ws ++ˢ "/tmp/scripts")
  assert "fuzz script left resources behind" (eqList _==ˢ_ before after ∧ eqList _==ˢ_ dirs [])
  F.putStr out
  unstamped cfg "a failing two-alias fuzz replay"
  where
    ws = workspace cfg
    hasPrefix : List Char → List Char → Bool
    hasPrefix [] _ = true
    hasPrefix (_ ∷ _) [] = false
    hasPrefix (x ∷ xs) (y ∷ ys) = primCharEquality x y ∧ hasPrefix xs ys
    nonCacheFiles : IO (List String)
    nonCacheFiles = filesBelow ws >>= λ fs →
      return (filterᵇ (λ f → not (hasPrefix (toList (ws ++ˢ "/tmp/ghc-script-cache/")) (toList f))) fs)

checkStamp : String → IO String
checkStamp ws = do
  hash ← shaFile (ws ++ˢ "/bin/candidate")
  inputs ← fingerprint ws
  stamp ← F.readFile (ws ++ˢ "/bin/replayed.sha256")
  assert "replay stamp digest or format" (stamp ==ˢ (hash ++ˢ "\n" ++ˢ inputs))
  return stamp

run : String → String → IO ⊤
run repo ws = do
  let cfg = sessionConfig repo ws "replay gate" (refSpec (local "/bin/cat") [] 30000)
              (ScriptedBackend [])
              (λ _ → ScriptedBackend [ submission "implement identity" replayBaseSource [] [ ⊥ ⇝ unit (mkQ ("Base" ∷ "dropBang" ∷ [])) ] ])
      stampFile = ws ++ˢ "/bin/replayed.sha256"
      exported = ws ++ˢ "/generated/T0/Base.agda"
  executeAction cfg (build-exe "attempt unverified module before drive-tree" "UnverifiedMod.app") >>= λ where
    (rejected e) → assert e (e ==ˢ "build-exe: entry module 'UnverifiedMod' is not exported by any verified (ok) Dialectica tree; verify it via drive-tree first")
    _ → failIO "build-exe accepted unverified module UnverifiedMod.app"
  tree ← perform cfg (drive-tree "T0" "seal fixture" replayBaseSpec [] nothing)
  assert tree (elemᵇ _==ˢ_ "ok T0" (lines tree))
  executeAction cfg (build-exe "attempt unverified module after drive-tree" "UnverifiedMod.app") >>= λ where
    (rejected e) → assert e (e ==ˢ "build-exe: entry module 'UnverifiedMod' is not exported by any verified (ok) Dialectica tree; verify it via drive-tree first")
    _ → failIO "build-exe accepted unverified module UnverifiedMod.app after T0"
  _ ← perform cfg (build-exe "build candidate that drops exclamation marks" "Base.buggyApp")
  unstamped cfg "build without replay"

  passingScript cfg probeSource "batch probe passed"
  unstamped cfg "a ref-only probe"
  passingScript cfg candProbe "cand only"
  unstamped cfg "separate ref-only and cand-only probes"
  checkFuzz cfg

  passingScript cfg replaySource "replay passed"
  genuine ← checkStamp ws
  hash ← shaFile (ws ++ˢ "/bin/candidate")
  inputs ← fingerprint ws
  F.writeFile stampFile ("wrong\n" ++ˢ inputs)
  refused cfg "a stale candidate digest"
  F.writeFile stampFile (hash ++ˢ "\nwrong")
  refused cfg "a stale input fingerprint"
  F.writeFile stampFile genuine
  source ← F.readFile exported
  F.writeFile exported (source ++ˢ "\n-- changed since replay\n")
  refused cfg "a changed generated source"
  F.writeFile exported source
  F.putStrLn "PASS finish rejected each stale digest and a changed generated source"

  _ ← perform cfg (build-exe "restore byte-for-byte echo" "Base.echoApp")
  unstamped cfg "a rebuild after passing batch replay"
  passingScript cfg ptyReplay "PTY replay passed"
  _ ← checkStamp ws
  executeAction cfg (finish "verified PTY replay") >>= λ where
    (finished msg) → assert msg (msg ==ˢ "verified PTY replay")
    (rejected e) → failIO e
    _ → failIO "expected finish after PTY replay"
  F.putStrLn "PASS finish accepted the rebuilt candidate after PTY replay"

main : IO ⊤
main = currentDirectory >>= λ repo → withPrivateTemp (repo ++ˢ "/tmp/replay-gate") (run repo)
