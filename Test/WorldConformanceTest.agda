{-# OPTIONS --guardedness #-}
module Test.WorldConformanceTest where

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length; upTo)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≡ᵇ_)
open import Data.Nat.DivMod using (_%_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Sum using (inj₂)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import System.Environment.Primitive using (getArgs)

open import Ownership using
  ( ≡-inst; St; Dir; Chan; Srv; Prog; withEphemeral; mkdir; openAs; call; stop; rmdir; done; _>>_; _>>=_ )
open import OwnershipIO using (EnvIO; evalIO)
open import OwnershipIO.FFI using (failIO)
open import Code.SessionProtocol using (refSpec; local; docker)
open import Code.SessionTools using (SessionΨ; sessionTools)
open import Code.TermTool using (hexBytes)
open import Context.Terminal using
  ( Bytes; byte; bytes; SandboxTarget; localSandbox; dockerSandbox
  ; TermTopology; allTTY; pipeStdioWithTTY; TermConfig; termConfig
  ; TermStep; writeStdin; writeTTY; closeStdin; sleepMs; resizeTTY; drainRaw
  ; RawTermObs; emptyObs; appendObs; blankScreen )
import Context.Terminal as Term
import Context.Tools.FsSandbox as Fs
import Context.Tools.NetSandbox as Net
open import Context.Tools.FuzzGen using (mkSeed; runGen; genBytes)
open import Context.World
open import Test.WorldFuzzTarget using (fuzzCliApp)
open import Test.WorldReactiveTarget using (RCaps; tty∈RCaps; reactiveCounter)

private
  infixl 1 _>>=ᵢ_ _>>ᵢ_
  _>>=ᵢ_ = IO._>>=_
  _>>ᵢ_ : ∀ {A B : Set} → IO.IO A → IO.IO B → IO.IO B
  m >>ᵢ n = m >>=ᵢ λ _ → n

  assertIO : String → Bool → IO.IO ⊤
  assertIO _   true  = IO.return tt
  assertIO msg false = F.putStrLn ("CONFORMANCE FAILURE:\n" ++ˢ msg) >>ᵢ failIO msg

  showTarget : SandboxTarget → String
  showTarget localSandbox        = "localSandbox"
  showTarget (dockerSandbox img) = "dockerSandbox(" ++ˢ img ++ˢ ")"

  eqMaybeNat : Maybe ℕ → Maybe ℕ → Bool
  eqMaybeNat nothing  nothing  = true
  eqMaybeNat (just a) (just b) = a ≡ᵇ b
  eqMaybeNat _        _        = false

  containsBytes : Bytes → Bytes → Bool
  containsBytes needle [] = Fs.eqBytes needle []
  containsBytes needle haystack@(_ ∷ rest) =
    if Fs.prefixBytes needle haystack then true else containsBytes needle rest

  dropLinkEntry : String → List Fs.FsEntryObs → List Fs.FsEntryObs
  dropLinkEntry _  []       = []
  dropLinkEntry nm (e ∷ es) =
    if Fs.eqStr (Fs.entryPath e) nm then dropLinkEntry nm es else (e ∷ dropLinkEntry nm es)

  genStdinForSeed : ℕ → Bytes
  genStdinForSeed idx =
    let rnd = proj₁ (runGen (genBytes 5) (mkSeed (500 + idx * 73)))
    in if (idx % 4) ≡ᵇ 0 then []
       else if (idx % 4) ≡ᵇ 1 then (bytes "first_‿\n" ++ rnd ++ bytes "\ntail_no_nl")
       else if (idx % 4) ≡ᵇ 2 then (byte 0 ∷ byte 255 ∷ bytes "\nsecond\n")
       else rnd

  ------------------------------------------------------------------------
  -- Suite A: 24 `FuzzGen` Multi-Capability Trials in `fsbox`
  --          (Clock + Symlink argv[0] + Env + Raw Stdin + TTY + VirtualFs Snapshot!)
  ------------------------------------------------------------------------

  runFsFuzzTrial : EnvIO SessionΨ → SandboxTarget → ℕ → IO.IO ⊤
  runFsFuzzTrial env tgt idx =
    let progStr  = if (idx % 2) ≡ᵇ 0 then "./app_a" else "./fuzzlink"
        cliArgs  = show idx ∷ []
        envPairs = ("FUZZ_KEY" , "val_" ++ˢ show idx) ∷ ("EMPTY_KEY" , "") ∷ []
        stdinB   = genStdinForSeed idx
        fixtures = Fs.fixDir "preset" 493
                 ∷ Fs.fixFile "preset/init.txt" 420 (bytes "init_‿\n")
                 ∷ Fs.fixSymlink "app_a" "cand"
                 ∷ Fs.fixSymlink "fuzzlink" "cand"
                 ∷ []
        fsCfg    = Fs.fsConfig tgt envPairs [] fixtures
        initVfs  = Fs.initVirtualFs fsCfg []
        simW     = simWorld
                     (fixedStepClock 10 1700000000000 8 1)
                     (simProcessEnv progStr cliArgs envPairs stdinB)
                     pipeTTY
                     initVfs
                     emptyNet
                     defaultGitRepo
                     emptyCanvasDOM
        pureRes  = runCliPure fuzzCliApp simW
        pureExit = proj₁ pureRes
        pureW′   = proj₂ pureRes
        pureOut  = stdoutBuf (tty pureW′)
        pureErr  = stderrBuf (tty pureW′)
        pureEnts = dropLinkEntry "app_a" (dropLinkEntry "fuzzlink" (Fs.fsEntries (fs pureW′)))

        prog : Prog SessionΨ (Dir []) (Dir []) (Fs.RawFsObs × Fs.RawFsObs)
        prog = withEphemeral "fsRun"
          (mkdir "fs" >> openAs "fs" "fsbox" fsCfg >>
           call "fs" (Fs.runCmd progStr cliArgs stdinB 15000) >>= λ cmdObs →
           call "fs" Fs.snapshotStep >>= λ snapObs →
           stop "fs" >> rmdir "fs" >> done (cmdObs , snapObs))
    in
    evalIO env prog tt >>=ᵢ λ { (_ , cmdObs , snapObs) →
    let realExit = Fs.exitStatus cmdObs
        realOut  = Fs.stdoutOut cmdObs
        realErr  = Fs.stderrOut cmdObs
        realEnts = dropLinkEntry "app_a" (dropLinkEntry "fuzzlink" (Fs.entries snapObs))
        exitOk   = eqMaybeNat realExit (just pureExit)
        outOk    = Fs.eqBytes realOut pureOut
        errOk    = Fs.eqBytes realErr pureErr
        snapOk   = Fs.eqEntries realEnts pureEnts
        diag     = "Suite A [" ++ˢ showTarget tgt ++ˢ "] seed=" ++ˢ show idx
                 ++ˢ " prog=" ++ˢ progStr
                 ++ˢ " pureExit=" ++ˢ show pureExit
                 ++ˢ " outOk=" ++ˢ (if outOk then "1" else "0")
                 ++ˢ " errOk=" ++ˢ (if errOk then "1" else "0")
                 ++ˢ " snapOk=" ++ˢ (if snapOk then "1" else "0")
                 ++ˢ "\nrealOutHex=" ++ˢ hexBytes realOut
                 ++ˢ "\npureOutHex=" ++ˢ hexBytes pureOut
                 ++ˢ "\nrealErrHex=" ++ˢ hexBytes realErr
                 ++ˢ "\npureErrHex=" ++ˢ hexBytes pureErr
    in assertIO diag (exitOk ∧ outOk ∧ errOk ∧ snapOk) }

  runAllSeeds : (ℕ → IO.IO ⊤) → List ℕ → IO.IO ⊤
  runAllSeeds _ []       = IO.return tt
  runAllSeeds f (i ∷ is) = f i >>ᵢ runAllSeeds f is

  ------------------------------------------------------------------------
  -- Suite B: Network + Multi-Capability Conformance in `netbox`
  --          (Fast HTTP Stub + Wire Capture + Closed Port + Invalid Port + Delayed Timeout)
  ------------------------------------------------------------------------

  stubRoutes : List Net.HttpRoute
  stubRoutes =
      Net.httpRoute "GET" "/alpha" 200 "OK" (("X-Mode" , "fast") ∷ []) (bytes "ALPHA_‿")
    ∷ Net.httpRoute "GET" "/beta"  201 "Created" [] (bytes "BETA_λ")
    ∷ []

  candArgv0 : String → SandboxTarget → String
  candArgv0 fuzzBin localSandbox      = fuzzBin
  candArgv0 _       (dockerSandbox _) = "/codetransport-cand"

  runNetFastTrial : String → EnvIO SessionΨ → SandboxTarget → ℕ → IO.IO ⊤
  runNetFastTrial fuzzBin env tgt idx =
    let envPairs = ("FUZZ_KEY" , "net_" ++ˢ show idx) ∷ ("EMPTY_KEY" , "") ∷ []
        stdinB   = bytes "net_line1\nnet_tail"
        netCfg   = Net.netConfig tgt (Net.httpStubMode stubRoutes) envPairs []
        simNetSt = simNet (httpStubEndpoint 18080 stubRoutes ∷ []) []
        simW     = simWorld
                     (fixedStepClock 0 1700000000000 8 1)
                     (simProcessEnv (candArgv0 fuzzBin tgt) (show idx ∷ "18080" ∷ "0" ∷ "1" ∷ []) envPairs stdinB)
                     pipeTTY
                     (Fs.virtualFs [])
                     simNetSt
                     defaultGitRepo
                     emptyCanvasDOM
        pureRes  = runCliPure fuzzCliApp simW
        pureExit = proj₁ pureRes
        pureW′   = proj₂ pureRes

        prog : Prog SessionΨ (Dir []) (Dir []) Net.RawNetObs
        prog = withEphemeral "netFast"
          (mkdir "n" >> openAs "n" "netbox" netCfg >>
           call "n" (Net.waitPortReady 3000) >>
           call "n" (Net.runClient "cand" (show idx ∷ "{{PORT}}" ∷ "0" ∷ "1" ∷ []) stdinB 15000) >>= λ obs →
           stop "n" >> rmdir "n" >> done obs)
    in
    evalIO env prog tt >>=ᵢ λ { (_ , obs) →
    let exitOk = eqMaybeNat (Net.exitStatus obs) (just pureExit)
        outOk  = Fs.eqBytes (Net.stdoutOut obs) (stdoutBuf (tty pureW′))
        errOk  = Fs.eqBytes (Net.stderrOut obs) (stderrBuf (tty pureW′))
        capOk  = length (Net.capturedReqs obs) ≡ᵇ 1
        diag   = "Suite B-Fast [" ++ˢ showTarget tgt ++ˢ "] seed=" ++ˢ show idx
               ++ˢ "\nrealOut=" ++ˢ hexBytes (Net.stdoutOut obs)
               ++ˢ "\npureOut=" ++ˢ hexBytes (stdoutBuf (tty pureW′))
               ++ˢ "\nrealErr=" ++ˢ hexBytes (Net.stderrOut obs)
               ++ˢ "\npureErr=" ++ˢ hexBytes (stderrBuf (tty pureW′))
    in assertIO diag (exitOk ∧ outOk ∧ errOk ∧ capOk) }

  runNetSlowTimeoutTrial : String → EnvIO SessionΨ → SandboxTarget → IO.IO ⊤
  runNetSlowTimeoutTrial fuzzBin env tgt =
    let envPairs = ("FUZZ_KEY" , "slow") ∷ ("EMPTY_KEY" , "") ∷ []
        stdinB   = bytes "timeout_check\n"
        slowTopo = Net.httpDelayedStubMode 650 stubRoutes
        netCfg   = Net.netConfig tgt slowTopo envPairs []
        simNetSt = simNet (netEndpoint "127.0.0.1" 18081 false true 0 slowTopo ∷ []) []
        simW     = simWorld
                     (fixedStepClock 0 1700000000000 8 1)
                     (simProcessEnv (candArgv0 fuzzBin tgt) ("5" ∷ "0" ∷ "18081" ∷ "0" ∷ []) envPairs stdinB)
                     pipeTTY
                     (Fs.virtualFs [])
                     simNetSt
                     defaultGitRepo
                     emptyCanvasDOM
        pureRes  = runCliPure fuzzCliApp simW
        pureExit = proj₁ pureRes
        pureW′   = proj₂ pureRes

        prog : Prog SessionΨ (Dir []) (Dir []) Net.RawNetObs
        prog = withEphemeral "netSlow"
          (mkdir "n" >> openAs "n" "netbox" netCfg >>
           call "n" (Net.waitPortReady 3000) >>
           call "n" (Net.runClient "cand" ("5" ∷ "0" ∷ "{{PORT}}" ∷ "0" ∷ []) stdinB 15000) >>= λ obs →
           stop "n" >> rmdir "n" >> done obs)
    in
    evalIO env prog tt >>=ᵢ λ { (_ , obs) →
    let exitOk = eqMaybeNat (Net.exitStatus obs) (just pureExit)
        outOk  = Fs.eqBytes (Net.stdoutOut obs) (stdoutBuf (tty pureW′))
        errOk  = Fs.eqBytes (Net.stderrOut obs) (stderrBuf (tty pureW′))
        diag   = "Suite B-SlowTimeout [" ++ˢ showTarget tgt ++ˢ "]"
               ++ˢ "\nrealErr=" ++ˢ hexBytes (Net.stderrOut obs)
               ++ˢ "\npureErr=" ++ˢ hexBytes (stderrBuf (tty pureW′))
    in assertIO diag (exitOk ∧ outOk ∧ errOk) }

  ------------------------------------------------------------------------
  -- Suite C: PTY `isTTYStdout` ANSI Toggle & `runReactiveIO` Event Loop
  ------------------------------------------------------------------------

  TermLive : St
  TermLive = Dir (("t" , Chan (Srv TermStep RawTermObs (Dir []))) ∷ [])

  settleTerm : ℕ → RawTermObs → Prog SessionΨ TermLive TermLive RawTermObs
  settleTerm zero    obs = done obs
  settleTerm (suc n) obs with Term.exitStatus obs
  ... | just _  = done obs
  ... | nothing = call "t" (sleepMs 20) >>= λ more → settleTerm n (appendObs obs more)

  maybeClosePipe : TermTopology → Prog SessionΨ TermLive TermLive RawTermObs
  maybeClosePipe pipeStdioWithTTY = call "t" closeStdin
  maybeClosePipe allTTY           = done emptyObs

  runPtyAnsiTrial : String → EnvIO SessionΨ → SandboxTarget → IO.IO ⊤
  runPtyAnsiTrial fuzzBin env tgt =
    let envPairs = ("FUZZ_KEY" , "pty") ∷ ("EMPTY_KEY" , "") ∷ []
        stdinB   = bytes "pty_in\n"
        simPipe  = simWorld
                     (fixedStepClock 0 1700000000000 8 1)
                     (simProcessEnv (candArgv0 fuzzBin tgt) ("2" ∷ []) envPairs stdinB)
                     pipeTTY
                     (Fs.virtualFs [])
                     emptyNet
                     defaultGitRepo
                     emptyCanvasDOM
        purePipe = runCliPure fuzzCliApp simPipe

        -- 2. Interactive TTY (`allTTY`, `isTTYStdout == true` -> emits `\x1b[32mTTY=1\x1b[0m`!)
        ttyCfg   = termConfig tgt allTTY "cand" ("2" ∷ []) envPairs 24 80 []
        simTty   = record simPipe { tty = interactiveTTY 24 80 [] }
        pureTty  = runCliPure fuzzCliApp simTty

        runTerm : TermTopology → Bytes → Prog SessionΨ (Dir []) (Dir []) RawTermObs
        runTerm topo inp = withEphemeral "ptySlot"
          (mkdir "t" >> openAs "t" "pty" (termConfig tgt topo "cand" ("2" ∷ []) envPairs 24 80 []) >>
           call "t" (writeStdin inp) >>= λ a →
           maybeClosePipe topo >>= λ b →
           settleTerm 150 (appendObs a b) >>= λ obs →
           stop "t" >> rmdir "t" >> done obs)
    in
    evalIO env (runTerm pipeStdioWithTTY stdinB) tt >>=ᵢ λ { (_ , obsPipe) →
    evalIO env (runTerm allTTY stdinB) tt >>=ᵢ λ { (_ , obsTty) →
    let okPipeExit = eqMaybeNat (Term.exitStatus obsPipe) (just (proj₁ purePipe))
        okPipeOut  = Fs.eqBytes (Term.stdoutOut obsPipe) (stdoutBuf (tty (proj₂ purePipe)))
        okPipeErr  = Fs.eqBytes (Term.stderrOut obsPipe) (stderrBuf (tty (proj₂ purePipe)))
        okTtyExit  = eqMaybeNat (Term.exitStatus obsTty) (just (proj₁ pureTty))
        okTtyAnsi  = containsBytes (bytes "\x1b[32mTTY=1\x1b[0m") (Term.ttyOut obsTty)
    in assertIO ("Suite C-PTY [" ++ˢ showTarget tgt ++ˢ "]")
         (okPipeExit ∧ okPipeOut ∧ okPipeErr ∧ okTtyExit ∧ okTtyAnsi) }}

  runReactiveTrial : EnvIO SessionΨ → SandboxTarget → IO.IO ⊤
  runReactiveTrial reactEnv tgt =
    let pureEvents : List (Event RCaps)
        pureEvents =
            mkEvent tty∈RCaps (evTTYBytes (bytes "a"))
          ∷ mkEvent tty∈RCaps (evTTYBytes (bytes "b"))
          ∷ mkEvent tty∈RCaps (evResize 30 90)
          ∷ mkEvent tty∈RCaps (evTTYBytes (bytes "q"))
          ∷ []
        pureRes  = runReactivePure reactiveCounter pureEvents defaultSimWorld
        pureOut  = stdoutBuf (tty (proj₂ pureRes))
        pureCode = caseExit (proj₁ pureRes)

        cfg : TermConfig
        cfg = termConfig tgt pipeStdioWithTTY "cand" [] [] 24 80 []

        prog : Prog SessionΨ (Dir []) (Dir []) RawTermObs
        prog = withEphemeral "reactSlot"
          (mkdir "t" >> openAs "t" "pty" cfg >>
           call "t" (sleepMs 80) >>= λ o₀ →
           call "t" (writeTTY (bytes "a")) >>= λ o₁ →
           call "t" (sleepMs 80) >>= λ o₂ →
           call "t" (writeTTY (bytes "b")) >>= λ o₃ →
           call "t" (sleepMs 80) >>= λ o₄ →
           call "t" (resizeTTY 30 90) >>= λ o₅ →
           call "t" (sleepMs 80) >>= λ o₆ →
           call "t" (writeTTY (bytes "q")) >>= λ o₇ →
           settleTerm 150
             (appendObs o₀ (appendObs o₁ (appendObs o₂ (appendObs o₃
               (appendObs o₄ (appendObs o₅ (appendObs o₆ o₇))))))) >>= λ finalObs →
           stop "t" >> rmdir "t" >> done finalObs)
    in
    evalIO reactEnv prog tt >>=ᵢ λ { (_ , obs) →
    let okExit = eqMaybeNat (Term.exitStatus obs) (just pureCode)
        okOut  = Fs.eqBytes (Term.stdoutOut obs) pureOut
        diag   = "Suite C-Reactive [" ++ˢ showTarget tgt ++ˢ "]"
               ++ˢ "\nrealOut=" ++ˢ hexBytes (Term.stdoutOut obs)
               ++ˢ "\npureOut=" ++ˢ hexBytes pureOut
    in assertIO diag (okExit ∧ okOut) }
    where
      caseExit : (ℕ Data.Sum.⊎ ExitCode) → ExitCode
      caseExit (inj₂ c) = c
      caseExit _        = 99

  runSuitesOnTarget : String → EnvIO SessionΨ → EnvIO SessionΨ → SandboxTarget → IO.IO ⊤
  runSuitesOnTarget fuzzBin fuzzEnv reactEnv tgt =
    F.putStrLn ("--- Running Differential Conformance Fuzzing on " ++ˢ showTarget tgt ++ˢ " ---") >>ᵢ
    runAllSeeds (runFsFuzzTrial fuzzEnv tgt) (upTo 24) >>ᵢ
    F.putStrLn ("  [PASS] 24/24 FuzzGen Multi-Cap (Clock + Symlink argv[0] + Env + Raw Stdin + VirtualFs Snapshot) matched 100% byte-for-byte!") >>ᵢ
    runAllSeeds (runNetFastTrial fuzzBin fuzzEnv tgt) (upTo 4) >>ᵢ
    runNetSlowTimeoutTrial fuzzBin fuzzEnv tgt >>ᵢ
    F.putStrLn ("  [PASS] 5/5 Multi-Cap Network (HTTP Stub + Wire Capture + ECONNREFUSED + EINVAL + ETIMEDOUT) matched 100% byte-for-byte!") >>ᵢ
    runPtyAnsiTrial fuzzBin fuzzEnv tgt >>ᵢ
    runReactiveTrial reactEnv tgt >>ᵢ
    F.putStrLn ("  [PASS] PTY ANSI Toggle & ReactiveApp (runReactivePure == runReactiveIO) matched 100% byte-for-byte!")

main : IO.IO ⊤
main = getArgs >>=ᵢ λ where
  (fuzzBin ∷ reactBin ∷ relayBin ∷ scratchDir ∷ dockerImg ∷ []) →
    let localFuzzEnv  = sessionTools (refSpec (local "/bin/cat") [] 30000) fuzzBin  relayBin (scratchDir ++ˢ "/local-fuzz")
        localReactEnv = sessionTools (refSpec (local "/bin/cat") [] 30000) reactBin relayBin (scratchDir ++ˢ "/local-react")
    in
    runSuitesOnTarget fuzzBin localFuzzEnv localReactEnv localSandbox >>ᵢ
    (if Fs.eqStr dockerImg "none" then IO.return tt
     else
       let dockFuzzEnv  = sessionTools (refSpec (docker dockerImg "/bin/cat") [] 30000) fuzzBin  relayBin (scratchDir ++ˢ "/dock-fuzz")
           dockReactEnv = sessionTools (refSpec (docker dockerImg "/bin/cat") [] 30000) reactBin relayBin (scratchDir ++ˢ "/dock-react")
       in runSuitesOnTarget fuzzBin dockFuzzEnv dockReactEnv (dockerSandbox dockerImg)) >>ᵢ
    F.putStrLn "=== ALL WORLD CONFORMANCE DIFFERENTIAL FUZZING GATES PASSED ==="
  _ → failIO "usage: WorldConformanceTest <fuzzCand> <reactiveCand> <termRelay> <scratchDir> <dockerImg|none>"
