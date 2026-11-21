{-# OPTIONS --safe #-}
module Test.Step1WorldTest where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Context.Terminal using (Bytes; bytes; Key; enter; textKey)
open import Context.Tools.FsSandbox using (VirtualFs; virtualFs)
open import Context.Tools.NetSandbox using (httpRoute; encodeHttpReq; parseHttpResp; HttpRespView; respCode; respBody)
open import Context.World

-- 1. Universal Cross-Capability Frame Laws hold DEFINITIONALLY (`refl`)!
frame-clock-fs : ∀ {Δ} (h : clockCap ∈ Δ) (ms : ℕ) (w : SimWorld) →
  fs (proj₂ (runWorldPure (sleepW h ms) w)) ≡ fs w
frame-clock-fs _ _ _ = refl

frame-fs-clock : ∀ {Δ} (h : fsCap ∈ Δ) (p : String) (bs : Bytes) (w : SimWorld) →
  clock (proj₂ (runWorldPure (writeFileW h p bs) w)) ≡ clock w
frame-fs-clock _ _ _ _ = refl

frame-net-fs : ∀ {Δ} (h : netCap ∈ Δ) (host : String) (port : ℕ) (req : Bytes) (tms : ℕ) (w : SimWorld) →
  fs (proj₂ (runWorldPure (tcpExchangeW h host port req false tms) w)) ≡ fs w
frame-net-fs _ _ _ _ _ _ = refl

frame-tty-net : ∀ {Δ} (h : ttyCap ∈ Δ) (bs : Bytes) (w : SimWorld) →
  net (proj₂ (runWorldPure (writeStdoutW h bs) w)) ≡ net w
frame-tty-net _ _ _ = refl

-- 2. Capability Subtyping (`Δ₁ ⊆ Δ₂`) via `liftWorld`
StorageSub : List Cap
StorageSub = fsCap ∷ []

storeSubProgram : String → Bytes → WorldProg StorageSub (FsError ⊎ Bytes)
storeSubProgram p bs =
  writeFileW here p bs >>w readFileW here p

storeInCli : StorageSub ⊆ CliCaps
storeInCli = ⊆-cons fs∈Cli ⊆-nil

cliStoreReadback : CliApp CliCaps
cliStoreReadback =
  getProgNameW env∈Cli >>=w λ prog →
  isTTYStdoutW tty∈Cli >>=w λ isTty →
  liftWorld storeInCli (storeSubProgram "item.json" (bytes "{\"ok\":1}\n")) >>=w λ res →
  dispatch prog isTty res
  where
    dispatch : String → Bool → FsError ⊎ Bytes → CliApp CliCaps
    dispatch _    _     (inj₁ _)  = pure 1
    dispatch prog isTty (inj₂ bs) =
      let out = if isTty then bytes "\ESC[32m" ++ bs else bs
      in writeStdoutW tty∈Cli out >>w pure (if eqStr prog "./ungron" then 0 else 2)
      where open import Data.List using (_++_)
            open import Context.Tools.FsSandbox using (eqStr)

nonTtyWorld : SimWorld
nonTtyWorld = cliSimWorld "./ungron" [] [] false (virtualFs [])

ttyWorld : SimWorld
ttyWorld = cliSimWorld "./ungron" [] [] true (virtualFs [])

test-cli-nonTty-exit : proj₁ (runCliPure cliStoreReadback nonTtyWorld) ≡ 0
test-cli-nonTty-exit = refl

test-cli-nonTty-no-ansi : stdoutBuf (tty (proj₂ (runCliPure cliStoreReadback nonTtyWorld))) ≡ bytes "{\"ok\":1}\n"
test-cli-nonTty-no-ansi = refl

test-cli-tty-ansi : stdoutBuf (tty (proj₂ (runCliPure cliStoreReadback ttyWorld))) ≡ bytes "\ESC[32m{\"ok\":1}\n"
test-cli-tty-ansi = refl

-- 3. Simulated Network Timeout vs Fast Stub Response
netWorld : ℕ → SimWorld
netWorld delayMs =
  record defaultSimWorld
    { net = simNet
        (netEndpoint "127.0.0.1" 8080 false true delayMs
          (httpStubMode (httpRoute "GET" "/ping" 200 "OK" [] (bytes "PONG") ∷ [])) ∷ [])
        [] }
  where open import Context.Tools.NetSandbox using (httpStubMode)

probeHttp : ℕ → CliApp CliCaps
probeHttp timeoutMs =
  tcpExchangeW net∈Cli "127.0.0.1" 8080 (encodeHttpReq "GET" "/ping" [] []) false timeoutMs >>=w finish
  where
    finish : NetError ⊎ Bytes → CliApp CliCaps
    finish (inj₁ netTimedOut) = pure 4
    finish (inj₁ _)           = pure 5
    finish (inj₂ raw) with parseHttpResp raw
    ... | just r  = writeStdoutW tty∈Cli (respBody r) >>w pure 0
    ... | nothing = pure 6

test-net-fast : proj₁ (runCliPure (probeHttp 1000) (netWorld 50)) ≡ 0
test-net-fast = refl

test-net-fast-out : stdoutBuf (tty (proj₂ (runCliPure (probeHttp 1000) (netWorld 50)))) ≡ bytes "PONG"
test-net-fast-out = refl

test-net-timeout : proj₁ (runCliPure (probeHttp 200) (netWorld 500)) ≡ 4
test-net-timeout = refl

-- 4. Pure `--safe` ReactiveApp (Zero `--guardedness`!)
CounterCaps : List Cap
CounterCaps = clockCap ∷ ttyCap ∷ []

counterApp : ReactiveApp CounterCaps ℕ
counterApp = reactiveApp
  (nowMonoW here)
  handle
  where
    handle : Event CounterCaps → ℕ → WorldProg CounterCaps (ℕ ⊎ ExitCode)
    handle (mkEvent _ (evTickMs d)) acc =
      sleepW here d >>w pure (inj₁ (d + acc))
    handle (mkEvent _ (evKey enter)) acc =
      pure (inj₂ acc)
    handle _ acc =
      pure (inj₁ (suc acc))

ev1 ev2 ev3 : Event CounterCaps
ev1 = mkEvent here (evTickMs 10)
ev2 = mkEvent (there here) (evKey (textKey "a"))
ev3 = mkEvent (there here) (evKey enter)

test-reactive-exit : proj₁ (runReactivePure counterApp (ev1 ∷ ev2 ∷ ev3 ∷ []) defaultSimWorld) ≡ inj₂ 11
test-reactive-exit = refl

test-reactive-clock : monoMs (clock (proj₂ (runReactivePure counterApp (ev1 ∷ ev2 ∷ ev3 ∷ []) defaultSimWorld))) ≡ 10
test-reactive-clock = refl
