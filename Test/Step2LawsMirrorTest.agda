{-# OPTIONS --safe #-}
module Test.Step2LawsMirrorTest where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Context.PolyTransport using (PortRel; idPort; graphPort; TransportsPoly)
open import Context.Terminal using (Bytes; bytes; Screen; stepANSI)
open import Context.Tools.Clock using (SimClock; advanceClock)
open import Context.Tools.ClockLaws using (advanceClock-add; advanceClock-comm; advanceClock-mono≤)
open import Context.Tools.TermLaws using (stepANSI-++)
open import Context.Tools.FsSandbox using (VirtualFs; virtualFs; FsEntryObs; entryPath)
open import Context.Tools.FsLaws using
  ( lookup-insert-same; lookup-insert-other
  ; ValidFlatFile; CanWriteReg; NotSymlink
  ; read-after-write-same; read-after-write-other )
open import Context.Tools.NetSandbox using
  ( HttpReqView; httpReqView; HttpRespView; httpRespView
  ; encodeHttpReq; parseHttpReq; encodeHttpResp; parseHttpResp; wireText )
open import Context.Tools.NetLaws using
  ( ValidHttpToken; NoCR
  ; parseHttpReq-encode-roundtrip; parseHttpResp-encode-roundtrip )
open import Context.Tools.GitSandbox using
  ( PureGitRepo; GitStep; gitStageAll; stepPureGit; projectSummary; modifiedPaths; runPureGit )
open import Context.Tools.GitLaws using
  ( stepPureGit-stageAll-modified-empty; runPureGit-++ )
open import Context.Tools.WebOperad using
  ( Rect; rect; QPoint; Scene; hitTest; paintOwner; visual-hit-consistent )
open import Context.World
open import Context.WorldLaws using
  ( runWorldPure-bind; liftWorld-preserves-run; notHasCap⇒∉
  ; prog-preserves-clock; prog-preserves-fs; prog-preserves-net; prog-preserves-tty )

-- 1. Universal Clock Algebra (`∀ a b c`)
clock-comm-check : ∀ (a b : ℕ) (c : SimClock) →
  advanceClock a (advanceClock b c) ≡ advanceClock b (advanceClock a c)
clock-comm-check = advanceClock-comm

clock-mono-check : ∀ (d : ℕ) (c : SimClock) →
  monoMs c ≤ monoMs (advanceClock d c)
clock-mono-check = advanceClock-mono≤

-- 2. Universal Terminal ANSI Homomorphism (`∀ s a b`)
ansi-hom-check : ∀ (s : Screen) (a b : Bytes) →
  stepANSI s (a ++ b) ≡ stepANSI (stepANSI s a) b
ansi-hom-check = stepANSI-++

-- 3. Universal Filesystem Read-After-Write & Distinct-Path Frame Laws (`∀ p q bs v`)
fs-put-get-check : ∀ (p : String) (bs : Bytes) (v : VirtualFs) →
  ValidFlatFile p ≡ true →
  CanWriteReg p v ≡ true →
  readVirtualFile p (proj₂ (writeVirtualFile p bs v)) ≡ inj₂ bs
fs-put-get-check = read-after-write-same

fs-frame-check : ∀ (p q : String) (bs : Bytes) (v : VirtualFs) →
  ValidFlatFile p ≡ true →
  ValidFlatFile q ≡ true →
  (q ≡ p → ⊥) →
  CanWriteReg p v ≡ true →
  NotSymlink q v ≡ true →
  readVirtualFile q (proj₂ (writeVirtualFile p bs v)) ≡ readVirtualFile q v
fs-frame-check = read-after-write-other

-- Concrete instantiation requires zero boilerplate thanks to Boolean reflection:
concrete-put-get : ∀ (bs : Bytes) →
  readVirtualFile "out.json" (proj₂ (writeVirtualFile "out.json" bs (virtualFs []))) ≡ inj₂ bs
concrete-put-get bs = read-after-write-same "out.json" bs (virtualFs []) refl refl

-- 4. Universal HTTP Request & Response Roundtrip Laws (`∀ body`)
http-req-roundtrip : ∀ (body : Bytes) →
  parseHttpReq (encodeHttpReq "POST" "/api/v1/items" [] body)
    ≡ just (httpReqView "POST" "/api/v1/items" body)
http-req-roundtrip body = parseHttpReq-encode-roundtrip "POST" "/api/v1/items" body refl refl

http-resp-roundtrip : ∀ (body : Bytes) →
  parseHttpResp (encodeHttpResp 200 "OK" [] body)
    ≡ just (httpRespView 200 body)
http-resp-roundtrip body = parseHttpResp-encode-roundtrip 200 "OK" body refl refl

-- 5. Universal Git Stage-All & Step-Concatenation Laws (`∀ repo xs ys`)
git-stage-clean : ∀ (r : PureGitRepo) →
  modifiedPaths (projectSummary (proj₁ (stepPureGit gitStageAll r))) ≡ []
git-stage-clean = stepPureGit-stageAll-modified-empty

git-trace-hom : ∀ (xs ys : List GitStep) (r : PureGitRepo) →
  runPureGit (xs ++ ys) r ≡ runPureGit ys (runPureGit xs r)
git-trace-hom = runPureGit-++

-- 6. Universal WebOperad Scene Visual-Hit Consistency + Record Update on `SimWorld`
web-hit-law : ∀ (s : Scene ℕ) (q : QPoint) →
  hitTest s q ≡ paintOwner s q
web-hit-law = visual-hit-consistent

worldWithCustomViewport : SimWorld → SimWorld
worldWithCustomViewport w =
  record w { web = record (web w) { domViewport = rect (+ 0) (+ 0) 1024 768 } }

-- Definitional `refl` Frame Law on `record w { web = ... }`: `fs` is untouched!
viewport-preserves-fs : ∀ (w : SimWorld) →
  fs (worldWithCustomViewport w) ≡ fs w
viewport-preserves-fs _ = refl

-- 7. Whole-Program Capability Non-Interference (`WorldProg [clockCap , ttyCap]` NEVER touches `fs` or `net`!)
ClockTtyCaps : List Cap
ClockTtyCaps = clockCap ∷ ttyCap ∷ []

noFsInClockTty : fsCap ∈ ClockTtyCaps → ⊥
noFsInClockTty (there (there ()))

noNetInClockTty : netCap ∈ ClockTtyCaps → ⊥
noNetInClockTty = notHasCap⇒∉ refl

subprog-preserves-fs : ∀ {A : Set} (m : WorldProg ClockTtyCaps A) (w : SimWorld) →
  fs (proj₂ (runWorldPure m w)) ≡ fs w
subprog-preserves-fs = prog-preserves-fs noFsInClockTty

subprog-preserves-net : ∀ {A : Set} (m : WorldProg ClockTtyCaps A) (w : SimWorld) →
  net (proj₂ (runWorldPure m w)) ≡ net w
subprog-preserves-net = prog-preserves-net noNetInClockTty

-- 8. Dialectica `PolyTransport` Square over `SimWorld`
exitCodeSquare : ∀ (app : CliApp CliCaps) →
  TransportsPoly
    (graphPort (λ (w : SimWorld) → proj₁ (runCliPure app w)))
    (idPort ExitCode)
    (λ _ → ⊤)
    (λ w → proj₁ (runWorldPure (liftWorld cli⊆All app) w))
    (λ c → c)
exitCodeSquare app w c _ eq = trans (liftWorld-preserves-run-fst app w) eq
  where
    liftWorld-preserves-run-fst : ∀ (m : CliApp CliCaps) (st : SimWorld) →
      proj₁ (runWorldPure (liftWorld cli⊆All m) st) ≡ proj₁ (runCliPure m st)
    liftWorld-preserves-run-fst m st =
      cong proj₁ (liftWorld-preserves-run cli⊆All m st)
