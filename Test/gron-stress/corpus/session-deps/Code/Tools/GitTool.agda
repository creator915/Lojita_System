{-# OPTIONS --guardedness #-}
module Code.Tools.GitTool where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (fromℕ)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _<ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; fromList) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
open import Ownership using (Ctx; Spec; specI; File; Dir; Srv)
open import OwnershipIO using (ModelsIO; ⟦_⟧IO)
open import Context.Terminal using (Byte; Bytes; byte; bytes; SandboxTarget; localSandbox; dockerSandbox)
open import Context.Tools.GitSandbox
open import OwnershipIO.Tools.GitFFI

GitOwnedCtx : GitConfig → Ctx
GitOwnedCtx cfg = map (λ name → name , File Bytes) (ownedFiles cfg)

gitSpec : Spec
gitSpec = specI "gitbox" GitConfig GitOwnedCtx
  (λ cfg → Srv GitStep RawGitObs (Dir (GitOwnedCtx cfg)))

hexBytes : Bytes → String
hexBytes [] = "-"
hexBytes bs = fromList (go bs)
  where
    digit = λ n → fromℕ (if n <ᵇ 10 then 48 + n else 87 + n)
    go : Bytes → List _
    go [] = []
    go (b ∷ rest) = digit (toℕ b / 16) ∷ digit (toℕ b % 16) ∷ go rest

hexText : String → String
hexText s = hexBytes (bytes s)

hexArgs : List String → String
hexArgs [] = ""
hexArgs (a ∷ rest) = " " ++ˢ hexText a ++ˢ hexArgs rest

command : GitStep → String
command (gitWriteFile p bs) = "W " ++ˢ hexText p ++ˢ " " ++ˢ hexBytes bs
command (gitRemoveFile p) = "U " ++ˢ hexText p
command gitStageAll = "A"
command (gitStagePaths ps) = "P " ++ˢ show (length ps) ++ˢ hexArgs ps
command (gitCommit msg offset) = "C " ++ˢ show offset ++ˢ " " ++ˢ hexText msg
command (gitSwitchBranch name create) = "B " ++ˢ (if create then "1" else "0") ++ˢ " " ++ˢ hexText name
command (gitCreateTag name) = "T " ++ˢ hexText name
command gitStatus = "S"
command (gitRunTarget exe args input timeout) = "R " ++ˢ show timeout ++ˢ " " ++ˢ hexText exe
  ++ˢ " " ++ˢ show (length args) ++ˢ hexArgs args ++ˢ " " ++ˢ hexBytes input

decodeSummary : Summary → GitRepoSummary
decodeSummary (wireSummary branch count branches tags staged modified untracked) =
  gitSummary branch count branches tags staged modified untracked

decodeMaybeSummary : Maybe Summary → Maybe GitRepoSummary
decodeMaybeSummary nothing = nothing
decodeMaybeSummary (just s) = just (decodeSummary s)

decodeWire : Wire → RawGitObs
decodeWire (wire out err oid status timeout s) =
  rawGitObs (map byte out) (map byte err) oid status timeout (decodeMaybeSummary s)

ownedContents : (ns : List String) → ModelsIO (map (λ n → n , File Bytes) ns) → List (List ℕ)
ownedContents [] _ = []
ownedContents (_ ∷ ns) (v , vs) = map toℕ v ∷ ownedContents ns vs

restoreContents : (ns : List String) → List (List ℕ) → Maybe (ModelsIO (map (λ n → n , File Bytes) ns))
restoreContents [] [] = just tt
restoreContents (_ ∷ ns) (v ∷ vs) with restoreContents ns vs
... | just rest = just (map byte v , rest)
... | nothing = nothing
restoreContents _ _ = nothing

isDocker : SandboxTarget → Bool
isDocker localSandbox = false
isDocker (dockerSandbox _) = true

imageName : SandboxTarget → String
imageName localSandbox = ""
imageName (dockerSandbox name) = name

gitToolWithCand : String → String → String → ⟦ gitSpec ⟧IO
gitToolWithCand relay cand scratch cfg owned = openGitWithCand relay cand scratch (isDocker (target cfg)) (imageName (target cfg))
  (defaultBranch cfg) (authorName cfg) (authorEmail cfg) (baseEpochSec cfg)
  (map (λ p → proj₁ p ++ˢ "=" ++ˢ proj₂ p) (envVars cfg)) (ownedFiles cfg)
  (ownedContents (ownedFiles cfg) owned) IO.>>= λ handle →
  IO.return (record
    { onCall = λ q → callGit handle (command q) IO.>>= λ response → IO.return (decodeWire response)
    ; onStop = stopGit handle IO.>>= λ values → restore values })
  where
    restore : List (List ℕ) → IO.IO (⊤ × ModelsIO (GitOwnedCtx cfg))
    restore values with restoreContents (ownedFiles cfg) values
    ... | just restored = IO.return (tt , restored)
    ... | nothing = transportError "git returned wrong number of owned files"

gitTool : String → String → ⟦ gitSpec ⟧IO
gitTool relay = gitToolWithCand relay ""
