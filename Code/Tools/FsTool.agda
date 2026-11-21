{-# OPTIONS --guardedness #-}
module Code.Tools.FsTool where

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
open import Context.Tools.FsSandbox
open import OwnershipIO.Tools.FsFFI

FsOwnedCtx : FsConfig → Ctx
FsOwnedCtx cfg = map (λ n → n , File Bytes) (ownedFiles cfg)

fsSpec : Spec
fsSpec = specI "fsbox" FsConfig FsOwnedCtx
  (λ cfg → Srv FsStep RawFsObs (Dir (FsOwnedCtx cfg)))

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

command : FsStep → String
command (runCmd exe args input timeout) = "R " ++ˢ show timeout ++ˢ " " ++ˢ hexText exe
  ++ˢ " " ++ˢ show (length args) ++ˢ hexArgs args ++ˢ " " ++ˢ hexBytes input
command (writeFileStep p bs) = "W " ++ˢ hexText p ++ˢ " " ++ˢ hexBytes bs
command (mkdirStep p mode) = "D " ++ˢ hexText p ++ˢ " " ++ˢ show (maskMode mode)
command (symlinkStep p dest) = "L " ++ˢ hexText p ++ˢ " " ++ˢ hexText dest
command (chmodStep p mode) = "M " ++ˢ hexText p ++ˢ " " ++ˢ show (maskMode mode)
command (unlinkStep p) = "U " ++ˢ hexText p
command snapshotStep = "S"

decodeKind : ℕ → FsNodeKind
decodeKind 0 = regularNode
decodeKind 1 = dirNode
decodeKind _ = symlinkNode

decodeEntry : Entry → FsEntryObs
decodeEntry (wireEntry p k mode bs) = fsEntry p (decodeKind k) mode (map byte bs)

decodeWire : Wire → RawFsObs
decodeWire (wire out err status timeout es) = rawFsObs (map byte out) (map byte err) status timeout (map decodeEntry es)

encodeFixture : FsFixture → Fixture
encodeFixture (fixDir p mode) = wireDir p (maskMode mode)
encodeFixture (fixFile p mode bs) = wireFile p (maskMode mode) (map toℕ bs)
encodeFixture (fixSymlink p dest) = wireSymlink p dest

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
imageName (dockerSandbox image) = image

fsToolWithCand : String → String → String → ⟦ fsSpec ⟧IO
fsToolWithCand relay cand scratch cfg owned = openFsWithCand relay cand scratch (isDocker (target cfg)) (imageName (target cfg))
  (map (λ p → proj₁ p ++ˢ "=" ++ˢ proj₂ p) (envVars cfg)) (ownedFiles cfg)
  (ownedContents (ownedFiles cfg) owned) (map encodeFixture (fixtures cfg)) IO.>>= λ handle →
  IO.return (record
    { onCall = λ q → callFs handle (command q) IO.>>= λ response → IO.return (decodeWire response)
    ; onStop = stopFs handle IO.>>= λ values → restore values })
  where
    restore : List (List ℕ) → IO.IO (⊤ × ModelsIO (FsOwnedCtx cfg))
    restore values with restoreContents (ownedFiles cfg) values
    ... | just restored = IO.return (tt , restored)
    ... | nothing = transportError "filesystem returned wrong number of owned files"

-- Ownership's existing interpreter consumes and restores the linear File Bytes.
fsTool : String → String → ⟦ fsSpec ⟧IO
fsTool relay = fsToolWithCand relay ""
