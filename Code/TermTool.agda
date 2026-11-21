{-# OPTIONS --guardedness #-}
module Code.TermTool where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (fromℕ)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _<ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Show using (show)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.String using (String; fromList) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
open import Ownership using (Ctx; Spec; specI; File; Dir; Srv)
open import OwnershipIO using (ModelsIO; ⟦_⟧IO)
open import Context.Terminal

TermFiles : TermConfig → Ctx
TermFiles cfg = map (λ n → n , File String) (files cfg)

ptySpec : Spec
ptySpec = specI "pty" TermConfig TermFiles
  (λ cfg → Srv TermStep RawTermObs (Dir (TermFiles cfg)))

open import OwnershipIO.TermFFI

hexBytes : Bytes → String
hexBytes [] = "-"
hexBytes bs = fromList (go bs)
  where
    digit = λ n → fromℕ (if n <ᵇ 10 then 48 + n else 87 + n)
    go : Bytes → List _
    go [] = []
    go (b ∷ rest) = digit (toℕ b / 16) ∷ digit (toℕ b % 16) ∷ go rest

signalNumber : Signal → ℕ
signalNumber sigINT = 2
signalNumber sigTERM = 15
signalNumber sigHUP = 1
signalNumber sigQUIT = 3
signalNumber sigKILL = 9

command : TermStep → String
command (writeStdin bs) = "W " ++ˢ hexBytes bs
command (writeTTY bs) = "T " ++ˢ hexBytes bs
command closeStdin = "C"
command (sleepMs ms) = "S " ++ˢ show ms
command (resizeTTY r c) = "R " ++ˢ show r ++ˢ " " ++ˢ show c
command (sendSignal sig) = "K " ++ˢ show (signalNumber sig)
command drainRaw = "D"

decodeWire : Wire → RawTermObs
decodeWire (wire t o e s) = rawObs (map byte t) (map byte o) (map byte e) s

ownedContents : (ns : List String) → ModelsIO (map (λ n → n , File String) ns) → List String
ownedContents [] _ = []
ownedContents (_ ∷ ns) (v , vs) = v ∷ ownedContents ns vs

restoreContents : (ns : List String) → List String → Maybe (ModelsIO (map (λ n → n , File String) ns))
restoreContents [] [] = just tt
restoreContents (_ ∷ ns) (v ∷ vs) with restoreContents ns vs
... | just rest = just (v , rest)
... | nothing = nothing
restoreContents _ _ = nothing

isDocker : SandboxTarget → Bool
isDocker localSandbox = false
isDocker (dockerSandbox _) = true

imageName : SandboxTarget → String
imageName localSandbox = ""
imageName (dockerSandbox image) = image

isPipe : TermTopology → Bool
isPipe allTTY = false
isPipe pipeStdioWithTTY = true

ptyToolWithCand : String → String → String → ⟦ ptySpec ⟧IO
ptyToolWithCand relay cand scratch cfg owned = openTermWithCand relay cand scratch (isDocker (target cfg)) (imageName (target cfg))
  (isPipe (topology cfg)) (executable cfg) (arguments cfg)
  (map (λ p → proj₁ p ++ˢ "=" ++ˢ proj₂ p) (envVars cfg))
  (rows cfg) (cols cfg) (files cfg) (ownedContents (files cfg) owned) IO.>>= λ handle →
  IO.return (record
    { onCall = λ q → callTerm handle (command q) IO.>>= λ response → IO.return (decodeWire response)
    ; onStop = stopTerm handle IO.>>= λ values → restore values })
  where
    restore : List String → IO.IO (⊤ Data.Product.× ModelsIO (TermFiles cfg))
    restore values with restoreContents (files cfg) values
    ... | just restored = IO.return (tt , restored)
    ... | nothing = transportError "terminal returned wrong number of owned files"

-- Supply this implementation as an EnvIO entry. openAs consumes the owned Dir;
-- stop restores it in place through the existing linear Ownership interpreter.
-- Its return type is ModelIO (Dir (TermFiles cfg)) = ModelsIO (TermFiles cfg).
ptyTool : String → String → ⟦ ptySpec ⟧IO
ptyTool relay = ptyToolWithCand relay ""
