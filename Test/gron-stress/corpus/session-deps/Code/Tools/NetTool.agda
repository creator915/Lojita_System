{-# OPTIONS --guardedness #-}
module Code.Tools.NetTool where

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
open import Context.Tools.NetSandbox
open import OwnershipIO.Tools.NetFFI

NetOwnedCtx : NetConfig → Ctx
NetOwnedCtx cfg = map (λ n → n , File Bytes) (ownedFiles cfg)

netSpec : Spec
netSpec = specI "netbox" NetConfig NetOwnedCtx
  (λ cfg → Srv NetStep RawNetObs (Dir (NetOwnedCtx cfg)))

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

command : NetStep → String
command (runClient exe args input timeout) = "R " ++ˢ show timeout ++ˢ " " ++ˢ hexText exe
  ++ˢ " " ++ˢ show (length args) ++ˢ hexArgs args ++ˢ " " ++ˢ hexBytes input
command (waitPortReady timeout) = "P " ++ˢ show timeout
command (tcpProbe payload timeout) = "C " ++ˢ show timeout ++ˢ " " ++ˢ hexBytes payload
command (httpProbe method path headers payload timeout) = "J " ++ˢ show timeout ++ˢ " "
  ++ˢ hexBytes (encodeHttpReq method path headers payload)
command (udpProbe payload timeout) = "G " ++ˢ show timeout ++ˢ " " ++ˢ hexBytes payload
command (sleepNetMs ms) = "S " ++ˢ show ms
command drainNet = "N"

decodeWire : Wire → RawNetObs
decodeWire (wire out err reply captures status timeout) =
  rawNetObs (map byte out) (map byte err) (map byte reply) (map (map byte) captures) status timeout

encodeRoute : HttpRoute → Route
encodeRoute r = wireRoute (routeMethod r) (routePath r)
  (map toℕ (encodeHttpResp (routeStatus r) (routeReason r) (routeHeaders r) (routeBody r)))

encodeRule : RawStubRule → Rule
encodeRule r = wireRule (map toℕ (matchPrefix r)) (map toℕ (replyPayload r))

-- HTTP, including the fallback, is encoded once by the safe Agda codec.
encodeTopology : NetTopology → Topology
encodeTopology (httpStubMode routes) = wireHttp
  (map toℕ (encodeHttpResp 404 "Not Found" [] [])) (map encodeRoute routes)
encodeTopology (tcpStubMode rules) = wireTcp (map encodeRule rules)
encodeTopology (udpStubMode rules) = wireUdp (map encodeRule rules)
encodeTopology (daemonProbeMode exe args) = wireDaemon exe args
encodeTopology (httpDelayedStubMode ms routes) = wireHttpDelayed ms
  (map toℕ (encodeHttpResp 404 "Not Found" [] [])) (map encodeRoute routes)
encodeTopology (tcpDelayedStubMode ms rules) = wireTcpDelayed ms (map encodeRule rules)

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

netToolWithCand : String → String → String → ⟦ netSpec ⟧IO
netToolWithCand relay cand scratch cfg owned = openNetWithCand relay cand scratch (isDocker (target cfg)) (imageName (target cfg))
  (map (λ p → proj₁ p ++ˢ "=" ++ˢ proj₂ p) (envVars cfg)) (ownedFiles cfg)
  (ownedContents (ownedFiles cfg) owned) (encodeTopology (topology cfg)) IO.>>= λ handle →
  IO.return (record
    { onCall = λ q → callNet handle (command q) IO.>>= λ response → IO.return (decodeWire response)
    ; onStop = stopNet handle IO.>>= λ values → restore values })
  where
    restore : List (List ℕ) → IO.IO (⊤ × ModelsIO (NetOwnedCtx cfg))
    restore values with restoreContents (ownedFiles cfg) values
    ... | just restored = IO.return (tt , restored)
    ... | nothing = transportError "network sandbox returned wrong number of owned files"

netTool : String → String → ⟦ netSpec ⟧IO
netTool relay = netToolWithCand relay ""
