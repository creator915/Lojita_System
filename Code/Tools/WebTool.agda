{-# OPTIONS --guardedness #-}
module Code.Tools.WebTool where

open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Product using (_,_; _×_)
open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
open import Context.Terminal using (Bytes; byte; SandboxTarget)
open import Ownership using (Spec; Ctx; File; Srv; Dir; specI; ≡-inst)
open import OwnershipIO using (ModelsIO; EnvIO; ⟦_⟧IO)
open import Code.Driver using (Registry; select; all-cons; all-nil)
open import Code.TermTool using (ptySpec; ptyTool; isDocker; imageName)
open import OwnershipIO.TermFFI using (transportError)
open import OwnershipIO.Tools.WebFFI public using (RawWebObs; ack; frame; pixelObs)
open import OwnershipIO.Tools.WebFFI using (WebHandle; openWeb; callWeb; stopWeb; flushWeb)

record WebConfig : Set where
  constructor webConfig
  field sandbox : SandboxTarget
        width height : ℕ
        ownedFiles : List String
open WebConfig public

data WebStep : Set where
  flush : String → WebStep
  pixel resize : ℕ → ℕ → WebStep
  exportPPM : String → WebStep

WebOwnedCtx : WebConfig → Ctx
WebOwnedCtx cfg = map (λ n → n , File Bytes) (ownedFiles cfg)

webSpec : Spec
webSpec = specI "webcanvas" WebConfig WebOwnedCtx
  (λ cfg → Srv WebStep RawWebObs (Dir (WebOwnedCtx cfg)))

private
  transfer : (ns : List String) → ModelsIO (map (λ n → n , File Bytes) ns) → List (List ℕ)
  transfer [] tt = []
  transfer (_ ∷ ns) (v , vs) = map toℕ v ∷ transfer ns vs

  recover : (ns : List String) → List (List ℕ) → Maybe (ModelsIO (map (λ n → n , File Bytes) ns))
  recover [] [] = just tt
  recover (_ ∷ ns) (v ∷ vs) with recover ns vs
  ... | nothing = nothing
  ... | just rest = just (map byte v , rest)
  recover _ _ = nothing

  serve : WebHandle → WebStep → IO.IO RawWebObs
  serve h (flush wire) = flushWeb h wire
  serve h (pixel x y) = callWeb h ("PIXEL " <> show x <> " " <> show y)
  serve h (resize w h′) = callWeb h ("RESIZE " <> show w <> " " <> show h′)
  serve h (exportPPM path) = callWeb h ("EXPORT_PPM " <> path)

webTool : String → String → ⟦ webSpec ⟧IO
webTool relay scratch cfg owned =
  openWeb relay scratch (isDocker (sandbox cfg)) (imageName (sandbox cfg))
    (width cfg) (height cfg) (ownedFiles cfg) (transfer (ownedFiles cfg) owned) IO.>>= λ h →
  IO.return (record { onCall = serve h ; onStop = stopWeb h IO.>>= restore })
  where
    restore : List (List ℕ) → IO.IO (⊤ × ModelsIO (WebOwnedCtx cfg))
    restore values with recover (ownedFiles cfg) values
    ... | just restored = IO.return (tt , restored)
    ... | nothing = transportError "wrong number of restored web files"

ViewTools : List Spec
ViewTools = ptySpec ∷ webSpec ∷ []

viewRegistry : String → String → String → Registry ViewTools
viewRegistry ptyRelay webRelay scratch = ptyTool ptyRelay scratch ∷ webTool webRelay scratch ∷ []

selectWeb : Registry ViewTools → EnvIO (webSpec ∷ [])
selectWeb = select (webSpec ∷ [])

selectBoth : Registry ViewTools → EnvIO (ptySpec ∷ webSpec ∷ [])
selectBoth = select (ptySpec ∷ webSpec ∷ [])
