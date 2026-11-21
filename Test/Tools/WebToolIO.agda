{-# OPTIONS --guardedness #-}
module Test.Tools.WebToolIO where

open import Context.Tools.WebOperad
open import UI.OperadApp
open import Test.Tools.WebOperadConformance using (start; zoomed; modal; fractional; halfScale)
import Context.Terminal as T
open import Code.Tools.WebTool
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin using (toℕ)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; length; drop; take)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat as N using (ℕ; zero; suc; _*_; _+_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _<>_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership using (St; Dir; Chan; Srv; Prog; done; openAs; call; stop; inside; read;
  _>>=_; _>>_; ⊤-inst; ×-inst; ≡-inst)
open import OwnershipIO using (evalIO)
open import OwnershipIO.FFI using (currentDirectory; exitFailure; readProcess; ProcResult; procResult)
open import System.Environment.Primitive using (lookupEnv)

record Check : Set where
  constructor expect
  field name : String
        step : WebStep
        expected : RawWebObs
open Check

equal : RawWebObs → RawWebObs → Bool
equal ack ack = true
equal (frame n d) (frame n′ d′) = (n ≡ᵇ n′) ∧ (d ≡ᵇ d′)
equal (pixelObs true r g b) (pixelObs true r′ g′ b′) = (r ≡ᵇ r′) ∧ (g ≡ᵇ g′) ∧ (b ≡ᵇ b′)
equal (pixelObs false 0 0 0) (pixelObs false 0 0 0) = true
equal _ _ = false

predict : Maybe Colour → RawWebObs
predict nothing = pixelObs false 0 0 0
predict (just (rgb r g b)) = pixelObs true (r N.⊓ 255) (g N.⊓ 255) (b N.⊓ 255)
predict (just defaultColour) = pixelObs true 0 0 0
predict (just (indexed i)) = pixelObs true (i N.⊓ 255) (i N.⊓ 255) (i N.⊓ 255)

samples : ∀ {A} → String → Scene A → List (ℕ × ℕ) → List Check
samples title s = map λ { (x , y) → expect (title <> " (" <> show x <> "," <> show y <> ")") (pixel x y)
  (predict (paintSurfaceColour s (fromPixel (pt (+ x) (+ y))))) }

workbenchFrame : String → AppInstance → List (ℕ × ℕ) → List Check
workbenchFrame title app ps = expect title (flush (renderWorkbenchWire app))
  (frame (length (hostDraw program (liveHost app))) 0) ∷ samples title (appScene app) ps

-- Each full wire includes text and lines. These samples are off the decorative
-- glyphs and edges, including both sides of half-open and fractional boundaries.
workbenchChecks : List Check
workbenchChecks =
  workbenchFrame "split and nodes" start
    ((0 , 0) ∷ (41 , 0) ∷ (42 , 0) ∷ (45 , 0) ∷ (150 , 35) ∷ (150 , 36) ∷ (150 , 39) ∷
     (127 , 40) ∷ (128 , 40) ∷ (131 , 40) ∷ (132 , 40) ∷ (151 , 60) ∷ (152 , 60) ∷
     (225 , 60) ∷ (226 , 60) ∷ (256 , 60) ∷ (257 , 60) ∷ (330 , 60) ∷ (331 , 60) ∷
     (197 , 125) ∷ (197 , 152) ∷ (197 , 153) ∷ []) ++
  workbenchFrame "2x pan and clip" zoomed
    ((127 , 86) ∷ (128 , 86) ∷ (131 , 86) ∷ (132 , 86) ∷ (259 , 86) ∷ (260 , 86) ∷
     (321 , 86) ∷ (322 , 86) ∷ (469 , 86) ∷ (470 , 86) ∷ (450 , 141) ∷ (450 , 142) ∷ []) ++
  workbenchFrame "3/2x" fractional ((319 , 70) ∷ (320 , 70) ∷ (430 , 70) ∷ (431 , 70) ∷ []) ++
  workbenchFrame "1/2x" halfScale ((194 , 50) ∷ (195 , 50) ∷ (231 , 50) ∷ (232 , 50) ∷ []) ++
  workbenchFrame "modal" modal
    ((79 , 90) ∷ (80 , 90) ∷ (100 , 128) ∷ (479 , 232) ∷ (480 , 232) ∷
     (547 , 232) ∷ (548 , 232) ∷ (559 , 268) ∷ (560 , 268) ∷ [])

small : Scene ℕ
small = over (clip (rect (+ 1) (+ 0) 4 3)
  (transform (matrix 2 1 -[1+ 0 ] (+ 1))
    (over (transform (affine 0 0 (+ 1) (+ 0)) (occludeRect (rgb 255 0 129) (rect (+ 0) (+ 0) 2 1)))
          (hitRect 9 (rgb 0 191 254) (rect (+ 0) (+ 0) 4 2)))))
  (hitRect 7 (rgb 12 0 50) (rect (+ 0) (+ 0) 5 4))

allSmall : List (ℕ × ℕ)
allSmall = concatMap (λ y → map (λ x → x , y) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])) (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])

pixelBytes : Maybe Colour → T.Bytes
pixelBytes c with predict c
... | pixelObs _ r g b = map T.byte (r ∷ g ∷ b ∷ [])
... | _ = []

smallPPM : T.Bytes
smallPPM = T.bytes "P6\n6 4\n255\n" ++ concatMap
  (λ { (x , y) → pixelBytes (paintSurfaceColour small (fromPixel (pt (+ x) (+ y)))) }) allSmall

imagePath smallPath binaryPath : String
imagePath = "frames/workbench.ppm"
smallPath = "frames/small.ppm"
binaryPath = "input.bin"

suite : List Check
suite = workbenchChecks ++
  (expect "export workbench" (exportPPM imagePath) ack ∷ expect "resize" (resize 6 4) ack ∷
   expect "resize clears" (pixel 2 1) (pixelObs false 0 0 0) ∷
   expect "nested surface stream" (flush (encodeDrawWire (compileSurfaceDraw small)))
     (frame (length (compileSurfaceDraw small)) 0) ∷ []) ++
  samples "all nested pixels" small allSmall ++ (expect "export small" (exportPPM smallPath) ack ∷ [])

config : T.SandboxTarget → WebConfig
config target = webConfig target 640 360 (imagePath ∷ smallPath ∷ binaryPath ∷ [])

Home Live : WebConfig → St
Home cfg = Dir (("canvas" , Dir (WebOwnedCtx cfg)) ∷ [])
Live cfg = Dir (("canvas" , Chan (Srv WebStep RawWebObs (Dir (WebOwnedCtx cfg)))) ∷ [])

trace : (cfg : WebConfig) → List Check → Prog (webSpec ∷ []) (Live cfg) (Live cfg) (Maybe String)
trace cfg [] = done nothing
trace cfg (c ∷ cs) = call "canvas" (step c) >>= λ actual →
  if equal actual (expected c) then trace cfg cs else done (just (name c))

byteEq : T.Bytes → T.Bytes → Bool
byteEq [] [] = true
byteEq (x ∷ xs) (y ∷ ys) = (toℕ x ≡ᵇ toℕ y) ∧ byteEq xs ys
byteEq _ _ = false

sentinel : T.Bytes
sentinel = map T.byte (0 ∷ 255 ∷ 128 ∷ 10 ∷ [])

checkImages : T.Bytes → T.Bytes → T.Bytes → Bool
checkImages img tiny original = byteEq tiny smallPPM ∧ byteEq original sentinel ∧
  byteEq (take (length header) img) header ∧ (length img ≡ᵇ length header + 640 * 360 * 3) ∧
  byteEq (take 3 (drop (length header + 3 * (128 * 640 + 100)) img))
    (pixelBytes (paintSurfaceColour (appScene modal) (fromPixel (pt (+ 100) (+ 128)))))
  where header = T.bytes "P6\n640 360\n255\n"

-- Read the restored file capabilities through the ordinary linear interpreter.
session : (target : T.SandboxTarget) → Prog (webSpec ∷ []) (Home (config target)) (Home (config target)) (Maybe String)
session target = openAs "canvas" "webcanvas" (config target) >> trace (config target) suite >>= λ result →
  stop "canvas" >> inside "canvas" (inside imagePath read) >>= λ img →
  inside "canvas" (inside smallPath read) >>= λ tiny → inside "canvas" (inside binaryPath read) >>= λ original →
  done (caseResult result img tiny original)
  where
    caseResult : Maybe String → T.Bytes → T.Bytes → T.Bytes → Maybe String
    caseResult (just failure) _ _ _ = just failure
    caseResult nothing img tiny original = if checkImages img tiny original then nothing else just "restored P6 or binary bytes"

runTarget : String → String → T.SandboxTarget → IO.IO ⊤
runTarget cwd targetName target =
  evalIO (selectWeb (viewRegistry (cwd <> "/tmp/term-build/term-relay")
                                 (cwd <> "/tmp/web-build/web-relay") (cwd <> "/tmp/web-sandboxes")))
    (session target) (([] , [] , sentinel , tt) , tt) IO.>>= λ where
      (_ , nothing) → F.putStrLn ("PASS " <> targetName <> " exact pixels and linear P6 restoration")
      (_ , just reason) → F.putStrLn ("FAIL " <> targetName <> " " <> reason) IO.>>= λ _ → exitFailure

fzfImage : String
fzfImage = "programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6"

dockerTests : String → ProcResult → IO.IO ⊤
dockerTests cwd (procResult zero _ _) = runTarget cwd "Docker" (T.dockerSandbox fzfImage)
dockerTests cwd _ = lookupEnv "REQUIRE_DOCKER" IO.>>= λ where
  (just "1") → F.putStrLn "Docker required and unavailable" IO.>>= λ _ → exitFailure
  _ → F.putStrLn "SKIP Docker framebuffer suite (docker info unavailable)"

main : IO.IO ⊤
main = currentDirectory IO.>>= λ cwd → runTarget cwd "local env -i" T.localSandbox IO.>>= λ _ →
  readProcess "/bin/sh" ("-c" ∷ "docker info >/dev/null 2>&1" ∷ []) "" IO.>>= dockerTests cwd
