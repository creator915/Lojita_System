{-# OPTIONS --safe #-}
module Test.Tools.WebOperadConformance where

open import Context.Tools.WebOperad
open import UI.OperadApp
import Context.Terminal as T
open import Data.Bool using (true; false)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Universal obligations, independently of the finite interaction script.
round-trips : ∀ t q r → (inRectQ (applyInv t (applyFwd t q)) r ≡ inRectQ q r) ×
                        (inRectQ (applyFwd t (applyInv t q)) r ≡ inRectQ q r)
round-trips t q r = inRectQ-inv-fwd t q r , inRectQ-fwd-inv t q r

containment : ∀ a b q → subRect a b ≡ true → inRectQ q a ≡ true → inRectQ q b ≡ true
containment a b q fits = subRect-sound {a} {b} fits q

separation : ∀ a b q → disjointRect a b ≡ true → inRectQ q a ≡ true → inRectQ q b ≡ false
separation a b q apart = disjointRect-sound {a} {b} apart q

render-laws : ∀ {A} (s : Scene A) q n → (hitTest s q ≡ paintOwner s q) ×
  (runDrawStack (compileSurfaceDraw s) q ≡ paintSurfaceColour s q) ×
  (stackDelta (compileDraw s) ≡ + 0) × stackSafe n (compileDraw s)
render-laws s q n = visual-hit-consistent s q , draw-machine-sound s q ,
                     compileDraw-balanced s , compileDraw-stackSafe s n

split-laws : ∀ {a b} gap r h-ok v-ok →
  siblingsApart (placeSlots (hsplitOp {a} {b} gap) r h-ok) ×
  siblingsApart (placeSlots (vsplitOp {a} {b} gap) r v-ok)
split-laws {a} {b} gap r ho vo = hsplitOp-disjoint {a} {b} gap r ho , vsplitOp-disjoint {a} {b} gap r vo

private
  c = slotColor (size 3 2) ℕ
  pairOp = hsplitOp {c} {c} 1
  one = buttonOp (size 3 2) "One" blue 1
  two = buttonOp (size 3 2) "Two" active 2
  target = rect -[1+ 2 ] (+ 1) 10 4
  fullTree = compOp pairOp (one ∷ᶠ two ∷ᶠ nil)
  rightGraft = plugOp (there here) pairOp two
  graftedTree = plugOp here rightGraft one

graft-agrees : assemble graftedTree target refl [] ≡ assemble fullTree target refl []
graft-agrees = refl

left-unit : assemble (compOp idOp (pairOp ∷ᶠ nil)) target refl (empty ∷ empty ∷ []) ≡
            assemble pairOp target refl (empty ∷ empty ∷ [])
left-unit = compOp-left-id pairOp target refl (empty ∷ empty ∷ [])

right-unit : ∀ (ss : Scenes (c ∷ c ∷ [])) →
  assemble (compOp pairOp (idForest (c ∷ c ∷ []))) target refl (singletonScenes ss) ≡ assemble pairOp target refl ss
right-unit = compOp-right-id pairOp target refl

negative-half-pixel : inRectQ (qpt -[1+ 0 ] (+ 1) 1) (rect -[1+ 0 ] (+ 0) 1 1) ≡ true
negative-half-pixel = refl

empty-child-away : subRect (rect (+ 500) (+ 90) 0 12) target ≡ true
empty-child-away = refl

start : AppInstance
start = initWorkbench 640 360

model : AppInstance → WorkbenchState
model app = T.state (machine (liveHost app))

chooseLeft : selectedNode (model (clickWorkbench 12 120 start)) ≡ Transport
chooseLeft = refl

changeStage : selectedTree (model (clickWorkbench 51 10 start)) ≡ T1
changeStage = refl

halfScale : AppInstance
halfScale = clickWorkbench 190 12 start

fractional : AppInstance
fractional = clickWorkbench 144 12 start

zoomed : AppInstance
zoomed = panWorkbench 3 6 (panWorkbench 0 60 (clickWorkbench 144 12 fractional))

camera-exact : camera (model zoomed) ≡ matrix 1 0 -[1+ 59 ] (+ 6)
camera-exact = refl

new-node-position : selectedNode (model (clickWorkbench 450 90 zoomed)) ≡ Parser
new-node-position = refl

old-position-clear : hitTest (appScene start) (fromPixel (pt (+ 450) (+ 90))) ≡ nothing
old-position-clear = refl

-- The transformed Root extends to x=112. The viewport starts at x=132;
-- x=130 is in the outer layout gap, inside the window.
clip-blocks-overflow : clickWorkbench 130 90 zoomed ≡ zoomed
clip-blocks-overflow = refl

outside-window : clickWorkbench 640 90 zoomed ≡ zoomed
outside-window = refl

modal : AppInstance
modal = clickWorkbench 304 12 start

covered-control : hitTest (appScene start) (fromPixel (pt (+ 100) (+ 128))) ≡ just (SelectNode Transport)
covered-control = refl

modal-occludes : route (appScene modal) (fromPixel (pt (+ 100) (+ 128))) ≡ blocked
modal-occludes = refl

modal-model-stable : clickWorkbench 100 128 modal ≡ modal
modal-model-stable = refl

close-dialog : modalOpen (model (clickWorkbench 485 237 modal)) ≡ false
close-dialog = refl

armed almost rearmed : AppInstance
armed = clickWorkbench 402 12 start
almost = tickWorkbench 499 armed
rearmed = clickWorkbench 402 12 almost

not-yet : probe (model almost) ≡ waiting
not-yet = refl

deadline : probe (model (tickWorkbench 1 almost)) ≡ verified
deadline = refl

replacement-at-old-deadline : probe (model (tickWorkbench 1 rearmed)) ≡ waiting
replacement-at-old-deadline = refl

replacement-deadline : probe (model (tickWorkbench 500 rearmed)) ≡ verified
replacement-deadline = refl

tiny-viewport : clickWorkbench 12 120 (resizeWorkbench 12 12 start) ≡ resizeWorkbench 12 12 start
tiny-viewport = refl

-- Padding shrinks both dimensions and translates the child within a signed
-- parent. Rendering the margin leaves the underlying canvas untouched.
private
  padded = compOp (padOp {size 3 2} {ℕ} 1) (one ∷ᶠ nil)

padded-origin : hitTest (assemble padded target refl []) (fromPixel (pt -[1+ 1 ] (+ 2))) ≡ just 1
padded-origin = refl

padded-margin : hitTest (assemble padded target refl []) (fromPixel (pt -[1+ 2 ] (+ 2))) ≡ nothing
padded-margin = refl

cache-is-projection : ∀ app → renderWorkbenchWire app ≡ encodeDrawWire (hostDraw program (liveHost app))
cache-is-projection = wire-current

long-idle : T.now (machine (liveHost (tickWorkbench 60000 start))) ≡ 60000
long-idle = refl

long-active : probe (model (tickWorkbench 60000 armed)) ≡ verified
long-active = refl
