{-# OPTIONS --safe #-}
module UI.OperadApp where

open import Context.Tools.WebOperad
import Context.Terminal as T
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Char using (fromℕ)
open import Data.Fin using (toℕ)
open import Data.Integer.Base as Z using (ℤ; +_)
import Data.Integer.Show as IS
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Maybe.Base using (nothing)
open import Data.Nat as N using (ℕ; zero; suc; _+_; _∸_; _*_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
import Data.Nat.Show as NS
open import Data.String.Base using (String; fromList; unlines; unwords) renaming (_++_ to _<>_)
open import Data.Sum.Base using (_⊎_; [_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

data Tree : Set where T0 T1 T2 : Tree
data Node : Set where Root Parser Transport Sandbox : Node
data ProbeState : Set where idle waiting verified : ProbeState
data TimerTag : Set where probeDue : TimerTag

data WorkbenchMsg : Set where
  SelectTree : Tree → WorkbenchMsg
  SelectNode : Node → WorkbenchMsg
  ZoomIn ZoomOut ResetView ToggleModal CloseModal TriggerProbe : WorkbenchMsg

record WorkbenchState : Set where
  constructor workbench
  field selectedTree : Tree
        selectedNode : Node
        camera : Affine2D
        modalOpen : Bool
        probe : ProbeState
open WorkbenchState public

initial : WorkbenchState
initial = workbench T0 Root idAffine false idle

nodeName : Node → String
nodeName Root = "Root"
nodeName Parser = "Parser"
nodeName Transport = "Transport"
nodeName Sandbox = "Sandbox"

sameNode : Node → Node → Bool
sameNode Root Root = true
sameNode Parser Parser = true
sameNode Transport Transport = true
sameNode Sandbox Sandbox = true
sameNode _ _ = false

sameTree : Tree → Tree → Bool
sameTree T0 T0 = true
sameTree T1 T1 = true
sameTree T2 T2 = true
sameTree _ _ = false

slate active canvas blue paper : Colour
slate = rgb 42 57 72
active = rgb 23 115 103
canvas = rgb 231 239 237
blue = rgb 54 84 127
paper = rgb 246 247 242

Component : Set₁
Component = Widget WorkbenchMsg

button : ℕ → ℕ → String → Colour → WorkbenchMsg → Component
button w h title c m = widget (size w h) (buttonOp (size w h) title c m)

-- The split and stack colours have a sum of message types. Fold the two
-- tagged branches back into the workbench's common action type at each join.
join : ∀ {a b sz} → LayoutOp (slotColor a WorkbenchMsg ∷ slotColor b WorkbenchMsg ∷ [])
                      (slotColor sz (WorkbenchMsg ⊎ WorkbenchMsg)) →
       LayoutOp [] (slotColor a WorkbenchMsg) → LayoutOp [] (slotColor b WorkbenchMsg) → Component
join {sz = sz} op l r = widget sz (compOp (mapMsgOp [ (λ m → m) , (λ m → m) ])
  (compOp op (l ∷ᶠ r ∷ᶠ nil) ∷ᶠ nil))

row column : ℕ → Component → Component → Component
row gap (widget a f) (widget b g) = join (hsplitOp gap) f g
column gap (widget a f) (widget b g) = join (vsplitOp gap) f g

layer : Component → Component → Component
layer (widget a f) (widget b g) = join zstackOp f g

toolbar : WorkbenchState → Component
toolbar s =
  row 3 (stage T0 "T0") (row 3 (stage T1 "T1") (row 3 (stage T2 "T2")
  (row 3 (button 44 36 "+" slate ZoomIn) (row 3 (button 44 36 "-" slate ZoomOut)
  (row 3 (button 62 36 "Reset" slate ResetView) (row 3 (button 86 36 "Details" blue ToggleModal)
  (button 80 36 "Probe" active TriggerProbe)))))))
  where
    stage : Tree → String → Component
    stage t name = button 42 36 name (if sameTree t (selectedTree s) then active else slate) (SelectTree t)

probeText : ProbeState → String
probeText idle = "Probe ready"
probeText waiting = "Checking..."
probeText verified = "Verified"

sidebar : WorkbenchState → Component
sidebar s = column 2 (item Root) (column 2 (item Parser) (column 2 (item Transport)
  (column 2 (item Sandbox) status)))
  where
    item : Node → Component
    item n = button 128 36 (nodeName n) (if sameNode n (selectedNode s) then active else slate) (SelectNode n)
    status : Component
    status = widget (size 128 22) (leafOp (λ r → over
      (decorRect (label (probeText (probe s)) slate) r) (occludeRect paper r)))

at : Rect → ℕ → ℕ → ℕ → ℕ → Rect
at parent x y = rect (rx parent Z.+ (+ x)) (ry parent Z.+ (+ y))

diagram : WorkbenchState → Rect → Scene WorkbenchMsg
diagram s r = over (node Root 20 20 74) (over (node Parser 125 20 74)
  (over (node Transport 65 85 88) (over (node Sandbox 180 85 84) edges′)))
  where
    point : ℕ → ℕ → Point
    point x y = pt (rx r Z.+ (+ x)) (ry r Z.+ (+ y))
    edge : ℕ → ℕ → ℕ → ℕ → Scene WorkbenchMsg
    edge x y u v = decorLine (point x y) (point u v) (rgb 103 126 138)
    arrow : ℕ → ℕ → ℕ → ℕ → Scene WorkbenchMsg
    arrow x y u v = over (edge x y u v) (over (edge (u ∸ 5) (v ∸ 3) u v) (edge (u ∸ 5) (v + 3) u v))
    links : Tree → Scene WorkbenchMsg
    links T0 = arrow 54 48 76 85
    links T1 = arrow 150 48 105 85
    links T2 = arrow 158 48 213 85
    edges′ = over (arrow 94 34 125 34) (over (arrow 153 99 180 99) (links (selectedTree s)))
    node : Node → ℕ → ℕ → ℕ → Scene WorkbenchMsg
    node n x y width = let b = at r x y width 28 in
      over (decorRect (label (nodeName n) paper) b)
           (hitRect (SelectNode n) (if sameNode n (selectedNode s) then active else blue) b)

graph : WorkbenchState → Component
graph s = widget (size 200 140) (compOp (viewportOp (camera s) canvas) (leafOp (diagram s) ∷ᶠ nil))

dialog : Rect → Scene WorkbenchMsg
dialog r = over (decorRect (label "Close" paper) close) (over (hitRect CloseModal active close)
  (over (decorRect (label "Commutative diagram" slate) title) (occludeRect (rgb 209 222 225) panel)))
  where
    panel = at r (rw r / 8) (rh r / 4) (rw r ∸ 2 * (rw r / 8)) (rh r / 2)
    title = at panel 10 8 (rw panel ∸ 20) 26
    close = at panel (rw panel ∸ 80) (rh panel ∸ 38) 68 26

workbenchView : WorkbenchState → Component
workbenchView s with column 4 (toolbar s) (row 4 (sidebar s) (graph s)) | modalOpen s
... | main | false = main
... | main | true = layer (widget (size 0 0) (leafOp dialog)) main

-- Zoom buttons choose among half, one, three-halves and double. Replacing
-- the scale preserves the pan in device pixels (including fractional pan).
private
  -- Euclid's second argument decreases at every remainder. Returning one on
  -- exhausted fuel also preserves the represented similarity.
  gcdFuel : ℕ → ℕ → ℕ → ℕ
  gcdFuel fuel a zero = a
  gcdFuel zero a (suc b) = 1
  gcdFuel (suc fuel) a (suc b) = gcdFuel fuel (suc b) (a % suc b)

  gcd : ℕ → ℕ → ℕ
  gcd a b = gcdFuel b a b

  divide : ℤ → ℕ → ℤ
  divide (+ n) k = + (n / suc k)
  divide (Z.-[1+ n ]) k = Z.- (+ (suc n / suc k))

  reduced : Affine2D → Affine2D
  reduced t with gcd (gcd (suc (num-1 t)) (suc (den-1 t))) (gcd (Z.∣ tx t ∣) (Z.∣ ty t ∣))
  ... | zero = t
  ... | suc k = matrix (suc (num-1 t) / suc k ∸ 1) (suc (den-1 t) / suc k ∸ 1)
                       (divide (tx t) k) (divide (ty t) k)

setScale : ℕ → ℕ → Affine2D → Affine2D
setScale n d t = reduced (matrix (suc n * suc (den-1 t) ∸ 1) (suc d * suc (den-1 t) ∸ 1)
  (tx t Z.* (+ suc d)) (ty t Z.* (+ suc d)))

zoomStep : Bool → Affine2D → Affine2D
zoomStep inward t = choose (suc (num-1 t)) (suc (den-1 t))
  where
    choose : ℕ → ℕ → Affine2D
    choose n d = if inward then
      (if n <ᵇ d then setScale 0 0 t else if (2 * n) <ᵇ (3 * d) then setScale 2 1 t else setScale 1 0 t)
      else (if (3 * d) <ᵇ (2 * n) then setScale 2 1 t else if d <ᵇ n then setScale 0 0 t else setScale 0 1 t)

respond : WorkbenchMsg → WorkbenchState → WebUpdate WorkbenchState TimerTag
respond (SelectTree t) s = webUpdate (record s { selectedTree = t }) []
respond (SelectNode n) s = webUpdate (record s { selectedNode = n }) []
respond ZoomIn s = webUpdate (record s { camera = zoomStep true (camera s) }) []
respond ZoomOut s = webUpdate (record s { camera = zoomStep false (camera s) }) []
respond ResetView s = webUpdate (record s { camera = idAffine }) []
respond ToggleModal s = webUpdate (record s { modalOpen = not (modalOpen s) }) []
respond CloseModal s = webUpdate (record s { modalOpen = false }) []
respond TriggerProbe s = webUpdate (record s { probe = waiting }) (T.cancel 0 ∷ T.arm 0 500 probeDue ∷ [])

workbenchUpdate : WebEvent TimerTag WorkbenchMsg → WorkbenchState → WebUpdate WorkbenchState TimerTag
workbenchUpdate (uiMsg m) = respond m
workbenchUpdate (timerFired probeDue) = λ s → webUpdate (record s { probe = verified }) []
workbenchUpdate (panZoom dx dy n d) = λ s → webUpdate (record s { camera = reduced (compAffine (affine n d dx dy) (camera s)) }) []
workbenchUpdate (keyInput T.escape) = respond CloseModal
workbenchUpdate (keyInput (T.textKey "+")) = respond ZoomIn
workbenchUpdate (keyInput (T.textKey "-")) = respond ZoomOut
workbenchUpdate _ = λ s → webUpdate s []

program : WebProgram WorkbenchState TimerTag WorkbenchMsg
program = webProgram workbenchView workbenchUpdate

hexText : String → String
hexText text with T.bytes text
... | [] = "-"
... | bs = fromList (digits bs)
  where
    nibble = λ n → fromℕ (if n <ᵇ 10 then 48 + n else 87 + n)
    digits : T.Bytes → List _
    digits [] = []
    digits (b ∷ bs) = nibble (toℕ b / 16) ∷ nibble (toℕ b % 16) ∷ digits bs

-- RGB channels saturate at 255. Indexed colours use the grayscale ramp.
colourWire : Colour → String
colourWire (rgb r g b) = unwords (map (λ n → NS.show (n N.⊓ 255)) (r ∷ g ∷ b ∷ []))
colourWire (indexed i) = colourWire (rgb i i i)
colourWire defaultColour = "0 0 0"

rectWire : Rect → String
rectWire r = unwords (IS.show (rx r) ∷ IS.show (ry r) ∷ NS.show (rw r) ∷ NS.show (rh r) ∷ [])

pointWire : Point → String
pointWire p = IS.show (px p) <> " " <> IS.show (py p)

commandWire : DrawCmd → String
commandWire cmdSave = "SAVE"
commandWire cmdRestore = "RESTORE"
commandWire (cmdTransform t) = unwords ("TRANSFORM" ∷ NS.show (suc (num-1 t)) ∷ NS.show (suc (den-1 t))
  ∷ IS.show (tx t) ∷ IS.show (ty t) ∷ [])
commandWire (cmdClip r) = "CLIP " <> rectWire r
commandWire (cmdFillRect c r) = "FILL " <> colourWire c <> " " <> rectWire r
commandWire (cmdStrokeRect c r) = "STROKE " <> colourWire c <> " " <> rectWire r
commandWire (cmdText text c r) = "TEXT " <> colourWire c <> " " <> rectWire r <> " " <> hexText text
commandWire (cmdLine p q c) = "LINE " <> colourWire c <> " " <> pointWire p <> " " <> pointWire q

encodeDrawWire : List DrawCmd → String
encodeDrawWire cs = unlines (map commandWire cs)

record AppInstance : Set where
  constructor instanceOf
  field liveHost : WebHost WorkbenchState TimerTag
        drawWire : String
        wire-current : drawWire ≡ encodeDrawWire (hostDraw program liveHost)
open AppInstance public

redraw : WebHost WorkbenchState TimerTag → AppInstance
redraw live = instanceOf live (encodeDrawWire (hostDraw program live)) refl

initWorkbench : ℕ → ℕ → AppInstance
initWorkbench w h = redraw (host (rect (+ 0) (+ 0) w h) (T.timed 0 initial [] T.emptyObs))

renderWorkbenchWire : AppInstance → String
renderWorkbenchWire = drawWire

appScene : AppInstance → Scene WorkbenchMsg
appScene app = hostScene program (liveHost app)

dispatch : HostInput → AppInstance → AppInstance
dispatch input app = redraw (stepWebHost program input (liveHost app))

clickWorkbench : ℕ → ℕ → AppInstance → AppInstance
clickWorkbench x y = dispatch (hostClick (+ x) (+ y))

panWorkbench : ℕ → ℕ → AppInstance → AppInstance
panWorkbench 0 step = dispatch (hostPanZoom (Z.- (+ step)) (+ 0) 0 0)
panWorkbench 1 step = dispatch (hostPanZoom (+ step) (+ 0) 0 0)
panWorkbench 2 step = dispatch (hostPanZoom (+ 0) (Z.- (+ step)) 0 0)
panWorkbench 3 step = dispatch (hostPanZoom (+ 0) (+ step) 0 0)
panWorkbench 4 _ = dispatch (hostKey (T.textKey "+"))
panWorkbench 5 _ = dispatch (hostKey (T.textKey "-"))
panWorkbench _ _ = dispatch (hostKey T.escape)

-- All business state is in the TimedMachine. During an idle interval the
-- old wire is still the exact projection and can be reused by the browser.
tickWorkbench : ℕ → AppInstance → AppInstance
tickWorkbench n a with clockDue n (machine (liveHost a)) in due
... | true = dispatch (hostTickMs n) a
... | false = instanceOf (stepWebHost program (hostTickMs n) (liveHost a)) (drawWire a)
  (trans (wire-current a) (cong encodeDrawWire (sym (idle-draw program n (liveHost a) due))))

resizeWorkbench : ℕ → ℕ → AppInstance → AppInstance
resizeWorkbench w h = dispatch (hostResize w h)

