{-# OPTIONS --safe #-}
module Context.Terminal where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Char using (Char; toℕ; fromℕ)
open import Data.Fin using (Fin) renaming (toℕ to octet)
open import Data.List using (List; []; _∷_; _++_; map; reverse; length; replicate; foldl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _⊓_; _⊔_)
open import Data.Nat.DivMod using (_mod_; _/_; _%_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)

-- Bytes are bounded values, never locale-dependent host characters.
Byte : Set
Byte = Fin 256

Bytes : Set
Bytes = List Byte

byte : ℕ → Byte
byte n = n mod 256

utf8Char : Char → Bytes
utf8Char c = enc (toℕ c)
  where
    enc : ℕ → Bytes
    enc n = if n <ᵇ 128 then byte n ∷ [] else
      if n <ᵇ 2048 then byte (192 + n / 64) ∷ byte (128 + n % 64) ∷ [] else
      if n <ᵇ 65536 then byte (224 + n / 4096) ∷ byte (128 + (n / 64) % 64) ∷ byte (128 + n % 64) ∷ [] else
      byte (240 + n / 262144) ∷ byte (128 + (n / 4096) % 64) ∷ byte (128 + (n / 64) % 64) ∷ byte (128 + n % 64) ∷ []

bytes : String → Bytes
bytes s = foldl (λ acc c → acc ++ utf8Char c) [] (toList s)

data Key : Set where
  textKey : String → Key
  enter escape backspace tab up down right left home end delete : Key
  ctrl : Char → Key

encodeKey : Key → Bytes
encodeKey (textKey s) = bytes s
encodeKey enter = byte 13 ∷ []
encodeKey escape = byte 27 ∷ []
encodeKey backspace = byte 127 ∷ []
encodeKey tab = byte 9 ∷ []
encodeKey up = bytes "\ESC[A"
encodeKey down = bytes "\ESC[B"
encodeKey right = bytes "\ESC[C"
encodeKey left = bytes "\ESC[D"
encodeKey home = bytes "\ESC[H"
encodeKey end = bytes "\ESC[F"
encodeKey delete = bytes "\ESC[3~"
encodeKey (ctrl c) = byte (toℕ c % 32) ∷ []

data TermTopology : Set where
  allTTY pipeStdioWithTTY : TermTopology

data SandboxTarget : Set where
  localSandbox : SandboxTarget
  dockerSandbox : String → SandboxTarget

record TermConfig : Set where
  constructor termConfig
  field
    target : SandboxTarget
    topology : TermTopology
    executable : String
    arguments : List String
    envVars : List (String × String)
    rows cols : ℕ
    files : List String
open TermConfig public

data Signal : Set where
  sigINT sigTERM sigHUP sigQUIT sigKILL : Signal

data TermStep : Set where
  writeStdin writeTTY : Bytes → TermStep
  closeStdin : TermStep
  sleepMs : ℕ → TermStep
  resizeTTY : ℕ → ℕ → TermStep
  sendSignal : Signal → TermStep
  drainRaw : TermStep

record RawTermObs : Set where
  constructor rawObs
  field
    ttyOut stdoutOut stderrOut : Bytes
    exitStatus : Maybe ℕ
open RawTermObs public

emptyObs : RawTermObs
emptyObs = rawObs [] [] [] nothing

latest : Maybe ℕ → Maybe ℕ → Maybe ℕ
latest a nothing = a
latest _ (just n) = just n

appendObs : RawTermObs → RawTermObs → RawTermObs
appendObs a b = rawObs (ttyOut a ++ ttyOut b) (stdoutOut a ++ stdoutOut b)
  (stderrOut a ++ stderrOut b) (latest (exitStatus a) (exitStatus b))

-- Logical time is explicit. Inputs cost zero ticks; only sleepMs advances time.
-- A timer is identified by a slot; arming replaces that slot, cancelling removes
-- it. Equal deadlines fire in insertion order. A sleep reaching a deadline fires
-- it before the next external input. An earlier input can cancel/rearm it (插队).
-- Zero-delay timers fire on the next tick: no instantaneous infinite cascade.
data TimerEdit (E : Set) : Set where
  arm : ℕ → ℕ → E → TimerEdit E
  cancel : ℕ → TimerEdit E

record Timer (E : Set) : Set where
  constructor timer
  field
    slot deadline : ℕ
    payload : E
open Timer public

data Event (E : Set) : Set where
  input : TermStep → Event E
  timeout : E → Event E

record Effect (S E : Set) : Set where
  constructor effect
  field
    nextState : S
    output : RawTermObs
    edits : List (TimerEdit E)
open Effect public

record TimedMachine (S E : Set) : Set where
  constructor timed
  field
    now : ℕ
    state : S
    timers : List (Timer E)
    pending : RawTermObs
open TimedMachine public

Handler : Set → Set → Set
Handler S E = Event E → S → Effect S E

removeTimer : ∀ {E} → ℕ → List (Timer E) → List (Timer E)
removeTimer n [] = []
removeTimer n (t ∷ ts) = if n ≡ᵇ slot t then removeTimer n ts else t ∷ removeTimer n ts

insertTimer : ∀ {E} → Timer E → List (Timer E) → List (Timer E)
insertTimer t [] = t ∷ []
insertTimer t (u ∷ us) = if deadline t <ᵇ deadline u then t ∷ u ∷ us else u ∷ insertTimer t us

editTimers : ∀ {E} → ℕ → List (TimerEdit E) → List (Timer E) → List (Timer E)
editTimers n [] ts = ts
editTimers n (cancel k ∷ es) ts = editTimers n es (removeTimer k ts)
editTimers n (arm k delay e ∷ es) ts =
  editTimers n es (insertTimer (timer k (n + (1 ⊔ delay)) e) (removeTimer k ts))

applyEffect : ∀ {S E} → Effect S E → TimedMachine S E → TimedMachine S E
applyEffect e m = timed (now m) (nextState e) (editTimers (now m) (edits e) (timers m))
  (appendObs (pending m) (output e))

-- Fuel is the number of timers at tick entry. Every fired timer is removed;
-- new timers have strictly later deadlines. Recursion is structural throughout.
fireDue : ∀ {S E} → ℕ → Handler S E → TimedMachine S E → TimedMachine S E
fireDue zero h m = m
fireDue (suc fuel) h m with timers m
... | [] = m
... | t ∷ ts = if deadline t ≤ᵇ now m
  then fireDue fuel h (applyEffect (h (timeout (payload t)) (state m)) (record m { timers = ts }))
  else m

advance : ∀ {S E} → ℕ → Handler S E → TimedMachine S E → TimedMachine S E
advance zero h m = m
advance (suc n) h m = advance n h (fireDue (length (timers m)) h (record m { now = suc (now m) }))

perform : ∀ {S E} → Handler S E → TermStep → TimedMachine S E → TimedMachine S E
perform h (sleepMs n) m = advance n h m
perform h q m = applyEffect (h (input q) (state m)) m

observe : ∀ {S E} → TimedMachine S E → TimedMachine S E × RawTermObs
observe m = record m { pending = rawObs [] [] [] (exitStatus (pending m)) } , pending m

stepTimed : ∀ {S E} → Handler S E → TermStep → TimedMachine S E → TimedMachine S E × RawTermObs
stepTimed h q m = observe (perform h q m)

traceTimed : ∀ {S E} → Handler S E → List TermStep → TimedMachine S E → List RawTermObs
traceTimed h [] m = []
traceTimed h (q ∷ qs) m with stepTimed h q m
... | m′ , o = o ∷ traceTimed h qs m′

-- ANSI/VT projection. The parser state belongs to the screen, so splitting an
-- escape sequence or a UTF-8 scalar across raw observations is lossless.
-- Cells have one column per scalar; wide/combining glyph layout is outside this
-- deliberately specified subset. Unknown CSI/ESC controls do not print text.
data Colour : Set where
  defaultColour : Colour
  indexed : ℕ → Colour
  rgb : ℕ → ℕ → ℕ → Colour

record Rendition : Set where
  constructor rendition
  field
    foreground background : Colour
    bold underline inverse : Bool
open Rendition public

plain : Rendition
plain = rendition defaultColour defaultColour false false false

record Cell : Set where
  constructor cell
  field
    glyph : Char
    style : Rendition
open Cell public

record Surface : Set where
  constructor surface
  field
    grid : List (List Cell)
    row col : ℕ
    ink : Rendition
    wrapPending : Bool
open Surface public

data Parser : Set where
  ground escaped osc oscEscape : Parser
  csi : Bool → List ℕ → ℕ → Parser
  utf : ℕ → ℕ → Parser

record Screen : Set where
  constructor screen
  field
    height width : ℕ
    active : Surface
    primary : Maybe Surface
    parser : Parser
open Screen public

blankSurface : ℕ → ℕ → Surface
blankSurface h w = surface (replicate h (replicate w (cell ' ' plain))) 0 0 plain false

blankScreen : ℕ → ℕ → Screen
blankScreen h w = screen (1 ⊔ h) (1 ⊔ w) (blankSurface (1 ⊔ h) (1 ⊔ w)) nothing ground

putAt : ∀ {A : Set} → ℕ → A → List A → List A
putAt n x [] = []
putAt zero x (_ ∷ xs) = x ∷ xs
putAt (suc n) x (y ∷ ys) = y ∷ putAt n x ys

getAt : ∀ {A : Set} → A → ℕ → List A → A
getAt d n [] = d
getAt d zero (x ∷ _) = x
getAt d (suc n) (_ ∷ xs) = getAt d n xs

move : ℕ → ℕ → Screen → Screen
move r c s = record s { active = record (active s)
  { row = r ⊓ (height s ∸ 1) ; col = c ⊓ (width s ∸ 1) ; wrapPending = false } }

lineFeed : Screen → Screen
lineFeed s = if suc (row (active s)) <ᵇ height s then move (suc (row (active s))) (col (active s)) s
  else record s { active = record (active s)
    { grid = scroll (grid (active s)) ; wrapPending = false } }
  where
    scroll : List (List Cell) → List (List Cell)
    scroll [] = []
    scroll (_ ∷ xs) = xs ++ (replicate (width s) (cell ' ' (ink (active s))) ∷ [])

printGlyph : Char → Screen → Screen
printGlyph c s = draw (if wrapPending (active s) then lineFeed (move (row (active s)) 0 s) else s)
  where
    draw : Screen → Screen
    draw t = record t { active = record (active t)
      { grid = putAt (row (active t))
          (putAt (col (active t)) (cell c (ink (active t)))
            (getAt [] (row (active t)) (grid (active t)))) (grid (active t))
      ; col = suc (col (active t)) ⊓ (width t ∸ 1)
      ; wrapPending = suc (col (active t)) ≡ᵇ width t } }

mapIndexed : ∀ {A B : Set} → (ℕ → A → B) → List A → List B
mapIndexed f xs = go 0 xs
  where
    go : ℕ → List _ → List _
    go n [] = []
    go n (x ∷ rest) = f n x ∷ go (suc n) rest

erase : Bool → ℕ → Screen → Screen
erase whole mode s = record s { active = record (active s) { grid = mapIndexed line (grid (active s)) } }
  where
    r = row (active s)
    c = col (active s)
    chosen : ℕ → ℕ → Bool
    chosen y x = if whole then
      ((mode ≡ᵇ 2) ∨ ((mode ≡ᵇ 0) ∧ ((r <ᵇ y) ∨ ((r ≡ᵇ y) ∧ (c ≤ᵇ x))))
      ∨ ((mode ≡ᵇ 1) ∧ ((y <ᵇ r) ∨ ((r ≡ᵇ y) ∧ (x ≤ᵇ c))))) else
      ((y ≡ᵇ r) ∧ ((mode ≡ᵇ 2) ∨ ((mode ≡ᵇ 0) ∧ (c ≤ᵇ x)) ∨ ((mode ≡ᵇ 1) ∧ (x ≤ᵇ c))))
    line : ℕ → List Cell → List Cell
    line y = mapIndexed (λ x v → if chosen y x then cell ' ' (ink (active s)) else v)

sgrOne : ℕ → Rendition → Rendition
sgrOne n a = if n ≡ᵇ 0 then plain else
  if n ≡ᵇ 1 then record a { bold = true } else
  if n ≡ᵇ 22 then record a { bold = false } else
  if n ≡ᵇ 4 then record a { underline = true } else
  if n ≡ᵇ 24 then record a { underline = false } else
  if n ≡ᵇ 7 then record a { inverse = true } else
  if n ≡ᵇ 27 then record a { inverse = false } else
  if n ≡ᵇ 39 then record a { foreground = defaultColour } else
  if n ≡ᵇ 49 then record a { background = defaultColour } else
  if (30 ≤ᵇ n) ∧ (n ≤ᵇ 37) then record a { foreground = indexed (n ∸ 30) } else
  if (40 ≤ᵇ n) ∧ (n ≤ᵇ 47) then record a { background = indexed (n ∸ 40) } else
  if (90 ≤ᵇ n) ∧ (n ≤ᵇ 97) then record a { foreground = indexed (8 + (n ∸ 90)) } else
  if (100 ≤ᵇ n) ∧ (n ≤ᵇ 107) then record a { background = indexed (8 + (n ∸ 100)) } else a

setColour : ℕ → Colour → Rendition → Rendition
setColour n c a = if n ≡ᵇ 38 then record a { foreground = c } else record a { background = c }

sgrFuel : ℕ → List ℕ → Rendition → Rendition
sgrFuel zero ns a = a
sgrFuel (suc fuel) [] a = a
sgrFuel (suc fuel) (n ∷ 5 ∷ c ∷ ns) a = if (n ≡ᵇ 38) ∨ (n ≡ᵇ 48)
  then sgrFuel fuel ns (setColour n (indexed c) a) else sgrFuel fuel (5 ∷ c ∷ ns) (sgrOne n a)
sgrFuel (suc fuel) (n ∷ 2 ∷ r ∷ g ∷ b ∷ ns) a = if (n ≡ᵇ 38) ∨ (n ≡ᵇ 48)
  then sgrFuel fuel ns (setColour n (rgb r g b) a) else sgrFuel fuel (2 ∷ r ∷ g ∷ b ∷ ns) (sgrOne n a)
sgrFuel (suc fuel) (n ∷ ns) a = sgrFuel fuel ns (sgrOne n a)

sgr : List ℕ → Rendition → Rendition
sgr ns = sgrFuel (length ns) ns

altScreen : Bool → Screen → Screen
altScreen true s with primary s
... | just _ = s
... | nothing = record s { active = blankSurface (height s) (width s) ; primary = just (active s) }
altScreen false s with primary s
... | nothing = s
... | just a = record s { active = a ; primary = nothing }

dispatchCSI : Bool → List ℕ → ℕ → Screen → Screen
dispatchCSI true ns cmd s = if getAt 0 0 ns ≡ᵇ 1049 then
  (if cmd ≡ᵇ 104 then altScreen true s else if cmd ≡ᵇ 108 then altScreen false s else s) else s
dispatchCSI false ns cmd s =
  if cmd ≡ᵇ 65 then move (row (active s) ∸ (1 ⊔ getAt 0 0 ns)) (col (active s)) s else
  if cmd ≡ᵇ 66 then move (row (active s) + (1 ⊔ getAt 0 0 ns)) (col (active s)) s else
  if cmd ≡ᵇ 67 then move (row (active s)) (col (active s) + (1 ⊔ getAt 0 0 ns)) s else
  if cmd ≡ᵇ 68 then move (row (active s)) (col (active s) ∸ (1 ⊔ getAt 0 0 ns)) s else
  if cmd ≡ᵇ 71 then move (row (active s)) (getAt 0 0 ns ∸ 1) s else
  if (cmd ≡ᵇ 72) ∨ (cmd ≡ᵇ 102) then move (getAt 0 0 ns ∸ 1) (getAt 0 1 ns ∸ 1) s else
  if cmd ≡ᵇ 74 then erase true (getAt 0 0 ns) s else
  if cmd ≡ᵇ 75 then erase false (getAt 0 0 ns) s else
  if cmd ≡ᵇ 109 then record s { active = record (active s) { ink = sgr ns (ink (active s)) } } else s

groundByte : ℕ → Screen → Screen
groundByte n s = if n ≡ᵇ 27 then record s { parser = escaped } else
  if n ≡ᵇ 13 then move (row (active s)) 0 s else
  if n ≡ᵇ 10 then lineFeed s else
  if n ≡ᵇ 8 then move (row (active s)) (col (active s) ∸ 1) s else
  if n ≡ᵇ 9 then move (row (active s)) ((1 + col (active s) / 8) * 8) s else
  if (32 ≤ᵇ n) ∧ (n <ᵇ 127) then printGlyph (fromℕ n) s else
  if (194 ≤ᵇ n) ∧ (n <ᵇ 224) then record s { parser = utf 1 (n ∸ 192) } else
  if (224 ≤ᵇ n) ∧ (n <ᵇ 240) then record s { parser = utf 2 (n ∸ 224) } else
  if (240 ≤ᵇ n) ∧ (n <ᵇ 245) then record s { parser = utf 3 (n ∸ 240) } else s

ansiByte : Byte → Screen → Screen
ansiByte b s with parser s
... | ground = groundByte (octet b) s
... | escaped = record s { parser = if octet b ≡ᵇ 91 then csi false [] 0 else if octet b ≡ᵇ 93 then osc else ground }
ansiByte b s | osc = record s { parser = if octet b ≡ᵇ 7 then ground else if octet b ≡ᵇ 27 then oscEscape else osc }
ansiByte b s | oscEscape = record s { parser = if octet b ≡ᵇ 92 then ground else osc }
ansiByte b s | csi priv ns n =
  if (48 ≤ᵇ octet b) ∧ (octet b ≤ᵇ 57) then record s { parser = csi priv ns (10 * n + (octet b ∸ 48)) } else
  if octet b ≡ᵇ 59 then record s { parser = csi priv (n ∷ ns) 0 } else
  if octet b ≡ᵇ 63 then record s { parser = csi true ns n } else
  if (64 ≤ᵇ octet b) ∧ (octet b ≤ᵇ 126) then dispatchCSI priv (reverse (n ∷ ns)) (octet b) (record s { parser = ground }) else
  if octet b ≡ᵇ 27 then record s { parser = escaped } else s
ansiByte b s | utf zero n = groundByte (octet b) (record s { parser = ground })
ansiByte b s | utf (suc remaining) n = if (128 ≤ᵇ octet b) ∧ (octet b <ᵇ 192) then
  (if remaining ≡ᵇ 0 then printGlyph (fromℕ (64 * n + (octet b ∸ 128))) (record s { parser = ground })
   else record s { parser = utf remaining (64 * n + (octet b ∸ 128)) })
  else groundByte (octet b) (record s { parser = ground })

stepANSI : Screen → Bytes → Screen
stepANSI = foldl (λ s b → ansiByte b s)

screenLines : Screen → List String
screenLines s = map (λ line → fromList (map glyph line)) (grid (active s))
