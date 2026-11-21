{-# OPTIONS --safe #-}
module Test.TermConformance where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context.Terminal

eqBytes : Bytes → Bytes → Bool
eqBytes [] [] = true
eqBytes (a ∷ as) (b ∷ bs) = (toℕ a ≡ᵇ toℕ b) ∧ eqBytes as bs
eqBytes _ _ = false

eqExit : Maybe ℕ → Maybe ℕ → Bool
eqExit nothing nothing = true
eqExit (just a) (just b) = a ≡ᵇ b
eqExit _ _ = false

eqObs : RawTermObs → RawTermObs → Bool
eqObs a b = eqBytes (ttyOut a) (ttyOut b) ∧ eqBytes (stdoutOut a) (stdoutOut b)
  ∧ eqBytes (stderrOut a) (stderrOut b) ∧ eqExit (exitStatus a) (exitStatus b)

tty : String → RawTermObs
tty s = rawObs (bytes s) [] [] nothing

halt : String → ℕ → RawTermObs
halt s n = rawObs (bytes s) [] [] (just n)

stay : ∀ {S E} → S → Effect S E
stay s = effect s emptyObs []

-- A cancellable two-second debounce, independent of host speed.
data Phase : Set where
  idle waiting preempted fired ended : Phase

timing : Handler Phase ⊤
timing e ended = stay ended
timing (input (writeStdin _)) _ = effect waiting (tty "armed\n") (arm 0 2000 tt ∷ [])
timing (input (writeTTY _)) fired = effect fired (tty "late\n") []
timing (input (writeTTY _)) s = effect preempted (tty "preempt\n") (cancel 0 ∷ [])
timing (input (sendSignal sigINT)) _ = effect ended (halt "bye\n" 0) (cancel 0 ∷ [])
timing (timeout _) waiting = effect fired (tty "timeout\n") []
timing _ s = stay s

timerInitial : TimedMachine Phase ⊤
timerInitial = timed 0 idle [] (tty "ready\n")

beforeSteps afterSteps : List TermStep
beforeSteps = drainRaw ∷ writeStdin (bytes "arm\n") ∷ writeTTY (bytes "x") ∷ sleepMs 2000 ∷ sendSignal sigINT ∷ []
afterSteps = drainRaw ∷ writeStdin (bytes "arm\n") ∷ sleepMs 2000 ∷ writeTTY (bytes "x") ∷ sendSignal sigINT ∷ []

preemption-before-sleep : traceTimed timing beforeSteps timerInitial ≡
  (tty "ready\n" ∷ tty "armed\n" ∷ tty "preempt\n" ∷ emptyObs ∷ halt "bye\n" 0 ∷ [])
preemption-before-sleep = refl

timeout-before-input : traceTimed timing afterSteps timerInitial ≡
  (tty "ready\n" ∷ tty "armed\n" ∷ tty "timeout\n" ∷ tty "late\n" ∷ halt "bye\n" 0 ∷ [])
timeout-before-input = refl

armedMachine : TimedMachine Phase ⊤
armedMachine = proj₁ (stepTimed timing (writeStdin (bytes "arm\n")) (timed 0 idle [] emptyObs))

not-early : state (perform timing (sleepMs 1999) armedMachine) ≡ waiting
not-early = refl

deadline-inclusive : state (perform timing (sleepMs 1) (perform timing (sleepMs 1999) armedMachine)) ≡ fired
deadline-inclusive = refl

last-tick-preemption : state (perform timing (sleepMs 1)
  (perform timing (writeTTY (bytes "x")) (perform timing (sleepMs 1999) armedMachine))) ≡ preempted
last-tick-preemption = refl

logical-clock : now (perform timing (sleepMs 2000) timerInitial) ≡ 2000
logical-clock = refl

input-costs-zero : now (perform timing (writeTTY (bytes "x")) timerInitial) ≡ 0
input-costs-zero = refl

recordTimers : Handler (List ℕ) ℕ
recordTimers (timeout n) ns = effect (ns ++ (n ∷ [])) emptyObs []
recordTimers _ ns = stay ns

same-deadline-order : state (advance 1 recordTimers
  (timed 0 [] (editTimers 0 (arm 1 1 11 ∷ arm 2 1 22 ∷ []) []) emptyObs)) ≡ (11 ∷ 22 ∷ [])
same-deadline-order = refl

replace-timer : state (advance 2 recordTimers
  (timed 0 [] (editTimers 0 (arm 1 1 11 ∷ arm 1 2 22 ∷ []) []) emptyObs)) ≡ (22 ∷ [])
replace-timer = refl

zero-delay-next-tick : map deadline (editTimers 7 (arm 0 0 tt ∷ []) []) ≡ (8 ∷ [])
zero-delay-next-tick = refl

-- Candidate records are parsed independently of stdin chunk boundaries.
record PipeState : Set where
  constructor pipeState
  field
    partial query : Bytes
    candidates : List Bytes
    finished : Bool
open PipeState public

prefix : Bytes → Bytes → Bool
prefix [] _ = true
prefix (_ ∷ _) [] = false
prefix (a ∷ as) (b ∷ bs) = (toℕ a ≡ᵇ toℕ b) ∧ prefix as bs

choose : Bytes → List Bytes → Bytes
choose q [] = []
choose q (c ∷ cs) = if prefix q c then c else choose q cs

candidateByte : Byte → PipeState → PipeState × RawTermObs
candidateByte b p = if toℕ b ≡ᵇ 10 then
  (record p { partial = [] ; candidates = candidates p ++ (partial p ∷ []) }
  , rawObs (bytes "candidate:" ++ partial p ++ bytes "\n") [] [] nothing)
  else record p { partial = partial p ++ (b ∷ []) } , emptyObs

keyByte : Byte → PipeState → PipeState × RawTermObs
keyByte b p = if finished p then p , emptyObs else if toℕ b ≡ᵇ 13 then
  record p { finished = true } , rawObs (bytes "chosen\n") (choose (query p) (candidates p) ++ bytes "\n") (bytes "done\n") (just 0)
  else record p { query = query p ++ (b ∷ []) } , rawObs (bytes "key:" ++ (b ∷ []) ++ bytes "\n") [] [] nothing

feed : (Byte → PipeState → PipeState × RawTermObs) → Bytes → PipeState → PipeState × RawTermObs
feed f [] p = p , emptyObs
feed f (b ∷ bs) p with f b p
... | p′ , o with feed f bs p′
...   | p″ , o′ = p″ , appendObs o o′

pipeEffect : PipeState × RawTermObs → Effect PipeState ⊤
pipeEffect (p , o) = effect p o []

pipeHandler : Handler PipeState ⊤
pipeHandler (input (writeStdin bs)) p = pipeEffect (feed candidateByte bs p)
pipeHandler (input (writeTTY bs)) p = pipeEffect (feed keyByte bs p)
pipeHandler (input closeStdin) p = effect p (tty "eof\n") []
pipeHandler _ p = stay p

pipeInitial : TimedMachine PipeState ⊤
pipeInitial = timed 0 (pipeState [] [] [] false) [] (rawObs (bytes "ready\n") [] (bytes "error-channel\n") nothing)

pipeSteps : List TermStep
pipeSteps = drainRaw ∷ writeStdin (bytes "al") ∷ writeStdin (bytes "pha\n") ∷ writeTTY (encodeKey (textKey "b"))
  ∷ writeStdin (bytes "beta\ngamma\n") ∷ closeStdin ∷ writeTTY (encodeKey enter) ∷ []

pipe-selection : stdoutOut (pending (perform pipeHandler (writeTTY (encodeKey enter))
  (perform pipeHandler (writeStdin (bytes "beta\n"))
    (perform pipeHandler (writeTTY (bytes "b")) pipeInitial)))) ≡ bytes "beta\n"
pipe-selection = refl

redraw : Bytes
redraw = bytes "\ESC[2J\ESC[Hstale\ESC[2K\rOK\ESC[2;4H!\ESC[1D?\ESC[1A\ESC[2C#\ESC[2;1frow\ESC[1G>\ESC[0m"

ansiHandler : Handler ⊤ ⊤
ansiHandler (input (writeStdin bs)) s = if eqBytes bs (bytes "draw\n")
  then effect tt (rawObs redraw [] [] nothing) [] else effect tt (halt "" 0) []
ansiHandler _ s = stay s

ansiInitial : TimedMachine ⊤ ⊤
ansiInitial = timed 0 tt [] (tty "ready\n")

ansiSteps : List TermStep
ansiSteps = drainRaw ∷ writeStdin (bytes "draw\n") ∷ writeStdin (bytes "quit\n") ∷ []

redraw-grid : screenLines (stepANSI (blankScreen 3 12) redraw) ≡ ("OK    #     " ∷ ">ow?        " ∷ "            " ∷ [])
redraw-grid = refl

cursor-controls : screenLines (stepANSI (blankScreen 2 5) (bytes "abc\rX\nY\bZ")) ≡ ("Xbc  " ∷ " Z   " ∷ [])
cursor-controls = refl

cursor : Screen → ℕ × ℕ
cursor s = row (active s) , col (active s)

cursor-clamps : let moved = stepANSI (blankScreen 2 5) (bytes "\ESC[99B\ESC[99C")
  in cursor moved ≡ (1 , 4)
cursor-clamps = refl

cursor-defaults : let moved = stepANSI (blankScreen 3 5) (bytes "\ESC[2;2H\ESC[A\ESC[D")
  in cursor moved ≡ (0 , 0)
cursor-defaults = refl

erase-line : screenLines (stepANSI (blankScreen 2 5) (bytes "abc\ESC[2KZ")) ≡ ("   Z " ∷ "     " ∷ [])
erase-line = refl

erase-prefix : screenLines (stepANSI (blankScreen 2 5) (bytes "abc\ESC[2G\ESC[1K")) ≡ ("  c  " ∷ "     " ∷ [])
erase-prefix = refl

erase-suffix : screenLines (stepANSI (blankScreen 2 5) (bytes "abc\ESC[2G\ESC[K")) ≡ ("a    " ∷ "     " ∷ [])
erase-suffix = refl

erase-display : screenLines (stepANSI (blankScreen 2 5) (bytes "abc\ESC[2;1Hxyz\ESC[1;2H\ESC[J")) ≡ ("a    " ∷ "     " ∷ [])
erase-display = refl

erase-display-prefix : screenLines (stepANSI (blankScreen 2 5) (bytes "abc\ESC[2;1Hxyz\ESC[2G\ESC[1J")) ≡ ("     " ∷ "  z  " ∷ [])
erase-display-prefix = refl

-- ED 3 clears saved scrollback, which this grid-only projection does not store.
erase-scrollback-keeps-grid : active (stepANSI (blankScreen 2 5) (bytes "abc\ESC[3J")) ≡ active (stepANSI (blankScreen 2 5) (bytes "abc"))
erase-scrollback-keeps-grid = refl

sgr-attributes : let coloured = stepANSI (blankScreen 1 3) (bytes "\ESC[1;31mX\ESC[0mY")
  in style (getAt (cell ' ' plain) 0 (getAt [] 0 (grid (active coloured)))) ≡ rendition (indexed 1) defaultColour true false false
sgr-attributes = refl

sgr-reset : ink (active (stepANSI (blankScreen 1 3) (bytes "\ESC[1;31mX\ESC[0mY"))) ≡ plain
sgr-reset = refl

alt-restores : active (stepANSI (blankScreen 2 5) (bytes "main\ESC[?1049hother\ESC[?1049l")) ≡ active (stepANSI (blankScreen 2 5) (bytes "main"))
alt-restores = refl

split-escape : stepANSI (stepANSI (blankScreen 2 5) (bytes "ab\ESC[2;")) (bytes "1HX") ≡ stepANSI (blankScreen 2 5) (bytes "ab\ESC[2;1HX")
split-escape = refl

utf8-key : screenLines (stepANSI (blankScreen 1 3) (encodeKey (textKey "λ"))) ≡ ("λ  " ∷ [])
utf8-key = refl

key-arrow : map toℕ (encodeKey up) ≡ (27 ∷ 91 ∷ 65 ∷ [])
key-arrow = refl

key-enter : map toℕ (encodeKey enter) ≡ (13 ∷ [])
key-enter = refl

signalHandler : Handler ⊤ ⊤
signalHandler (input (resizeTTY r c)) s = effect tt (tty ("size:" ++ˢ show r ++ˢ "x" ++ˢ show c ++ˢ "\n")) []
signalHandler (input (sendSignal sigINT)) s = effect tt (rawObs (bytes "interrupt\n") [] (bytes "handled\n") (just 0)) []
signalHandler _ s = stay s

signalInitial : TimedMachine ⊤ ⊤
signalInitial = timed 0 tt [] (tty "size:24x80\n")

signalSteps : List TermStep
signalSteps = drainRaw ∷ resizeTTY 31 97 ∷ sendSignal sigINT ∷ []

fileHandler : Handler ⊤ ⊤
fileHandler _ s = stay s

fileInitial : TimedMachine ⊤ ⊤
fileInitial = timed 0 tt [] (rawObs (bytes "owned\n") (bytes "env:clean:visible\n") (bytes "file:written\n") nothing)

octetsFrom : ℕ → ℕ → Bytes
octetsFrom zero n = []
octetsFrom (suc count) n = byte n ∷ octetsFrom count (suc n)

allOctets : Bytes
allOctets = octetsFrom 256 0

binaryHandler : Handler ⊤ ⊤
binaryHandler (input (writeStdin bs)) s = effect tt (rawObs bs bs bs nothing) []
binaryHandler (input (writeTTY bs)) s = effect tt (rawObs bs [] [] (just 0)) []
binaryHandler _ s = stay s

binarySteps : List TermStep
binarySteps = drainRaw ∷ writeStdin allOctets ∷ writeTTY allOctets ∷ drainRaw ∷ []

allTTYHandler : Handler ⊤ ⊤
allTTYHandler (input (writeStdin bs)) s = effect tt (halt "input\n" 7) []
allTTYHandler _ s = stay s

allTTYInitial : TimedMachine ⊤ ⊤
allTTYInitial = timed 0 tt [] (tty "stdout\nstderr\ntty\n")
