{-# OPTIONS --safe #-}
module Context.World where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Char using (Char; fromℕ; toℕ)
open import Data.Fin using () renaming (toℕ to octet)
open import Data.Integer.Base using (+_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Context.Terminal using
  ( Byte; Bytes; byte; bytes; Key; Signal
  ; SandboxTarget; localSandbox
  ; Screen; blankScreen; stepANSI; screenLines )
open import Context.Tools.Clock public using
  ( SimClock; simClock; monoMs; wallEpochMs; autoTicks
  ; initClock; zeroClock; fixedStepClock
  ; advanceClock; tickClock; readMonoMs; readWallMs; sleepClockMs
  ; deadlineReached; remainingMs )
open import Context.Tools.FsSandbox using
  ( eqStr; all; validRelPath; maskMode; parentPaths; ensureParents
  ; FsNodeKind; regularNode; dirNode; symlinkNode; eqKind
  ; FsEntryObs; fsEntry; entryPath; entryKind; entryMode; entryBytes
  ; VirtualFs; virtualFs; fsEntries; lookupEntry; putEntry; removeEntry; isParent )
open import Context.Tools.NetSandbox using
  ( HttpRoute; RawStubRule; NetTopology
  ; httpStubMode; tcpStubMode; udpStubMode; daemonProbeMode
  ; httpDelayedStubMode; tcpDelayedStubMode
  ; wireText; stubReply )
open import Context.Tools.GitSandbox using
  ( GitConfig; gitConfig; GitStep; GitRepoSummary; PureGitRepo
  ; initPureGit; stepPureGit; projectSummary )
open import Context.Tools.WebOperad using
  ( Point; Size; Rect; rect; QPoint; Scene; DrawCmd; HostInput
  ; compileDraw; hitTest )

------------------------------------------------------------------------
-- §1 Capability Lattice (`Cap`, `_∈_`, `_⊆_`)
------------------------------------------------------------------------

data Cap : Set where
  clockCap envCap ttyCap fsCap netCap gitCap webCap : Cap

eqCap : Cap → Cap → Bool
eqCap clockCap clockCap = true
eqCap envCap   envCap   = true
eqCap ttyCap   ttyCap   = true
eqCap fsCap    fsCap    = true
eqCap netCap   netCap   = true
eqCap gitCap   gitCap   = true
eqCap webCap   webCap   = true
eqCap _        _        = false

infix 4 _∈_ _⊆_

data _∈_ (c : Cap) : List Cap → Set where
  here  : ∀ {cs} → c ∈ (c ∷ cs)
  there : ∀ {d cs} → c ∈ cs → c ∈ (d ∷ cs)

_⊆_ : List Cap → List Cap → Set
Δ₁ ⊆ Δ₂ = ∀ {c} → c ∈ Δ₁ → c ∈ Δ₂

⊆-refl : ∀ {Δ} → Δ ⊆ Δ
⊆-refl h = h

⊆-trans : ∀ {Δ₁ Δ₂ Δ₃} → Δ₁ ⊆ Δ₂ → Δ₂ ⊆ Δ₃ → Δ₁ ⊆ Δ₃
⊆-trans f g h = g (f h)

⊆-nil : ∀ {Δ} → [] ⊆ Δ
⊆-nil ()

⊆-step : ∀ {d Δ₁ Δ₂} → Δ₁ ⊆ Δ₂ → Δ₁ ⊆ (d ∷ Δ₂)
⊆-step sub h = there (sub h)

⊆-cons : ∀ {c Δ₁ Δ₂} → c ∈ Δ₂ → Δ₁ ⊆ Δ₂ → (c ∷ Δ₁) ⊆ Δ₂
⊆-cons hc _   here      = hc
⊆-cons _  sub (there h) = sub h

hasCap : Cap → List Cap → Bool
hasCap _ []       = false
hasCap c (d ∷ ds) = eqCap c d ∨ hasCap c ds

findCap∈ : (c : Cap) → (Δ : List Cap) → Maybe (c ∈ Δ)
findCap∈ _        []              = nothing
findCap∈ clockCap (clockCap ∷ _)  = just here
findCap∈ envCap   (envCap   ∷ _)  = just here
findCap∈ ttyCap   (ttyCap   ∷ _)  = just here
findCap∈ fsCap    (fsCap    ∷ _)  = just here
findCap∈ netCap   (netCap   ∷ _)  = just here
findCap∈ gitCap   (gitCap   ∷ _)  = just here
findCap∈ webCap   (webCap   ∷ _)  = just here
findCap∈ c        (_        ∷ ds) with findCap∈ c ds
... | just m  = just (there m)
... | nothing = nothing

PureCaps : List Cap
PureCaps = []

CliCaps : List Cap
CliCaps = clockCap ∷ envCap ∷ ttyCap ∷ fsCap ∷ netCap ∷ []

AllCaps : List Cap
AllCaps = clockCap ∷ envCap ∷ ttyCap ∷ fsCap ∷ netCap ∷ gitCap ∷ webCap ∷ []

clock∈Cli : clockCap ∈ CliCaps
clock∈Cli = here

env∈Cli : envCap ∈ CliCaps
env∈Cli = there here

tty∈Cli : ttyCap ∈ CliCaps
tty∈Cli = there (there here)

fs∈Cli : fsCap ∈ CliCaps
fs∈Cli = there (there (there here))

net∈Cli : netCap ∈ CliCaps
net∈Cli = there (there (there (there here)))

clock∈All : clockCap ∈ AllCaps
clock∈All = here

env∈All : envCap ∈ AllCaps
env∈All = there here

tty∈All : ttyCap ∈ AllCaps
tty∈All = there (there here)

fs∈All : fsCap ∈ AllCaps
fs∈All = there (there (there here))

net∈All : netCap ∈ AllCaps
net∈All = there (there (there (there here)))

git∈All : gitCap ∈ AllCaps
git∈All = there (there (there (there (there here))))

web∈All : webCap ∈ AllCaps
web∈All = there (there (there (there (there (there here)))))

cli⊆All : CliCaps ⊆ AllCaps
cli⊆All = ⊆-cons clock∈All (⊆-cons env∈All (⊆-cons tty∈All (⊆-cons fs∈All (⊆-cons net∈All ⊆-nil))))

------------------------------------------------------------------------
-- §2 Pure UTF-8 & Deterministic Error Models (`Set₀`)
------------------------------------------------------------------------

decodeUtf8Chars : List ℕ → Maybe (List Char)
decodeUtf8Chars [] = just []
decodeUtf8Chars (b₁ ∷ rest) =
  if b₁ <ᵇ 128 then
    mapMaybeChars (fromℕ b₁) (decodeUtf8Chars rest)
  else if (194 ≤ᵇ b₁) ∧ (b₁ <ᵇ 224) then
    twoByte b₁ rest
  else if (224 ≤ᵇ b₁) ∧ (b₁ <ᵇ 240) then
    threeByte b₁ rest
  else if (240 ≤ᵇ b₁) ∧ (b₁ <ᵇ 245) then
    fourByte b₁ rest
  else nothing
  where
    isCont : ℕ → Bool
    isCont x = (128 ≤ᵇ x) ∧ (x <ᵇ 192)

    mapMaybeChars : Char → Maybe (List Char) → Maybe (List Char)
    mapMaybeChars _ nothing   = nothing
    mapMaybeChars c (just cs) = just (c ∷ cs)

    twoByte : ℕ → List ℕ → Maybe (List Char)
    twoByte _ [] = nothing
    twoByte a (b₂ ∷ rs) =
      if isCont b₂ then
        mapMaybeChars (fromℕ ((a ∸ 192) * 64 + (b₂ ∸ 128))) (decodeUtf8Chars rs)
      else nothing

    threeByte : ℕ → List ℕ → Maybe (List Char)
    threeByte _ [] = nothing
    threeByte _ (_ ∷ []) = nothing
    threeByte a (b₂ ∷ b₃ ∷ rs) =
      let cp = (a ∸ 224) * 4096 + (b₂ ∸ 128) * 64 + (b₃ ∸ 128)
          surrogate = (55296 ≤ᵇ cp) ∧ (cp <ᵇ 57344)
      in if isCont b₂ ∧ isCont b₃ ∧ (2048 ≤ᵇ cp) ∧ not surrogate then
           mapMaybeChars (fromℕ cp) (decodeUtf8Chars rs)
         else nothing

    fourByte : ℕ → List ℕ → Maybe (List Char)
    fourByte _ [] = nothing
    fourByte _ (_ ∷ []) = nothing
    fourByte _ (_ ∷ _ ∷ []) = nothing
    fourByte a (b₂ ∷ b₃ ∷ b₄ ∷ rs) =
      let cp = (a ∸ 240) * 262144 + (b₂ ∸ 128) * 4096 + (b₃ ∸ 128) * 64 + (b₄ ∸ 128)
      in if isCont b₂ ∧ isCont b₃ ∧ isCont b₄ ∧ (65536 ≤ᵇ cp) ∧ (cp <ᵇ 1114112) then
           mapMaybeChars (fromℕ cp) (decodeUtf8Chars rs)
         else nothing

decodeUtf8 : Bytes → Maybe String
decodeUtf8 bs = toStr (decodeUtf8Chars (map octet bs))
  where
    toStr : Maybe (List Char) → Maybe String
    toStr nothing   = nothing
    toStr (just cs) = just (fromList cs)

decodeUtf8LossyChars : List ℕ → List Char
decodeUtf8LossyChars [] = []
decodeUtf8LossyChars (b₁ ∷ rest) =
  if b₁ <ᵇ 128 then
    fromℕ b₁ ∷ decodeUtf8LossyChars rest
  else if (194 ≤ᵇ b₁) ∧ (b₁ <ᵇ 224) then
    twoL b₁ rest
  else if (224 ≤ᵇ b₁) ∧ (b₁ <ᵇ 240) then
    threeL b₁ rest
  else if (240 ≤ᵇ b₁) ∧ (b₁ <ᵇ 245) then
    fourL b₁ rest
  else fromℕ 65533 ∷ decodeUtf8LossyChars rest
  where
    isCont : ℕ → Bool
    isCont x = (128 ≤ᵇ x) ∧ (x <ᵇ 192)

    twoL : ℕ → List ℕ → List Char
    twoL _ [] = fromℕ 65533 ∷ []
    twoL a (b₂ ∷ rs) =
      if isCont b₂ then fromℕ ((a ∸ 192) * 64 + (b₂ ∸ 128)) ∷ decodeUtf8LossyChars rs
      else fromℕ 65533 ∷ decodeUtf8LossyChars (b₂ ∷ rs)

    threeL : ℕ → List ℕ → List Char
    threeL _ [] = fromℕ 65533 ∷ []
    threeL _ (b₂ ∷ []) = fromℕ 65533 ∷ decodeUtf8LossyChars (b₂ ∷ [])
    threeL a (b₂ ∷ b₃ ∷ rs) =
      let cp = (a ∸ 224) * 4096 + (b₂ ∸ 128) * 64 + (b₃ ∸ 128)
          surrogate = (55296 ≤ᵇ cp) ∧ (cp <ᵇ 57344)
      in if isCont b₂ ∧ isCont b₃ ∧ (2048 ≤ᵇ cp) ∧ not surrogate then
           fromℕ cp ∷ decodeUtf8LossyChars rs
         else fromℕ 65533 ∷ decodeUtf8LossyChars (b₂ ∷ b₃ ∷ rs)

    fourL : ℕ → List ℕ → List Char
    fourL _ [] = fromℕ 65533 ∷ []
    fourL _ (b₂ ∷ []) = fromℕ 65533 ∷ decodeUtf8LossyChars (b₂ ∷ [])
    fourL _ (b₂ ∷ b₃ ∷ []) = fromℕ 65533 ∷ decodeUtf8LossyChars (b₂ ∷ b₃ ∷ [])
    fourL a (b₂ ∷ b₃ ∷ b₄ ∷ rs) =
      let cp = (a ∸ 240) * 262144 + (b₂ ∸ 128) * 4096 + (b₃ ∸ 128) * 64 + (b₄ ∸ 128)
      in if isCont b₂ ∧ isCont b₃ ∧ isCont b₄ ∧ (65536 ≤ᵇ cp) ∧ (cp <ᵇ 1114112) then
           fromℕ cp ∷ decodeUtf8LossyChars rs
         else fromℕ 65533 ∷ decodeUtf8LossyChars (b₂ ∷ b₃ ∷ b₄ ∷ rs)

decodeUtf8Lossy : Bytes → String
decodeUtf8Lossy bs = fromList (decodeUtf8LossyChars (map octet bs))

data FsError : Set where
  fsNotFound fsIsDirectory fsNotDirectory fsAlreadyExists
    fsPermissionDenied fsSymlinkLoop fsInvalidPath fsIoError : FsError

eqFsError : FsError → FsError → Bool
eqFsError fsNotFound         fsNotFound         = true
eqFsError fsIsDirectory      fsIsDirectory      = true
eqFsError fsNotDirectory     fsNotDirectory     = true
eqFsError fsAlreadyExists    fsAlreadyExists    = true
eqFsError fsPermissionDenied fsPermissionDenied = true
eqFsError fsSymlinkLoop      fsSymlinkLoop      = true
eqFsError fsInvalidPath      fsInvalidPath      = true
eqFsError fsIoError          fsIoError          = true
eqFsError _                  _                  = false

describeFsError : FsError → String
describeFsError fsNotFound         = "no such file or directory"
describeFsError fsIsDirectory      = "is a directory"
describeFsError fsNotDirectory     = "not a directory"
describeFsError fsAlreadyExists    = "file exists"
describeFsError fsPermissionDenied = "permission denied"
describeFsError fsSymlinkLoop      = "too many levels of symbolic links"
describeFsError fsInvalidPath      = "invalid path"
describeFsError fsIoError          = "input/output error"

data NetError : Set where
  netConnRefused netTimedOut netInvalidEndpoint netTlsError netIoError : NetError

eqNetError : NetError → NetError → Bool
eqNetError netConnRefused     netConnRefused     = true
eqNetError netTimedOut        netTimedOut        = true
eqNetError netInvalidEndpoint netInvalidEndpoint = true
eqNetError netTlsError        netTlsError        = true
eqNetError netIoError         netIoError         = true
eqNetError _                  _                  = false

describeNetError : NetError → String
describeNetError netConnRefused     = "connection refused"
describeNetError netTimedOut        = "operation timed out"
describeNetError netInvalidEndpoint = "invalid host or port"
describeNetError netTlsError        = "tls handshake or verification failed"
describeNetError netIoError         = "network io error"

------------------------------------------------------------------------
-- §3 Simulated World Components & `SimWorld` Record (Free Frame Laws!)
------------------------------------------------------------------------

record SimProcessEnv : Set where
  constructor simProcessEnv
  field
    progName   : String
    args       : List String
    envVars    : List (String × String)
    stdinBytes : Bytes
open SimProcessEnv public

emptyProcessEnv : SimProcessEnv
emptyProcessEnv = simProcessEnv "cand" [] [] []

cliProcessEnv : String → List String → Bytes → SimProcessEnv
cliProcessEnv prog as inp = simProcessEnv prog as [] inp

record SimTTY : Set where
  constructor simTTY
  field
    ttyStdin  : Bool
    ttyStdout : Bool
    ttyStderr : Bool
    stdoutBuf : Bytes
    stderrBuf : Bytes
    ttyInput  : Bytes
    ttyScreen : Screen
open SimTTY public

pipeTTY : SimTTY
pipeTTY = simTTY false false false [] [] [] (blankScreen 24 80)

interactiveTTY : ℕ → ℕ → Bytes → SimTTY
interactiveTTY rows cols keys = simTTY true true true [] [] keys (blankScreen rows cols)

record NetEndpoint : Set where
  constructor netEndpoint
  field
    epHost      : String
    epPort      : ℕ
    epTls       : Bool
    epCertOk    : Bool
    epLatencyMs : ℕ
    epTopology  : NetTopology
open NetEndpoint public

record SimNet : Set where
  constructor simNet
  field
    endpoints    : List NetEndpoint
    capturedWire : List (String × ℕ × Bytes)
open SimNet public

emptyNet : SimNet
emptyNet = simNet [] []

httpStubEndpoint : ℕ → List HttpRoute → NetEndpoint
httpStubEndpoint port routes = netEndpoint "127.0.0.1" port false true 0 (httpStubMode routes)

record CanvasDOM : Set where
  constructor canvasDOM
  field
    domViewport : Rect
    domCommands : List DrawCmd
    domTitle    : String
    domEvents   : List HostInput
open CanvasDOM public

emptyCanvasDOM : CanvasDOM
emptyCanvasDOM = canvasDOM (rect (+ 0) (+ 0) 800 600) [] "" []

record SimWorld : Set where
  constructor simWorld
  field
    clock : SimClock
    env   : SimProcessEnv
    tty   : SimTTY
    fs    : VirtualFs
    net   : SimNet
    git   : PureGitRepo
    web   : CanvasDOM
open SimWorld public

defaultGitRepo : PureGitRepo
defaultGitRepo = initPureGit (gitConfig localSandbox "main" "CodeTransport" "ct@local" 0 [] []) []

defaultSimWorld : SimWorld
defaultSimWorld = simWorld zeroClock emptyProcessEnv pipeTTY (virtualFs []) emptyNet defaultGitRepo emptyCanvasDOM

cliSimWorld : String → List String → Bytes → Bool → VirtualFs → SimWorld
cliSimWorld prog as stdinB isTtyOut vfs =
  simWorld
    zeroClock
    (simProcessEnv prog as [] stdinB)
    (simTTY false isTtyOut false [] [] [] (blankScreen 24 80))
    vfs
    emptyNet
    defaultGitRepo
    emptyCanvasDOM

------------------------------------------------------------------------
-- §4 Closed-World Effect Algebra (`Op`, `Ret`, `WorldProg`, `liftWorld`)
------------------------------------------------------------------------

data Op : Cap → Set where
  -- Clock
  opNowMono       : Op clockCap
  opNowWall       : Op clockCap
  opSleepMs       : ℕ → Op clockCap
  -- Process Env
  opGetProgName   : Op envCap
  opGetArgs       : Op envCap
  opLookupEnv     : String → Op envCap
  opReadStdinAll  : Op envCap
  opReadStdinLine : Op envCap
  -- Terminal / Stdio
  opIsTTYStdin    : Op ttyCap
  opIsTTYStdout   : Op ttyCap
  opIsTTYStderr   : Op ttyCap
  opTermSize      : Op ttyCap
  opWriteStdout   : Bytes → Op ttyCap
  opWriteStderr   : Bytes → Op ttyCap
  opReadTTYByte   : Op ttyCap
  -- Filesystem
  opReadFile      : String → Op fsCap
  opWriteFile     : String → Bytes → Op fsCap
  opMkdir         : String → ℕ → Op fsCap
  opSymlink       : String → String → Op fsCap
  opUnlink        : String → Op fsCap
  opStat          : String → Op fsCap
  -- Network
  opTcpExchange   : String → ℕ → Bytes → Bool → ℕ → Op netCap
  opTlsExchange   : String → ℕ → String → Bool → Bytes → Bytes → ℕ → Op netCap
  -- Git
  opGitStep       : GitStep → Op gitCap
  opGitSummary    : Op gitCap
  -- Web Canvas / DOM
  opWebViewport   : Op webCap
  opWebSetTitle   : String → Op webCap
  opWebDrawScene  : Scene ℕ → Op webCap
  opWebHitTest    : Scene ℕ → QPoint → Op webCap
  opWebPollInput  : Op webCap

Ret : ∀ {c} → Op c → Set
Ret opNowMono                     = ℕ
Ret opNowWall                     = ℕ
Ret (opSleepMs _)                 = ⊤
Ret opGetProgName                 = String
Ret opGetArgs                     = List String
Ret (opLookupEnv _)               = Maybe String
Ret opReadStdinAll                = Bytes
Ret opReadStdinLine               = Maybe Bytes
Ret opIsTTYStdin                  = Bool
Ret opIsTTYStdout                 = Bool
Ret opIsTTYStderr                 = Bool
Ret opTermSize                    = ℕ × ℕ
Ret (opWriteStdout _)             = ⊤
Ret (opWriteStderr _)             = ⊤
Ret opReadTTYByte                 = Maybe Byte
Ret (opReadFile _)                = FsError ⊎ Bytes
Ret (opWriteFile _ _)             = FsError ⊎ ⊤
Ret (opMkdir _ _)                 = FsError ⊎ ⊤
Ret (opSymlink _ _)               = FsError ⊎ ⊤
Ret (opUnlink _)                  = FsError ⊎ ⊤
Ret (opStat _)                    = FsError ⊎ FsNodeKind
Ret (opTcpExchange _ _ _ _ _)     = NetError ⊎ Bytes
Ret (opTlsExchange _ _ _ _ _ _ _) = NetError ⊎ Bytes
Ret (opGitStep _)                 = Maybe GitRepoSummary
Ret opGitSummary                  = GitRepoSummary
Ret opWebViewport                 = Rect
Ret (opWebSetTitle _)             = ⊤
Ret (opWebDrawScene _)            = ⊤
Ret (opWebHitTest _ _)            = Maybe ℕ
Ret opWebPollInput                = Maybe HostInput

data WorldProg (Δ : List Cap) (A : Set) : Set where
  pure : A → WorldProg Δ A
  step : ∀ {c} → c ∈ Δ → (op : Op c) → (Ret op → WorldProg Δ A) → WorldProg Δ A

infixl 1 _>>=w_ _>>w_

_>>=w_ : ∀ {Δ A B} → WorldProg Δ A → (A → WorldProg Δ B) → WorldProg Δ B
pure a       >>=w k = k a
step h op k₁ >>=w k = step h op (λ r → k₁ r >>=w k)

_>>w_ : ∀ {Δ A B} → WorldProg Δ A → WorldProg Δ B → WorldProg Δ B
m >>w n = m >>=w (λ _ → n)

mapWorld : ∀ {Δ A B} → (A → B) → WorldProg Δ A → WorldProg Δ B
mapWorld f (pure a)      = pure (f a)
mapWorld f (step h op k) = step h op (λ r → mapWorld f (k r))

liftWorld : ∀ {Δ₁ Δ₂ A} → Δ₁ ⊆ Δ₂ → WorldProg Δ₁ A → WorldProg Δ₂ A
liftWorld _   (pure a)      = pure a
liftWorld sub (step h op k) = step (sub h) op (λ r → liftWorld sub (k r))

-- Ergonomic single-step smart constructors
nowMonoW : ∀ {Δ} → clockCap ∈ Δ → WorldProg Δ ℕ
nowMonoW h = step h opNowMono pure

nowWallW : ∀ {Δ} → clockCap ∈ Δ → WorldProg Δ ℕ
nowWallW h = step h opNowWall pure

sleepW : ∀ {Δ} → clockCap ∈ Δ → ℕ → WorldProg Δ ⊤
sleepW h ms = step h (opSleepMs ms) pure

getProgNameW : ∀ {Δ} → envCap ∈ Δ → WorldProg Δ String
getProgNameW h = step h opGetProgName pure

getArgsW : ∀ {Δ} → envCap ∈ Δ → WorldProg Δ (List String)
getArgsW h = step h opGetArgs pure

lookupEnvW : ∀ {Δ} → envCap ∈ Δ → String → WorldProg Δ (Maybe String)
lookupEnvW h k = step h (opLookupEnv k) pure

readStdinAllW : ∀ {Δ} → envCap ∈ Δ → WorldProg Δ Bytes
readStdinAllW h = step h opReadStdinAll pure

readStdinLineW : ∀ {Δ} → envCap ∈ Δ → WorldProg Δ (Maybe Bytes)
readStdinLineW h = step h opReadStdinLine pure

isTTYStdinW : ∀ {Δ} → ttyCap ∈ Δ → WorldProg Δ Bool
isTTYStdinW h = step h opIsTTYStdin pure

isTTYStdoutW : ∀ {Δ} → ttyCap ∈ Δ → WorldProg Δ Bool
isTTYStdoutW h = step h opIsTTYStdout pure

isTTYStderrW : ∀ {Δ} → ttyCap ∈ Δ → WorldProg Δ Bool
isTTYStderrW h = step h opIsTTYStderr pure

termSizeW : ∀ {Δ} → ttyCap ∈ Δ → WorldProg Δ (ℕ × ℕ)
termSizeW h = step h opTermSize pure

writeStdoutW : ∀ {Δ} → ttyCap ∈ Δ → Bytes → WorldProg Δ ⊤
writeStdoutW h bs = step h (opWriteStdout bs) pure

writeStdoutStrW : ∀ {Δ} → ttyCap ∈ Δ → String → WorldProg Δ ⊤
writeStdoutStrW h s = writeStdoutW h (bytes s)

writeStderrW : ∀ {Δ} → ttyCap ∈ Δ → Bytes → WorldProg Δ ⊤
writeStderrW h bs = step h (opWriteStderr bs) pure

writeStderrStrW : ∀ {Δ} → ttyCap ∈ Δ → String → WorldProg Δ ⊤
writeStderrStrW h s = writeStderrW h (bytes s)

readTTYByteW : ∀ {Δ} → ttyCap ∈ Δ → WorldProg Δ (Maybe Byte)
readTTYByteW h = step h opReadTTYByte pure

readFileW : ∀ {Δ} → fsCap ∈ Δ → String → WorldProg Δ (FsError ⊎ Bytes)
readFileW h p = step h (opReadFile p) pure

writeFileW : ∀ {Δ} → fsCap ∈ Δ → String → Bytes → WorldProg Δ (FsError ⊎ ⊤)
writeFileW h p bs = step h (opWriteFile p bs) pure

mkdirW : ∀ {Δ} → fsCap ∈ Δ → String → ℕ → WorldProg Δ (FsError ⊎ ⊤)
mkdirW h p mode = step h (opMkdir p mode) pure

symlinkW : ∀ {Δ} → fsCap ∈ Δ → String → String → WorldProg Δ (FsError ⊎ ⊤)
symlinkW h p dst = step h (opSymlink p dst) pure

unlinkW : ∀ {Δ} → fsCap ∈ Δ → String → WorldProg Δ (FsError ⊎ ⊤)
unlinkW h p = step h (opUnlink p) pure

statW : ∀ {Δ} → fsCap ∈ Δ → String → WorldProg Δ (FsError ⊎ FsNodeKind)
statW h p = step h (opStat p) pure

tcpExchangeW : ∀ {Δ} → netCap ∈ Δ → String → ℕ → Bytes → Bool → ℕ → WorldProg Δ (NetError ⊎ Bytes)
tcpExchangeW h host port req hc tms = step h (opTcpExchange host port req hc tms) pure

tlsExchangeW : ∀ {Δ} → netCap ∈ Δ → String → ℕ → String → Bool → Bytes → Bytes → ℕ → WorldProg Δ (NetError ⊎ Bytes)
tlsExchangeW h host port sni ins tun req tms = step h (opTlsExchange host port sni ins tun req tms) pure

gitStepW : ∀ {Δ} → gitCap ∈ Δ → GitStep → WorldProg Δ (Maybe GitRepoSummary)
gitStepW h s = step h (opGitStep s) pure

gitSummaryW : ∀ {Δ} → gitCap ∈ Δ → WorldProg Δ GitRepoSummary
gitSummaryW h = step h opGitSummary pure

webViewportW : ∀ {Δ} → webCap ∈ Δ → WorldProg Δ Rect
webViewportW h = step h opWebViewport pure

webSetTitleW : ∀ {Δ} → webCap ∈ Δ → String → WorldProg Δ ⊤
webSetTitleW h t = step h (opWebSetTitle t) pure

webDrawSceneW : ∀ {Δ} → webCap ∈ Δ → Scene ℕ → WorldProg Δ ⊤
webDrawSceneW h sc = step h (opWebDrawScene sc) pure

webHitTestW : ∀ {Δ} → webCap ∈ Δ → Scene ℕ → QPoint → WorldProg Δ (Maybe ℕ)
webHitTestW h sc q = step h (opWebHitTest sc q) pure

webPollInputW : ∀ {Δ} → webCap ∈ Δ → WorldProg Δ (Maybe HostInput)
webPollInputW h = step h opWebPollInput pure

------------------------------------------------------------------------
-- §5 Batch CLI & Interactive Reactive Application Shapes (`--safe`)
------------------------------------------------------------------------

ExitCode : Set
ExitCode = ℕ

CliApp : List Cap → Set
CliApp Δ = WorldProg Δ ExitCode

data EventPayload : Cap → Set where
  evTickMs   : ℕ → EventPayload clockCap
  evSignal   : Signal → EventPayload envCap
  evKey      : Key → EventPayload ttyCap
  evResize   : ℕ → ℕ → EventPayload ttyCap
  evTTYBytes : Bytes → EventPayload ttyCap
  evFsWatch  : String → EventPayload fsCap
  evNetConn  : Bytes → EventPayload netCap
  evGitHook  : String → EventPayload gitCap
  evWebInput : HostInput → EventPayload webCap

record Event (Δ : List Cap) : Set where
  constructor mkEvent
  field
    {evCap}   : Cap
    evHasCap  : evCap ∈ Δ
    evPayload : EventPayload evCap
open Event public

liftEvent : ∀ {Δ₁ Δ₂} → Δ₁ ⊆ Δ₂ → Event Δ₁ → Event Δ₂
liftEvent sub e = mkEvent (sub (evHasCap e)) (evPayload e)

record ReactiveApp (Δ : List Cap) (S : Set) : Set where
  constructor reactiveApp
  field
    init   : WorldProg Δ S
    onStep : Event Δ → S → WorldProg Δ (S ⊎ ExitCode)
open ReactiveApp public

------------------------------------------------------------------------
-- §6 Pure Deterministic Single-Component Helpers & `runWorldPure`
------------------------------------------------------------------------

lookupEnvVar : String → List (String × String) → Maybe String
lookupEnvVar _ []              = nothing
lookupEnvVar k ((name , v) ∷ xs) =
  if eqStr k name then just v else lookupEnvVar k xs

takeLineBytes : Bytes → Maybe Bytes × Bytes
takeLineBytes [] = nothing , []
takeLineBytes (b ∷ bs) = just (proj₁ (scan b bs)) , proj₂ (scan b bs)
  where
    scan : Byte → Bytes → Bytes × Bytes
    scan cur [] = (cur ∷ []) , []
    scan cur (x ∷ xs) =
      if octet cur ≡ᵇ 10 then (cur ∷ []) , (x ∷ xs)
      else (let r = scan x xs in (cur ∷ proj₁ r) , proj₂ r)

popByte : Bytes → Maybe Byte × Bytes
popByte []       = nothing , []
popByte (b ∷ bs) = just b , bs

hasDotSlashPrefix : List Char → Bool
hasDotSlashPrefix (c₁ ∷ c₂ ∷ _) = (toℕ c₁ ≡ᵇ 46) ∧ (toℕ c₂ ≡ᵇ 47)
hasDotSlashPrefix _             = false

stripDotSlashChars : List Char → List Char
stripDotSlashChars (c₁ ∷ c₂ ∷ cs) =
  if (toℕ c₁ ≡ᵇ 46) ∧ (toℕ c₂ ≡ᵇ 47)
    then stripDotSlashChars cs
    else (c₁ ∷ c₂ ∷ cs)
stripDotSlashChars cs = cs

normalizeRelPath : String → String
normalizeRelPath p =
  if hasDotSlashPrefix (toList p)
    then fromList (stripDotSlashChars (toList p))
    else p

readVirtualFileFuel : ℕ → String → VirtualFs → FsError ⊎ Bytes
readVirtualFileFuel zero _ _ = inj₁ fsSymlinkLoop
readVirtualFileFuel (suc fuel) rawP v =
  let p = normalizeRelPath rawP
  in if eqStr p "." then inj₁ fsIsDirectory
     else if not (validRelPath p) then inj₁ fsInvalidPath
     else stepEntry (lookupEntry p (fsEntries v))
  where
    stepEntry : Maybe FsEntryObs → FsError ⊎ Bytes
    stepEntry nothing  = inj₁ fsNotFound
    stepEntry (just e) =
      if eqKind (entryKind e) regularNode then inj₂ (entryBytes e)
      else if eqKind (entryKind e) dirNode then inj₁ fsIsDirectory
      else readVirtualFileFuel fuel (wireText (entryBytes e)) v

readVirtualFile : String → VirtualFs → FsError ⊎ Bytes
readVirtualFile = readVirtualFileFuel 8

writeVirtualFileFuel : ℕ → String → Bytes → VirtualFs → (FsError ⊎ ⊤) × VirtualFs
writeVirtualFileFuel zero _ _ v = inj₁ fsSymlinkLoop , v
writeVirtualFileFuel (suc fuel) rawP bs v =
  let p = normalizeRelPath rawP
  in if eqStr p "." then (inj₁ fsIsDirectory , v)
     else if not (validRelPath p) then (inj₁ fsInvalidPath , v)
     else withPrepared p (ensureParents true (parentPaths p) v)
  where
    withExisting : String → VirtualFs → Maybe FsEntryObs → (FsError ⊎ ⊤) × VirtualFs
    withExisting p v₁ nothing =
      inj₂ tt , putEntry (fsEntry p regularNode 420 bs) v₁
    withExisting p v₁ (just e) =
      if eqKind (entryKind e) regularNode then
        (inj₂ tt , putEntry (fsEntry p regularNode (entryMode e) bs) v₁)
      else if eqKind (entryKind e) dirNode then
        (inj₁ fsIsDirectory , v)
      else
        writeVirtualFileFuel fuel (wireText (entryBytes e)) bs v

    withPrepared : String → Maybe VirtualFs → (FsError ⊎ ⊤) × VirtualFs
    withPrepared _ nothing   = inj₁ fsNotDirectory , v
    withPrepared p (just v₁) = withExisting p v₁ (lookupEntry p (fsEntries v₁))

writeVirtualFile : String → Bytes → VirtualFs → (FsError ⊎ ⊤) × VirtualFs
writeVirtualFile = writeVirtualFileFuel 8

mkdirVirtual : String → ℕ → VirtualFs → (FsError ⊎ ⊤) × VirtualFs
mkdirVirtual rawP mode v =
  let p = normalizeRelPath rawP
  in if eqStr p "." then (inj₂ tt , v)
     else if not (validRelPath p) then (inj₁ fsInvalidPath , v)
     else go p (ensureParents true (parentPaths p) v)
  where
    putDir : String → VirtualFs → Maybe FsEntryObs → (FsError ⊎ ⊤) × VirtualFs
    putDir p v₁ nothing =
      inj₂ tt , putEntry (fsEntry p dirNode (maskMode mode) []) v₁
    putDir p v₁ (just e) =
      if eqKind (entryKind e) dirNode then
        (inj₂ tt , putEntry (fsEntry p dirNode (maskMode mode) []) v₁)
      else (inj₁ fsAlreadyExists , v)

    go : String → Maybe VirtualFs → (FsError ⊎ ⊤) × VirtualFs
    go _ nothing   = inj₁ fsNotDirectory , v
    go p (just v₁) = putDir p v₁ (lookupEntry p (fsEntries v₁))

symlinkVirtual : String → String → VirtualFs → (FsError ⊎ ⊤) × VirtualFs
symlinkVirtual rawP dest v =
  let p     = normalizeRelPath rawP
      okDst = not (eqStr dest "") ∧ all (λ c → not (toℕ c ≡ᵇ 0)) (toList dest)
  in if not okDst ∨ eqStr p "." ∨ not (validRelPath p) then (inj₁ fsInvalidPath , v)
     else go p (ensureParents true (parentPaths p) v)
  where
    putLink : String → VirtualFs → Maybe FsEntryObs → (FsError ⊎ ⊤) × VirtualFs
    putLink p v₁ nothing =
      inj₂ tt , putEntry (fsEntry p symlinkNode 511 (bytes dest)) v₁
    putLink p v₁ (just e) =
      if eqKind (entryKind e) dirNode then (inj₁ fsIsDirectory , v)
      else (inj₂ tt , putEntry (fsEntry p symlinkNode 511 (bytes dest)) v₁)

    go : String → Maybe VirtualFs → (FsError ⊎ ⊤) × VirtualFs
    go _ nothing   = inj₁ fsNotDirectory , v
    go p (just v₁) = putLink p v₁ (lookupEntry p (fsEntries v₁))

unlinkVirtual : String → VirtualFs → (FsError ⊎ ⊤) × VirtualFs
unlinkVirtual rawP v =
  let p = normalizeRelPath rawP
  in if eqStr p "." ∨ not (validRelPath p) then (inj₁ fsInvalidPath , v)
     else go p (ensureParents false (parentPaths p) v)
  where
    del : String → Maybe FsEntryObs → (FsError ⊎ ⊤) × VirtualFs
    del _ nothing  = inj₁ fsNotFound , v
    del p (just _) =
      if all (λ x → not (isParent p (entryPath x))) (fsEntries v) then
        (inj₂ tt , virtualFs (removeEntry p (fsEntries v)))
      else (inj₁ fsIsDirectory , v)

    go : String → Maybe VirtualFs → (FsError ⊎ ⊤) × VirtualFs
    go _ nothing  = inj₁ fsNotDirectory , v
    go p (just _) = del p (lookupEntry p (fsEntries v))

statVirtual : String → VirtualFs → FsError ⊎ FsNodeKind
statVirtual rawP v =
  let p = normalizeRelPath rawP
  in if eqStr p "." then inj₂ dirNode
     else if not (validRelPath p) then inj₁ fsInvalidPath
     else go (lookupEntry p (fsEntries v))
  where
    go : Maybe FsEntryObs → FsError ⊎ FsNodeKind
    go nothing  = inj₁ fsNotFound
    go (just e) = inj₂ (entryKind e)

isLoopbackHost : String → Bool
isLoopbackHost h = eqStr h "127.0.0.1" ∨ eqStr h "localhost" ∨ eqStr h "[::1]" ∨ eqStr h "::1"

hostMatches : String → String → Bool
hostMatches epH reqH =
  eqStr epH "*" ∨ eqStr epH reqH ∨ (isLoopbackHost epH ∧ isLoopbackHost reqH)

findEndpoint : Bool → String → ℕ → List NetEndpoint → Maybe NetEndpoint
findEndpoint _       _    _    [] = nothing
findEndpoint wantTls host port (ep ∷ eps) =
  let sameTls = if wantTls then epTls ep else not (epTls ep)
  in if sameTls ∧ (epPort ep ≡ᵇ port) ∧ hostMatches (epHost ep) host then
       just ep
     else findEndpoint wantTls host port eps

stubDelayOf : NetTopology → ℕ
stubDelayOf (httpDelayedStubMode d _) = d
stubDelayOf (tcpDelayedStubMode  d _) = d
stubDelayOf _                         = 0

evalNetExchange : Bool → Bool → String → ℕ → Bytes → ℕ → SimNet → (NetError ⊎ Bytes) × SimNet
evalNetExchange wantTls insecure host port req timeoutMs netSt =
  let badHostPort = eqStr host "" ∨ (port ≡ᵇ 0) ∨ (65535 <ᵇ port)
  in if badHostPort then (inj₁ netInvalidEndpoint , netSt)
     else dispatch (findEndpoint wantTls host port (endpoints netSt))
  where
    dispatch : Maybe NetEndpoint → (NetError ⊎ Bytes) × SimNet
    dispatch nothing   = inj₁ netConnRefused , netSt
    dispatch (just ep) =
      let effTimeout = if timeoutMs ≡ᵇ 0 then 30000 else timeoutMs
          totalDelay = epLatencyMs ep + stubDelayOf (epTopology ep)
          certBad    = wantTls ∧ not insecure ∧ not (epCertOk ep)
          timedOut   = (0 <ᵇ totalDelay) ∧ (effTimeout ≤ᵇ totalDelay)
          recorded   = record netSt { capturedWire = capturedWire netSt ++ ((host , port , req) ∷ []) }
      in if certBad then (inj₁ netTlsError , recorded)
         else if timedOut then (inj₁ netTimedOut , recorded)
         else (inj₂ (stubReply (epTopology ep) req) , recorded)

popWebEvent : List HostInput → Maybe HostInput × List HostInput
popWebEvent []       = nothing , []
popWebEvent (e ∷ es) = just e , es

-- CRITICAL INVARIANT: Every clause of `stepWorldPure` constructs `(ret , w)`
-- or `(ret , record w { <singleField> = ... })` directly at the top level!
-- Consequently, for ANY symbolic arguments and ANY universally quantified `w`,
-- projecting any other capability's field reduces to `<field> w` by `refl`!
stepWorldPure : ∀ {c} → (op : Op c) → SimWorld → Ret op × SimWorld
-- Clock
stepWorldPure opNowMono w =
  let r = readMonoMs (clock w)
  in proj₁ r , record w { clock = proj₂ r }
stepWorldPure opNowWall w =
  let r = readWallMs (clock w)
  in proj₁ r , record w { clock = proj₂ r }
stepWorldPure (opSleepMs ms) w =
  tt , record w { clock = sleepClockMs ms (clock w) }
-- Process Env
stepWorldPure opGetProgName w =
  progName (env w) , w
stepWorldPure opGetArgs w =
  args (env w) , w
stepWorldPure (opLookupEnv k) w =
  lookupEnvVar k (envVars (env w)) , w
stepWorldPure opReadStdinAll w =
  stdinBytes (env w) , record w { env = record (env w) { stdinBytes = [] } }
stepWorldPure opReadStdinLine w =
  let r = takeLineBytes (stdinBytes (env w))
  in proj₁ r , record w { env = record (env w) { stdinBytes = proj₂ r } }
-- Terminal / Stdio
stepWorldPure opIsTTYStdin w =
  ttyStdin (tty w) , w
stepWorldPure opIsTTYStdout w =
  ttyStdout (tty w) , w
stepWorldPure opIsTTYStderr w =
  ttyStderr (tty w) , w
stepWorldPure opTermSize w =
  (Screen.height (ttyScreen (tty w)) , Screen.width (ttyScreen (tty w))) , w
stepWorldPure (opWriteStdout bs) w =
  let t = tty w
      nextScr = if ttyStdout t then stepANSI (ttyScreen t) bs else ttyScreen t
  in tt , record w { tty = record t { stdoutBuf = stdoutBuf t ++ bs ; ttyScreen = nextScr } }
stepWorldPure (opWriteStderr bs) w =
  let t = tty w
      nextScr = if ttyStderr t then stepANSI (ttyScreen t) bs else ttyScreen t
  in tt , record w { tty = record t { stderrBuf = stderrBuf t ++ bs ; ttyScreen = nextScr } }
stepWorldPure opReadTTYByte w =
  let t = tty w
      r = popByte (ttyInput t)
  in proj₁ r , record w { tty = record t { ttyInput = proj₂ r } }
-- Filesystem
stepWorldPure (opReadFile p) w =
  readVirtualFile p (fs w) , w
stepWorldPure (opWriteFile p bs) w =
  let r = writeVirtualFile p bs (fs w)
  in proj₁ r , record w { fs = proj₂ r }
stepWorldPure (opMkdir p mode) w =
  let r = mkdirVirtual p mode (fs w)
  in proj₁ r , record w { fs = proj₂ r }
stepWorldPure (opSymlink p dst) w =
  let r = symlinkVirtual p dst (fs w)
  in proj₁ r , record w { fs = proj₂ r }
stepWorldPure (opUnlink p) w =
  let r = unlinkVirtual p (fs w)
  in proj₁ r , record w { fs = proj₂ r }
stepWorldPure (opStat p) w =
  statVirtual p (fs w) , w
-- Network
stepWorldPure (opTcpExchange host port req _ tms) w =
  let r = evalNetExchange false false host port req tms (net w)
  in proj₁ r , record w { net = proj₂ r }
stepWorldPure (opTlsExchange host port _ ins _ req tms) w =
  let r = evalNetExchange true ins host port req tms (net w)
  in proj₁ r , record w { net = proj₂ r }
-- Git
stepWorldPure (opGitStep gs) w =
  let r = stepPureGit gs (git w)
  in proj₂ r , record w { git = proj₁ r }
stepWorldPure opGitSummary w =
  projectSummary (git w) , w
-- Web Canvas / DOM
stepWorldPure opWebViewport w =
  domViewport (web w) , w
stepWorldPure (opWebSetTitle title) w =
  tt , record w { web = record (web w) { domTitle = title } }
stepWorldPure (opWebDrawScene sc) w =
  tt , record w { web = record (web w) { domCommands = compileDraw sc } }
stepWorldPure (opWebHitTest sc q) w =
  hitTest sc q , w
stepWorldPure opWebPollInput w =
  let r = popWebEvent (domEvents (web w))
  in proj₁ r , record w { web = record (web w) { domEvents = proj₂ r } }

runWorldPure : ∀ {Δ A} → WorldProg Δ A → SimWorld → A × SimWorld
runWorldPure (pure a)      w = a , w
runWorldPure (step _ op k) w =
  let rw = stepWorldPure op w
  in runWorldPure (k (proj₁ rw)) (proj₂ rw)

runCliPure : ∀ {Δ} → CliApp Δ → SimWorld → ExitCode × SimWorld
runCliPure = runWorldPure

runReactiveSteps : ∀ {Δ S} → ReactiveApp Δ S → S → List (Event Δ) → SimWorld → (S ⊎ ExitCode) × SimWorld
runReactiveSteps         _   s []       w = inj₁ s , w
runReactiveSteps {Δ} {S} app s (e ∷ es) w =
  let r = runWorldPure (onStep app e s) w
  in continue (proj₁ r) (proj₂ r)
  where
    continue : S ⊎ ExitCode → SimWorld → (S ⊎ ExitCode) × SimWorld
    continue (inj₁ s′)   w′ = runReactiveSteps app s′ es w′
    continue (inj₂ code) w′ = inj₂ code , w′

runReactivePure : ∀ {Δ S} → ReactiveApp Δ S → List (Event Δ) → SimWorld → (S ⊎ ExitCode) × SimWorld
runReactivePure app evs w =
  let initRes = runWorldPure (init app) w
  in runReactiveSteps app (proj₁ initRes) evs (proj₂ initRes)
