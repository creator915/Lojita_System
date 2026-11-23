import LojitaCtx.Clock
import LojitaCtx.NetSandbox
import LojitaCtx.GitSandbox
import LojitaCtx.WebOperad

namespace LojitaCtx.World

open LojitaCtx.Terminal

export Clock (SimClock)
export FsSandbox (eqStr)
export NetSandbox (showDec)
open Clock
open FsSandbox (FsNodeKind FsEntryObs VirtualFs)
open NetSandbox (HttpRoute RawStubRule NetTopology)
open GitSandbox (GitConfig GitStep GitRepoSummary PureGitRepo)
open WebOperad (Point Size Rect QPoint Scene DrawCmd HostInput)

inductive Cap : Type where
  | clockCap : Cap
  | envCap   : Cap
  | ttyCap   : Cap
  | fsCap    : Cap
  | netCap   : Cap
  | gitCap   : Cap
  | webCap   : Cap

/-- Standard streams use the terminal capability of the world runner. -/
abbrev Cap.stdioCap : Cap := .ttyCap

-- Lean's deriving handler uses constructor indices for finite enumerations.
def Cap.ctorIdx : Cap → Nat
  | .clockCap => 0
  | .envCap => 1
  | .ttyCap => 2
  | .fsCap => 3
  | .netCap => 4
  | .gitCap => 5
  | .webCap => 6

deriving instance DecidableEq for Cap

def eqCap : Cap → Cap → Bool
  | .clockCap, .clockCap => true
  | .envCap,   .envCap   => true
  | .ttyCap,   .ttyCap   => true
  | .fsCap,    .fsCap    => true
  | .netCap,   .netCap   => true
  | .gitCap,   .gitCap   => true
  | .webCap,   .webCap   => true
  | _,         _         => false

inductive CapMem (c : Cap) : List Cap → Type where
  | here  : {cs : List Cap} → CapMem c (c :: cs)
  | there : {d : Cap} → {cs : List Cap} → CapMem c cs → CapMem c (d :: cs)

abbrev CapSub (Δ₁ Δ₂ : List Cap) : Type :=
  {c : Cap} → CapMem c Δ₁ → CapMem c Δ₂

def capSubRefl {Δ : List Cap} : CapSub Δ Δ :=
  fun h => h

def capSubTrans {Δ₁ Δ₂ Δ₃ : List Cap} (f : CapSub Δ₁ Δ₂) (g : CapSub Δ₂ Δ₃) : CapSub Δ₁ Δ₃ :=
  fun h => g (f h)

def capSubNil {Δ : List Cap} : CapSub [] Δ :=
  fun h => nomatch h

def capSubStep {d : Cap} {Δ₁ Δ₂ : List Cap} (sub : CapSub Δ₁ Δ₂) : CapSub Δ₁ (d :: Δ₂) :=
  fun h => .there (sub h)

def capSubCons {c : Cap} {Δ₁ Δ₂ : List Cap} (hc : CapMem c Δ₂) (sub : CapSub Δ₁ Δ₂) : CapSub (c :: Δ₁) Δ₂
  | _, .here    => hc
  | _, .there h => sub h

def hasCap (c : Cap) : List Cap → Bool
  | [] => false
  | d :: ds => eqCap c d || hasCap c ds
termination_by structural ds => ds

def findCapIn (c : Cap) : (cs : List Cap) → Option (CapMem c cs)
  | [] => none
  | d :: ds => if h : c = d then some (h ▸ CapMem.here) else (findCapIn c ds).map CapMem.there
termination_by structural ds => ds

def PureCaps : List Cap := []

def CliCaps : List Cap :=
  [.clockCap, .envCap, .ttyCap, .fsCap, .netCap]

def AllCaps : List Cap :=
  [.clockCap, .envCap, .ttyCap, .fsCap, .netCap, .gitCap, .webCap]

def clockInCli : CapMem .clockCap CliCaps := .here
def envInCli   : CapMem .envCap   CliCaps := .there .here
def ttyInCli   : CapMem .ttyCap   CliCaps := .there (.there .here)
def fsInCli    : CapMem .fsCap    CliCaps := .there (.there (.there .here))
def netInCli   : CapMem .netCap   CliCaps := .there (.there (.there (.there .here)))

def clockInAll : CapMem .clockCap AllCaps := .here
def envInAll   : CapMem .envCap   AllCaps := .there .here
def ttyInAll   : CapMem .ttyCap   AllCaps := .there (.there .here)
def fsInAll    : CapMem .fsCap    AllCaps := .there (.there (.there .here))
def netInAll   : CapMem .netCap   AllCaps := .there (.there (.there (.there .here)))
def gitInAll   : CapMem .gitCap   AllCaps := .there (.there (.there (.there (.there .here))))
def webInAll   : CapMem .webCap   AllCaps := .there (.there (.there (.there (.there (.there .here)))))

def cliSubAll : CapSub CliCaps AllCaps :=
  capSubCons clockInAll (capSubCons envInAll (capSubCons ttyInAll (capSubCons fsInAll (capSubCons netInAll capSubNil))))

private def isUtf8Cont (x : Nat) : Bool :=
  128 ≤ x && x < 192

private def mapMaybeChars (c : Char) : Option (List Char) → Option (List Char)
  | .none => .none
  | .some cs => .some (c :: cs)

def decodeUtf8Chars : List Nat → Option (List Char)
  | [] => .some []
  | b₁ :: rest =>
    if b₁ < 128 then mapMaybeChars (Char.ofNat b₁) (decodeUtf8Chars rest)
    else
      if 194 ≤ b₁ && b₁ < 224 then
        match rest with
        | [] => .none
        | b₂ :: rs =>
          if isUtf8Cont b₂ then
            mapMaybeChars (Char.ofNat ((b₁ - 192) * 64 + (b₂ - 128))) (decodeUtf8Chars rs)
          else .none
      else
        if 224 ≤ b₁ && b₁ < 240 then
          match rest with
          | b₂ :: b₃ :: rs =>
            let cp := (b₁ - 224) * 4096 + ((b₂ - 128) * 64 + (b₃ - 128))
            let surrogate := 55296 ≤ cp && cp < 57344
            if isUtf8Cont b₂ && (isUtf8Cont b₃ && (2048 ≤ cp && Bool.not surrogate)) then
              mapMaybeChars (Char.ofNat cp) (decodeUtf8Chars rs)
            else .none
          | [] | [_] => .none
        else
          if 240 ≤ b₁ && b₁ < 245 then
            match rest with
            | b₂ :: b₃ :: b₄ :: rs =>
              let cp := (b₁ - 240) * 262144 + ((b₂ - 128) * 4096 + ((b₃ - 128) * 64 + (b₄ - 128)))
              if
                  isUtf8Cont b₂ &&
                    (isUtf8Cont b₃ && (isUtf8Cont b₄ && (65536 ≤ cp && cp < 1114112))) then
                mapMaybeChars (Char.ofNat cp) (decodeUtf8Chars rs)
              else .none
            | [] | [_] | [_, _] => .none
          else .none
termination_by structural xs => xs

def decodeUtf8 (bs : Bytes) : Option String :=
  match decodeUtf8Chars (List.map UInt8.toNat bs) with
  | .none => .none
  | .some cs => .some (String.ofList cs)

def decodeUtf8LossyChars : List Nat → List Char
  | [] => []
  | b₁ :: rest =>
    let replacement := fun _ : Unit => Char.ofNat 65533 :: decodeUtf8LossyChars rest
    if b₁ < 128 then Char.ofNat b₁ :: decodeUtf8LossyChars rest
    else
      if 194 ≤ b₁ && b₁ < 224 then
        match rest with
        | [] => [Char.ofNat 65533]
        | b₂ :: rs =>
          if isUtf8Cont b₂ then Char.ofNat ((b₁ - 192) * 64 + (b₂ - 128)) :: decodeUtf8LossyChars rs
          else replacement ()
      else
        if 224 ≤ b₁ && b₁ < 240 then
          match rest with
          | [] => [Char.ofNat 65533]
          | [_] => replacement ()
          | b₂ :: b₃ :: rs =>
            let cp := (b₁ - 224) * 4096 + ((b₂ - 128) * 64 + (b₃ - 128))
            let surrogate := 55296 ≤ cp && cp < 57344
            if isUtf8Cont b₂ && (isUtf8Cont b₃ && (2048 ≤ cp && Bool.not surrogate)) then
              Char.ofNat cp :: decodeUtf8LossyChars rs
            else replacement ()
        else
          if 240 ≤ b₁ && b₁ < 245 then
            match rest with
            | [] => [Char.ofNat 65533]
            | [_] => replacement ()
            | [_, _] => replacement ()
            | b₂ :: b₃ :: b₄ :: rs =>
              let cp := (b₁ - 240) * 262144 + ((b₂ - 128) * 4096 + ((b₃ - 128) * 64 + (b₄ - 128)))
              if
                  isUtf8Cont b₂ &&
                    (isUtf8Cont b₃ && (isUtf8Cont b₄ && (65536 ≤ cp && cp < 1114112))) then
                Char.ofNat cp :: decodeUtf8LossyChars rs
              else replacement ()
          else replacement ()
termination_by structural xs => xs

def decodeUtf8Lossy (bs : Bytes) : String :=
  String.ofList (decodeUtf8LossyChars (List.map UInt8.toNat bs))

inductive FsError : Type where
  | fsNotFound         : FsError
  | fsIsDirectory      : FsError
  | fsNotDirectory     : FsError
  | fsAlreadyExists    : FsError
  | fsPermissionDenied : FsError
  | fsSymlinkLoop      : FsError
  | fsInvalidPath      : FsError
  | fsIoError          : FsError

def eqFsError : FsError → FsError → Bool
  | .fsNotFound,         .fsNotFound         => true
  | .fsIsDirectory,      .fsIsDirectory      => true
  | .fsNotDirectory,     .fsNotDirectory     => true
  | .fsAlreadyExists,    .fsAlreadyExists    => true
  | .fsPermissionDenied, .fsPermissionDenied => true
  | .fsSymlinkLoop,      .fsSymlinkLoop      => true
  | .fsInvalidPath,      .fsInvalidPath      => true
  | .fsIoError,          .fsIoError          => true
  | _,                   _                   => false

def describeFsError : FsError → String
  | .fsNotFound         => "no such file or directory"
  | .fsIsDirectory      => "is a directory"
  | .fsNotDirectory     => "not a directory"
  | .fsAlreadyExists    => "file exists"
  | .fsPermissionDenied => "permission denied"
  | .fsSymlinkLoop      => "too many levels of symbolic links"
  | .fsInvalidPath      => "invalid path"
  | .fsIoError          => "input/output error"

inductive NetError : Type where
  | netConnRefused     : NetError
  | netTimedOut        : NetError
  | netInvalidEndpoint : NetError
  | netTlsError        : NetError
  | netIoError         : NetError

def eqNetError : NetError → NetError → Bool
  | .netConnRefused,     .netConnRefused     => true
  | .netTimedOut,        .netTimedOut        => true
  | .netInvalidEndpoint, .netInvalidEndpoint => true
  | .netTlsError,        .netTlsError        => true
  | .netIoError,         .netIoError         => true
  | _,                   _                   => false

def describeNetError : NetError → String
  | .netConnRefused     => "connection refused"
  | .netTimedOut        => "operation timed out"
  | .netInvalidEndpoint => "invalid host or port"
  | .netTlsError        => "tls handshake or verification failed"
  | .netIoError         => "network io error"

structure SimProcessEnv : Type where simProcessEnv ::
  progName : String
  args : List String
  envVars : List (String × String)
  stdinBytes : Bytes

def emptyProcessEnv : SimProcessEnv :=
  SimProcessEnv.simProcessEnv "cand" [] [] []

def cliProcessEnv (prog : String) (as : List String) (inp : Bytes) : SimProcessEnv :=
  SimProcessEnv.simProcessEnv prog as [] inp

structure SimTTY : Type where
  simTTY ::
  ttyStdin  : Bool
  ttyStdout : Bool
  ttyStderr : Bool
  stdoutBuf : ByteArray
  stderrBuf : ByteArray
  ttyInput  : Bytes
  ttyScreen : Screen

def pipeTTY : SimTTY :=
  SimTTY.simTTY false false false .empty .empty [] (blankScreen 24 80)

def interactiveTTY (rows cols : Nat) (keys : Bytes) : SimTTY :=
  SimTTY.simTTY true true true .empty .empty keys (blankScreen rows cols)

structure NetEndpoint : Type where
  netEndpoint ::
  epHost      : String
  epPort      : Nat
  epTls       : Bool
  epCertOk    : Bool
  epLatencyMs : Nat
  epTopology  : NetTopology

structure SimNet : Type where simNet ::
  endpoints : List NetEndpoint
  capturedWire : Array (String × Nat × Bytes)

def emptyNet : SimNet :=
  SimNet.simNet [] #[]

def httpStubEndpoint (port : Nat) (routes : List HttpRoute) : NetEndpoint :=
  NetEndpoint.netEndpoint "127.0.0.1" port false true 0 (.httpStubMode routes)

structure CanvasDOM : Type where
  canvasDOM ::
  domViewport : Rect
  domCommands : List DrawCmd
  domTitle    : String
  domEvents   : List HostInput

def emptyCanvasDOM : CanvasDOM :=
  CanvasDOM.canvasDOM (Rect.rect (Int.ofNat 0) (Int.ofNat 0) 800 600) [] "" []

structure SimWorld : Type where
  simWorld ::
  clock : SimClock
  env   : SimProcessEnv
  tty   : SimTTY
  fs    : VirtualFs
  net   : SimNet
  git   : PureGitRepo
  web   : CanvasDOM

def defaultGitRepo : PureGitRepo :=
  GitSandbox.initPureGit (GitConfig.gitConfig .localSandbox "main" "CodeTransport" "ct@local" 0 [] []) []

def defaultSimWorld : SimWorld :=
  SimWorld.simWorld zeroClock emptyProcessEnv pipeTTY (VirtualFs.virtualFs []) emptyNet defaultGitRepo emptyCanvasDOM

def cliSimWorld (prog : String) (as : List String) (stdinB : Bytes) (isTtyOut : Bool) (vfs : VirtualFs) : SimWorld :=
  SimWorld.simWorld
    zeroClock
    (SimProcessEnv.simProcessEnv prog as [] stdinB)
    (SimTTY.simTTY false isTtyOut false .empty .empty [] (blankScreen 24 80))
    vfs
    emptyNet
    defaultGitRepo
    emptyCanvasDOM

inductive Op : Cap → Type where
  | opNowMono     : Op .clockCap
  | opNowWall     : Op .clockCap
  | opSleepMs     : Nat → Op .clockCap
  | opGetProgName : Op .envCap
  | opGetArgs     : Op .envCap
  | opLookupEnv   : String → Op .envCap
  | opReadStdinAll  : Op .envCap
  | opReadStdinLine : Op .envCap
  | opIsTTYStdin  : Op .ttyCap
  | opIsTTYStdout : Op .ttyCap
  | opIsTTYStderr : Op .ttyCap
  | opTermSize    : Op .ttyCap
  | opWriteStdout : Bytes → Op .ttyCap
  | opWriteStderr : Bytes → Op .ttyCap
  | opReadTTYByte : Op .ttyCap
  | opReadFile    : String → Op .fsCap
  | opWriteFile   : String → Bytes → Op .fsCap
  | opMkdir       : String → Nat → Op .fsCap
  | opSymlink     : String → String → Op .fsCap
  | opUnlink      : String → Op .fsCap
  | opStat        : String → Op .fsCap
  | opTcpExchange : String → Nat → Bytes → Bool → Nat → Op .netCap
  | opTlsExchange : String → Nat → String → Bool → Bytes → Bytes → Nat → Op .netCap
  | opGitStep     : GitStep → Op .gitCap
  | opGitSummary  : Op .gitCap
  | opWebViewport  : Op .webCap
  | opWebSetTitle  : String → Op .webCap
  | opWebDrawScene : Scene Nat → Op .webCap
  | opWebHitTest   : Scene Nat → QPoint → Op .webCap
  | opWebPollInput : Op .webCap

def Ret : {c : Cap} → Op c → Type
  | _, .opNowMono                 => Nat
  | _, .opNowWall                 => Nat
  | _, .opSleepMs _               => Unit
  | _, .opGetProgName             => String
  | _, .opGetArgs                 => List String
  | _, .opLookupEnv _             => Option String
  | _, .opReadStdinAll            => Bytes
  | _, .opReadStdinLine           => Option Bytes
  | _, .opIsTTYStdin              => Bool
  | _, .opIsTTYStdout             => Bool
  | _, .opIsTTYStderr             => Bool
  | _, .opTermSize                => (Nat × Nat)
  | _, .opWriteStdout _           => Unit
  | _, .opWriteStderr _           => Unit
  | _, .opReadTTYByte             => Option Byte
  | _, .opReadFile _              => Sum FsError Bytes
  | _, .opWriteFile _ _           => Sum FsError Unit
  | _, .opMkdir _ _               => Sum FsError Unit
  | _, .opSymlink _ _             => Sum FsError Unit
  | _, .opUnlink _                => Sum FsError Unit
  | _, .opStat _                  => Sum FsError FsNodeKind
  | _, .opTcpExchange _ _ _ _ _   => Sum NetError Bytes
  | _, .opTlsExchange _ _ _ _ _ _ _ => Sum NetError Bytes
  | _, .opGitStep _               => Option GitRepoSummary
  | _, .opGitSummary              => GitRepoSummary
  | _, .opWebViewport             => Rect
  | _, .opWebSetTitle _           => Unit
  | _, .opWebDrawScene _          => Unit
  | _, .opWebHitTest _ _          => Option Nat
  | _, .opWebPollInput            => Option HostInput

inductive WorldProg (Δ : List Cap) (A : Type) : Type where
  | pure : A → WorldProg Δ A
  | step : {c : Cap} → CapMem c Δ → (op : Op c) → (Ret op → WorldProg Δ A) → WorldProg Δ A

def worldBind {Δ : List Cap} {A B : Type} : WorldProg Δ A → (A → WorldProg Δ B) → WorldProg Δ B
  | .pure a,       k => k a
  | .step h op k₁, k => .step h op (fun r => worldBind (k₁ r) k)
termination_by structural x _ => x

instance {Δ : List Cap} : Monad (WorldProg Δ) where
  pure := .pure
  bind := worldBind

@[macro_inline] def worldSeq {Δ : List Cap} {A B : Type} (m : WorldProg Δ A) (n : WorldProg Δ B) : WorldProg Δ B :=
  worldBind m (fun _ => n)

def mapWorld {Δ : List Cap} {A B : Type} (f : A → B) : WorldProg Δ A → WorldProg Δ B
  | .pure a      => .pure (f a)
  | .step h op k => .step h op (fun r => mapWorld f (k r))
termination_by structural x => x

def liftWorld {Δ₁ Δ₂ : List Cap} {A : Type} (sub : CapSub Δ₁ Δ₂) : WorldProg Δ₁ A → WorldProg Δ₂ A
  | .pure a      => .pure a
  | .step h op k => .step (sub h) op (fun r => liftWorld sub (k r))
termination_by structural x => x

def nowMonoW {Δ : List Cap} (h : CapMem .clockCap Δ) : WorldProg Δ Nat := .step h .opNowMono .pure
def nowWallW {Δ : List Cap} (h : CapMem .clockCap Δ) : WorldProg Δ Nat := .step h .opNowWall .pure
def sleepW {Δ : List Cap} (h : CapMem .clockCap Δ) (ms : Nat) : WorldProg Δ Unit := .step h (.opSleepMs ms) .pure
def getProgNameW {Δ : List Cap} (h : CapMem .envCap Δ) : WorldProg Δ String := .step h .opGetProgName .pure
def getArgsW {Δ : List Cap} (h : CapMem .envCap Δ) : WorldProg Δ (List String) := .step h .opGetArgs .pure
def lookupEnvW {Δ : List Cap} (h : CapMem .envCap Δ) (k : String) : WorldProg Δ (Option String) := .step h (.opLookupEnv k) .pure
def readStdinAllW {Δ : List Cap} (h : CapMem .envCap Δ) : WorldProg Δ Bytes := .step h .opReadStdinAll .pure
def readStdinLineW {Δ : List Cap} (h : CapMem .envCap Δ) : WorldProg Δ (Option Bytes) := .step h .opReadStdinLine .pure
def isTTYStdinW {Δ : List Cap} (h : CapMem .ttyCap Δ) : WorldProg Δ Bool := .step h .opIsTTYStdin .pure
def isTTYStdoutW {Δ : List Cap} (h : CapMem .ttyCap Δ) : WorldProg Δ Bool := .step h .opIsTTYStdout .pure
def isTTYStderrW {Δ : List Cap} (h : CapMem .ttyCap Δ) : WorldProg Δ Bool := .step h .opIsTTYStderr .pure
def termSizeW {Δ : List Cap} (h : CapMem .ttyCap Δ) : WorldProg Δ ((Nat × Nat)) := .step h .opTermSize .pure
def writeStdoutW {Δ : List Cap} (h : CapMem .ttyCap Δ) (bs : Bytes) : WorldProg Δ Unit := .step h (.opWriteStdout bs) .pure
def writeStdoutStrW {Δ : List Cap} (h : CapMem .ttyCap Δ) (s : String) : WorldProg Δ Unit := writeStdoutW h (bytes s)
def writeStderrW {Δ : List Cap} (h : CapMem .ttyCap Δ) (bs : Bytes) : WorldProg Δ Unit := .step h (.opWriteStderr bs) .pure
def writeStderrStrW {Δ : List Cap} (h : CapMem .ttyCap Δ) (s : String) : WorldProg Δ Unit := writeStderrW h (bytes s)
def readTTYByteW {Δ : List Cap} (h : CapMem .ttyCap Δ) : WorldProg Δ (Option Byte) := .step h .opReadTTYByte .pure
def readFileW {Δ : List Cap} (h : CapMem .fsCap Δ) (p : String) : WorldProg Δ (Sum FsError Bytes) := .step h (.opReadFile p) .pure
def writeFileW {Δ : List Cap} (h : CapMem .fsCap Δ) (p : String) (bs : Bytes) : WorldProg Δ (Sum FsError Unit) := .step h (.opWriteFile p bs) .pure
def mkdirW {Δ : List Cap} (h : CapMem .fsCap Δ) (p : String) (mode : Nat) : WorldProg Δ (Sum FsError Unit) := .step h (.opMkdir p mode) .pure
def symlinkW {Δ : List Cap} (h : CapMem .fsCap Δ) (p dst : String) : WorldProg Δ (Sum FsError Unit) := .step h (.opSymlink p dst) .pure
def unlinkW {Δ : List Cap} (h : CapMem .fsCap Δ) (p : String) : WorldProg Δ (Sum FsError Unit) := .step h (.opUnlink p) .pure
def statW {Δ : List Cap} (h : CapMem .fsCap Δ) (p : String) : WorldProg Δ (Sum FsError FsNodeKind) := .step h (.opStat p) .pure
def tcpExchangeW {Δ : List Cap} (h : CapMem .netCap Δ) (host : String) (port : Nat) (req : Bytes) (hc : Bool) (tms : Nat) :
    WorldProg Δ (Sum NetError Bytes) := .step h (.opTcpExchange host port req hc tms) .pure
def tlsExchangeW {Δ : List Cap} (h : CapMem .netCap Δ) (host : String) (port : Nat) (sni : String) (ins : Bool) (tun req : Bytes) (tms : Nat) :
    WorldProg Δ (Sum NetError Bytes) := .step h (.opTlsExchange host port sni ins tun req tms) .pure
def gitStepW {Δ : List Cap} (h : CapMem .gitCap Δ) (s : GitStep) : WorldProg Δ (Option GitRepoSummary) := .step h (.opGitStep s) .pure
def gitSummaryW {Δ : List Cap} (h : CapMem .gitCap Δ) : WorldProg Δ GitRepoSummary := .step h .opGitSummary .pure
def webViewportW {Δ : List Cap} (h : CapMem .webCap Δ) : WorldProg Δ Rect := .step h .opWebViewport .pure
def webSetTitleW {Δ : List Cap} (h : CapMem .webCap Δ) (t : String) : WorldProg Δ Unit := .step h (.opWebSetTitle t) .pure
def webDrawSceneW {Δ : List Cap} (h : CapMem .webCap Δ) (sc : Scene Nat) : WorldProg Δ Unit := .step h (.opWebDrawScene sc) .pure
def webHitTestW {Δ : List Cap} (h : CapMem .webCap Δ) (sc : Scene Nat) (q : QPoint) : WorldProg Δ (Option Nat) := .step h (.opWebHitTest sc q) .pure
def webPollInputW {Δ : List Cap} (h : CapMem .webCap Δ) : WorldProg Δ (Option HostInput) := .step h .opWebPollInput .pure

abbrev ExitCode : Type := Nat
abbrev CliApp (Δ : List Cap) : Type := WorldProg Δ ExitCode

inductive EventPayload : Cap → Type where
  | evTickMs   : Nat → EventPayload .clockCap
  | evSignal   : TermSignal → EventPayload .envCap
  | evKey      : Key → EventPayload .ttyCap
  | evResize   : Nat → Nat → EventPayload .ttyCap
  | evTTYBytes : Bytes → EventPayload .ttyCap
  | evFsWatch  : String → EventPayload .fsCap
  | evNetConn  : Bytes → EventPayload .netCap
  | evGitHook  : String → EventPayload .gitCap
  | evWebInput : HostInput → EventPayload .webCap

structure Event (Δ : List Cap) : Type where
  mkEvent ::
  {evCap    : Cap}
  evHasCap  : CapMem evCap Δ
  evPayload : EventPayload evCap

def liftEvent {Δ₁ Δ₂ : List Cap} (sub : CapSub Δ₁ Δ₂) (e : Event Δ₁) : Event Δ₂ :=
  Event.mkEvent (sub e.evHasCap) e.evPayload

structure ReactiveApp (Δ : List Cap) (S : Type) : Type where
  reactiveApp ::
  init   : WorldProg Δ S
  onStep : Event Δ → S → WorldProg Δ (Sum S ExitCode)

def lookupEnvVar (k : String) : List (String × String) → Option String
  | [] => .none
  | nv :: xs => if FsSandbox.eqStr k nv.1 then .some nv.2 else lookupEnvVar k xs
termination_by structural xs => xs

private def scanLineBytes : Byte → Bytes → Bytes × Bytes
  | cur, [] => Prod.mk [cur] []
  | cur, x :: xs =>
    if UInt8.toNat cur == 10 then Prod.mk [cur] (x :: xs)
    else
      let r := scanLineBytes x xs
      Prod.mk (cur :: r.1) r.2
termination_by structural _ xs => xs

def takeLineBytes : Bytes → Option Bytes × Bytes
  | [] => Prod.mk .none []
  | b :: bs =>
    let r := scanLineBytes b bs
    Prod.mk (.some r.1) r.2

def popByte : Bytes → Option Byte × Bytes
  | [] => Prod.mk .none []
  | b :: bs => Prod.mk (.some b) bs

def hasDotSlashPrefix : List Char → Bool
  | c₁ :: c₂ :: _ => Char.toNat c₁ == 46 && Char.toNat c₂ == 47
  | _ => false

def stripDotSlashChars : List Char → List Char
  | c₁ :: c₂ :: cs =>
    if Char.toNat c₁ == 46 && Char.toNat c₂ == 47 then stripDotSlashChars cs else c₁ :: c₂ :: cs
  | cs => cs
termination_by structural cs => cs

def normalizeRelPath (p : String) : String :=
  (if (hasDotSlashPrefix (String.toList p)) then (String.ofList (stripDotSlashChars (String.toList p))) else p)

def readVirtualFileFuel : Nat → String → VirtualFs → Sum FsError Bytes
  | 0, _, _ => .inl .fsSymlinkLoop
  | Nat.succ fuel, rawP, v =>
    let p := normalizeRelPath rawP
    if FsSandbox.eqStr p "." then .inl .fsIsDirectory
    else
      if Bool.not (FsSandbox.validRelPath p) then .inl .fsInvalidPath
      else
        match FsSandbox.lookupEntry p v.fsEntries with
        | .none => .inl .fsNotFound
        | .some e =>
          if FsSandbox.eqKind e.entryKind .regularNode then .inr e.entryBytes
          else
            if FsSandbox.eqKind e.entryKind .dirNode then .inl .fsIsDirectory
            else readVirtualFileFuel fuel (NetSandbox.wireText e.entryBytes) v
termination_by structural f _ _ => f

def readVirtualFile : String → VirtualFs → Sum FsError Bytes :=
  readVirtualFileFuel 8

def writeVirtualFileFuel : Nat → String → Bytes → VirtualFs → Sum FsError Unit × VirtualFs
  | 0, _, _, v => Prod.mk (.inl .fsSymlinkLoop) v
  | Nat.succ fuel, rawP, bs, v =>
    let p := normalizeRelPath rawP
    if FsSandbox.eqStr p "." then Prod.mk (.inl .fsIsDirectory) v
    else
      if Bool.not (FsSandbox.validRelPath p) then Prod.mk (.inl .fsInvalidPath) v
      else
        match FsSandbox.ensureParents true (FsSandbox.parentPaths p) v with
        | .none => Prod.mk (.inl .fsNotDirectory) v
        | .some v₁ =>
          match FsSandbox.lookupEntry p v₁.fsEntries with
          | .none =>
            Prod.mk (.inr ()) (FsSandbox.putEntry (FsEntryObs.fsEntry p .regularNode 420 bs) v₁)
          | .some e =>
            if FsSandbox.eqKind e.entryKind .regularNode then
              Prod.mk (.inr ())
                (FsSandbox.putEntry (FsEntryObs.fsEntry p .regularNode e.entryMode bs) v₁)
            else
              if FsSandbox.eqKind e.entryKind .dirNode then Prod.mk (.inl .fsIsDirectory) v
              else writeVirtualFileFuel fuel (NetSandbox.wireText e.entryBytes) bs v
termination_by structural f _ _ _ => f

def writeVirtualFile : String → Bytes → VirtualFs → Sum FsError Unit × VirtualFs :=
  writeVirtualFileFuel 8

def mkdirVirtual (rawP : String) (mode : Nat) (v : VirtualFs) : Sum FsError Unit × VirtualFs :=
  let p := normalizeRelPath rawP
  if FsSandbox.eqStr p "." then Prod.mk (.inr ()) v
  else
    if Bool.not (FsSandbox.validRelPath p) then Prod.mk (.inl .fsInvalidPath) v
    else
      match FsSandbox.ensureParents true (FsSandbox.parentPaths p) v with
      | .none => Prod.mk (.inl .fsNotDirectory) v
      | .some v₁ =>
        match FsSandbox.lookupEntry p v₁.fsEntries with
        | .none =>
          Prod.mk (.inr ())
            (FsSandbox.putEntry (FsEntryObs.fsEntry p .dirNode (FsSandbox.maskMode mode) []) v₁)
        | .some e =>
          if FsSandbox.eqKind e.entryKind .dirNode then
            Prod.mk (.inr ())
              (FsSandbox.putEntry (FsEntryObs.fsEntry p .dirNode (FsSandbox.maskMode mode) []) v₁)
          else Prod.mk (.inl .fsAlreadyExists) v

def symlinkVirtual (rawP dest : String) (v : VirtualFs) : Sum FsError Unit × VirtualFs :=
  let p := normalizeRelPath rawP
  let okDst :=
    Bool.not (FsSandbox.eqStr dest "") &&
      FsSandbox.all (fun c => Bool.not (Char.toNat c == 0)) (String.toList dest)
  if Bool.not okDst || (FsSandbox.eqStr p "." || Bool.not (FsSandbox.validRelPath p)) then
    Prod.mk (.inl .fsInvalidPath) v
  else
    match FsSandbox.ensureParents true (FsSandbox.parentPaths p) v with
    | .none => Prod.mk (.inl .fsNotDirectory) v
    | .some v₁ =>
      match FsSandbox.lookupEntry p v₁.fsEntries with
      | .none =>
        Prod.mk (.inr ())
          (FsSandbox.putEntry (FsEntryObs.fsEntry p .symlinkNode 511 (bytes dest)) v₁)
      | .some e =>
        if FsSandbox.eqKind e.entryKind .dirNode then Prod.mk (.inl .fsIsDirectory) v
        else
          Prod.mk (.inr ())
            (FsSandbox.putEntry (FsEntryObs.fsEntry p .symlinkNode 511 (bytes dest)) v₁)

def unlinkVirtual (rawP : String) (v : VirtualFs) : Sum FsError Unit × VirtualFs :=
  let p := normalizeRelPath rawP
  if FsSandbox.eqStr p "." || Bool.not (FsSandbox.validRelPath p) then
    Prod.mk (.inl .fsInvalidPath) v
  else
    match FsSandbox.ensureParents false (FsSandbox.parentPaths p) v with
    | .none => Prod.mk (.inl .fsNotDirectory) v
    | .some _ =>
      match FsSandbox.lookupEntry p v.fsEntries with
      | .none => Prod.mk (.inl .fsNotFound) v
      | .some _ =>
        if FsSandbox.all (fun x => Bool.not (FsSandbox.isParent p x.entryPath)) v.fsEntries then
          Prod.mk (.inr ()) (VirtualFs.virtualFs (FsSandbox.removeEntry p v.fsEntries))
        else Prod.mk (.inl .fsIsDirectory) v

def statVirtual (rawP : String) (v : VirtualFs) : Sum FsError FsNodeKind :=
  let p := normalizeRelPath rawP
  if FsSandbox.eqStr p "." then .inr .dirNode
  else
    if Bool.not (FsSandbox.validRelPath p) then .inl .fsInvalidPath
    else
      match FsSandbox.lookupEntry p v.fsEntries with
      | .none => .inl .fsNotFound
      | .some e => .inr e.entryKind

def isLoopbackHost (h : String) : Bool :=
  FsSandbox.eqStr h "127.0.0.1" ||
    (FsSandbox.eqStr h "localhost" || (FsSandbox.eqStr h "[::1]" || FsSandbox.eqStr h "::1"))

def hostMatches (epH reqH : String) : Bool :=
  FsSandbox.eqStr epH "*" || (FsSandbox.eqStr epH reqH || isLoopbackHost epH && isLoopbackHost reqH)

def findEndpoint (wantTls : Bool) (host : String) (port : Nat) :
    List NetEndpoint → Option NetEndpoint
  | [] => .none
  | ep :: eps =>
    let sameTls := if wantTls then ep.epTls else Bool.not ep.epTls
    if sameTls && (ep.epPort == port && hostMatches ep.epHost host) then .some ep
    else findEndpoint wantTls host port eps
termination_by structural eps => eps

def stubDelayOf : NetTopology → Nat
  | .httpDelayedStubMode d _ => d
  | .tcpDelayedStubMode  d _ => d
  | _                        => 0

def evalNetExchange (wantTls insecure : Bool) (host : String) (port : Nat) (req : Bytes)
    (timeoutMs : Nat) (netSt : SimNet) : Sum NetError Bytes × SimNet :=
  let badHostPort := FsSandbox.eqStr host "" || (port == 0 || 65535 < port)
  if badHostPort then Prod.mk (.inl .netInvalidEndpoint) netSt
  else
    match findEndpoint wantTls host port netSt.endpoints with
    | .none => Prod.mk (.inl .netConnRefused) netSt
    | .some ep =>
      let effTimeout := if timeoutMs == 0 then 30000 else timeoutMs
      let totalDelay := ep.epLatencyMs + stubDelayOf ep.epTopology
      let certBad := wantTls && (Bool.not insecure && Bool.not ep.epCertOk)
      let timedOut := 0 < totalDelay && effTimeout ≤ totalDelay
      let recorded :=
        { netSt with capturedWire := netSt.capturedWire.push (host, port, req) }
      if certBad then Prod.mk (.inl .netTlsError) recorded
      else
        if timedOut then Prod.mk (.inl .netTimedOut) recorded
        else Prod.mk (.inr (NetSandbox.stubReply ep.epTopology req)) recorded

def popWebEvent : List HostInput → Option HostInput × List HostInput
  | [] => Prod.mk .none []
  | e :: es => Prod.mk (.some e) es

/-- Each operation updates only the component selected by its capability. -/
def stepWorldPure {c : Cap} : (op : Op c) → SimWorld → ((Ret op) × SimWorld)
  | .opNowMono, w =>
      let r := readMonoMs w.clock
      Prod.mk r.1 { w with clock := r.2 }
  | .opNowWall, w =>
      let r := readWallMs w.clock
      Prod.mk r.1 { w with clock := r.2 }
  | .opSleepMs ms, w =>
      Prod.mk () { w with clock := sleepClockMs ms w.clock }
  | .opGetProgName, w =>
      Prod.mk w.env.progName w
  | .opGetArgs, w =>
      Prod.mk w.env.args w
  | .opLookupEnv k, w =>
      Prod.mk (lookupEnvVar k w.env.envVars) w
  | .opReadStdinAll, w =>
      Prod.mk w.env.stdinBytes { w with env := { w.env with stdinBytes := [] } }
  | .opReadStdinLine, w =>
      let r := takeLineBytes w.env.stdinBytes
      Prod.mk r.1 { w with env := { w.env with stdinBytes := r.2 } }
  | .opIsTTYStdin, w  => Prod.mk w.tty.ttyStdin w
  | .opIsTTYStdout, w => Prod.mk w.tty.ttyStdout w
  | .opIsTTYStderr, w => Prod.mk w.tty.ttyStderr w
  | .opTermSize, w =>
      Prod.mk (Prod.mk w.tty.ttyScreen.height w.tty.ttyScreen.width) w
  | .opWriteStdout bs, w =>
      let t := w.tty
      let nextScr := (if t.ttyStdout then (stepANSI t.ttyScreen bs) else t.ttyScreen)
      Prod.mk () { w with tty := { t with stdoutBuf := (bs.foldl ByteArray.push t.stdoutBuf), ttyScreen := nextScr } }
  | .opWriteStderr bs, w =>
      let t := w.tty
      let nextScr := (if t.ttyStderr then (stepANSI t.ttyScreen bs) else t.ttyScreen)
      Prod.mk () { w with tty := { t with stderrBuf := (bs.foldl ByteArray.push t.stderrBuf), ttyScreen := nextScr } }
  | .opReadTTYByte, w =>
      let t := w.tty
      let r := popByte t.ttyInput
      Prod.mk r.1 { w with tty := { t with ttyInput := r.2 } }
  | .opReadFile p, w =>
      Prod.mk (readVirtualFile p w.fs) w
  | .opWriteFile p bs, w =>
      let r := writeVirtualFile p bs w.fs
      Prod.mk r.1 { w with fs := r.2 }
  | .opMkdir p mode, w =>
      let r := mkdirVirtual p mode w.fs
      Prod.mk r.1 { w with fs := r.2 }
  | .opSymlink p dst, w =>
      let r := symlinkVirtual p dst w.fs
      Prod.mk r.1 { w with fs := r.2 }
  | .opUnlink p, w =>
      let r := unlinkVirtual p w.fs
      Prod.mk r.1 { w with fs := r.2 }
  | .opStat p, w =>
      Prod.mk (statVirtual p w.fs) w
  | .opTcpExchange host port req _ tms, w =>
      let r := evalNetExchange false false host port req tms w.net
      Prod.mk r.1 { w with net := r.2 }
  | .opTlsExchange host port _ ins _ req tms, w =>
      let r := evalNetExchange true ins host port req tms w.net
      Prod.mk r.1 { w with net := r.2 }
  | .opGitStep gs, w =>
      let r := GitSandbox.stepPureGit gs w.git
      Prod.mk r.2 { w with git := r.1 }
  | .opGitSummary, w =>
      Prod.mk (GitSandbox.projectSummary w.git) w
  | .opWebViewport, w =>
      Prod.mk w.web.domViewport w
  | .opWebSetTitle title, w =>
      Prod.mk () { w with web := { w.web with domTitle := title } }
  | .opWebDrawScene sc, w =>
      Prod.mk () { w with web := { w.web with domCommands := WebOperad.compileDraw sc } }
  | .opWebHitTest sc q, w =>
      Prod.mk (WebOperad.hitTest sc q) w
  | .opWebPollInput, w =>
      let r := popWebEvent w.web.domEvents
      Prod.mk r.1 { w with web := { w.web with domEvents := r.2 } }

def runWorldPure {Δ : List Cap} {A : Type} : WorldProg Δ A → SimWorld → (A × SimWorld)
  | .pure a,      w => Prod.mk a w
  | .step _ op k, w =>
      let rw := stepWorldPure op w
      runWorldPure (k rw.1) rw.2
termination_by structural x _ => x

def runCliPure {Δ : List Cap} : CliApp Δ → SimWorld → (ExitCode × SimWorld) :=
  runWorldPure

def runReactiveSteps {Δ : List Cap} {S : Type} (app : ReactiveApp Δ S) :
    S → List (Event Δ) → SimWorld → Sum S ExitCode × SimWorld
  | s, [], w => Prod.mk (.inl s) w
  | s, e :: es, w =>
    let r := runWorldPure (app.onStep e s) w
    match r.1 with
    | .inl s' => runReactiveSteps app s' es r.2
    | .inr code => Prod.mk (.inr code) r.2
termination_by structural _ evs _ => evs

def runReactivePure {Δ : List Cap} {S : Type} (app : ReactiveApp Δ S)
    (evs : List (Event Δ)) (w : SimWorld) : ((Sum S ExitCode) × SimWorld) :=
  let initRes := runWorldPure app.init w
  runReactiveSteps app initRes.1 evs initRes.2
end LojitaCtx.World