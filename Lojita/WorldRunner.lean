import LojitaCtx.World

namespace Lojita.WorldRunner

open LojitaCtx LojitaCtx.Terminal LojitaCtx.World LojitaCtx.FsSandbox LojitaCtx.GitSandbox LojitaCtx.WebOperad

@[extern "ct_lean_now_mono_ms"]
private opaque ctLeanNowMonoMs : IO Nat

@[extern "ct_lean_now_wall_ms"]
private opaque ctLeanNowWallMs : IO Nat

@[extern "ct_lean_sleep_ms"]
private opaque ctLeanSleepMs (ms : UInt32) : IO Unit

@[extern "ct_lean_lookup_env"]
private opaque ctLeanLookupEnvRaw (key : @& String) : IO (Option String)

@[extern "ct_lean_read_stdin_all"]
private opaque ctLeanReadStdinAll : IO ByteArray

@[extern "ct_lean_read_stdin_line"]
private opaque ctLeanReadStdinLine : IO (Option ByteArray)

@[extern "ct_lean_term_size"]
private opaque ctLeanTermSize : IO (Nat × Nat)

@[extern "ct_lean_write_fd"]
private opaque ctLeanWriteFd (fd : UInt32) (ba : @& ByteArray) : IO Unit

@[extern "ct_lean_read_tty_byte"]
private opaque ctLeanReadTTYByte : IO (Option Nat)

@[extern "ct_lean_poll_reactive_event"]
private opaque ctLeanPollReactiveEvent (waitMs : UInt32) : IO (Nat × (Nat × Nat))

@[extern "ct_lean_fs_read_file"]
private opaque ctLeanFsReadFile (path : @& String) : IO (Except Nat ByteArray)

@[extern "ct_lean_fs_write_file"]
private opaque ctLeanFsWriteFile (path : @& String) (ba : @& ByteArray) : IO (Except Nat Unit)

@[extern "ct_lean_fs_mkdir"]
private opaque ctLeanFsMkdir (path : @& String) (mode : UInt32) : IO (Except Nat Unit)

@[extern "ct_lean_fs_symlink"]
private opaque ctLeanFsSymlink (path : @& String) (dest : @& String) : IO (Except Nat Unit)

@[extern "ct_lean_fs_unlink"]
private opaque ctLeanFsUnlink (path : @& String) : IO (Except Nat Unit)

@[extern "ct_lean_fs_stat"]
private opaque ctLeanFsStat (path : @& String) : IO (Except Nat Nat)

@[extern "ct_lean_tcp_exchange_code"]
private opaque ctLeanTcpExchangeCode (host : @& String) (port : UInt32) (req : @& ByteArray)
    (halfClose : UInt8) (timeoutMs : UInt32) : IO (Except Nat ByteArray)

@[extern "ct_lean_tls_exchange_code"]
private opaque ctLeanTlsExchangeCode (host : @& String) (port : UInt32) (sni : @& String)
    (insecure : UInt8) (tunnelReq : @& ByteArray) (req : @& ByteArray)
    (timeoutMs : UInt32) : IO (Except Nat ByteArray)

@[extern "ct_lean_prog_name"] private opaque progName : IO String
@[extern "ct_lean_argc"] private opaque argCount : IO Nat
@[extern "ct_lean_arg_at"] private opaque argAt (i : UInt32) : IO String
@[extern "ct_lean_is_tty"] private opaque isTTY (fd : UInt32) : IO Bool

private def getArgs : IO (List String) := do
  let mut args := #[]
  for i in [:← argCount] do
    args := args.push (← argAt i.toUInt32)
  return args.toList

private def toBytes (bs : Bytes) := ByteArray.mk bs.toArray
private def fromBytes (ba : ByteArray) := ba.data.toList

private def decodeFsError : Nat → FsError
  | 1 => .fsNotFound
  | 2 => .fsIsDirectory
  | 3 => .fsNotDirectory
  | 4 => .fsAlreadyExists
  | 5 => .fsPermissionDenied
  | 6 => .fsSymlinkLoop
  | 7 => .fsInvalidPath
  | _ => .fsIoError

private def decodeNodeKind : Nat → FsNodeKind
  | 0 => .regularNode
  | 1 => .dirNode
  | _ => .symlinkNode

private def decodeNetError : Nat → NetError
  | 1 => .netConnRefused
  | 2 => .netTimedOut
  | 3 => .netInvalidEndpoint
  | 4 => .netTlsError
  | _ => .netIoError

private def decodeSignal : Nat → TermSignal
  | 1 => .sigINT
  | 2 => .sigTERM
  | 3 => .sigHUP
  | _ => .sigQUIT

private def execOpIO : {c : Cap} → (op : Op c) → PureGitRepo → CanvasDOM → IO (Ret op × PureGitRepo × CanvasDOM)
  | .clockCap, .opNowMono, g, w => do
      let t ← ctLeanNowMonoMs
      pure (t, g, w)
  | .clockCap, .opNowWall, g, w => do
      let t ← ctLeanNowWallMs
      pure (t, g, w)
  | .clockCap, .opSleepMs ms, g, w => do
      let clamped := if ms > 3600000 then 3600000 else ms
      ctLeanSleepMs (UInt32.ofNat clamped)
      pure ((), g, w)
  | .envCap, .opGetProgName, g, w => do
      let p ← progName
      pure (p, g, w)
  | .envCap, .opGetArgs, g, w => do
      let as ← getArgs
      pure (as, g, w)
  | .envCap, .opLookupEnv k, g, w => do
      match (← ctLeanLookupEnvRaw k) with
      | some v => pure (.some v, g, w)
      | none   => pure (.none, g, w)
  | .envCap, .opReadStdinAll, g, w => do
      let ba ← ctLeanReadStdinAll
      pure (fromBytes ba, g, w)
  | .envCap, .opReadStdinLine, g, w => do
      match (← ctLeanReadStdinLine) with
      | some ba => pure (.some (fromBytes ba), g, w)
      | none    => pure (.none, g, w)
  | .ttyCap, .opIsTTYStdin, g, w => do
      let b ← isTTY 0
      pure (b, g, w)
  | .ttyCap, .opIsTTYStdout, g, w => do
      let b ← isTTY 1
      pure (b, g, w)
  | .ttyCap, .opIsTTYStderr, g, w => do
      let b ← isTTY 2
      pure (b, g, w)
  | .ttyCap, .opTermSize, g, w => do
      let (r, c) ← ctLeanTermSize
      pure (Prod.mk r c, g, w)
  | .ttyCap, .opWriteStdout bs, g, w => do
      ctLeanWriteFd 1 (toBytes bs)
      pure ((), g, w)
  | .ttyCap, .opWriteStderr bs, g, w => do
      ctLeanWriteFd 2 (toBytes bs)
      pure ((), g, w)
  | .ttyCap, .opReadTTYByte, g, w => do
      match (← ctLeanReadTTYByte) with
      | some b => pure (.some (byte b), g, w)
      | none   => pure (.none, g, w)
  | .fsCap, .opReadFile p, g, w => do
      match (← ctLeanFsReadFile p) with
      | .error ec => pure (.inl (decodeFsError ec), g, w)
      | .ok ba    => pure (.inr (fromBytes ba), g, w)
  | .fsCap, .opWriteFile p bs, g, w => do
      match (← ctLeanFsWriteFile p (toBytes bs)) with
      | .error ec => pure (.inl (decodeFsError ec), g, w)
      | .ok _     => pure (.inr (), g, w)
  | .fsCap, .opMkdir p mode, g, w => do
      match (← ctLeanFsMkdir p (UInt32.ofNat (mode % 512))) with
      | .error ec => pure (.inl (decodeFsError ec), g, w)
      | .ok _     => pure (.inr (), g, w)
  | .fsCap, .opSymlink p dst, g, w => do
      match (← ctLeanFsSymlink p dst) with
      | .error ec => pure (.inl (decodeFsError ec), g, w)
      | .ok _     => pure (.inr (), g, w)
  | .fsCap, .opUnlink p, g, w => do
      match (← ctLeanFsUnlink p) with
      | .error ec => pure (.inl (decodeFsError ec), g, w)
      | .ok _     => pure (.inr (), g, w)
  | .fsCap, .opStat p, g, w => do
      match (← ctLeanFsStat p) with
      | .error ec => pure (.inl (decodeFsError ec), g, w)
      | .ok kd    => pure (.inr (decodeNodeKind kd), g, w)
  | .netCap, .opTcpExchange host port req hc tms, g, w => do
      let clampedT := if tms > 3600000 then 3600000 else tms
      let portU := if port > 65535 then 65536 else port
      match (← ctLeanTcpExchangeCode host (UInt32.ofNat portU) (toBytes req) (if hc then 1 else 0) (UInt32.ofNat clampedT)) with
      | .error ec => pure (.inl (decodeNetError ec), g, w)
      | .ok ba    => pure (.inr (fromBytes ba), g, w)
  | .netCap, .opTlsExchange host port sni ins tun req tms, g, w => do
      let clampedT := if tms > 3600000 then 3600000 else tms
      let portU := if port > 65535 then 65536 else port
      match (← ctLeanTlsExchangeCode host (UInt32.ofNat portU) sni (if ins then 1 else 0) (toBytes tun) (toBytes req) (UInt32.ofNat clampedT)) with
      | .error ec => pure (.inl (decodeNetError ec), g, w)
      | .ok ba    => pure (.inr (fromBytes ba), g, w)
  | .gitCap, .opGitStep gs, g, w =>
      let r := stepPureGit gs g
      pure (r.2, r.1, w)
  | .gitCap, .opGitSummary, g, w =>
      pure (projectSummary g, g, w)
  | .webCap, .opWebViewport, g, w =>
      pure (w.domViewport, g, w)
  | .webCap, .opWebSetTitle title, g, w =>
      pure ((), g, { w with domTitle := title })
  | .webCap, .opWebDrawScene sc, g, w =>
      pure ((), g, { w with domCommands := compileDraw sc })
  | .webCap, .opWebHitTest sc q, g, w =>
      pure (hitTest sc q, g, w)
  | .webCap, .opWebPollInput, g, w =>
      let r := popWebEvent w.domEvents
      pure (r.1, g, { w with domEvents := r.2 })

private def runWorldState {Δ : List Cap} {A : Type} :
    PureGitRepo → CanvasDOM → WorldProg Δ A → IO (A × PureGitRepo × CanvasDOM)
  | g, w, .pure a      => pure (a, g, w)
  | g, w, .step _ op k => do
      let (ret, g', w') ← execOpIO op g w
      runWorldState g' w' (k ret)

termination_by structural _ _ p => p

private def hasLiveEventSource (Δ : List Cap) : Bool :=
  match findCapIn .clockCap Δ, findCapIn .envCap Δ, findCapIn .ttyCap Δ with
  | .some _,  _,        _        => true
  | .none, .some _,  _        => true
  | .none, .none, .some _  => true
  | .none, .none, .none => false

private def decodePolledEvent (Δ : List Cap) (kind a b : Nat) : Option (Event Δ) :=
  if kind == 2 then
    match findCapIn .envCap Δ with
    | .some hEnv => some (Event.mkEvent hEnv (.evSignal (decodeSignal a)))
    | .none   => none
  else if kind == 3 then
    match findCapIn .ttyCap Δ with
    | .some hTty => some (Event.mkEvent hTty (.evResize a b))
    | .none   => none
  else if kind == 4 then
    match findCapIn .ttyCap Δ with
    | .some hTty => some (Event.mkEvent hTty (.evTTYBytes [byte a]))
    | .none   => none
  else
    match findCapIn .clockCap Δ with
    | .some hClk => some (Event.mkEvent hClk (.evTickMs a))
    | .none   => none


def runWorldIO {Δ : List Cap} {A : Type} (p : WorldProg Δ A) : IO A := do
  let (a, _, _) ← runWorldState defaultGitRepo emptyCanvasDOM p
  return a

def runCliIO {Δ : List Cap} (app : CliApp Δ) : IO UInt32 := do
  return ((← runWorldIO app) % 256).toUInt32

def runReactiveIO {Δ : List Cap} {S : Type} (app : ReactiveApp Δ S) : IO UInt32 := do
  let (initial, git, web) ← runWorldState defaultGitRepo emptyCanvasDOM app.init
  if !hasLiveEventSource Δ then return 0
  let mut s := initial
  let mut g := git
  let mut w := web
  repeat
    let (kind, a, b) ← ctLeanPollReactiveEvent 25
    if let some ev := decodePolledEvent Δ kind a b then
      let (result, nextGit, nextWeb) ← runWorldState g w (app.onStep ev s)
      match result with
      | .inr code => return (code % 256).toUInt32
      | .inl next =>
        s := next
        g := nextGit
        w := nextWeb
  return 0

end Lojita.WorldRunner
