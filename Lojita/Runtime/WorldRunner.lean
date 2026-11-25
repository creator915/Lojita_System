import Lojita.Runtime.PosixNative

namespace Lojita.Runtime.WorldRunner
open LojitaCtx.Posix Lojita.Runtime.PosixNative

/-- Interpret one typed request. libc error codes survive the wire, including
    uncommon codes outside the model's named subset. -/
def perform (args : List Bytes) (op : SysOp) : IO (Ret op.Result) :=
  match (motive := (o : SysOp) → IO (Ret o.Result)) op with
  | .read fd n => do return (← invoke 0 (fdArg fd) (min n 0x7ffff000)).packed
  | .write fd bs => do return (← invoke 1 (fdArg fd) 0 0 bs).number
  | .pread fd n off => do
    if off > 9223372036854775807 then return .err (.other 75)
    return (← invoke 2 (fdArg fd) (min n 0x7ffff000) off).packed
  | .pwrite fd bs off => do
    if off > 9223372036854775807 then return .err (.other 75)
    return (← invoke 3 (fdArg fd) 0 off bs).number
  | .lseek fd off whence => do
    if off < -9223372036854775808 || off > 9223372036854775807 then return .err (.other 75)
    let whence := match whence with | .set => 0 | .cur => 1 | .end => 2
    return (← invoke 4 (fdArg fd) off.toInt64.toUInt64.toNat whence).number
  | .close fd => do return (← invoke 5 (fdArg fd)).unit
  | .dup2 src dst => do return (← invoke 6 (fdArg src) (fdArg dst)).number
  | .setNonblock fd on => do
    let before ← invoke 7 (fdArg fd)
    if before.error != 0 then return .err (Errno.decode before.error)
    let clear := before.value - (before.value &&& 2048)
    return (← invoke 8 (fdArg fd) (clear + on.toNat * 2048)).unit
  | .setCloexec fd on => do return (← invoke 9 (fdArg fd) on.toNat).unit
  | .pipe2 nb ce => do
    return (← invoke 10 nb.toNat ce.toNat).result (fun r => (r.value,word r.data 0 4))
  | .ppoll reqs timeout catchSignals => do
    let input := reqs.flatMap fun r => encodeWord (fdArg r.fd) 4 ++ encodeWord r.events 4
    let r ← invoke 11 (timeout.getD 0) timeout.isSome.toNat catchSignals.toNat input.toByteArray
    return r.result (fun v => (List.range reqs.length).map (fun i => word v.data (2*i) 2))
  | .fstat fd => do return stat (← invoke 12 (fdArg fd))
  | .openat d p f mode => do return (← pathCall 13 (dirArg d) p (flags f) mode).number
  | .mkdirat d p mode => do return (← pathCall 14 (dirArg d) p mode).unit
  | .unlinkat d p rd => do return (← pathCall 15 (dirArg d) p rd.toNat).unit
  | .symlinkat target d p => do return (← pathCall 16 (dirArg d) p 0 0 target).unit
  | .renameat d p e q => do return (← pathCall 17 (dirArg d) p (dirArg e) 0 q).unit
  | .readlinkat d p => do return (← pathCall 18 (dirArg d) p).bytes
  | .fstatat d p follow => do return stat (← pathCall 19 (dirArg d) p follow.toNat)
  | .chdir p => do return (← pathCall 20 0 p).unit
  | .getcwd => do return (← invoke 21).bytes
  | .tcgetattr fd => do return (← invoke 22 (fdArg fd)).result (fun r => fromBits r.value)
  | .tcsetattr fd t => do
    let before ← invoke 22 (fdArg fd)
    if before.error != 0 then return .err (Errno.decode before.error)
    return (← invoke 23 (fdArg fd) (ttyBits t) 0 before.data).unit
  | .getWinsize fd => do
    return (← invoke 24 (fdArg fd)).result (fun r => ⟨r.value,word r.data 0 2⟩)
  | .setWinsize fd ws => do return (← invoke 25 (fdArg fd) ws.rows ws.cols).unit
  | .isatty fd => do return (← invoke 26 (fdArg fd)).result (fun r => r.value != 0)
  | .socketStream nb ce => do return (← invoke 27 nb.toNat ce.toNat).number
  | .connectLoopback fd port => do
    if port > 65535 then return .err .EINVAL
    return (← invoke 28 (fdArg fd) port).unit
  | .shutdown fd rd wr => do
    if !rd && !wr then return .err .EINVAL
    return (← invoke 29 (fdArg fd) (if rd then (if wr then 2 else 0) else 1)).unit
  | .clockGettime => do return (← invoke 30).number
  | .nanosleep ns => do return (← invoke 31 ns).unit
  | .getArgs => pure (.ok args)
  | .lookupEnv key => do
    return (← pathCall 32 0 key).result fun r => if r.value = 0 then none else some r.data.data.toList

/-- Interpret the current finite tree, releasing requests and replies as it advances. -/
private def runStep {A : Type} (args : List Bytes) (tree : FreeSys CoreCaps A) : IO A := do
  let mut current := tree
  repeat
    match current with
    | .pure a => return a
    | .step op _ next => current := next (← perform args op)

/-- The only state retained between rounds is the application's explicit state. -/
def runBytes {S : Type} (p : PosixMachine CoreCaps S UInt32) (args : List Bytes) : IO UInt32 := do
  -- Keep SIGPIPE observable as EPIPE, then restore the inherited SIGINT policy
  -- on the interpreter thread after native worker initialization.
  for signal in [0,1] do
    let setup ← invoke 33 signal
    if setup.error != 0 then throw (IO.userError s!"sigaction: errno {setup.error}")
  let mut state := p.init
  repeat
    match ← runStep args (p.step state) with
    | .inl next => state := next
    | .inr code => return code

def run {S : Type} (p : PosixMachine CoreCaps S UInt32) (args : List String := []) : IO UInt32 :=
  runBytes p (args.map fun s => s.toUTF8.data.toList)

/-- The static entry sends original argv bytes through the Lean String entry
    ABI as ASCII hex. The trusted decoder runs once before interpreting the app. -/
def processMain {S : Type} (p : PosixMachine CoreCaps S UInt32) (encoded : List String) : IO UInt32 := do
  let args ← encoded.mapM fun s => do
    let digits := s.toUTF8
    if digits.size % 2 != 0 then throw (IO.userError "invalid argv encoding")
    let nibble := fun (b : UInt8) => if b ≤ 57 then b-48 else b-87
    let mut bytes : Array UInt8 := #[]
    for i in [:digits.size/2] do
      bytes := bytes.push ((nibble digits[2*i]!) * (16 : UInt8) + nibble digits[2*i+1]!)
    return bytes.toList
  runBytes p args

end Lojita.Runtime.WorldRunner
