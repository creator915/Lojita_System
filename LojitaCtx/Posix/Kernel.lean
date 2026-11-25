import LojitaCtx.Posix.Kernel.FdIo

namespace LojitaCtx.Posix

def openPath (m : Machine) (dir : DirFd) (path : Bytes) (f : OpenFlags) (mode : FileMode) :
    Except Errno (Transition Fd) := do
  if m.fds.size ≥ m.proc.limit then throw .EMFILE
  let start ← m.dirStart dir path
  let (ino,t) ← vfsOpenat m.kernel.vfs m.proc.root start path f (mode &&& (511-m.proc.umask))
  let (fd,m') ← (m.setVfs t).allocate (.inode ino) f
  return (.ok fd,m')

def ttyOf (m : Machine) (fd : Fd) : Except Errno (PtyId × PtyState) := do
  let (_,d) ← m.lookup fd
  let .pty id _ := d.target | throw .ENOTTY
  let some tty := m.kernel.ptys[id]? | throw .EBADF
  return (id,tty)

private def socketOf (m : Machine) (fd : Fd) : Except Errno (SockId × SocketState) := do
  let (_,d) ← m.lookup fd
  let .sock id := d.target | throw .ENOTSOCK
  let some sock := m.kernel.socks[id]? | throw .EBADF
  return (id,sock)

private def readyMask (events : Nat) (readable writable hup err : Bool) : Nat :=
  (((if readable then 1 else 0) ||| (if writable then 4 else 0)) &&& events) |||
    (if hup then 16 else 0) ||| (if err then 8 else 0)

def pollOne (m : Machine) (req : PollReq) : Nat := Id.run do
  let .ok (_,d) := m.lookup req.fd | return 32
  let ev := req.events
  match d.target with
  | .inode _ => return readyMask ev true true false false
  | .pipe i wr =>
    let some s := m.kernel.pipes[i]? | return 32
    if wr then return readyMask ev false (PipePages.freeSlots (m.pages i s) s.cap > 0) false (s.readers == 0)
    return readyMask ev (!s.pendingBytes.isEmpty) false (s.writers == 0) false
  | .pty i master =>
    let some t := m.kernel.ptys[i]? | return 32
    let stream := if master then t.toMaster else t.toSlave
    let hup := stream.writers == 0
    let readable := !stream.pendingBytes.isEmpty || (!master && (hup || t.records.head? == some 0))
    return readyMask ev readable true hup (!master && hup)
  | .sock i =>
    let some s := m.kernel.socks[i]? | return 32
    return readyMask ev (!s.input.pendingBytes.isEmpty || s.rdShutdown || (s.connected && s.input.writers == 0))
      (s.connected && s.output.freeSpace > 0) (s.wrShutdown && s.rdShutdown) false

def pollAll (m : Machine) (sl : StepSlice) (reqs : List PollReq) (ms : Option Nat)
    (signals : Bool) : Transition (List Nat) :=
  let masks := reqs.map (pollOne m)
  if masks.any (· != 0) then (.ok masks,m)
  else if sl.intrBefore || signals && !m.proc.sigQueue.isEmpty then
    (.err .EINTR,{m with proc := {m.proc with sigQueue := m.proc.sigQueue.drop 1}})
  else match ms with
    | none => (.wouldBlock .readable,m)
    | some n => (.ok masks,{m with kernel := {m.kernel with clock := m.kernel.clock+1000000*n}})

def dispatchSyscall (m : Machine) (sl : StepSlice) (op : SysOp) :
    Except Errno (Transition op.Result) :=
  let t := m.kernel.vfs
  let root := m.proc.root
  match (motive := (o : SysOp) → Except Errno (Transition o.Result)) op with
  | .read fd n => do fdRead m sl fd n none
  | .write fd bs => do fdWrite m sl fd bs none
  | .pread fd n off => do fdRead m sl fd n (some off)
  | .pwrite fd bs off => do fdWrite m sl fd bs (some off)
  | .lseek fd delta w => do fdSeek m fd delta w
  | .dup2 src dst => do fdDup2 m src dst
  | .close fd => do
    discard <| m.lookup fd
    return (.ok (), m.setFds (m.fds.erase fd))
  | .setNonblock fd on => do
    let (id,d) ← m.lookup fd
    return (.ok (),m.setDesc id {d with flags := {d.flags with nonblock := on}})
  | .setCloexec fd on => do
    let (id,_) ← m.lookup fd
    return (.ok (),m.setFds (m.fds.insert fd ⟨id,on⟩))
  | .pipe2 nb ce => do fdPipe m nb ce
  | .ppoll reqs ms signals => do return pollAll m sl reqs ms signals
  | .fstat fd => do return (.ok (← fdStat m fd),m)
  | .openat d p f mode => do openPath m d p f mode
  | .mkdirat d p mode => do
    return (.ok (),m.setVfs (← vfsMkdirat t root (← m.dirStart d p) p (mode &&& (511-m.proc.umask))))
  | .unlinkat d p removeDir => do
    return (.ok (),m.setVfs (← vfsUnlinkat t root (← m.dirStart d p) p removeDir))
  | .symlinkat target d p => do
    return (.ok (),m.setVfs (← vfsSymlinkat t root (← m.dirStart d p) target p))
  | .renameat d p e q => do
    return (.ok (),m.setVfs (← vfsRenameat t root (← m.dirStart d p) p (← m.dirStart e q) q))
  | .readlinkat d p => do return (.ok (← vfsReadlinkat t root (← m.dirStart d p) p),m)
  | .fstatat d p follow => do return (.ok (← vfsFstatat t root (← m.dirStart d p) p follow),m)
  | .chdir p => do
    let id ← resolveAt t root m.proc.cwd 40 p true
    discard <| t.directory id
    return (.ok (),{m with proc := {m.proc with cwd := id}})
  | .getcwd => do return (.ok (← vfsGetcwd t root m.proc.cwd),m)
  | .tcgetattr fd => do let (_,tty) ← ttyOf m fd; return (.ok tty.attrs,m)
  | .tcsetattr fd a => do let (id,tty) ← ttyOf m fd; return (.ok (),m.setPty id (tcsetattr tty a))
  | .getWinsize fd => do let (_,tty) ← ttyOf m fd; return (.ok tty.size,m)
  | .setWinsize fd size => do
    let (id,tty) ← ttyOf m fd
    let m' := m.setPty id {tty with size}
    return (.ok (),if tty.size = size then m' else m'.signal .winch)
  | .isatty fd => do
    let (_,d) ← m.lookup fd
    return (.ok (match d.target with | .pty .. => true | _ => false),m)
  | .socketStream nb ce => do
    let id := tableFresh m.kernel.socks
    let (fd,m') ← (m.setSock id {}).allocate (.sock id) {access := .readWrite, nonblock := nb, cloexec := ce}
    return (.ok fd,m')
  | .connectLoopback fd port => do
    let (id,s) ← socketOf m fd
    if s.connected then throw .EISCONN
    let some peer := m.kernel.listeners[port]? | throw .ECONNREFUSED
    return (.ok (),m.setSock id {peer with connected := true})
  | .shutdown fd rd wr => do
    let (id,s) ← socketOf m fd
    if !rd && !wr then throw .EINVAL
    if !s.connected then throw .ENOTCONN
    return (.ok (),m.setSock id {s with rdShutdown := rd || s.rdShutdown, wrShutdown := wr || s.wrShutdown})
  | .clockGettime => do return (.ok m.kernel.clock,m)
  | .nanosleep ns => do
    if sl.intrBefore then throw .EINTR
    return (.ok (), {m with kernel := {m.kernel with clock := m.kernel.clock+ns}})
  | .getArgs => do return (.ok m.proc.argv,m)
  | .lookupEnv name => do return (.ok ((m.proc.envVars.find? (fun e => e.1 == name)).map Prod.snd),m)

/-- Read operations change offsets or buffered data without changing descriptor ownership. -/
@[simp] def SysOp.publishesRead : SysOp → Bool
  | .read .. | .pread .. => true
  | _ => false

/-- Keep the complete representation of unrelated state across split reads. -/
def stepSyscall (m : Machine) (slice : StepSlice) (op : SysOp) : Transition op.Result :=
  match dispatchSyscall m slice op with
  | .error e => (.err e,m)
  | .ok (r,next) =>
    if fdLinks next.proc next.kernel.ofds then (r,if op.publishesRead then next else next.account) else (.err .EIO,m)

inductive SimOutcome (A : Type) where
  | done (value : A)
  | suspended

def runPrefix {Δ : List Cap} {A : Type} (p : Prefix Δ A) (m : Machine)
    (schedule : List StepSlice) : SimOutcome A × Machine :=
  match p with
  | .done a => (.done a,m)
  | .suspended => (.suspended,m)
  | .ask op _ next => match schedule with
    | [] => (.suspended,m)
    | sl :: rest =>
      let (r,m') := stepSyscall m sl op
      runPrefix (next r) m' rest
termination_by structural schedule

/-- Once a finite run finishes, any unused scheduling slices leave its complete result intact. -/
theorem runPrefix_done_append {Δ : List Cap} {A : Type} {p : Prefix Δ A} {m z : Machine}
    {slices : List StepSlice} {a : A} (done : runPrefix p m slices = (.done a,z))
    (unused : List StepSlice) : runPrefix p m (slices ++ unused) = (.done a,z) := by
  induction slices generalizing p m with
  | nil =>
    cases p with
    | done _ | suspended => cases unused <;> exact done
    | ask op h k =>
      have impossible : false = true := congrArg
        (fun (out : SimOutcome A × Machine) => match out.1 with | .done _ => true | .suspended => false) done
      contradiction
  | cons sl rest ih =>
    cases p with
    | done _ | suspended => exact done
    | ask op h k =>
      simp only [runPrefix] at done
      exact ih done

end LojitaCtx.Posix
