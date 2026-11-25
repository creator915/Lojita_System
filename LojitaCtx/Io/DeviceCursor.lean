import LojitaCtx.Io.PipeCursor

namespace LojitaCtx.Io
open LojitaCtx.Posix FsLib

private def suffix (s : StreamBuf) (bytes : Bytes) (off : Nat) : StreamBuf :=
  {s with pendingBytes := bytes.drop off}

private theorem read_suffix (s : StreamBuf) (bytes : Bytes) (off size : Nat)
    (sl : StepSlice) (nb : Bool) (fin : s.writers = 0) :
    streamRead {sl with maxBytes := min (max 1 size) (max 1 sl.maxBytes)} nb (suffix s bytes off) =
    if sl.intrBefore then (.err .EINTR,suffix s bytes off)
    else let bs := nextChunk bytes off size sl; (.ok bs,suffix s bytes (off+bs.length)) := by
  let n := min (max 1 size) (max 1 sl.maxBytes)
  have read := closed_stream (suffix s bytes off) fin nb sl n (by dsimp [n]; omega)
  simpa [n,suffix,nextChunk,List.drop_drop] using read

/-- A connected stream has received FIN from its peer. Bytes already queued
    remain readable, including with O_NONBLOCK; FIN supplies persistent EOF. -/
def socketCursor (m : Machine) (id : SockId) (peer : SocketState) (bytes : Bytes) (off : Nat) : Machine :=
  m.setSock id {peer with input := suffix peer.input bytes off}

theorem socket_cursor_law (m : Machine) (fd : Fd) (ofd : OfdId) (d : OpenFileDesc)
    (id : SockId) (peer : SocketState) (bytes : Bytes) (backed : fdLinks m.proc m.kernel.ofds)
    (look : m.lookup fd = .ok (ofd,d)) (found : m.kernel.socks[id]? = some peer)
    (target : d.target = .sock id) (canRead : d.flags.access ≠ .writeOnly)
    (connected : peer.connected = true) (readOpen : peer.rdShutdown = false)
    (peerFin : peer.input.writers = 0) : CursorLaw bytes fd (socketCursor m id peer bytes) := by
  intro off size sl
  let here := socketCursor m id peer bytes off
  let sock := {peer with input := suffix peer.input bytes off}
  have current : here.kernel.socks[id]? = some sock := Std.TreeMap.getElem?_insert_self
  have fdHere : here.lookup fd = .ok (ofd,d) := look
  have sizeNe : max 1 size ≠ 0 := by omega
  have reads := read_suffix peer.input bytes off size sl d.flags.nonblock peerFin
  let bs := nextChunk bytes off size sl
  let after := socketCursor m id peer bytes (off + bs.length)
  have keeps (k : Nat) : fdLinks (socketCursor m id peer bytes k).proc
      (socketCursor m id peer bytes k).kernel.ofds := backed
  cases hi : sl.intrBefore
  · have hread := reads
    simp only [hi,Bool.false_eq_true,ite_false] at hread
    have raw : dispatchSyscall here sl (.read fd (max 1 size)) = .ok (.ok bs,after) := by
      simp [dispatchSyscall,fdRead,fdHere,target,canRead,current,sock,sizeNe,readOpen,connected,
        Bind.bind,Except.bind,Pure.pure,Except.pure,hi,hread]
      simp [after,here,socketCursor,Machine.setSock,bs,connected,readOpen,table_overwrite _ _ peer _ _ found] <;> rfl
    change stepSyscall here sl _ = _
    simp [stepSyscall,raw,show fdLinks after.proc after.kernel.ofds from keeps _,after,bs]
  · have hread := reads
    simp only [hi,ite_true] at hread
    have raw : dispatchSyscall here sl (.read fd (max 1 size)) = .ok (.err .EINTR,here) := by
      simp [dispatchSyscall,fdRead,fdHere,target,canRead,current,sock,sizeNe,readOpen,connected,
        Bind.bind,Except.bind,Pure.pure,Except.pure,hi,hread]
      simp [here,socketCursor,Machine.setSock,connected,readOpen,table_overwrite _ _ peer _ _ found] <;> rfl
    change stepSyscall here sl _ = _
    simp [stepSyscall,raw,show fdLinks here.proc here.kernel.ofds from keeps _,here]


theorem socket_cursor_initial (m : Machine) (id : SockId) (peer : SocketState)
    (found : m.kernel.socks[id]? = some peer) :
    socketCursor m id peer peer.input.pendingBytes 0 = m := by
  simp [socketCursor,suffix,Machine.setSock,table_restore _ _ peer found]

theorem kernel_pty_read (m : Machine) (fd ofd id size : Nat) (d : OpenFileDesc)
    (p : PtyState) (sl : StepSlice) (backed : fdLinks m.proc m.kernel.ofds)
    (look : m.lookup fd = .ok (ofd,d)) (target : d.target = .pty id false)
    (canRead : d.flags.access ≠ .writeOnly) (found : m.kernel.ptys[id]? = some p) :
    let step := ptyRead {sl with maxBytes := min (max 1 size) (max 1 sl.maxBytes)}
      d.flags.nonblock false p
    stepSyscall m sl (.read fd (max 1 size)) = (step.1,m.setPty id step.2) := by
  intro step
  have nz : max 1 size ≠ 0 := by omega
  have raw : dispatchSyscall m sl (.read fd (max 1 size)) = .ok (step.1,m.setPty id step.2) := by
    simp [dispatchSyscall,fdRead,look,target,canRead,found,nz,Bind.bind,Except.bind,Pure.pure,Except.pure,step]
    rfl
  simp [stepSyscall,raw,show fdLinks (m.setPty id step.2).proc (m.setPty id step.2).kernel.ofds from backed] <;> rfl

/-- The final master close flushes the slave's input. EOF persists with either line discipline. -/
theorem hung_slave_cursor_law (m : Machine) (fd ofd id : Nat) (d : OpenFileDesc)
    (p : PtyState) (backed : fdLinks m.proc m.kernel.ofds)
    (look : m.lookup fd = .ok (ofd,d)) (target : d.target = .pty id false)
    (canRead : d.flags.access ≠ .writeOnly) (found : m.kernel.ptys[id]? = some p)
    (fin : p.toSlave.writers = 0) (empty : p.toSlave.pendingBytes = []) (records : p.records = []) :
    CursorLaw [] fd (fun _ => m) := by
  intro off size sl
  have keep : m.setPty id p = m := by simp [Machine.setPty,table_restore _ _ p found]
  have reset : {p with records := []} = p := by cases p; simp_all
  rw [kernel_pty_read m fd ofd id size d p sl backed look target canRead found]
  cases hi : sl.intrBefore <;> cases canon : p.attrs.icanon <;>
    simp [ptyRead,canon,records,streamRead,empty,fin,keep,nextChunk,reset] <;>
      rfl


end LojitaCtx.Io
