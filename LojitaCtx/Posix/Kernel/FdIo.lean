import LojitaCtx.Posix.Kernel.State

namespace LojitaCtx.Posix

abbrev KResult (A : Type) := Except Errno (Transition A)

def Machine.advance (m : Machine) (id : OfdId) (d : OpenFileDesc) (off : Nat)
    (positioned : Bool) : Machine :=
  if positioned then m else m.setDesc id {d with offset := off}

def fdRead (m : Machine) (sl : StepSlice) (fd count : Nat) (atOff : Option Nat) :
    Except Errno (Transition Bytes) := do
  let (id, d) ← m.lookup fd
  if atOff.isSome && (match d.target with | .inode _ => false | _ => true) then throw .ESPIPE
  if d.flags.access = .writeOnly then throw .EBADF
  let n := min count (max 1 sl.maxBytes)
  let slice := {sl with maxBytes := n}
  match d.target with
  | .inode i =>
    if sl.intrBefore && count > 0 then throw .EINTR
    let off := atOff.getD d.offset
    let bs ← inodeRead m.kernel.vfs i off n
    return (.ok bs, m.advance id d (off+bs.length) atOff.isSome)
  | .pipe i wr =>
    if atOff.isSome then throw .ESPIPE
    if wr then throw .EBADF
    let some s := m.kernel.pipes[i]? | throw .EBADF
    if count = 0 then return (.ok [], m)
    let (r, s') := streamRead slice d.flags.nonblock s
    let ps := m.pages i s
    let ps' := match r with | .ok bytes => PipePages.consume ps bytes.length | _ => ps
    return (r, (m.setPipe i s').setPages i ps')
  | .pty i master =>
    if atOff.isSome then throw .ESPIPE
    let some tty := m.kernel.ptys[i]? | throw .EBADF
    if count = 0 then return (.ok [],m)
    let (r,next) := ptyRead slice d.flags.nonblock master tty
    return (r,m.setPty i next)
  | .sock i =>
    if atOff.isSome then throw .ESPIPE
    let some sock := m.kernel.socks[i]? | throw .EBADF
    if count = 0 || sock.rdShutdown then return (.ok [],m)
    if !sock.connected then throw .ENOTCONN
    let (r,s) := streamRead slice d.flags.nonblock sock.input
    return (r,m.setSock i {sock with input := s})

def fdWrite (m : Machine) (sl : StepSlice) (fd : Fd) (bs : Bytes) (atOff : Option Nat) :
    Except Errno (Transition Nat) := do
  let (id,d) ← m.lookup fd
  if atOff.isSome && (match d.target with | .inode _ => false | _ => true) then throw .ESPIPE
  if d.flags.access = .readOnly then throw .EBADF
  match d.target with
  | .inode i =>
    if sl.intrBefore && !bs.isEmpty then throw .EINTR
    let off : Nat ← if d.flags.append then (inodeStat m.kernel.vfs i).map StatObs.size else pure (atOff.getD d.offset)
    let chunk := bs.take (max 1 sl.maxBytes)
    let t ← inodeWrite m.kernel.vfs i off chunk
    return (.ok chunk.length,(m.setVfs t).advance id d (off+chunk.length) atOff.isSome)
  | .pipe i wr =>
    if atOff.isSome then throw .ESPIPE
    if !wr then throw .EBADF
    let some s := m.kernel.pipes[i]? | throw .EBADF
    let (r,s',ps') := PipePages.write (m.pages i s) sl d.flags.nonblock bs s
    let m := (m.setPipe i s').setPages i ps'
    return (r,if r = .err .EPIPE then m.signal .pipe else m)
  | .pty i master =>
    if atOff.isSome then throw .ESPIPE
    let some tty := m.kernel.ptys[i]? | throw .EBADF
    if !master && tty.toMaster.readers == 0 then throw .EIO
    if sl.intrBefore && !bs.isEmpty then throw .EINTR
    let chunk := bs.take (max 1 sl.maxBytes)
    if master then
      let n := min chunk.length (tty.toSlave.freeSpace - tty.editing.length)
      if n = 0 && !bs.isEmpty then
        return (if d.flags.nonblock then .err .EAGAIN else .wouldBlock .writable,m)
      let tty' := ptyMasterWrite tty (chunk.take n)
      let m := m.setPty i tty'
      return (.ok n,if tty'.interruptPending then m.signal .interrupt else m)
    return (.ok chunk.length,m.setPty i (ptySlaveWrite tty chunk))
  | .sock i =>
    if atOff.isSome then throw .ESPIPE
    let some sock := m.kernel.socks[i]? | throw .EBADF
    if !sock.connected || sock.wrShutdown then return (.err .EPIPE,m.signal .pipe)
    let (r,s) := streamWrite sl d.flags.nonblock bs sock.output
    return (r,m.setSock i {sock with output := s})

def fdSeek (m : Machine) (fd : Fd) (delta : Int) (base : Whence) : Except Errno (Transition Nat) := do
  let (id,d) ← m.lookup fd
  let .inode i := d.target | throw .ESPIPE
  let start : Nat ← match base with
    | .set => pure 0 | .cur => pure d.offset
    | .end => do
      let stat ← inodeStat m.kernel.vfs i
      if stat.kind = .directory then throw .EINVAL -- Linux tmpfs directory offsets
      pure stat.size
  let off := Int.ofNat start + delta
  if off < 0 then throw .EINVAL
  return (.ok off.toNat,m.setDesc id {d with offset := off.toNat})

def fdDup2 (m : Machine) (src dst : Fd) : Except Errno (Transition Fd) := do
  let (id,_) ← m.lookup src
  if dst ≥ m.proc.limit then throw .EBADF
  if src = dst then return (.ok dst,m)
  return (.ok dst,m.setFds (m.fds.insert dst ⟨id,false⟩))

def fdPipe (m : Machine) (nb ce : Bool) : Except Errno (Transition (Fd × Fd)) := do
  let i := tableFresh m.kernel.pipes
  let flags : OpenFlags := {nonblock := nb, cloexec := ce}
  let (r,m) ← (m.setPipe i {}).allocate (.pipe i false) flags
  let (w,m) ← m.allocate (.pipe i true) {flags with access := .writeOnly}
  return (.ok (r,w),m)

def fdStat (m : Machine) (fd : Fd) : Except Errno StatObs := do
  let (_,d) ← m.lookup fd
  match d.target with
  | .inode i => inodeStat m.kernel.vfs i
  | .pipe i _ => return ⟨i,.fifo,384,1,0⟩
  | .pty i _ => return ⟨i,.tty,400,1,0⟩
  | .sock i => return ⟨i,.socket,511,1,0⟩

end LojitaCtx.Posix
