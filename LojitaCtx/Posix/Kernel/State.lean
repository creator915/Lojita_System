import LojitaCtx.Posix.Program
import LojitaCtx.Posix.Kernel.PipePages
import LojitaCtx.Posix.Vfs
import Std.Data.TreeMap.Lemmas

namespace LojitaCtx.Posix

abbrev Table (α : Type) := Std.TreeMap Nat α

inductive KernelTarget where
  | inode (id : InodeId)
  | pipe (id : PipeId) (writeEnd : Bool)
  | pty (id : PtyId) (master : Bool)
  | sock (id : SockId)
  deriving Repr, Inhabited

def KernelTarget.ctorIdx : KernelTarget → Nat
  | .inode _ => 0 | .pipe .. => 1 | .pty .. => 2 | .sock _ => 3
deriving instance DecidableEq for KernelTarget

structure FdEntry where
  ofd : OfdId
  cloexec : Bool := false
  deriving Repr, DecidableEq, Inhabited

structure OpenFileDesc where
  target : KernelTarget
  flags : OpenFlags
  offset : Nat := 0
  refcnt : Nat := 1
  deriving Repr, DecidableEq, Inhabited

inductive PosixSignal where | interrupt | winch | pipe
  deriving Repr, Inhabited

structure ProcState where
  fds : Table FdEntry := {}
  cwd : InodeId := 1
  root : InodeId := 1
  umask : FileMode := 18
  limit : Nat := 1024
  argv : List Bytes := []
  envVars : List (Bytes × Bytes) := []
  sigQueue : List PosixSignal := []
  deriving Inhabited

structure SocketState where
  input : StreamBuf := {}
  output : StreamBuf := {}
  connected : Bool := false
  rdShutdown : Bool := false
  wrShutdown : Bool := false
  deriving Inhabited

structure KernelState where
  ofds : Table OpenFileDesc := {}
  vfs : InodeTable := InodeTable.empty
  pipes : Table StreamBuf := {}
  pipePages : Table PipePages := {}
  ptys : Table PtyState := {}
  socks : Table SocketState := {}
  listeners : Table SocketState := {}
  clock : Nat := 0
  deriving Inhabited

structure Machine where
  proc : ProcState := {}
  kernel : KernelState := {}
  deriving Inhabited

abbrev Transition (α : Type) := Ret α × Machine

def Machine.fds (m : Machine) := m.proc.fds

def Machine.lookup (m : Machine) (fd : Fd) : Except Errno (OfdId × OpenFileDesc) := do
  let some e := m.fds[fd]? | throw .EBADF
  let some d := m.kernel.ofds[e.ofd]? | throw .EBADF
  return (e.ofd, d)

def Machine.setFds (m : Machine) (fds : Table FdEntry) : Machine :=
  { m with proc := {m.proc with fds} }

def Machine.setDesc (m : Machine) (id : OfdId) (d : OpenFileDesc) : Machine :=
  { m with kernel := {m.kernel with ofds := m.kernel.ofds.insert id d} }

def Machine.setVfs (m : Machine) (t : InodeTable) : Machine :=
  { m with kernel := {m.kernel with vfs := t} }

def Machine.setPipe (m : Machine) (id : PipeId) (s : StreamBuf) : Machine :=
  { m with kernel := {m.kernel with pipes := m.kernel.pipes.insert id s} }

def Machine.pages (m : Machine) (id : PipeId) (s : StreamBuf) : PipePages :=
  match m.kernel.pipePages[id]? with
  | some ps => ps
  | none => PipePages.packed s.available

def Machine.setPages (m : Machine) (id : PipeId) (ps : PipePages) : Machine :=
  {m with kernel := {m.kernel with pipePages := m.kernel.pipePages.insert id ps}}

def Machine.setPty (m : Machine) (id : PtyId) (p : PtyState) : Machine :=
  { m with kernel := {m.kernel with ptys := m.kernel.ptys.insert id p} }

def Machine.setSock (m : Machine) (id : SockId) (s : SocketState) : Machine :=
  { m with kernel := {m.kernel with socks := m.kernel.socks.insert id s} }

def Machine.signal (m : Machine) (sig : PosixSignal) : Machine :=
  { m with proc := {m.proc with sigQueue := m.proc.sigQueue ++ [sig]} }

def tableFresh {α : Type} (t : Table α) := (t.maxKey?.getD 0) + 1

def Machine.allocate (m : Machine) (target : KernelTarget) (flags : OpenFlags) :
    Except Errno (Fd × Machine) := do
  let some fd := (List.range (min m.proc.limit (m.fds.size+1))).find? (!m.fds.contains ·)
    | throw .EMFILE
  let id := tableFresh m.kernel.ofds
  let k := m.setDesc id {target, flags := {flags with cloexec := false}}
  return (fd, k.setFds (m.fds.insert fd ⟨id, flags.cloexec⟩))

def Machine.dirStart (m : Machine) (dir : DirFd) (path : Bytes) : Except Errno InodeId := do
  if path.head? == some 47 then return m.proc.root
  match dir with
  | none => return m.proc.cwd
  | some fd =>
    let (_,d) ← m.lookup fd
    let .inode id := d.target | throw .ENOTDIR
    discard <| m.kernel.vfs.directory id
    return id

def fdCount (p : ProcState) (id : OfdId) := p.fds.toList.countP (fun e => e.2.ofd == id)
def targetCount (ds : Table OpenFileDesc) (t : KernelTarget) :=
  ds.toList.countP (fun d => d.2.target == t)

def liveOfds (p : ProcState) (ds : Table OpenFileDesc) : Table OpenFileDesc :=
  ds.filterMap fun id d =>
    let n := fdCount p id
    if n = 0 then none else some {d with refcnt := n}

def liveInodes (t : InodeTable) (ds : Table OpenFileDesc) : InodeTable :=
  {t with nodes := t.nodes.filterMap fun id inode =>
    let n := targetCount ds (.inode id)
    if n = 0 && inode.nlink = 0 then none else some {inode with openRefs := n}}

def livePipes (pipes : Table StreamBuf) (ds : Table OpenFileDesc) : Table StreamBuf :=
  pipes.filterMap fun id s =>
    let r := targetCount ds (.pipe id false)
    let w := targetCount ds (.pipe id true)
    if r + w = 0 then none else some {s with readers := r, writers := w}

/-- Publish reference counts from distinct open descriptions, not descriptor aliases. -/
def Machine.account (m : Machine) : Machine :=
  let ds := liveOfds m.proc m.kernel.ofds
  {m with kernel := {m.kernel with
    ofds := ds
    vfs := liveInodes m.kernel.vfs ds
    pipes := livePipes m.kernel.pipes ds
    pipePages := m.kernel.pipePages.filter fun id _ => targetCount ds (.pipe id false) + targetCount ds (.pipe id true) > 0
    ptys := m.kernel.ptys.filter fun id _ => targetCount ds (.pty id false) + targetCount ds (.pty id true) > 0
    socks := m.kernel.socks.filter fun id _ => targetCount ds (.sock id) > 0}}

def fdLinks (p : ProcState) (ds : Table OpenFileDesc) : Bool :=
  p.fds.toList.all fun row => ds[row.2.ofd]?.isSome

structure WFKernel (p : ProcState) (k : KernelState) : Prop where
  fdLive : ∀ (fd : Fd) (e : FdEntry), p.fds[fd]? = some e → (k.ofds[e.ofd]?).isSome
  descriptions : ∀ (id : OfdId) (d : OpenFileDesc), k.ofds[id]? = some d → d.refcnt = fdCount p id ∧ 0 < d.refcnt
  inodes : ∀ (id : InodeId) (n : Inode), k.vfs.nodes[id]? = some n → n.openRefs = targetCount k.ofds (.inode id)
  pipes : ∀ (id : PipeId) (s : StreamBuf), k.pipes[id]? = some s →
    s.readers = targetCount k.ofds (.pipe id false) ∧ s.writers = targetCount k.ofds (.pipe id true)

end LojitaCtx.Posix
