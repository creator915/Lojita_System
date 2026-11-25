import Lojita.Store.TreeCAS.Image
import LojitaCtx.Io.HalfLine
import LojitaCtx.Io.BufferState
import LojitaCtx.Io.FileRefinement
import LojitaCtx.Io.Lines
import LojitaCtx.Io.WriteConfluence
import LojitaCtx.Posix.Kernel.DescriptorLaws
import LojitaCtx.Posix.Kernel.TtyLaw
import LojitaCtx.Posix.Kernel.Frame
import LojitaCtx.Posix.Kernel.Accounting
import LojitaCtx.Posix.Stream
import LojitaCtx.Posix.Tty
import LojitaCtx.Posix.Vfs
import LojitaCtx.Posix.Vfs.Edit
import LojitaCtx.Posix.Vfs.Namei

open LojitaCtx.Posix LojitaCtx.Io LojitaCtx.Io.FsLib Lojita.Store.TreeCAS

namespace TheoremPin

-- T1
example (sl : StepSlice) (nb : Bool) (s : StreamBuf)
    (h : sl.intrBefore = false) :
    (streamRead sl nb s).1 = .ok [] ↔ s.available = 0 ∧ s.writers = 0 :=
  @streamRead_eof_iff sl nb s h

-- T2
example (sl : StepSlice) (nb : Bool) (s : StreamBuf)
    (h : (streamRead sl nb s).1 = .err .EAGAIN ∨ (streamRead sl nb s).1 = .err .EINTR ∨
      ∃ w, (streamRead sl nb s).1 = .wouldBlock w) : (streamRead sl nb s).2 = s :=
  @streamRead_blocked_preserves sl nb s h

-- T3
example (sl : StepSlice) (nb : Bool) (s s' : StreamBuf)
    (out : Bytes) (h : streamRead sl nb s = (.ok out, s')) :
    out ++ s'.pendingBytes = s.pendingBytes :=
  @streamRead_byte_conservation sl nb s s' out h

-- T4
example (sl : StepSlice) (nb : Bool) (bs : Bytes) (s : StreamBuf)
    (hr : s.readers = 0) (hne : bs ≠ []) : streamWrite sl nb bs s = (.err .EPIPE, s) :=
  @streamWrite_epipe sl nb bs s hr hne

-- T5
example (p : PtyState) (t : Termios) :
    tcgetattr (tcsetattr p t) = t :=
  @tcsetattr_tcgetattr_roundtrip p t

example (m : Machine) (fd : Fd) (e : FdEntry)
    (d : OpenFileDesc) (pty : PtyId) (master : Bool) (tty : PtyState)
    (backed : fdLinks m.proc m.kernel.ofds)
    (entry : m.fds[fd]? = some e) (desc : m.kernel.ofds[e.ofd]? = some d)
    (kind : d.target = .pty pty master) (present : m.kernel.ptys[pty]? = some tty)
    (attrs : Termios) (setSlice getSlice : StepSlice) :
    let set := stepSyscall m setSlice (.tcsetattr fd attrs)
    set.1 = .ok () ∧ (stepSyscall set.2 getSlice (.tcgetattr fd)).1 = .ok attrs :=
  @syscall_tcsetattr_tcgetattr m fd e d pty master tty backed entry desc kind present attrs setSlice getSlice

-- T6
example (p : PtyState) (bs : Bytes) (raw : p.attrs = rawTermios)
    (fits : bs.length ≤ p.toSlave.freeSpace - p.editing.length) :
    (ptyMasterWrite p bs).toSlave.pendingBytes = p.toSlave.pendingBytes ++ bs ∧
    (ptyMasterWrite p bs).toMaster.pendingBytes = p.toMaster.pendingBytes :=
  @pty_raw_passthrough p bs raw fits

-- T7
example (t : InodeTable) (S : InodeId → Prop) (closed : DirClosed t S)
    (root start fuel : Nat) (p : Bytes) (follow : Bool) (id : InodeId)
    (hr : S root) (hs : S start) (resolved : resolveAt t root start fuel p follow = .ok id) :
    S id :=
  @resolve_root_confined t S closed root start fuel p follow id hr hs resolved

-- T8
example (t : InodeTable) (root start : InodeId) (p : Bytes) (mode : FileMode) :
    (resolveParentAt t root start 40 p false false = .error .ENOENT →
      vfsMkdirat t root start p mode = .error .ENOENT) ∧
    (∀ (a : NameSlot InodeId) id, resolveParentAt t root start 40 p false false = .ok a →
      a.target = some id → vfsMkdirat t root start p mode = .error .EEXIST) :=
  @mkdirat_strict_posix t root start p mode

-- T9
example (t next : InodeTable) (root start : InodeId) (p : Bytes)
    (a : NameSlot InodeId) (id : Nat) (n : Inode) (data : ByteArray)
    (located : resolveParentAt t root start 40 p false = .ok a)
    (target : a.target = some id) (node : t.node id = .ok n)
    (regular : n.payload = .reg data) (opened : 0 < n.openRefs)
    (unlinked : vfsUnlinkat t root start p false = .ok next) :
    (∀ follow, resolveAt next root start 40 p follow = .error .ENOENT) ∧
    (next.node id).map Inode.payload = .ok (.reg data) ∧
    ∀ off count, inodeRead next id off count = inodeRead t id off count :=
  @unlink_open_inode_alive t next root start p a id n data located target node regular opened unlinked

-- T10
example (t : InodeTable) (es : List InodeEdit) (i : InodeId)
    (ro : t.protectedAt i = true) :
    ((∃ e ∈ es, e.id = i) → t.commit es = .error .EROFS) ∧
    (∀ next, t.commit es = .ok next → next.nodes[i]? = t.nodes[i]?) :=
  @roLayer_vfs_immutable t es i ro

-- T10 at each path mutation entry point
example (t u : InodeTable) (root dir : Nat) (path : Bytes) :
    (∀ flags mode id, vfsOpenat t root dir path flags mode = .ok (id,u) → RoFrame t u) ∧
    (∀ mode, vfsMkdirat t root dir path mode = .ok u → RoFrame t u) ∧
    (∀ target, vfsSymlinkat t root dir target path = .ok u → RoFrame t u) ∧
    (∀ removedir, vfsUnlinkat t root dir path removedir = .ok u → RoFrame t u) ∧
    (∀ dir' path', vfsRenameat t root dir path dir' path' = .ok u → RoFrame t u) :=
  path_mutations_preserve_ro t u root dir path

-- T11
example (m : Machine) (s : StepSlice) (op : SysOp)
    (h : WFKernel m.proc m.kernel) :
    WFKernel (stepSyscall m s op).2.proc (stepSyscall m s op).2.kernel :=
  @stepSyscall_preserves_WF m s op h

-- T12
example :
    (∀ {m n : Machine} {a b id : Nat} (src : Holds m a id) {sl : StepSlice}
    (success : stepSyscall m sl (.dup2 a b) = (.ok b,n)),
    Holds n a id ∧ Holds n b id) ∧
    (∀ {m n : Machine} {a b id ino size : Nat} {d : OpenFileDesc}
    (src : Holds m a id) (dst : Holds m b id) (desc : m.kernel.ofds[id]? = some d)
    (reg : d.target = .inode ino) (readable : d.flags.access ≠ .writeOnly)
    (sl nextSlice : StepSlice) (out : Bytes)
    (read : stepSyscall m sl (.read a size) = (.ok out,n)),
    (stepSyscall n nextSlice (.lseek b 0 .cur)).1 = .ok (d.offset+out.length)) ∧
    (∀ {m n : Machine} {sl : StepSlice} {fd mode : Nat}
    {dir : DirFd} {path : Bytes} {f : OpenFlags}
    (h : stepSyscall m sl (.openat dir path f mode) = (.ok fd,n)),
    ∃ id, Holds n fd id ∧ (∀ old ∈ m.kernel.ofds, id ≠ old) ∧
      ∀ other j, Holds m other j → Holds n other j) ∧
    (∀ {m n : Machine} {a b i j ino : Nat} {writer reader : OpenFileDesc}
    (src : Holds m a i) (dst : Holds m b j) (distinct : i ≠ j)
    (w : m.kernel.ofds[i]? = some writer) (r : m.kernel.ofds[j]? = some reader)
    (wreg : writer.target = .inode ino) (rreg : reader.target = .inode ino)
    (writable : writer.flags.access ≠ .readOnly) (readable : reader.flags.access ≠ .writeOnly)
    (appendOff : writer.flags.append = false) (offset : reader.offset = writer.offset)
    {old : Inode} {before : ByteArray} (node : m.kernel.vfs.node ino = .ok old)
    (regular : old.payload = .reg before) (linked : old.nlink ≠ 0)
    (data : Bytes) (nonempty : data ≠ []) (sl rd : StepSlice)
    (awake : sl.intrBefore = false) (rdAwake : rd.intrBefore = false)
    (fits : (data.take (max 1 sl.maxBytes)).length ≤ max 1 rd.maxBytes)
    (success : stepSyscall m sl (.write a data) = (.ok (data.take (max 1 sl.maxBytes)).length,n)),
    let bs := data.take (max 1 sl.maxBytes)
    (stepSyscall n rd (.lseek b 0 .cur)).1 = .ok reader.offset ∧
    (stepSyscall n rd (.read b bs.length)).1 = .ok bs) :=
  dup2_shared_vs_openat_isolated

-- T13
example {Δ : List Cap} {A : Type} (program : PosixProg Δ A)
    (m : Machine) (fuel : Nat) (schedule : List StepSlice)
    (denied : Cap.fsPathCap ∉ Δ) (safe : ReadOnlyRegularFds m) :
    namespaceAt (runPrefix (program.observe fuel) m schedule).2.kernel.vfs = namespaceAt m.kernel.vfs :=
  capsicum_vfs_frame program m fuel schedule denied safe

-- T14
example (fd : Fd) (pre post : Bytes)
    (hpre : lf ∉ pre) (hpost : lf ∉ post) (pipe : StreamBuf)
    (empty : pipe.pendingBytes = []) (openWriter : pipe.writers ≠ 0) :
    let r := (BufReader.mk fd 4096 ByteArray.empty 0 [] false).ingest pre
    r.inspect .line = none ∧
    r.receive (streamRead canonicalSlice true pipe).1 = .stopped (.err .EAGAIN, r) ∧
    ∃ r', (r.ingest (post ++ [lf])).inspect .line =
      some (.ok (some (pre ++ post ++ [lf])), r') :=
  @bufReader_halfline_lossless fd pre post hpre hpost pipe empty openWriter

example {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (fd : Fd)
    (pre post : Bytes) (noLF₀ : lf ∉ pre) (noLF₁ : lf ∉ post) (pipe : StreamBuf)
    (empty : pipe.pendingBytes = []) (openEnd : pipe.writers ≠ 0) :
    let r₀ : BufReader := {fd,chunkSize := max 1 (max pre.length (post.length+1))}
    let r := r₀.ingest pre
    let a := (streamRead canonicalSlice true pipe).1
    let resumed := {pipe with pendingBytes := post ++ [lf]}
    let b := (streamRead {maxBytes := post.length+1} true resumed).1
    Finishes ((readLine cap r).observe 1) (readAnswers [a]) (.err .EAGAIN,r) ∧
    ∃ final, Finishes ((readLine cap r).observe 1) (readAnswers [b])
      (.ok (some (pre ++ post ++ [lf])),final) :=
  @readLine_halfline_syscalls Δ cap fd pre post noLF₀ noLF₁ pipe empty openEnd

-- T15
example {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (r : BufReader)
    (awake : r.eof = false) {s a b q₁ q₂ z₁ z₂}
    (one : ReadTrace r.chunkSize s a q₁ z₁) (two : ReadTrace r.chunkSize s b q₂ z₂) :
    let final := {r.clear with eof := true}
    let bytes := r.pending ++ s.pendingBytes
    let lines := (r.frame.chunk s.pendingBytes).lines
    Finishes ((readAll cap r).observe q₁.length) (readAnswers q₁) (.ok bytes, final) ∧
    Finishes ((readAll cap r).observe q₂.length) (readAnswers q₂) (.ok bytes, final) ∧
    LineRun cap (.ready r) q₁ lines final ∧ LineRun cap (.ready r) q₂ lines final ∧ z₁ = z₂ :=
  @ioBuf_chunk_confluence Δ cap r awake s a b q₁ q₂ z₁ z₂ one two

-- T16
example {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (fs : .fsPathCap ∈ Δ)
    {m opened before closed : Machine} {fd ino size : Nat} {bytes : ByteArray}
    {path : Bytes} {slOpen slClose slices qs}
    (acquired : stepSyscall m slOpen (.openat none path {} 0) = (.ok fd,opened))
    (reads : FileReads fd ino size bytes 0 opened slices qs before)
    (released : stepSyscall before slClose (.close fd) = (.ok (),closed)) :
    runPrefix ((readFileAll cap fs path size).observe qs.length) m
        (slOpen :: (slices ++ [slClose])) = (.done (.ok bytes.data.toList),closed) ∧
    sameDescriptors closed m :=
  @readFileAll_refines_spec Δ cap fs m opened before closed fd ino size bytes path slOpen slClose slices qs acquired reads released

-- T17
example (image : ImageTable) (ro : Bool)
    (h : canonicalTree image.toList = true) :
    (mountTreeToVfs image ro >>= freezeVfsToTree) = .ok image.toList :=
  @freeze_mount_roundtrip image ro h

-- T15 write
example {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {w s slices qs z} (t : WriteTrace w s slices qs z) :
    Finishes ((writeAll cap w).observe qs.length) (writeAnswers qs)
      (.ok (), {w with remaining := [], written := w.written + w.remaining.length}) ∧
    z.pendingBytes = s.pendingBytes ++ w.remaining :=
  @writeAll_chunk_confluence Δ cap w s slices qs z t

-- T16 acquisition failure
example {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (fs : .fsPathCap ∈ Δ)
    {m : Machine} {path : Bytes} {sl size depth} {e : Errno}
    (failed : stepSyscall m sl (.openat none path {} 0) = (.err e,m)) :
    runPrefix ((readFileAll cap fs path size).observe depth) m [sl] = (.done (.err e), m) :=
  @readFileAll_open_error Δ cap fs m path sl size depth e failed

end TheoremPin
