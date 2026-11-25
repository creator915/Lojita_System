import LojitaCtx.Io.MachineConfluence
import LojitaCtx.Posix.Kernel.TableWrites

namespace LojitaCtx.Io
open LojitaCtx.Posix

def fileCursor (m : Machine) (id : OfdId) (d : OpenFileDesc) (off : Nat) : Machine :=
  m.setDesc id {d with offset := off}

private theorem fileCursor_links {m : Machine} (backed : fdLinks m.proc m.kernel.ofds)
    (id : OfdId) (d : OpenFileDesc) (off : Nat) :
    fdLinks (fileCursor m id d off).proc (fileCursor m id d off).kernel.ofds := by
  apply List.all_eq_true.mpr
  intro pair mem
  have was := List.all_eq_true.mp backed pair mem
  by_cases same : id = pair.2.ofd <;> simp_all [fileCursor,Machine.setDesc]

theorem regular_cursor_law (m : Machine) (fd : Fd) (e : FdEntry) (d : OpenFileDesc)
    (ino : InodeId) (n : Inode) (data : ByteArray) (backed : fdLinks m.proc m.kernel.ofds)
    (entry : m.fds[fd]? = some e) (desc : m.kernel.ofds[e.ofd]? = some d)
    (reg : d.target = .inode ino) (readable : d.flags.access ≠ .writeOnly)
    (node : m.kernel.vfs.node ino = .ok n) (contents : n.payload = .reg data) :
    CursorLaw data.data.toList fd (fileCursor m e.ofd d) := by
  intro off size sl
  let here := fileCursor m e.ofd d off
  let updated := {d with offset := off}
  let bs := nextChunk data.data.toList off size sl
  let dest := fileCursor m e.ofd d (off+bs.length)
  have look : here.lookup fd = .ok (e.ofd,updated) := by
    have fe : here.fds[fd]? = some e := entry
    have ofd : here.kernel.ofds[e.ofd]? = some updated := Std.TreeMap.getElem?_insert_self
    simp [Machine.lookup,fe,ofd]; rfl
  have positive : 0 < max 1 size := by omega
  cases hi : sl.intrBefore
  · have raw : dispatchSyscall here sl (.read fd (max 1 size)) = .ok (.ok bs,dest) := by
      have recorded : inodeRead here.kernel.vfs ino off (min (max 1 size) (max 1 sl.maxBytes)) = .ok bs := by
        simp [inodeRead,here,fileCursor,Machine.setDesc,node,contents,bs,nextChunk,Bind.bind,Except.bind,Pure.pure,Except.pure]
      simp only [dispatchSyscall,fdRead,look,Bind.bind,Except.bind,Pure.pure,Except.pure,updated,
        Option.isSome_none, Bool.false_and, Bool.false_eq_true, ite_false, reg,readable,hi,Option.getD_none,
        recorded]
      rw [← reg]
      change Except.ok (Ret.ok bs, (here.setDesc e.ofd {d with offset := off+bs.length})) = _
      simp [here,dest,fileCursor,Machine.setDesc,table_overwrite _ _ d _ _ desc] <;> rfl
    have hl := fileCursor_links backed e.ofd d (off+bs.length)
    change stepSyscall here sl _ = _
    simp [stepSyscall,raw,show fdLinks dest.proc dest.kernel.ofds from hl,dest,bs]
  · have raw : dispatchSyscall here sl (.read fd (max 1 size)) = .error .EINTR := by
      simp [dispatchSyscall,fdRead,look,updated,readable,reg,hi,positive,Bind.bind,Except.bind,
        throw,throwThe,MonadExceptOf.throw] <;> rfl
    change stepSyscall here sl _ = _
    simp [stepSyscall,raw,here]

theorem fileCursor_initial (m : Machine) (id : OfdId) (d : OpenFileDesc)
    (desc : m.kernel.ofds[id]? = some d) : fileCursor m id d d.offset = m := by
  simp [fileCursor,Machine.setDesc,table_restore _ _ _ desc]

/-- Rebase the logical input to the current seek position. When the FD starts
    beyond EOF Linux returns no bytes and keeps the original physical offset. -/
theorem regular_suffix_cursor {m : Machine} {fd id : Nat} {d : OpenFileDesc} {bs : Bytes}
    (law : CursorLaw bs fd (fileCursor m id d)) :
    CursorLaw (bs.drop d.offset) fd (fun i => fileCursor m id d (d.offset+i)) := by
  intro off size sl
  simpa [nextChunk,List.drop_drop,Nat.add_assoc] using law (d.offset+off) size sl

/-- For a stationary regular file these two successful schedules have the same
    complete machine. Existing aliases see the final shared offset, including
    the case of an initial seek past EOF. -/
theorem regular_file_confluence {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    (m : Machine) (fd : Fd) (e : FdEntry) (d : OpenFileDesc)
    (ino : InodeId) (n : Inode) (data : ByteArray) (backed : fdLinks m.proc m.kernel.ofds)
    (entry : m.fds[fd]? = some e) (desc : m.kernel.ofds[e.ofd]? = some d)
    (reg : d.target = .inode ino) (readable : d.flags.access ≠ .writeOnly)
    (node : m.kernel.vfs.node ino = .ok n) (contents : n.payload = .reg data)
    {n₁ n₂ ss₁ ss₂ qs₁ qs₂}
    (first : Progressing (data.data.toList.drop d.offset) n₁ 0 ss₁ qs₁)
    (second : Progressing (data.data.toList.drop d.offset) n₂ 0 ss₂ qs₂) :
    let bytes := data.data.toList.drop d.offset
    let final := fileCursor m e.ofd d (d.offset+bytes.length)
    BufferedObservations cap fd n₁ bytes ss₁ qs₁.length m final ∧
    BufferedObservations cap fd n₂ bytes ss₂ qs₂.length m final := by
  have law := regular_suffix_cursor (regular_cursor_law m fd e d ino n data backed entry desc reg readable node contents)
  have start := law 0
  simp only [Nat.add_zero, fileCursor_initial m e.ofd d desc] at start
  exact machine_chunk_confluence cap law start first second

end LojitaCtx.Io
