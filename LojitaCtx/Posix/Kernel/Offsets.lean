import LojitaCtx.Posix.Kernel.Accounting

namespace LojitaCtx.Posix

/-- A process-visible alias for a given open-file description, independently
    of the per-descriptor close-on-exec flag. -/
def Holds (m : Machine) (fd id : Nat) : Prop :=
  ∃ e, m.fds[fd]? = some e ∧ e.ofd = id

theorem Holds.lookup {m : Machine} {fd id : Nat} {d : OpenFileDesc}
    (held : Holds m fd id) (desc : m.kernel.ofds[id]? = some d) :
    m.lookup fd = .ok (id,d) := by
  obtain ⟨e,he,rfl⟩ := held
  simp [Machine.lookup,he,desc,Pure.pure,Except.pure]

theorem dup2_aliases {m n : Machine} {a b id : Nat} (src : Holds m a id) {sl : StepSlice}
    (success : stepSyscall m sl (.dup2 a b) = (.ok b,n)) : Holds n a id ∧ Holds n b id := by
  obtain ⟨e,he,rfl⟩ := src
  cases hd : m.kernel.ofds[e.ofd]? with
  | none =>
    have no : m.lookup a = .error .EBADF := by simp [Machine.lookup,he,hd,throw,throwThe,MonadExceptOf.throw]
    simp [stepSyscall, dispatchSyscall,fdDup2,no, Bind.bind,Except.bind] at success
  | some d =>
    have look := Holds.lookup (show Holds m a e.ofd from ⟨e,he,rfl⟩) hd
    by_cases bound : b ≥ m.proc.limit
    · simp [stepSyscall,dispatchSyscall,fdDup2,look,bound,Bind.bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at success
    · by_cases same : a = b
      · subst b
        cases hl : fdLinks m.proc m.kernel.ofds <;>
          simp [stepSyscall,dispatchSyscall,fdDup2,look,bound,Bind.bind,Except.bind,Pure.pure,Except.pure,hl] at success
        have eq := congrArg Prod.snd success
        dsimp at eq
        subst n
        exact ⟨⟨e,he,rfl⟩,⟨e,he,rfl⟩⟩
      · let next := m.setFds (m.fds.insert b ⟨e.ofd,false⟩)
        have raw : dispatchSyscall m sl (.dup2 a b) = .ok (.ok b,next) := by
          simp [dispatchSyscall,fdDup2,look,bound,same,Bind.bind,Except.bind,Pure.pure,Except.pure,next] <;> rfl
        cases hl : fdLinks next.proc next.kernel.ofds <;> simp [stepSyscall,raw,hl] at success
        cases success
        have other : compare b a ≠ .eq := by simp [Ne.symm same]
        exact ⟨⟨e,by simpa [Machine.account,Machine.fds,Machine.setFds,next,Std.TreeMap.getElem?_insert,other] using he,rfl⟩,
           ⟨⟨e.ofd,false⟩,by simp [Machine.account,Machine.fds,Machine.setFds,next],rfl⟩⟩

theorem accounted_offset {m : Machine} {fd id : Nat} {d : OpenFileDesc}
    (alias : Holds m fd id) (found : m.kernel.ofds[id]? = some d) :
    ∃ live, m.account.lookup fd = .ok (id,live) ∧ live.offset = d.offset ∧ live.target = d.target := by
  obtain ⟨e,he,rfl⟩ := alias
  have mem := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr he
  have count : 0 < fdCount m.proc e.ofd := List.countP_pos_iff.mpr ⟨(fd,e),mem,by simp⟩
  refine ⟨{d with refcnt := fdCount m.proc e.ofd}, ?_,rfl,rfl⟩
  apply Holds.lookup (show Holds m.account fd e.ofd from ⟨e,he,rfl⟩)
  simp [Machine.account,liveOfds,found,Nat.ne_of_gt count]

theorem seek_cur {m : Machine} {fd id : Nat} {d : OpenFileDesc} {ino : Nat}
    (look : m.lookup fd = .ok (id,d)) (reg : d.target = .inode ino)
    (wf : fdLinks m.proc m.kernel.ofds = true) (sl : StepSlice) :
    (stepSyscall m sl (.lseek fd 0 .cur)).1 = .ok d.offset := by
  have next : dispatchSyscall m sl (.lseek fd 0 .cur) =
      .ok (.ok d.offset,m.setDesc id {d with offset := d.offset}) := by
    have nn : ¬ (Int.ofNat d.offset < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
    cases d with
    | mk tgt flags off refs =>
      dsimp at reg
      subst tgt
      simp_all [dispatchSyscall,fdSeek,Bind.bind,Except.bind,Pure.pure,Except.pure] <;> rfl
  have linked : fdLinks m.proc (m.kernel.ofds.insert id {d with offset := d.offset}) := by
    apply List.all_eq_true.mpr
    intro pair member
    have old := List.all_eq_true.mp wf pair member
    by_cases eq : id = pair.2.ofd <;> simp_all [Std.TreeMap.getElem?_insert,fdLinks]
  simp [stepSyscall,next,Machine.setDesc,linked]

/-- A successful ordinary read advances every alias as seen by a subsequent
    SEEK_CUR, by exactly the number of bytes delivered on this slice. -/
theorem read_alias_seek {m n : Machine} {a b id ino size : Nat} {d : OpenFileDesc}
    (src : Holds m a id) (dst : Holds m b id) (desc : m.kernel.ofds[id]? = some d)
    (reg : d.target = .inode ino) (readable : d.flags.access ≠ .writeOnly)
    (sl nextSlice : StepSlice) (out : Bytes)
    (read : stepSyscall m sl (.read a size) = (.ok out.toByteArray,n)) :
    (stepSyscall n nextSlice (.lseek b 0 .cur)).1 = .ok (d.offset+out.length) := by
  let count := min size (max 1 sl.maxBytes)
  let look := src.lookup desc
  by_cases interrupted : sl.intrBefore && decide (0 < size)
  · simp [stepSyscall,dispatchSyscall,fdRead,look,reg,readable,interrupted,Bind.bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at read
  · cases hr : inodeRead m.kernel.vfs ino d.offset count with
    | error e =>
      simp [stepSyscall,dispatchSyscall,fdRead,look,reg,readable,interrupted,count,Bind.bind,Except.bind,hr] at read
    | ok bs =>
      let next := m.setDesc id {d with offset := d.offset+bs.length}
      have raw : dispatchSyscall m sl (.read a size) = .ok (.ok bs.toByteArray,next) := by
        simp [dispatchSyscall,fdRead,look,reg,readable,interrupted,count,Bind.bind,Except.bind,Pure.pure,Except.pure,Machine.advance,next] at hr ⊢
        rw [hr]
        rfl
      cases hl : fdLinks next.proc next.kernel.ofds <;> simp [stepSyscall,raw,hl] at read
      obtain ⟨val,rfl⟩ := read
      have eq : bs = out := packed_bytes_injective (Ret.ok.inj val)
      subst bs
      have hnext : next.kernel.ofds[id]? = some {d with offset := d.offset + out.length} := by
        simp [next,Machine.setDesc]
      exact seek_cur (Holds.lookup (m := next) dst hnext) reg hl nextSlice

end LojitaCtx.Posix
