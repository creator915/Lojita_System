import LojitaCtx.Posix.Kernel.Accounting

namespace LojitaCtx.Posix

/-- A descriptor that names a real pty survives the accounting pass performed
    by stepSyscall. Thus tcgetattr observes any termios installed by tcsetattr. -/
theorem syscall_tcsetattr_tcgetattr (m : Machine) (fd : Fd) (e : FdEntry)
    (d : OpenFileDesc) (pty : PtyId) (master : Bool) (tty : PtyState)
    (backed : fdLinks m.proc m.kernel.ofds)
    (entry : m.fds[fd]? = some e) (desc : m.kernel.ofds[e.ofd]? = some d)
    (kind : d.target = .pty pty master) (present : m.kernel.ptys[pty]? = some tty)
    (attrs : Termios) (setSlice getSlice : StepSlice) :
    let set := stepSyscall m setSlice (.tcsetattr fd attrs)
    set.1 = .ok () ∧ (stepSyscall set.2 getSlice (.tcgetattr fd)).1 = .ok attrs := by
  let updated := tcsetattr tty attrs
  let next := m.setPty pty updated
  have look : m.lookup fd = .ok (e.ofd,d) := by simp [Machine.lookup,entry,desc]; rfl
  have query : ttyOf m fd = .ok (pty,tty) := by
    simp [ttyOf,look,kind,present, Bind.bind,Except.bind,Pure.pure,Except.pure]
  have setRaw : dispatchSyscall m setSlice (.tcsetattr fd attrs) = .ok (.ok (),next) := by
    simp [dispatchSyscall, query, Bind.bind, Except.bind, Pure.pure, Except.pure, next, updated]
  have set : stepSyscall m setSlice (.tcsetattr fd attrs) = (.ok (),next.account) := by
    simp [stepSyscall,setRaw,show fdLinks next.proc next.kernel.ofds from backed]
  have oldEntry := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr entry
  have held : 0 < fdCount m.proc e.ofd := List.countP_pos_iff.mpr ⟨(fd,e),oldEntry,by simp⟩
  let accounted := {d with refcnt := fdCount m.proc e.ofd}
  have live : (liveOfds m.proc m.kernel.ofds)[e.ofd]? = some accounted := by
    simp [liveOfds, desc, Nat.ne_of_gt held,accounted]
  have targetLive : 0 < targetCount (liveOfds m.proc m.kernel.ofds) (.pty pty master) := by
    apply List.countP_pos_iff.mpr
    exact ⟨(e.ofd,accounted), Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr live, by simp [accounted,kind]⟩
  have either : 0 < targetCount (liveOfds m.proc m.kernel.ofds) (.pty pty false) +
        targetCount (liveOfds m.proc m.kernel.ofds) (.pty pty true) := by cases master <;> omega
  have recorded : next.account.kernel.ptys[pty]? = some updated := by
    simp [Machine.account, next, Machine.setPty, either]
  have lookup' : next.account.lookup fd = .ok (e.ofd,accounted) := by
    have ef : next.account.fds[fd]? = some e := entry
    have df : next.account.kernel.ofds[e.ofd]? = some accounted := live
    simp [Machine.lookup,ef,df]; rfl
  have query' : ttyOf next.account fd = .ok (pty,updated) := by
    simp [ttyOf,lookup',accounted,kind,recorded,Bind.bind,Except.bind,Pure.pure,Except.pure]
  have getRaw : dispatchSyscall next.account getSlice (.tcgetattr fd) = .ok (.ok attrs,next.account) := by
    have recordedAttrs : updated.attrs = attrs := tcsetattr_tcgetattr_roundtrip tty attrs
    simp [dispatchSyscall,query',recordedAttrs,Functor.map,Except.map]
  have stillBacked : fdLinks next.account.proc next.account.kernel.ofds := by
    apply List.all_eq_true.mpr
    intro pair mem
    exact (account_WF next backed).fdLive _ _ (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp mem)
  simp only [set]
  exact ⟨True.intro,by simp [stepSyscall,getRaw,stillBacked]⟩

end LojitaCtx.Posix
