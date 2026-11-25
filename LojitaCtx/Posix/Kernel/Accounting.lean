import LojitaCtx.Posix.Kernel

namespace LojitaCtx.Posix

theorem account_WF (m : Machine) (backed : fdLinks m.proc m.kernel.ofds) :
    WFKernel m.account.proc m.account.kernel := by
  constructor
  · intro fd e he
    change m.proc.fds[fd]? = some e at he
    have mem := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr he
    have hd := List.all_eq_true.mp backed (fd,e) mem
    have pos : 0 < fdCount m.proc e.ofd := List.countP_pos_iff.mpr ⟨(fd,e),mem,by simp⟩
    change ((liveOfds m.proc m.kernel.ofds)[e.ofd]?).isSome
    obtain ⟨d,found⟩ := Option.isSome_iff_exists.mp hd
    simp [liveOfds, found, Nat.ne_of_gt pos]
  · intro id d hd
    change (liveOfds m.proc m.kernel.ofds)[id]? = some d at hd
    rw [liveOfds, Std.TreeMap.getElem?_filterMap'] at hd
    obtain ⟨old,_,h⟩ := Option.bind_eq_some_iff.mp hd
    by_cases hz : fdCount m.proc id = 0
    · simp [hz] at h
    · simp [hz] at h
      subst d
      exact ⟨rfl,Nat.pos_of_ne_zero hz⟩
  · intro id n hn
    change (liveInodes m.kernel.vfs (liveOfds m.proc m.kernel.ofds)).nodes[id]? = some n at hn
    rw [liveInodes, Std.TreeMap.getElem?_filterMap'] at hn
    obtain ⟨old,_,h⟩ := Option.bind_eq_some_iff.mp hn
    dsimp only at h
    split at h <;> simp_all [Machine.account]
    subst n
    rfl
  · intro id s hs
    change (livePipes m.kernel.pipes (liveOfds m.proc m.kernel.ofds))[id]? = some s at hs
    rw [livePipes, Std.TreeMap.getElem?_filterMap'] at hs
    obtain ⟨old,_,h⟩ := Option.bind_eq_some_iff.mp hs
    dsimp only at h
    split at h <;> simp_all [Machine.account]
    subst s
    exact ⟨rfl,rfl⟩

theorem stepSyscall_preserves_WF (m : Machine) (s : StepSlice) (op : SysOp)
    (h : WFKernel m.proc m.kernel) :
    WFKernel (stepSyscall m s op).2.proc (stepSyscall m s op).2.kernel := by
  unfold stepSyscall
  split
  · exact h
  · split
    · exact account_WF _ (by assumption)
    · exact h

end LojitaCtx.Posix
