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

private theorem targetCount_offset (ds : Table OpenFileDesc) (id : Nat) (d : OpenFileDesc)
    (found : ds[id]? = some d) (off : Nat) (t : KernelTarget) :
    targetCount (ds.insert id {d with offset := off}) t = targetCount ds t := by
  have same : (ds.insert id d).Equiv ds := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro k
    by_cases eq : id = k <;> simp_all [Std.TreeMap.getElem?_insert]
  unfold targetCount
  rw [← same.toList_eq]
  rw [(Std.TreeMap.toList_insert_perm (t := ds) (k := id) (v := {d with offset := off})).countP_eq,
      (Std.TreeMap.toList_insert_perm (t := ds) (k := id) (v := d)).countP_eq]
  simp [List.countP_cons]

private theorem advance_WF {m : Machine} (wf : WFKernel m.proc m.kernel) {fd id : Nat}
    {d : OpenFileDesc} (look : m.lookup fd = .ok (id,d)) (off : Nat) (positioned : Bool) :
    WFKernel (m.advance id d off positioned).proc (m.advance id d off positioned).kernel := by
  cases positioned <;> simp [Machine.advance]
  case true => exact wf
  have found : m.kernel.ofds[id]? = some d := by
    cases he : m.fds[fd]? <;> simp [Machine.lookup,he,throw,throwThe,MonadExceptOf.throw] at look
    rename_i e
    cases hd : m.kernel.ofds[e.ofd]? <;> simp [hd,Pure.pure,Except.pure] at look
    obtain ⟨rfl,rfl⟩ := look
    exact hd
  constructor
  · intro f e fe
    by_cases eq : id = e.ofd <;> simp_all [Machine.setDesc,Std.TreeMap.getElem?_insert,wf.fdLive f e fe]
  · intro k v hv
    change (m.kernel.ofds.insert id {d with offset := off})[k]? = some v at hv
    by_cases eq : id = k
    · subst k; simp at hv; subst v; exact wf.descriptions id d found
    · simp [Std.TreeMap.getElem?_insert,eq] at hv
      exact wf.descriptions _ _ hv
  · intro i n hn
    exact (wf.inodes i n hn).trans (targetCount_offset _ _ _ found _ _).symm
  · intro i s hs
    obtain ⟨r,w⟩ := wf.pipes i s hs
    exact ⟨r.trans (targetCount_offset _ _ _ found _ _).symm,w.trans (targetCount_offset _ _ _ found _ _).symm⟩

private theorem pipeRead_WF {m : Machine} (wf : WFKernel m.proc m.kernel) (i : Nat)
    {s : StreamBuf} (found : m.kernel.pipes[i]? = some s) (sl : StepSlice) (nb : Bool) (ps : PipePages) :
    let next := (m.setPipe i (streamRead sl nb s).2).setPages i ps
    WFKernel next.proc next.kernel := by
  refine ⟨wf.fdLive,wf.descriptions,wf.inodes,?_⟩
  intro k v hv
  change (m.kernel.pipes.insert i (streamRead sl nb s).2)[k]? = some v at hv
  by_cases eq : i = k
  · subst k; simp at hv; subst v
    have counts := wf.pipes i s found
    unfold streamRead
    split <;> first | exact counts | split <;> exact counts
  · simp [Std.TreeMap.getElem?_insert,eq] at hv
    exact wf.pipes _ _ hv

theorem fdRead_preserves_WF {m n : Machine} (wf : WFKernel m.proc m.kernel)
    {r : Ret Bytes} {sl : StepSlice} {fd size : Nat} {atOff : Option Nat}
    (h : fdRead m sl fd size atOff = .ok (r,n)) : WFKernel n.proc n.kernel := by
  cases look : m.lookup fd with
  | error e => simp [fdRead,look,Bind.bind,Except.bind] at h
  | ok v =>
    rcases v with ⟨id,d⟩
    cases ht : d.target <;> simp [fdRead,look,ht,Bind.bind,Except.bind,Pure.pure,Except.pure,
      throw,throwThe,MonadExceptOf.throw] at h <;>
      repeat' first | (split at h) | contradiction
    all_goals cases h
    all_goals first
      | exact wf
      | exact ⟨wf.fdLive,wf.descriptions,wf.inodes,wf.pipes⟩
      | exact advance_WF wf look _ _
      | apply pipeRead_WF wf <;> assumption

theorem stepSyscall_preserves_WF (m : Machine) (s : StepSlice) (op : SysOp)
    (h : WFKernel m.proc m.kernel) :
    WFKernel (stepSyscall m s op).2.proc (stepSyscall m s op).2.kernel := by
  unfold stepSyscall
  split
  · exact h
  · rename_i r n dispatch
    split
    · split
      · rename_i read
        cases op <;> simp at read <;> exact fdRead_preserves_WF h (packRead_source dispatch).choose_spec
      · exact account_WF _ (by assumption)
    · exact h

end LojitaCtx.Posix
