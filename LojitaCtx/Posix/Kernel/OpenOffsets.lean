import LojitaCtx.Posix.Kernel.Independent

namespace LojitaCtx.Posix

private theorem fresh_ne {α : Type} (t : Table α) {k : Nat} (hk : k ∈ t) :
    tableFresh t ≠ k := by
  obtain ⟨km,hm⟩ := Option.isSome_iff_exists.mp (Std.TreeMap.isSome_maxKey?_of_mem hk)
  have hle := (Std.TreeMap.maxKey?_eq_some_iff_mem_and_forall.mp hm).2 k hk
  have le : k ≤ km := Nat.isLE_compare.mp hle
  simp [tableFresh,hm]
  omega

private theorem allocates {m n : Machine} {f : OpenFlags} {target : KernelTarget} {fd : Nat}
    (h : m.allocate target f = .ok (fd,n)) :
    Holds n fd (tableFresh m.kernel.ofds) ∧
    ∀ old i, Holds m old i → Holds n old i := by
  cases hf : (List.range (min m.proc.limit (m.fds.size+1))).find? (!m.fds.contains ·) with
  | none => simp [Machine.allocate,hf] at h
  | some fd' =>
    simp [Machine.allocate,hf] at h
    obtain ⟨rfl,rfl⟩ := h
    refine ⟨⟨⟨tableFresh m.kernel.ofds,f.cloexec⟩, ?_, rfl⟩, ?_⟩
    · simp [Machine.fds,Machine.setFds,Machine.setDesc]
    · intro old i held
      obtain ⟨e,he,hi⟩ := held
      have miss := List.find?_some hf
      have neq : fd ≠ old := by
        intro eq
        subst old
        simp [Std.TreeMap.contains_eq_isSome_getElem?,he] at miss
      exact ⟨e,by simpa [Machine.fds,Machine.setFds,Machine.setDesc,Std.TreeMap.getElem?_insert,neq] using he,hi⟩

/-- Every successful path open gets a new description even if the inode is
    already held, and preserves every formerly held descriptor binding. -/
theorem open_new_description {m n : Machine} {sl : StepSlice} {fd mode : Nat}
    {dir : DirFd} {path : Bytes} {f : OpenFlags}
    (h : stepSyscall m sl (.openat dir path f mode) = (.ok fd,n)) :
    ∃ id, Holds n fd id ∧ (∀ old ∈ m.kernel.ofds, id ≠ old) ∧
      ∀ other j, Holds m other j → Holds n other j := by
  simp only [stepSyscall,dispatchSyscall,openPath] at h
  by_cases space : m.fds.size ≥ m.proc.limit
  · simp [space,Bind.bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
  · cases hd : m.dirStart dir path with
    | error e => simp [space,hd,Bind.bind,Except.bind] at h
    | ok start =>
      cases hv : vfsOpenat m.kernel.vfs m.proc.root start path f (mode &&& (511-m.proc.umask)) with
      | error e => simp [space,hd,hv,Bind.bind,Except.bind] at h
      | ok pair =>
        obtain ⟨ino,table⟩ := pair
        cases ha : (m.setVfs table).allocate (.inode ino) f with
        | error e => simp [space,hd,hv,ha,Bind.bind,Except.bind] at h
        | ok result =>
          obtain ⟨k,next⟩ := result
          cases hl : fdLinks next.proc next.kernel.ofds <;>
            simp [space,hd,hv,ha,hl,Bind.bind,Except.bind,Pure.pure,Except.pure] at h
          cases h
          obtain ⟨fresh,preserved⟩ := allocates ha
          exact ⟨_,fresh,fun _ hk => fresh_ne _ hk,preserved⟩

end LojitaCtx.Posix
