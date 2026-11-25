import LojitaCtx.Posix.Kernel

namespace LojitaCtx.Posix

/-- The linked namespace includes modes, link counts, bytes, directory maps
    and symlink targets. Open-reference counts and nameless inodes are local
    descriptor bookkeeping, including final-close collection. -/
def namespaceAt (t : InodeTable) (id : Nat) : Option Inode :=
  (t.nodes[id]?).bind fun n => if n.nlink = 0 then none else some {n with openRefs := 0}

theorem liveInodes_namespace (t : InodeTable) (ds : Table OpenFileDesc) :
    namespaceAt (liveInodes t ds) = namespaceAt t := by
  funext i
  cases h : t.nodes[i]? with
  | none => simp [namespaceAt, liveInodes, h]
  | some n =>
    by_cases orphan : n.nlink = 0 <;> by_cases closed : targetCount ds (.inode i) = 0 <;>
      simp [namespaceAt, liveInodes, h, orphan, closed]

def SafeDesc (t : InodeTable) (d : OpenFileDesc) : Prop :=
  ∀ i n bytes, d.target = .inode i → t.nodes[i]? = some n →
    n.payload = .reg bytes → d.flags.access = .readOnly

def ReadOnlyRegularFds (m : Machine) : Prop :=
  ∀ (fd : Nat) (e : FdEntry) (d : OpenFileDesc), m.fds[fd]? = some e →
    m.kernel.ofds[e.ofd]? = some d → SafeDesc m.kernel.vfs d

private theorem lookup_safe {m : Machine} (safe : ReadOnlyRegularFds m)
    {fd id : Nat} {d : OpenFileDesc} (lookup : m.lookup fd = .ok (id,d)) :
    SafeDesc m.kernel.vfs d := by
  cases he : m.fds[fd]? <;> simp [Machine.lookup,he,throw,throwThe,MonadExceptOf.throw] at lookup
  rename_i e
  cases hd : m.kernel.ofds[e.ofd]? <;> simp [hd,Pure.pure,Except.pure] at lookup
  obtain ⟨rfl,rfl⟩ := lookup
  exact safe _ _ _ he hd

private theorem same_rights {t : InodeTable} {a b : OpenFileDesc} (ha : SafeDesc t a)
    (target : b.target = a.target) (access : b.flags.access = a.flags.access) : SafeDesc t b := by
  intro i n bs d node reg
  exact access.trans (ha i n bs (target.symm.trans d) node reg)

private theorem update_desc {m : Machine} (safe : ReadOnlyRegularFds m) (id : Nat)
    (d : OpenFileDesc) (good : SafeDesc m.kernel.vfs d) :
    ReadOnlyRegularFds (m.setDesc id d) := by
  intro fd e desc fe de
  change (m.kernel.ofds.insert id d)[e.ofd]? = some desc at de
  by_cases h : id = e.ofd
  · subst id; simp at de; subst desc; exact good
  · simp [Std.TreeMap.getElem?_insert,h] at de
    exact safe fd e desc fe de

private theorem alias_fd {m : Machine} (safe : ReadOnlyRegularFds m) (fd id : Nat) (flag : Bool)
    (held : ∃ (src : Nat) (e : FdEntry), m.fds[src]? = some e ∧ e.ofd = id) :
    ReadOnlyRegularFds (m.setFds (m.fds.insert fd ⟨id,flag⟩)) := by
  intro f e d fe de
  change (m.fds.insert fd ⟨id,flag⟩)[f]? = some e at fe
  by_cases h : fd = f
  · subst f; simp at fe; subst e
    obtain ⟨src,entry,hsrc,rfl⟩ := held
    exact safe src entry d hsrc de
  · simp [Std.TreeMap.getElem?_insert,h] at fe
    exact safe f e d fe de

private theorem held_lookup {m : Machine} {fd id : Nat} {d : OpenFileDesc}
    (look : m.lookup fd = .ok (id,d)) : ∃ (src : Nat) (e : FdEntry), m.fds[src]? = some e ∧ e.ofd = id := by
  cases he : m.fds[fd]? <;> simp [Machine.lookup,he,throw,throwThe,MonadExceptOf.throw] at look
  rename_i e
  cases hd : m.kernel.ofds[e.ofd]? <;> simp [hd,Pure.pure,Except.pure] at look
  exact ⟨fd,e,he,look.1⟩

private theorem erase_fd {m : Machine} (safe : ReadOnlyRegularFds m) (fd : Nat) :
    ReadOnlyRegularFds (m.setFds (m.fds.erase fd)) := by
  intro f e d fe de
  change (m.fds.erase fd)[f]? = some e at fe
  by_cases h : fd = f
  · subst f; simp at fe
  · simp [Std.TreeMap.getElem?_erase,h] at fe
    exact safe f e d fe de

private theorem safe_account (m : Machine) (safe : ReadOnlyRegularFds m) : ReadOnlyRegularFds m.account := by
  intro fd e d fe de i n bs tgt found reg
  change (liveOfds m.proc m.kernel.ofds)[e.ofd]? = some d at de
  rw [liveOfds, Std.TreeMap.getElem?_filterMap'] at de
  obtain ⟨old,oldD,adj⟩ := Option.bind_eq_some_iff.mp de
  dsimp only at adj
  split at adj <;> simp_all only [Option.some.injEq, reduceCtorEq]
  subst d
  change (liveInodes m.kernel.vfs _).nodes[i]? = some n at found
  rw [liveInodes, Std.TreeMap.getElem?_filterMap'] at found
  obtain ⟨original,oldN,kept⟩ := Option.bind_eq_some_iff.mp found
  dsimp only at kept
  split at kept <;> simp_all only [Option.some.injEq, reduceCtorEq]
  subst n
  exact safe fd e old fe oldD i original bs tgt oldN reg

private abbrev Stable (m n : Machine) := n.kernel.vfs = m.kernel.vfs ∧ ReadOnlyRegularFds n

private theorem allocate_frame {m n : Machine} (s : ReadOnlyRegularFds m) (target : KernelTarget)
    (flags : OpenFlags) (nonFile : ∀ i, target ≠ .inode i) {fd : Nat}
    (h : m.allocate target flags = .ok (fd,n)) : Stable m n := by
  unfold Machine.allocate at h
  split at h <;> try contradiction
  rename_i newFd _
  simp only [Pure.pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
  obtain ⟨rfl,rfl⟩ := h
  refine ⟨rfl, ?_⟩
  intro f e d fe de
  change (m.fds.insert _ _)[f]? = some e at fe
  change (m.kernel.ofds.insert _ _)[e.ofd]? = some d at de
  by_cases fresh : tableFresh m.kernel.ofds = e.ofd
  · simp only [Std.TreeMap.getElem?_insert,Std.compare_eq_iff_eq,fresh,ite_true,Option.some.injEq] at de
    subst d
    intro i _ _ eq
    exact False.elim (nonFile i eq)
  · simp [Std.TreeMap.getElem?_insert, fresh] at de
    by_cases same : newFd = f
    · subst f; simp at fe; subst e; exact False.elim (fresh rfl)
    · simp [Std.TreeMap.getElem?_insert,same] at fe
      exact s f e d fe de

private theorem pipe_frame {m n : Machine} (safe : ReadOnlyRegularFds m) {r : Ret (Fd × Fd)}
    {nb ce : Bool} (h : fdPipe m nb ce = .ok (r,n)) : Stable m n := by
  unfold fdPipe at h
  simp only [Bind.bind,Except.bind,Pure.pure,Except.pure] at h
  split at h <;> try contradiction
  rename_i pair h1
  rcases pair with ⟨rd,k⟩
  have p1 := allocate_frame (m := m.setPipe (tableFresh m.kernel.pipes) {}) safe _ _ (fun _ no => by cases no) h1
  split at h <;> try contradiction
  rename_i pair h2
  rcases pair with ⟨wr,k'⟩
  have p2 := allocate_frame p1.2 _ _ (fun _ no => by cases no) h2
  cases h
  exact ⟨p2.1.trans p1.1,p2.2⟩

private theorem advance_frame {m : Machine} (safe : ReadOnlyRegularFds m) {fd id : Nat}
    {d : OpenFileDesc} (h : m.lookup fd = .ok (id,d)) (off : Nat) (pos : Bool) :
    Stable m (m.advance id d off pos) := by
  cases pos
  · exact ⟨rfl, update_desc safe _ _ (same_rights (lookup_safe safe h) rfl rfl)⟩
  · exact ⟨rfl, safe⟩

private theorem read_frame {m n : Machine} (safe : ReadOnlyRegularFds m) {r : Ret Bytes}
    {sl : StepSlice} {fd size : Nat} {atOff : Option Nat} (h : fdRead m sl fd size atOff = .ok (r,n)) :
    Stable m n := by
  cases look : m.lookup fd with
  | error e => simp [fdRead,look,Bind.bind,Except.bind] at h
  | ok v =>
    rcases v with ⟨id,d⟩
    cases ht : d.target <;> simp [fdRead,look,ht,Bind.bind,Except.bind,Pure.pure,Except.pure,
      throw,throwThe,MonadExceptOf.throw] at h <;>
      repeat' first | (split at h) | contradiction
    all_goals cases h
    all_goals first | exact ⟨rfl,safe⟩ | exact advance_frame safe look _ _

private theorem write_frame {m n : Machine} (safe : ReadOnlyRegularFds m) {r : Ret Nat}
    {sl : StepSlice} {fd : Nat} {bs : Bytes} {atOff : Option Nat}
    (h : fdWrite m sl fd bs atOff = .ok (r,n)) : Stable m n := by
  cases look : m.lookup fd with
  | error e => simp [fdWrite,look,Bind.bind,Except.bind] at h
  | ok v =>
    rcases v with ⟨id,d⟩
    cases ht : d.target with
    | inode i =>
      cases hn : m.kernel.vfs.nodes[i]? with
      | none =>
        simp [fdWrite,look,ht,inodeWrite,InodeTable.node,hn,Bind.bind,Except.bind,
          throw,throwThe,MonadExceptOf.throw] at h
        repeat' first | (split at h) | contradiction
      | some node =>
        cases kind : node.payload <;>
          simp [fdWrite,look,ht,inodeWrite,InodeTable.node,hn,kind,Bind.bind,Except.bind,
            Pure.pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h
        case reg bytes =>
          have no := lookup_safe safe look i node bytes ht hn kind
          simp [no] at h
        all_goals repeat' first | (split at h) | contradiction
        all_goals cases ro : node.roLayer <;> simp_all
    | pipe i wr | pty i wr | sock i =>
      simp [fdWrite,look,ht,Bind.bind,Except.bind,Pure.pure,Except.pure,
        throw,throwThe,MonadExceptOf.throw] at h
      repeat' first | (split at h) | contradiction
      all_goals cases h
      all_goals first | exact ⟨rfl,safe⟩ | (split <;> exact ⟨rfl,safe⟩)

private theorem seek_frame {m n : Machine} (safe : ReadOnlyRegularFds m) {r : Ret Nat}
    {fd : Nat} {delta : Int} {w : Whence} (h : fdSeek m fd delta w = .ok (r,n)) : Stable m n := by
  cases look : m.lookup fd with
  | error e => simp [fdSeek,look,Bind.bind,Except.bind] at h
  | ok v =>
    rcases v with ⟨id,d⟩
    simp [fdSeek,look,Bind.bind,Except.bind,Pure.pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h
    repeat' first | (split at h) | contradiction
    all_goals cases h
    all_goals exact ⟨rfl,update_desc safe _ _ (same_rights (lookup_safe safe look) rfl rfl)⟩

private theorem dup_frame {m n : Machine} (safe : ReadOnlyRegularFds m) {r : Ret Nat}
    {src dst : Nat} (h : fdDup2 m src dst = .ok (r,n)) : Stable m n := by
  cases look : m.lookup src with
  | error e => simp [fdDup2,look,Bind.bind,Except.bind] at h
  | ok v =>
    rcases v with ⟨id,d⟩
    simp [fdDup2,look,Bind.bind,Except.bind,Pure.pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h
    repeat' first | (split at h) | contradiction
    all_goals cases h
    all_goals first | exact ⟨rfl,safe⟩ | exact ⟨rfl,alias_fd safe _ _ _ (held_lookup look)⟩

private theorem poll_frame (m : Machine) (safe : ReadOnlyRegularFds m) (sl : StepSlice)
    (reqs : List PollReq) (ms : Option Nat) (signals : Bool) :
    Stable m (pollAll m sl reqs ms signals).2 := by
  unfold pollAll
  dsimp only
  split
  · exact ⟨rfl,safe⟩
  · split
    · exact ⟨rfl,safe⟩
    · cases ms <;> exact ⟨rfl,safe⟩

private theorem dispatch_frame (m : Machine) (safe : ReadOnlyRegularFds m) (sl : StepSlice)
    (op : SysOp) (nonpath : op.cap ≠ .fsPathCap) (r : Ret op.Result) (n : Machine)
    (h : dispatchSyscall m sl op = .ok (r,n)) : Stable m n := by
  cases op <;> simp only [SysOp.cap, ne_eq, not_true_eq_false] at nonpath <;> try contradiction
  case read => exact read_frame safe (packRead_source h).choose_spec
  case pread => exact read_frame safe (packRead_source h).choose_spec
  case write => exact write_frame safe h
  case pwrite => exact write_frame safe h
  case lseek => exact seek_frame safe h
  case dup2 => exact dup_frame safe h
  case pipe2 => exact pipe_frame safe h
  case ppoll reqs ms signals =>
    change Except.ok (pollAll m sl reqs ms signals) = Except.ok (r,n) at h
    have eq : (pollAll m sl reqs ms signals).2 = n := congrArg Prod.snd (Except.ok.inj h)
    rw [← eq]
    exact poll_frame m safe sl reqs ms signals
  case close fd =>
    cases look : m.lookup fd with
    | error e => simp [dispatchSyscall,discard,Functor.mapConst,Except.map,look,Bind.bind,Except.bind] at h
    | ok pair =>
      simp [dispatchSyscall,discard,look,Bind.bind,Except.bind,Pure.pure,Except.pure] at h
      obtain ⟨_,rfl⟩ := h
      exact ⟨rfl,erase_fd safe fd⟩
  case setNonblock fd val =>
    cases look : m.lookup fd with
    | error e => simp [dispatchSyscall,look,Bind.bind,Except.bind] at h
    | ok val =>
      rcases val with ⟨id,d⟩
      simp [dispatchSyscall,look,Bind.bind,Except.bind,Pure.pure,Except.pure] at h
      obtain ⟨_,rfl⟩ := h
      exact ⟨rfl,update_desc safe _ _ (same_rights (lookup_safe safe look) rfl rfl)⟩
  case setCloexec fd val =>
    cases look : m.lookup fd with
    | error e => simp [dispatchSyscall,look,Bind.bind,Except.bind] at h
    | ok val =>
      rcases val with ⟨id,d⟩
      simp [dispatchSyscall,look,Bind.bind,Except.bind,Pure.pure,Except.pure] at h
      obtain ⟨_,rfl⟩ := h
      exact ⟨rfl,alias_fd safe _ _ _ (held_lookup look)⟩
  case socketStream nb ce =>
    simp [dispatchSyscall,Bind.bind,Except.bind,Pure.pure,Except.pure] at h
    split at h <;> try contradiction
    rename_i pair halloc
    rcases pair with ⟨fd,k⟩
    cases h
    exact allocate_frame (m := m.setSock (tableFresh m.kernel.socks) {}) safe _ _ (fun _ no => by cases no) halloc
  all_goals
    simp only [dispatchSyscall, Bind.bind, Except.bind, Pure.pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at h
    repeat' first
      | (solve | cases h; exact ⟨rfl,safe⟩)
      | contradiction
      | split at h

private theorem step_frame (m : Machine) (safe : ReadOnlyRegularFds m) (sl : StepSlice)
    (op : SysOp) (noPath : op.cap ≠ .fsPathCap) :
    let next := (stepSyscall m sl op).2
    namespaceAt next.kernel.vfs = namespaceAt m.kernel.vfs ∧ ReadOnlyRegularFds next := by
  cases h : dispatchSyscall m sl op with
  | error e => simpa [stepSyscall,h] using (And.intro rfl safe :
      namespaceAt m.kernel.vfs = namespaceAt m.kernel.vfs ∧ ReadOnlyRegularFds m)
  | ok pair =>
    rcases pair with ⟨r,n⟩
    have raw := dispatch_frame m safe sl op noPath r n h
    cases links : fdLinks n.proc n.kernel.ofds <;> simp only [stepSyscall,h,links,Bool.false_eq_true,ite_false,ite_true, true_and, eq_self]
    · exact safe
    · split
      · exact ⟨congrArg namespaceAt raw.1,raw.2⟩
      · exact ⟨(liveInodes_namespace n.kernel.vfs _).trans (congrArg namespaceAt raw.1), safe_account n raw.2⟩

private theorem prefix_frame {Δ : List Cap} {A : Type} (denied : Cap.fsPathCap ∉ Δ)
    (schedule : List StepSlice) (p : Prefix Δ A) (m : Machine) (safe : ReadOnlyRegularFds m) :
    namespaceAt (runPrefix p m schedule).2.kernel.vfs = namespaceAt m.kernel.vfs := by
  induction schedule generalizing p m with
  | nil => cases p <;> rfl
  | cons sl rest ih =>
    cases p with
    | done _ | suspended => rfl
    | ask op allowed next =>
      have noPath : op.cap ≠ .fsPathCap := fun eq => denied (eq ▸ allowed)
      have frame := step_frame m safe sl op noPath
      exact (ih (next (stepSyscall m sl op).1) (stepSyscall m sl op).2 frame.2).trans frame.1

/-- Every finite observation, including suspended executions, preserves the
    entire linked namespace for a process without a path or writable file capability. -/
theorem capsicum_vfs_frame {Δ : List Cap} {S A : Type} (program : PosixMachine Δ S A)
    (m : Machine) (fuel : Nat) (schedule : List StepSlice)
    (denied : Cap.fsPathCap ∉ Δ) (safe : ReadOnlyRegularFds m) :
    namespaceAt (runPrefix (program.observe fuel) m schedule).2.kernel.vfs = namespaceAt m.kernel.vfs :=
  prefix_frame denied schedule (program.observe fuel) m safe

end LojitaCtx.Posix
