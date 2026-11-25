import LojitaCtx.Posix.Vfs.UnlinkFrame

namespace LojitaCtx.Posix

private def writable (t : InodeTable) (id : InodeId) : Except Errno Unit := do
  if (← t.node id).roLayer then throw .EROFS

private def directoryPatch (t : InodeTable) (id : InodeId) (f : Entries → Entries)
    (linkDelta : Int := 0) : Except Errno InodeEdit := do
  let n ← t.node id
  let .dir p es := n.payload | throw .ENOTDIR
  return .put id { n with payload := .dir p (f es), nlink := (Int.ofNat n.nlink + linkDelta).toNat }

private def create (t : InodeTable) (a : NameSlot InodeId) (n : Inode) : Except Errno (InodeId × InodeTable) := do
  if a.target.isSome then throw .EEXIST
  writable t a.parent
  let id := t.nextId
  let parent ← directoryPatch t a.parent (·.insert a.name id) (if n.payload.kind = .directory then 1 else 0)
  return (id, ← t.commit [parent, .put id n])

def vfsMkdirat (t : InodeTable) (root start : InodeId) (p : Bytes)
    (mode : FileMode := 493) : Except Errno InodeTable := do
  let a ← resolveParentAt t root start 40 p false false
  if a.target.isSome then throw .EEXIST
  return (← create t a {payload := .dir a.parent {}, mode, nlink := 2}).2

def vfsSymlinkat (t : InodeTable) (root start : InodeId) (target p : Bytes) :
    Except Errno InodeTable := do
  if target.contains 0 then throw .EINVAL
  if target.isEmpty then throw .ENOENT
  if target.length ≥ 4096 then throw .ENAMETOOLONG
  let a ← resolveParentAt t root start 40 p false false
  if a.slash && a.target.isNone then throw .ENOENT
  return (← create t a {payload := .symlink target, mode := 511}).2

def vfsOpenat (t : InodeTable) (root start : InodeId) (p : Bytes)
    (flags : OpenFlags) (mode : FileMode := 420) : Except Errno (InodeId × InodeTable) := do
  if flags.create && flags.directory then throw .EINVAL
  let trailing := p.getLast? == some 47
  let follow := trailing || !(flags.nofollow || (flags.create && flags.excl))
  let a ← resolveParentAt t root start 40 p follow
  if flags.create && a.slash then throw .EISDIR
  let some id := a.target | do
    if !flags.create then throw .ENOENT
    return ← create t a {payload := .reg ByteArray.empty, mode}
  if flags.excl && flags.create then throw .EEXIST
  let n ← t.node id
  if flags.directory && n.payload.kind != .directory then throw .ENOTDIR
  if n.payload.kind = .symlink then throw .ELOOP
  if n.payload.kind = .directory && (flags.access != .readOnly || flags.create || flags.trunc) then throw .EISDIR
  if flags.access != .readOnly || flags.trunc then writable t id
  if flags.trunc && n.payload.kind == .regular then
    return (id, ← t.commit [.put id {n with payload := .reg ByteArray.empty}])
  return (id, t)

def vfsFstatat (t : InodeTable) (root start : InodeId) (p : Bytes)
    (followLast : Bool := true) : Except Errno StatObs := do
  inodeStat t (← resolveAt t root start 40 p (followLast || p.getLast? == some 47))

def vfsReadlinkat (t : InodeTable) (root start : InodeId) (p : Bytes) : Except Errno Bytes := do
  let id ← resolveAt t root start 40 p (p.getLast? == some 47)
  let .symlink bytes := (← t.node id).payload | throw .EINVAL
  return bytes

private def removalEdits (t : InodeTable) (a : NameSlot InodeId) (id : InodeId)
    (n : Inode) : Except Errno (List InodeEdit) := do
  let dir := n.payload.kind == .directory
  let parent ← directoryPatch t a.parent (·.erase a.name) (if dir then -1 else 0)
  let kept := {n with nlink := if dir then 0 else n.nlink - 1}
  let child := if kept.nlink == 0 && kept.openRefs == 0 then .erase id else .put id kept
  return [parent, child]

def vfsUnlinkat (t : InodeTable) (root start : InodeId) (p : Bytes)
    (removeDir : Bool := false) : Except Errno InodeTable := do
  let a ← resolveParentAt t root start 40 p false
  let some id := a.target | throw .ENOENT
  let n ← t.node id
  if removeDir then
    if a.name == [46] then throw .EINVAL
    if a.name == [46,46] then throw .ENOTEMPTY
    let .dir _ es := n.payload | throw .ENOTDIR
    if !es.isEmpty then throw .ENOTEMPTY
  else if n.payload.kind == .directory || a.name == [46] || a.name == [46,46] then throw .EISDIR
  t.commit (← removalEdits t a id n)

/-- A bounded parent walk rejects malformed cyclic inode tables as well. -/
private def checkMove (t : InodeTable) (source : InodeId) : Nat → InodeId → Except Errno Unit
  | 0, _ => .error .ELOOP
  | fuel+1, cur => do
    if cur = source then throw .EINVAL
    let (parent, _) ← t.directory cur
    if parent = cur then return ()
    checkMove t source fuel parent

def vfsRenameat (t : InodeTable) (root fromDir : InodeId) (fromPath : Bytes)
    (toDir : InodeId) (toPath : Bytes) : Except Errno InodeTable := do
  let src ← resolveParentAt t root fromDir 40 fromPath false
  let dst ← resolveParentAt t root toDir 40 toPath false
  if !validSeg src.name || !validSeg dst.name then throw (.other 16)
  let some id := src.target | throw .ENOENT
  let n ← t.node id
  let dir := n.payload.kind == .directory
  if dst.slash && !dir then throw .ENOTDIR
  if dst.target == some id then return t
  writable t src.parent
  writable t dst.parent
  writable t id
  if dir then checkMove t id (t.nodes.size + 1) dst.parent
  let mut edits : List InodeEdit := [.claim id]
  if let some replace := dst.target then
    let old ← t.node replace
    writable t replace
    match old.payload with
    | .dir _ es =>
      if !dir then throw .EISDIR
      if !es.isEmpty then throw .ENOTEMPTY
    | _ => if dir then throw .ENOTDIR
    edits := edits ++ (← removalEdits t dst replace old)
  edits := edits ++ [← directoryPatch (t.preview edits) src.parent (·.erase src.name) (if dir then -1 else 0)]
  edits := edits ++ [← directoryPatch (t.preview edits) dst.parent (·.insert dst.name id) (if dir then 1 else 0)]
  if let .dir _ es := n.payload then
    edits := edits ++ [.put id {n with payload := .dir dst.parent es}]
  t.commit edits

def vfsGetcwd (t : InodeTable) (root cwd : InodeId) : Except Errno Bytes :=
  let rec climb (fuel cur : Nat) (rev : List Seg) : Except Errno Bytes := do
    if cur = root then return 47 :: List.intercalate [47] rev
    match fuel with
    | 0 => throw .ELOOP
    | k+1 =>
      let (p, _) ← t.directory cur
      let (_, es) ← t.directory p
      let some (name, _) := es.toList.find? (fun entry => entry.2 == cur) | throw .ENOENT
      climb k p (name :: rev)
  climb (t.nodes.size + 1) cwd []

theorem unlink_open_inode_alive (t next : InodeTable) (root start : InodeId) (p : Bytes)
    (a : NameSlot InodeId) (id : Nat) (n : Inode) (data : ByteArray)
    (located : resolveParentAt t root start 40 p false = .ok a)
    (target : a.target = some id) (node : t.node id = .ok n)
    (regular : n.payload = .reg data) (opened : 0 < n.openRefs)
    (unlinked : vfsUnlinkat t root start p false = .ok next) :
    (∀ follow, resolveAt next root start 40 p follow = .error .ENOENT) ∧
    (next.node id).map Inode.payload = .ok (.reg data) ∧
    ∀ off count, inodeRead next id off count = inodeRead t id off count := by
  have nz : n.openRefs ≠ 0 := by omega
  have ordinary : a.name ≠ [46] ∧ a.name ≠ [46,46] := by
    constructor <;> intro h <;>
      simp [vfsUnlinkat, located, target, node, regular, h, InodePayload.kind,
        Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at unlinked
  obtain ⟨plan, prepared, clear, parEq, nameEq, last⟩ := nofollow_plan t root start 40 p a located
  have edge : t.entryAt a.parent a.name = some id := by
    rw [← parEq, ← nameEq] at last
    simpa [lastEntry, ordinary.1, ordinary.2, target] using last.symm
  simp [vfsUnlinkat, located, target, node, regular, InodePayload.kind, ordinary.1, ordinary.2,
    removalEdits, directoryPatch, Bind.bind, Except.bind, Pure.pure, Except.pure, nz] at unlinked
  cases hp : t.node a.parent with
  | error e => simp [hp] at unlinked
  | ok par =>
    cases hk : par.payload <;> simp [hp, hk, throw, throwThe, MonadExceptOf.throw] at unlinked
    rename_i parent es
    have ne : id ≠ a.parent := by
      intro same
      rw [← same, node] at hp
      cases hp
      rw [regular] at hk
      contradiction
    unfold InodeTable.commit at unlinked
    split at unlinked
    · contradiction
    next =>
      have asMap (t : InodeTable) (i : Nat) (v : Inode) (h : t.node i = .ok v) :
          t.nodes[i]? = some v := by
        unfold InodeTable.node at h
        cases e : t.nodes[i]? <;> simp [e] at h
        exact congrArg some h
      have frame := removed_leaf_navigation t next a.parent id parent a.name es par n data ne
        (asMap t _ _ hp) (asMap t _ _ node) hk regular edge (by cases unlinked; rfl)
      constructor
      · intro follow
        apply missing_leaf next root start 40 p plan _ clear _ follow
        · rwa [frame.1]
        · simpa [← parEq, ← nameEq, lastEntry, ordinary.1, ordinary.2] using frame.2
      cases unlinked
      simp only [inodeRead, Except.map,
        InodeTable.preview, List.foldl_cons, List.foldl_nil, InodeEdit.apply, InodeTable.put,
        InodeTable.node, Std.TreeMap.getElem?_insert,
        Std.compare_eq_iff_eq, Ne.symm ne, ite_false, ite_true, Option.elim_some, Bind.bind, Except.bind, Pure.pure, Except.pure]
      unfold InodeTable.node at node
      simp [node, regular]

theorem mkdirat_strict_posix (t : InodeTable) (root start : InodeId) (p : Bytes) (mode : FileMode) :
    (resolveParentAt t root start 40 p false false = .error .ENOENT →
      vfsMkdirat t root start p mode = .error .ENOENT) ∧
    (∀ (a : NameSlot InodeId) id, resolveParentAt t root start 40 p false false = .ok a →
      a.target = some id → vfsMkdirat t root start p mode = .error .EEXIST) := by
  constructor
  · intro h; simp [vfsMkdirat, h, Bind.bind, Except.bind]
  · intro a id h ha; simp [vfsMkdirat, h, ha, Bind.bind, Except.bind]; rfl

/-- Direct frame at all five public path mutation entry points. -/
def RoFrame (t u : InodeTable) : Prop :=
  ∀ i, t.protectedAt i = true → u.nodes[i]? = t.nodes[i]?

private theorem commit_frame {t u : InodeTable} {es : List InodeEdit} (h : t.commit es = .ok u) :
    RoFrame t u := fun i ro => (roLayer_vfs_immutable t es i ro).2 u h

private theorem create_frame {t : InodeTable} {v : Nat × InodeTable} {a : NameSlot Nat}
    {n : Inode} (h : create t a n = .ok v) : RoFrame t v.2 := by
  simp only [create, Bind.bind, Except.bind, Pure.pure, Except.pure,
    throw,throwThe,MonadExceptOf.throw] at h
  repeat' first | (solve | cases h; apply commit_frame; assumption) | contradiction | split at h

theorem path_mutations_preserve_ro (t u : InodeTable) (root dir : Nat) (path : Bytes) :
    (∀ flags mode id, vfsOpenat t root dir path flags mode = .ok (id,u) → RoFrame t u) ∧
    (∀ mode, vfsMkdirat t root dir path mode = .ok u → RoFrame t u) ∧
    (∀ target, vfsSymlinkat t root dir target path = .ok u → RoFrame t u) ∧
    (∀ removedir, vfsUnlinkat t root dir path removedir = .ok u → RoFrame t u) ∧
    (∀ dir' path', vfsRenameat t root dir path dir' path' = .ok u → RoFrame t u) := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> intros
  all_goals rename_i h
  all_goals simp only [vfsOpenat,vfsMkdirat,vfsSymlinkat,vfsUnlinkat,vfsRenameat,
    Bind.bind,Except.bind,Pure.pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h
  all_goals
    repeat' first
      | exact commit_frame h
      | exact create_frame h
      | (solve | cases h; exact fun _ _ => rfl)
      | (solve | cases h; apply commit_frame; assumption)
      | (solve | cases h; apply create_frame; assumption)
      | contradiction
      | split at h

end LojitaCtx.Posix
