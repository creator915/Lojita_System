import LojitaCtx.Posix.Vfs.Plan

namespace LojitaCtx.Posix

structure DirClosed (t : InodeTable) (S : Nat → Prop) : Prop where
  up : ∀ i j, S i → t.parentOf i = some j → S j
  entry : ∀ i s j, S i → t.entryAt i s = some j → S j

theorem DirClosed.navigation {t : InodeTable} {S : Nat → Prop} (c : DirClosed t S) :
    NavClosed t.nav S := by
  refine ⟨c.up, ?_⟩
  intro i s j hi h
  change (t.entryAt i s >>= _) = some j at h
  obtain ⟨k,hk,step⟩ := Option.bind_eq_some_iff.mp h
  split at step <;> simp_all
  exact c.entry _ _ _ hi hk

structure NameSlot (id : Type) where
  parent : id
  name : Seg
  target : Option id
  slash : Bool
  deriving Inhabited

def lastEntry (t : InodeTable) (root parent : Nat) (s : Seg) : Option Nat :=
  if s == [46] then some parent
  else if s == [46,46] then if parent == root then some root else t.parentOf parent
  else t.entryAt parent s

private theorem last_closed (t : InodeTable) (S : Nat → Prop) (c : DirClosed t S)
    (root parent id : Nat) (s : Seg) (hr : S root) (hp : S parent)
    (h : lastEntry t root parent s = some id) : S id := by
  unfold lastEntry at h
  split at h
  · cases h; exact hp
  · split at h
    · split at h
      · cases h; exact hr
      · exact c.up _ _ hp h
    · exact c.entry _ _ _ hp h

inductive NameResult (fuel : Nat) where
  | done (a : NameSlot Nat)
  | again (parent : Nat) (path : Bytes) (trailing : Bool) (fuel' : Nat) (smaller : fuel' < fuel)

def inspect (t : InodeTable) (root : Nat) {fuel : Nat} (a : PathPrefix fuel)
    (follow checkSlash trailing : Bool) : Except Errno (NameResult fuel) :=
  let hit := lastEntry t root a.parent a.name
  if a.blocked then
    .error (if hit.any (fun id => (t.nodes[id]?).isSome) then .ENOTDIR else .ENOENT)
  else match hit with
  | none => .ok (.done ⟨a.parent,a.name,none,trailing⟩)
  | some id =>
    if (t.nodes[id]?).isNone then .error .ENOENT
    else match (if follow then t.linkAt id else none) with
    | some target =>
      match hk : a.remaining with
      | 0 => .error .ELOOP
      | k+1 =>
        have h := a.bounded
        .ok (.again a.parent target (trailing || target.getLast? == some 47) k (by omega))
    | none =>
      if trailing && checkSlash && (t.parentOf id).isNone then .error .ENOTDIR
      else .ok (.done ⟨a.parent,a.name,some id,trailing⟩)

def resolveLoop (t : InodeTable) (root start fuel : Nat) (p : Bytes)
    (follow checkSlash trailing : Bool) : Except Errno (NameSlot Nat) := do
  let a ← t.nav.prepare root start fuel p
  match ← inspect t root a follow checkSlash trailing with
  | .done slot => return slot
  | .again dir target slash f _ => resolveLoop t root dir f target follow checkSlash slash
termination_by fuel

def resolveParentAt (t : InodeTable) (root start fuel : Nat) (p : Bytes)
    (followLast : Bool := false) (checkSlash : Bool := true) : Except Errno (NameSlot InodeId) :=
  resolveLoop t root start fuel p followLast checkSlash (p.getLast? == some 47)

def resolveAt (t : InodeTable) (root start fuel : Nat) (p : Bytes)
    (followLast : Bool := true) : Except Errno InodeId := do
  let a ← resolveParentAt t root start fuel p followLast
  a.target.elim (.error .ENOENT) .ok

private theorem inspect_closed (t : InodeTable) (S : Nat → Prop) (closed : DirClosed t S)
    (root fuel : Nat) (a : PathPrefix fuel) (follow checkSlash trailing : Bool)
    (hr : S root) (hp : S a.parent) (r : NameResult fuel)
    (h : inspect t root a follow checkSlash trailing = .ok r) :
    match r with
    | .done slot => ∀ i, slot.target = some i → S i
    | .again dir .. => S dir := by
  cases hb : a.blocked <;> simp [inspect, hb] at h
  cases he : lastEntry t root a.parent a.name with
  | none => simp [he] at h; subst r; simp
  | some id =>
    have hi := last_closed t S closed root a.parent id a.name hr hp he
    simp [he] at h
    split at h <;> try contradiction
    split at h <;> split at h <;> try contradiction
    · cases h; exact hp
    · cases h; simpa using hi

private theorem resolveLoop_closed (t : InodeTable) (S : Nat → Prop) (c : DirClosed t S)
    (root start fuel : Nat) (p : Bytes) (follow checkSlash slash : Bool)
    (hr : S root) (hs : S start) (out : NameSlot Nat)
    (h : resolveLoop t root start fuel p follow checkSlash slash = .ok out) :
    ∀ i, out.target = some i → S i := by
  rw [resolveLoop] at h
  cases ha : t.nav.prepare root start fuel p with
  | error e => simp [ha, Bind.bind, Except.bind] at h
  | ok a =>
    have hp := Nav.prepare_reach _ _ _ _ _ _ ha S c.navigation hr hs
    cases hb : inspect t root a follow checkSlash slash with
    | error e => simp [ha, hb, Bind.bind, Except.bind] at h
    | ok result =>
      have hc := inspect_closed t S c root fuel a follow checkSlash slash hr hp result hb
      cases result with
      | done slot =>
        simp [ha, hb, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        exact h ▸ hc
      | again dir path trailing f decr =>
        apply resolveLoop_closed t S c root dir f path follow checkSlash trailing hr hc out
        simpa [ha, hb, Bind.bind, Except.bind] using h
termination_by fuel

/-- A successful no-follow lookup identifies exactly one resolved prefix and
    its final directory entry. No table data is hidden in the prefix value. -/
theorem nofollow_plan (t : InodeTable) (r start fuel : Nat) (path : Bytes)
    (slot : NameSlot Nat) (h : resolveParentAt t r start fuel path false = .ok slot) :
    ∃ a, t.nav.prepare r start fuel path = .ok a ∧ a.blocked = false ∧
      slot.parent = a.parent ∧ slot.name = a.name ∧ slot.target = lastEntry t r a.parent a.name := by
  unfold resolveParentAt at h
  rw [resolveLoop] at h
  cases ha : t.nav.prepare r start fuel path with
  | error e => simp [ha, Bind.bind, Except.bind] at h
  | ok a =>
    refine ⟨a, rfl, ?_⟩
    cases hb : a.blocked <;>
      simp [ha, inspect, hb, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases he : lastEntry t r a.parent a.name <;> simp [he] at h
    · cases h; simp
    · rename_i id
      by_cases live : id ∈ t.nodes <;> simp [live] at h
      by_cases bad : path.getLast? = some 47 ∧ t.parentOf id = none <;> simp [bad] at h
      cases h; simp

theorem missing_leaf (t : InodeTable) (r start fuel : Nat) (path : Bytes) (a : PathPrefix fuel)
    (prepared : t.nav.prepare r start fuel path = .ok a) (clear : a.blocked = false)
    (absent : lastEntry t r a.parent a.name = none) (follow : Bool) :
    resolveAt t r start fuel path follow = .error .ENOENT := by
  unfold resolveAt resolveParentAt
  rw [resolveLoop]
  simp [prepared, inspect, clear, absent, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem resolve_root_confined (t : InodeTable) (S : InodeId → Prop) (closed : DirClosed t S)
    (root start fuel : Nat) (p : Bytes) (follow : Bool) (id : InodeId)
    (hr : S root) (hs : S start) (resolved : resolveAt t root start fuel p follow = .ok id) :
    S id := by
  cases h : resolveParentAt t root start fuel p follow with
  | error e => simp [resolveAt, h, Bind.bind, Except.bind] at resolved
  | ok a =>
    cases ht : a.target with
    | none => simp [resolveAt, h, ht, Bind.bind, Except.bind] at resolved
    | some i =>
      simp [resolveAt, h, ht, Bind.bind, Except.bind] at resolved
      exact resolved ▸ resolveLoop_closed t S closed root start fuel p follow true _ hr hs a h i ht

end LojitaCtx.Posix
