import LojitaCtx.Posix.Vfs.Namei
import Std.Data.TreeMap.Lemmas

namespace LojitaCtx.Posix

/-- A directory operation prepares a finite edit list; failures never publish
    a partially changed graph. A permission-only access is represented by claim. -/
inductive InodeEdit where
  | put (id : InodeId) (node : Inode)
  | erase (id : InodeId)
  | claim (id : InodeId)

def InodeEdit.id : InodeEdit → InodeId
  | .put i _ | .erase i | .claim i => i

def InodeEdit.apply (t : InodeTable) : InodeEdit → InodeTable
  | .put id n => { t.put id n with nextId := max t.nextId (id+1) }
  | .erase id => { t with nodes := t.nodes.erase id }
  | .claim _ => t

def InodeTable.preview (t : InodeTable) (edits : List InodeEdit) : InodeTable :=
  edits.foldl InodeEdit.apply t

def InodeTable.protectedAt (t : InodeTable) (id : InodeId) : Bool :=
  (t.nodes[id]?).any (·.roLayer)

def InodeTable.commit (t : InodeTable) (edits : List InodeEdit) : Except Errno InodeTable :=
  if edits.any (fun e => t.protectedAt e.id) then .error .EROFS else .ok (t.preview edits)

theorem preview_unmentioned (es : List InodeEdit) (t : InodeTable) (i : InodeId)
    (h : ∀ e ∈ es, e.id ≠ i) : (t.preview es).nodes[i]? = t.nodes[i]? := by
  induction es generalizing t with
  | nil => rfl
  | cons e rest ih =>
    change ((InodeEdit.apply t e).preview rest).nodes[i]? = _
    rw [ih _ (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    have ne := h e (List.mem_cons_self ..)
    cases e <;> simp_all [InodeEdit.apply, InodeEdit.id, InodeTable.put,
      Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_erase]

/-- Both the rejection obligation and the frame of a successful transaction.
    The read-only inode, including its bytes and directory map, stays identical. -/
theorem roLayer_vfs_immutable (t : InodeTable) (es : List InodeEdit) (i : InodeId)
    (ro : t.protectedAt i = true) :
    ((∃ e ∈ es, e.id = i) → t.commit es = .error .EROFS) ∧
    (∀ next, t.commit es = .ok next → next.nodes[i]? = t.nodes[i]?) := by
  constructor
  · rintro ⟨e, he, id⟩
    have h : es.any (fun x => t.protectedAt x.id) = true :=
      List.any_eq_true.mpr ⟨e, he, id ▸ ro⟩
    simp [InodeTable.commit, h]
  · intro next h
    unfold InodeTable.commit at h
    split at h
    · contradiction
    · rename_i ok
      cases h
      apply preview_unmentioned
      intro e he id
      exact ok (List.any_eq_true.mpr ⟨e, he, id ▸ ro⟩)

end LojitaCtx.Posix
