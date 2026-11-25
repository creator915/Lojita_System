import LojitaCtx.Posix.Vfs.Edit

namespace LojitaCtx.Posix

/-- Removing a regular file changes the final dentry, never a navigable
    component. The prefix of any path is consequently resolved identically,
    including absolute or relative symlinks and parent directory traversal. -/
theorem removed_leaf_navigation (t u : InodeTable) (parent id up : Nat) (key : Seg)
    (es : Entries) (p n : Inode) (bytes : ByteArray) (ne : id ≠ parent)
    (oldParent : t.nodes[parent]? = some p) (oldFile : t.nodes[id]? = some n)
    (pd : p.payload = .dir up es) (reg : n.payload = .reg bytes)
    (hit : t.entryAt parent key = some id)
    (update : u.nodes = (t.nodes.insert parent {p with payload := .dir up (es.erase key)}).insert id
      {n with payload := .reg bytes, nlink := n.nlink - 1}) :
    u.nav = t.nav ∧ u.entryAt parent key = none := by
  have unaffected (i : Nat) (f : id ≠ i) (d : parent ≠ i) : u.nodes[i]? = t.nodes[i]? := by
    simp only [update, Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq, f, d, ite_false]
  have pf : u.nodes[parent]? = some {p with payload := .dir up (es.erase key)} := by
    simp only [update, Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq, ne, ite_false, ite_true]
  have ff : u.nodes[id]? = some {n with payload := .reg bytes, nlink := n.nlink - 1} := by
    simp [update]
  have pu (i : Nat) : u.parentOf i = t.parentOf i := by
    by_cases f : id = i
    · subst i; simp [InodeTable.parentOf, oldFile, ff, reg]
    by_cases d : parent = i
    · subst i; simp [InodeTable.parentOf, oldParent, pf, pd]
    simp only [InodeTable.parentOf, unaffected i f d]
  have lu (i : Nat) : u.linkAt i = t.linkAt i := by
    by_cases f : id = i
    · subst i; simp [InodeTable.linkAt, oldFile, ff, reg]
    by_cases d : parent = i
    · subst i; simp [InodeTable.linkAt, oldParent, pf, pd]
    simp only [InodeTable.linkAt, unaffected i f d]
  have eu (i : Nat) (s : Seg) :
      u.entryAt i s = if i = parent ∧ s = key then none else t.entryAt i s := by
    by_cases f : id = i
    · subst i; simp [InodeTable.entryAt, oldFile, ff, reg, ne]
    by_cases d : parent = i
    · subst i
      by_cases k : key = s
      · subst s; simp [InodeTable.entryAt, pf]
      · simp [InodeTable.entryAt, oldParent, pf, pd, Std.TreeMap.getElem?_erase,
          k, Ne.symm k]
    simp only [InodeTable.entryAt, unaffected i f d, Ne.symm d, false_and, ite_false]
  refine ⟨?_, by simp [eu]⟩
  have step (i : Nat) (s : Seg) : u.nav.step i s = t.nav.step i s := by
    simp only [InodeTable.nav, eu, pu, lu]
    by_cases h : i = parent ∧ s = key
    · obtain ⟨rfl,rfl⟩ := h
      simp [hit, InodeTable.parentOf, InodeTable.linkAt, oldFile, reg]
    · simp [h]
  have ext (g h : Nav) (a : g.parent = h.parent) (b : g.step = h.step)
      (c : g.link = h.link) : g = h := by cases g; cases h; congr
  exact ext _ _ (funext pu) (funext (fun i => funext (step i))) (funext lu)

end LojitaCtx.Posix
