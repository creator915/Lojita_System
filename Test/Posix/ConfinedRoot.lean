import LojitaCtx.Posix.Vfs.Namei

namespace Test.Posix.ConfinedRoot
open LojitaCtx.Posix

private def jail : InodeTable :=
  let children := ({} : Entries).insert "jail".toUTF8.data.toList 2
  {nodes := ({} : Std.TreeMap InodeId Inode)
    |>.insert 1 {payload := .dir 1 children}
    |>.insert 2 {payload := .dir 1 {}}, nextId := 3}

-- The physical parent of the process root lies outside the allowed set.
example : jail.parentOf 2 = some 1 := by decide

private theorem confined : DirClosed jail 2 (· = 2) := by
  constructor
  · intro i j other inside
    exact False.elim (other inside)
  · intro i s j inside hit
    subst i
    change ({} : Entries)[s]? = some j at hit
    simp at hit

theorem confinedLookup (p : Bytes) (id : InodeId)
    (h : resolveAt jail 2 2 40 p = .ok id) : id = 2 :=
  resolve_root_confined jail 2 (· = 2) confined 2 40 p true id rfl rfl h

example : (resolveAt jail 2 2 40 "/../..".toUTF8.data.toList).toOption = some 2 := by native_decide

end Test.Posix.ConfinedRoot
