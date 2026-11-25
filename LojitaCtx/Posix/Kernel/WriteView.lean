import LojitaCtx.Posix.Kernel.Offsets
import Init.Data.ByteArray.Lemmas

namespace LojitaCtx.Posix

/-- File contents after a successful write, including a possible zero-filled hole. -/
def replaceBytes (before : ByteArray) (off : Nat) (bs : Bytes) : ByteArray :=
  before.extract 0 off ++ ⟨Array.replicate (off-before.size) 0⟩ ++ bs.toByteArray ++
    before.extract (off+bs.length) before.size

theorem read_replaced (before : ByteArray) (off : Nat) (bs : Bytes) :
    ((replaceBytes before off bs).extract off (off+bs.length)).data.toList = bs := by
  let pre := (before.data.toList.take off) ++ List.replicate (off-before.size) (0 : UInt8)
  have preLen : pre.length = off := by
    have sz : before.data.toList.length = before.size := rfl
    simp only [pre,List.length_append,List.length_take,List.length_replicate,sz]
    omega
  have content : (replaceBytes before off bs).data.toList =
      pre ++ (bs ++ (before.extract (off+bs.length) before.size).data.toList) := by
    simp [replaceBytes,pre,ByteArray.data_append,ByteArray.data_extract,List.extract_eq_take_drop,List.append_assoc]
  rw [ByteArray.data_extract,Array.toList_extract,List.extract_eq_take_drop,content]
  simp [← preLen]

theorem written_inode {t next : InodeTable} {ino off : Nat} {old : Inode} {before : ByteArray}
    {bs : Bytes} (reg : t.node ino = .ok old) (kind : old.payload = .reg before)
    (written : inodeWrite t ino off bs = .ok next) (nonempty : bs ≠ []) :
    ∃ node, next.nodes[ino]? = some node ∧ node.payload = .reg (replaceBytes before off bs) ∧ node.nlink = old.nlink := by
  by_cases ro : old.roLayer
  · simp [inodeWrite,reg,ro,Bind.bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at written
  · have hbs : bs.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
    simp [inodeWrite,reg,kind,ro,hbs,Bind.bind,Except.bind,Pure.pure,Except.pure] at written
    subst next
    exact ⟨{old with payload := .reg (replaceBytes before off bs)},by simp [InodeTable.put,replaceBytes,ro],rfl,rfl⟩

/-- Normalizing the descriptor counts does not change the payload of a linked inode. -/
theorem account_linked_payload {m : Machine} {node : Inode} {ino : Nat}
    (hn : m.kernel.vfs.nodes[ino]? = some node) (linked : node.nlink ≠ 0) :
    ∃ after, m.account.kernel.vfs.node ino = .ok after ∧ after.payload = node.payload := by
  let count := targetCount (liveOfds m.proc m.kernel.ofds) (.inode ino)
  refine ⟨{node with openRefs := count}, ?_,rfl⟩
  simp [Machine.account,liveInodes,InodeTable.node,Std.TreeMap.getElem?_filterMap',hn,linked,count]

end LojitaCtx.Posix
