import LojitaCtx.Posix.Kernel.State
import Std.Data.DTreeMap.Internal.Model

namespace LojitaCtx.Posix
open Std.DTreeMap.Internal

/-- Updating a present entry preserves all search-tree branches. This matters
    for structural kernel-state equality, beyond the standard TreeMap.Equiv. -/
private theorem insert_present {A : Type} (t : Impl Nat (fun _ => A)) (balanced : t.Balanced)
    (k : Nat) (old v : A) (found : Impl.Const.get? t k = some old) :
    (Impl.insert k v t balanced).impl = Impl.Const.modify k (fun _ => v) t := by
  induction t with
  | leaf => simp [Impl.Const.get?] at found
  | inner sz key value left right il ir =>
    cases cmp : compare k key with
    | eq => simp [Impl.insert,Impl.Const.modify,cmp]
    | lt =>
      simp only [Impl.Const.get?,cmp] at found
      have sub := il balanced.left found
      simp only [Impl.insert,cmp,Impl.Const.modify]
      rw [Impl.balanceL_eq_balance, ← sub]
      apply Impl.balance_eq_inner
      rw [Impl.balanced_inner_iff]
      have h := Impl.balanced_inner_iff.mp balanced
      exact ⟨by rw [sub]; exact Impl.Const.balanced_modify balanced.left, h.2.1,
        by simpa only [sub,Impl.Const.aux_size_modify] using h.2.2.1,
        by simpa only [sub,Impl.Const.aux_size_modify] using h.2.2.2⟩
    | gt =>
      simp only [Impl.Const.get?,cmp] at found
      have sub := ir balanced.right found
      simp only [Impl.insert,cmp,Impl.Const.modify]
      rw [Impl.balanceR_eq_balance, ← sub]
      apply Impl.balance_eq_inner
      rw [Impl.balanced_inner_iff]
      have h := Impl.balanced_inner_iff.mp balanced
      exact ⟨h.1,by rw [sub]; exact Impl.Const.balanced_modify balanced.right,
        by simpa only [sub,Impl.Const.aux_size_modify] using h.2.2.1,
        by simpa only [sub,Impl.Const.aux_size_modify] using h.2.2.2⟩

private theorem modify_twice {A : Type} (t : Impl Nat (fun _ => A)) (k : Nat) (a b : A) :
    Impl.Const.modify k (fun _ => b) (Impl.Const.modify k (fun _ => a) t) =
    Impl.Const.modify k (fun _ => b) t := by
  induction t with
  | leaf => rfl
  | inner sz key value l r il ir =>
    cases cmp : compare k key <;> simp [Impl.Const.modify,cmp,il,ir]

private theorem modify_original {A : Type} (t : Impl Nat (fun _ => A)) (k : Nat) (a : A)
    (seen : Impl.Const.get? t k = some a) : Impl.Const.modify k (fun _ => a) t = t := by
  induction t with
  | leaf => simp [Impl.Const.get?] at seen
  | inner sz key value l r il ir =>
    cases cmp : compare k key with
    | lt => simp only [Impl.Const.get?,cmp] at seen; simp [Impl.Const.modify,cmp,il seen]
    | gt => simp only [Impl.Const.get?,cmp] at seen; simp [Impl.Const.modify,cmp,ir seen]
    | eq =>
      have eq : k = key := by simpa using cmp
      simp [Impl.Const.get?,cmp] at seen
      simp [Impl.Const.modify,eq,seen]

theorem table_insert_present {A : Type} (t : Table A) (k : Nat) (old v : A)
    (found : t[k]? = some old) : t.insert k v = t.modify k (fun _ => v) := by
  cases t with | mk t =>
    cases t with | mk tree wf =>
      exact congrArg (fun x : Std.DTreeMap Nat (fun _ => A) compare => Std.TreeMap.mk x)
        (Std.DTreeMap.mk.injEq .. |>.mpr (insert_present tree wf.balanced k old v found))

theorem table_overwrite {A : Type} (t : Table A) (k : Nat) (old a b : A)
    (found : t[k]? = some old) : (t.insert k a).insert k b = t.insert k b := by
  rw [table_insert_present _ _ a b (Std.TreeMap.getElem?_insert_self),
    table_insert_present _ _ old a found,table_insert_present _ _ old b found]
  cases t with | mk t =>
    cases t with | mk tree wf =>
      exact congrArg (fun x : Std.DTreeMap Nat (fun _ => A) compare => Std.TreeMap.mk x)
        (Std.DTreeMap.mk.injEq .. |>.mpr (modify_twice tree k a b))

theorem table_restore {A : Type} (t : Table A) (k : Nat) (a : A) (found : t[k]? = some a) :
    t.insert k a = t := by
  rw [table_insert_present _ _ a a found]
  cases t with | mk t =>
    cases t with | mk tree wf =>
      exact congrArg (fun x : Std.DTreeMap Nat (fun _ => A) compare => Std.TreeMap.mk x)
        (Std.DTreeMap.mk.injEq .. |>.mpr (modify_original tree k a found))

theorem PipePages.consume_add (ps : PipePages) (i j : Nat) :
    PipePages.consume (PipePages.consume ps i) j = PipePages.consume ps (i+j) := by
  induction ps generalizing i j with
  | nil => rfl
  | cons p ps ih =>
    by_cases hi : i < p.readable
    · by_cases hj : j < p.readable - i
      · have total : i+j < p.readable := by omega
        simp [PipePages.consume,hi,hj,total,Nat.sub_sub]
      · have total : ¬i+j < p.readable := by omega
        have sub : j-(p.readable-i) = i+j-p.readable := by omega
        simp [PipePages.consume,hi,hj,total,sub]
    · have total : ¬i+j < p.readable := by omega
      have sub : i-p.readable+j = i+j-p.readable := by omega
      simp [PipePages.consume,hi,total,ih,sub]

end LojitaCtx.Posix
