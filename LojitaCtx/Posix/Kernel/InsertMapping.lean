import LojitaCtx.Posix.Kernel.TableWrites

namespace LojitaCtx.Posix
open Std.DTreeMap.Internal

private theorem map_balL {A B : Type} (f : Nat → A → B)
    (k : Nat) (v : A) (l r : Impl Nat (fun _ => A)) (bl br h) :
    (Impl.balanceL k v l r bl br h).map (γ := fun _ => B) f =
    Impl.balanceL! k (f k v) (l.map f) (r.map f) := by
  fun_cases Impl.balanceL k v l r bl br h <;>
    simp_all [Impl.balanceL!, Impl.map] <;> intro impossible <;> omega

private theorem map_balR {A B : Type} (f : Nat → A → B)
    (k : Nat) (v : A) (l r : Impl Nat (fun _ => A)) (bl br h) :
    (Impl.balanceR k v l r bl br h).map (γ := fun _ => B) f =
    Impl.balanceR! k (f k v) (l.map f) (r.map f) := by
  fun_cases Impl.balanceR k v l r bl br h <;>
    simp_all [Impl.balanceR!, Impl.map] <;> intro impossible <;> omega

private theorem map_insert {A B : Type} (f : Nat → A → B) (k : Nat) (v : A)
    (t : Impl Nat (fun _ => A)) (bal : t.Balanced) :
    (Impl.insert k v t bal).impl.map (γ := fun _ => B) f = Impl.insert! k (f k v) (t.map f) := by
  induction t with
  | leaf => rfl
  | inner sz key val l r il ir =>
    cases cmp : compare k key <;>
      simp [Impl.insert,Impl.insert!,Impl.map,cmp,map_balL,map_balR,il,ir]

private def shape {A : Type} (t : Impl Nat (fun _ => A)) : Impl Nat (fun _ => Unit) :=
  t.map fun _ _ => ()

private theorem shape_modify {A : Type} (k : Nat) (b : A) (t : Impl Nat (fun _ => A)) :
    shape (Impl.Const.modify k (fun _ => b) t) = shape t := by
  induction t with
  | leaf => rfl
  | inner sz key value l r il ir =>
    cases cmp : compare k key with
    | eq => have eq : k = key := by simpa using cmp
            simp [Impl.Const.modify,shape,Impl.map,eq]
    | lt => simp [Impl.Const.modify,cmp,shape,Impl.map] at il ⊢; exact il
    | gt => simp [Impl.Const.modify,cmp,shape,Impl.map] at ir ⊢; exact ir

private theorem length_shape {A : Type} (t : Impl Nat (fun _ => A)) :
    (shape t).toListModel.length = t.toListModel.length := by
  induction t with
  | leaf => rfl
  | inner sz key value l r il ir =>
    simp [shape,Impl.map] at il ir ⊢; omega

private theorem eq_of_shape_entries {A : Type} (t u : Impl Nat (fun _ => A))
    (same : shape t = shape u) (entries : t.toListModel = u.toListModel) : t = u := by
  induction t generalizing u with
  | leaf => cases u <;> simp_all [shape,Impl.map]
  | inner sz key v l r il ir =>
    cases u with
    | leaf => simp [shape,Impl.map] at same
    | inner sz' key' v' l' r' =>
      change Impl.inner sz key () (shape l) (shape r) = Impl.inner sz' key' () (shape l') (shape r') at same
      simp only [Impl.inner.injEq,heq_eq_eq,true_and] at same
      obtain ⟨hs,hk,hl,hr⟩ := same
      have lengths : l.toListModel.length = l'.toListModel.length :=
        (length_shape l).symm.trans ((congrArg (fun x => x.toListModel.length) hl).trans (length_shape l'))
      obtain ⟨equalLeft,tail⟩ := List.append_inj entries lengths
      obtain ⟨head,equalRight⟩ := List.cons.inj tail
      cases hs
      cases hk
      have val : v = v' := congrArg (fun x => x.2) head
      rw [il _ hl equalLeft,ir _ hr equalRight,val]

/-- Same-key overwrite, including the first lazy insertion of a pipe-page
    layout. Erasing values commutes with the actual tree rotations, so the
    equality also holds for the internal balanced-tree representation. -/
theorem table_insert_overwrite {A : Type} (t : Table A) (k : Nat) (a b : A) :
    (t.insert k a).insert k b = t.insert k b := by
  let x := (t.insert k a).insert k b
  let y := t.insert k b
  have maps : x.Equiv y := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro i
    by_cases same : k = i <;> simp [x,y,Std.TreeMap.getElem?_insert,same]
  have entries : x.inner.inner.toListModel = y.inner.inner.toListModel := by
    rw [← Impl.toList_eq_toListModel,← Impl.toList_eq_toListModel]
    exact maps.1.toList_eq
  have sh : shape x.inner.inner = shape y.inner.inner := by
    dsimp only [x,y]
    rw [table_insert_present _ k a b Std.TreeMap.getElem?_insert_self]
    change shape (Impl.Const.modify k _ _) = _
    rw [shape_modify]
    unfold shape
    rw [show ((t.insert k a).inner.inner.map (γ := fun _ => Unit) (fun _ _ => ())) = _ from
       map_insert (fun _ (_ : A) => ()) k a t.inner.inner t.inner.wf.balanced]
    exact (map_insert (fun _ (_ : A) => ()) k b t.inner.inner t.inner.wf.balanced).symm
  exact congrArg Std.TreeMap.mk (Std.DTreeMap.mk.injEq .. |>.mpr (eq_of_shape_entries _ _ sh entries))

end LojitaCtx.Posix
