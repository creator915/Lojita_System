namespace LojitaCtx.Countermodel

structure StringAlg where
  Str : Type
  toList : Str → List Char
  fromList : List Char → Str
  append : Str → Str → Str
  strEq : Str → Str → Bool
  toListInjective : ∀ {a b}, toList a = toList b → a = b
  fromListInjective : ∀ {xs ys}, fromList xs = fromList ys → xs = ys

structure CharAlg where
  Chr : Type
  charToNat : Chr → Nat
  natToChar : Nat → Chr
  charEq : Chr → Chr → Bool
  charToNatInjective : ∀ {a b}, charToNat a = charToNat b → a = b

inductive Alg where
  | string (ops : StringAlg)
  | char (ops : CharAlg)

abbrev within (k : Nat) (xs : List Char) := xs.length ≤ k

structure SoundStringModel where
  atStage : Nat → StringAlg
  toFromWithin : ∀ k xs, within k xs → (atStage k).toList ((atStage k).fromList xs) = xs
  appendWithin :
    ∀ k xs ys,
      within k xs →
        within k ys →
          within k (xs ++ ys) →
            (atStage k).append ((atStage k).fromList xs) ((atStage k).fromList ys) =
              (atStage k).fromList (xs ++ ys)
  strEqWithin :
    ∀ k xs ys,
      within k xs →
        within k ys →
          (atStage k).strEq ((atStage k).fromList xs) ((atStage k).fromList ys) = (xs == ys)

structure SoundCharModel where
  atCharStage : Nat → CharAlg
  embedChar : (k : Nat) → Char → (atCharStage k).Chr
  charToNatWithin : ∀ k c, c.toNat ≤ k → (atCharStage k).charToNat (embedChar k c) = c.toNat
  natToCharLaw : ∀ k n, (atCharStage k).natToChar n = embedChar k (Char.ofNat n)
  charEqLaw : ∀ k c d, (atCharStage k).charEq (embedChar k c) (embedChar k d) = (c == d)

inductive CountermodelBundle where
  | stringCountermodel (claim : StringAlg → Prop) (model : SoundStringModel)
      (refute : ∀ k, claim (model.atStage k) → False)
  | charCountermodel (claim : CharAlg → Prop) (model : SoundCharModel)
      (refute : ∀ k, claim (model.atCharStage k) → False)

def swapChar (a b c : Char) := if c = a then b else if c = b then a else c

private theorem swapTwice (a b c : Char) : swapChar a b (swapChar a b c) = c := by
  by_cases ca : c = a <;> by_cases cb : c = b <;> simp_all [swapChar]

def fromListSwapped (a b : Char) (k : Nat) : List Char → List Char
  | [] => []
  | c :: cs => (if cs.length < k then c else swapChar a b c) :: cs

private theorem swappedWithin (a b : Char) (k : Nat) (xs : List Char) (h : within k xs) :
    fromListSwapped a b k xs = xs := by
  cases xs with
  | nil => rfl
  | cons c cs => simp [fromListSwapped, show cs.length < k from h]

private theorem swappedTwice (a b : Char) (k : Nat) (xs : List Char) :
    fromListSwapped a b k (fromListSwapped a b k xs) = xs := by
  cases xs with
  | nil => rfl
  | cons c cs => by_cases h : cs.length < k <;> simp [fromListSwapped, h, swapTwice]

def swapStringAlg (a b : Char) (k : Nat) : StringAlg where
  Str := List Char
  toList := id
  fromList := fromListSwapped a b k
  append := List.append
  strEq := (· == ·)
  toListInjective := id
  fromListInjective h :=
    (swappedTwice a b k _).symm.trans
      ((congrArg (fromListSwapped a b k) h).trans (swappedTwice a b k _))

def swapStringModel (a b : Char) : SoundStringModel where
  atStage := swapStringAlg a b
  toFromWithin := swappedWithin a b
  appendWithin k xs ys hx hy hxy := by
    change fromListSwapped a b k xs ++ fromListSwapped a b k ys = fromListSwapped a b k (xs ++ ys)
    rw [swappedWithin _ _ _ _ hx, swappedWithin _ _ _ _ hy, swappedWithin _ _ _ _ hxy]
  strEqWithin k xs ys hx hy := by simp [swapStringAlg, swappedWithin, hx, hy]

def breakStrEqModel : SoundStringModel where
  atStage k := {
    Str := List Char, toList := id, fromList := id, append := List.append
    strEq := fun xs ys => decide (within k xs) && decide (within k ys) && xs == ys
    toListInjective := id, fromListInjective := id }
  toFromWithin _ _ _ := rfl
  appendWithin _ _ _ _ _ _ := rfl
  strEqWithin _ _ _ hx hy := by simp [hx, hy]

def phantomCharAlg (k : Nat) : CharAlg where
  Chr := Option Char
  charToNat
    | none => k + 1
    | some c => if c.toNat ≤ k then c.toNat else c.toNat + 1
  natToChar n := some (Char.ofNat n)
  charEq
    | some c, some d => c == d
    | _, _ => false
  charToNatInjective := by
    intro a b h
    cases a <;> cases b <;> simp only [Option.some.injEq] at *
    · split at h <;> omega
    · split at h <;> omega
    · apply Char.toNat_inj.mp
      split at h <;> split at h <;> omega

def phantomCharModel : SoundCharModel where
  atCharStage := phantomCharAlg
  embedChar _ := some
  charToNatWithin _ _ h := ite_eq_left h
  natToCharLaw _ _ := rfl
  charEqLaw _ _ _ := rfl

inductive ClosedString where
  | literal (xs : List Char)
  | append (left right : ClosedString)

def ClosedString.chars : ClosedString → List Char
  | .literal xs => xs
  | .append x y => x.chars ++ y.chars
termination_by structural term => term

def ClosedString.eval (alg : StringAlg) : ClosedString → alg.Str
  | .literal xs => alg.fromList xs
  | .append x y => alg.append (x.eval alg) (y.eval alg)
termination_by structural term => term

theorem evalClosed (m : SoundStringModel) (k : Nat) (t : ClosedString) (h : within k t.chars) :
    t.eval (m.atStage k) = (m.atStage k).fromList t.chars := by
  induction t with
  | literal => rfl
  | append x y ihx ihy =>
    change (x.chars ++ y.chars).length ≤ k at h
    have bound := List.length_append (as := x.chars) (bs := y.chars)
    have hx : within k x.chars := by unfold within; omega
    have hy : within k y.chars := by unfold within; omega
    exact (congr (congrArg _ (ihx hx)) (ihy hy)).trans (m.appendWithin k _ _ hx hy h)

/-- Every closed expression is conserved at every stage covering its concrete result. -/
theorem conservesClosed (m : SoundStringModel) (k : Nat) (t : ClosedString) (h : within k t.chars) :
    (m.atStage k).toList (t.eval (m.atStage k)) = t.chars := by
  rw [evalClosed m k t h, m.toFromWithin k _ h]

end LojitaCtx.Countermodel
