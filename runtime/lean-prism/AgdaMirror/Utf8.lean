set_option autoImplicit false

namespace AgdaMirror.Utf8

-- Lean's public UTF-8 inverse theorems and several Nat division lemmas use
-- extensional axioms.  These division equations follow the fuel recursion
-- of Nat.div and Nat.modCore and need only intensional equality.
private theorem smallMod {x k : Nat} (h : x < k) : x % k = x := by
  cases x with
  | zero => rfl
  | succ n =>
    change (if k ≤ n+1 then _ else _) = _
    exact ite_eq_right (Nat.not_le_of_gt h)

private theorem smallDiv {x k : Nat} (hk : 0 < k) (h : x < k) : x / k = 0 := by
  change Nat.div x k = _
  unfold Nat.div
  rw [dite_eq_left hk, Nat.div.go, dite_eq_right (Nat.not_le_of_gt h)]

private theorem divFuel (y : Nat) (hy : 0 < y) (f g x : Nat) (hf : x < f) (hg : x < g) :
    Nat.div.go y hy f x hf = Nat.div.go y hy g x hg := by
  match f, g with
  | 0, _ => exact (Nat.not_lt_zero _ hf).elim
  | _, 0 => exact (Nat.not_lt_zero _ hg).elim
  | _ + 1, _ + 1 =>
    simp only [Nat.div.go]
    split
    · exact congrArg Nat.succ (divFuel ..)
    · rfl
termination_by structural f

private theorem modFuel (y : Nat) (hy : 0 < y) (f g x : Nat) (hf : x < f) (hg : x < g) :
    Nat.modCore.go y hy f x hf = Nat.modCore.go y hy g x hg := by
  match f, g with
  | 0, _ => exact (Nat.not_lt_zero _ hf).elim
  | _, 0 => exact (Nat.not_lt_zero _ hg).elim
  | _ + 1, _ + 1 =>
    simp only [Nat.modCore.go]
    split
    · exact modFuel ..
    · rfl
termination_by structural f

private theorem divStep (x k : Nat) (hk : 0 < k) (h : k ≤ x) :
    x / k = (x-k)/k + 1 := by
  change Nat.div x k = Nat.div (x-k) k + 1
  unfold Nat.div
  rw [dite_eq_left hk, dite_eq_left hk, Nat.div.go, dite_eq_left h]
  exact congrArg Nat.succ (divFuel ..)

private theorem modCoreEq (x k : Nat) (hk : 0 < k) : Nat.modCore x k = x % k := by
  cases x with
  | zero =>
    unfold Nat.modCore
    rw [dite_eq_left hk, Nat.modCore.go, dite_eq_right (Nat.not_le_of_gt hk)]
    rfl
  | succ n =>
    change Nat.modCore (n+1) k = if k ≤ n+1 then _ else _
    split
    · rfl
    · rename_i h
      unfold Nat.modCore
      rw [dite_eq_left hk, Nat.modCore.go, dite_eq_right h]

private theorem modStep (x k : Nat) (hk : 0 < k) (h : k ≤ x) :
    x % k = (x-k) % k := by
  rw [←modCoreEq _ _ hk, ←modCoreEq _ _ hk]
  unfold Nat.modCore
  rw [dite_eq_left hk, dite_eq_left hk, Nat.modCore.go, dite_eq_left h]
  exact modFuel ..

private theorem subAdd {k x : Nat} (h : k ≤ x) : x-k+k = x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    cases x with
    | zero => exact (Nat.not_succ_le_zero _ h).elim
    | succ x => rw [Nat.succ_sub_succ]; exact congrArg Nat.succ (ih (Nat.le_of_succ_le_succ h))

private theorem parts (x k : Nat) (hk : 0 < k) : x % k < k ∧ x % k + k*(x/k) = x := by
  induction x, k using Nat.div.inductionOn with
  | base x k h =>
    have hlt := Nat.lt_of_not_ge (fun ge => h ⟨hk, ge⟩)
    rw [smallMod hlt, smallDiv hk hlt]
    exact ⟨hlt, rfl⟩
  | ind x k h ih =>
    rw [divStep x k hk h.2, modStep x k hk h.2, Nat.mul_succ, ←Nat.add_assoc, (ih hk).2, subAdd h.2]
    exact ⟨(ih hk).1, rfl⟩

private theorem addSub (x k : Nat) : x+k-k = x := by
  induction k with
  | zero => rfl
  | succ _ ih => rw [Nat.add_succ, Nat.succ_sub_succ]; exact ih

private theorem mulAssoc (a b c : Nat) : a * b * c = a * (b*c) := by
  induction c with
  | zero => rfl
  | succ c ih => rw [Nat.mul_succ, ih, Nat.mul_succ b, Nat.mul_add]

private theorem divRepr (r q k : Nat) (hr : r < k) : (r+k*q)/k = q := by
  induction q with
  | zero => exact smallDiv (Nat.lt_of_le_of_lt (Nat.zero_le _) hr) hr
  | succ q ih =>
    rw [Nat.mul_succ, ←Nat.add_assoc, divStep _ _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hr) (Nat.le_add_left ..), addSub, ih]

private theorem groupDiv (x k d : Nat) (hk : 0 < k) (hd : 0 < d) :
    x / (k*d) = x / k / d := by
  have a := parts x k hk
  have b := parts (x/k) d hd
  have repr : (x%k + k*(x/k%d)) + k*d*(x/k/d) = x := by
    rw [Nat.add_assoc, mulAssoc, ←Nat.mul_add, b.2, a.2]
  have bound : x%k + k*(x/k%d) < k*d := by
    apply Nat.lt_of_lt_of_le (Nat.add_lt_add_right a.1 _)
    rw [Nat.add_comm, ←Nat.mul_succ]
    exact Nat.mul_le_mul_left _ b.1
  exact (congrArg (· / (k*d)) repr).symm.trans (divRepr _ _ _ bound)

private theorem divBound {x k d : Nat} (hk : 0 < k) (hx : x < k*d) : x/k < d := by
  apply Nat.lt_of_not_ge
  intro h
  have hd := Nat.mul_le_mul_left k h
  have hq := Nat.le_add_left (k*(x/k)) (x%k)
  rw [(parts x k hk).2] at hq
  exact Nat.not_le_of_gt hx (Nat.le_trans hd hq)

private theorem byteNat {x : Nat} (h : x < 256) : (UInt8.ofNat x).toNat = x := by
  change x % 256 = x
  exact smallMod h

private inductive State where
  | lead
  | one (acc : Nat)
  | two (acc : Nat)
  | three (acc : Nat)

-- The state counts continuation bytes and accumulates the leading digits.
private def decodeFrom : List UInt8 → State → List Char
  | [], _ => []
  | b :: bs, state =>
    let v := b.toNat
    match state with
    | .lead =>
      if v < 128 then Char.ofNat v :: decodeFrom bs .lead
      else if v < 224 then decodeFrom bs (.one (v-192))
      else if v < 240 then decodeFrom bs (.two (v-224))
      else decodeFrom bs (.three (v-240))
    | .one acc => Char.ofNat (v-128 + 64*acc) :: decodeFrom bs .lead
    | .two acc => decodeFrom bs (.one (v-128 + 64*acc))
    | .three acc => decodeFrom bs (.two (v-128 + 64*acc))
termination_by structural bs _ => bs

def decode (bs : List UInt8) : List Char := decodeFrom bs .lead

private theorem tagBound {v k t b : Nat} (hv : v < k) (h : k+t ≤ b) : v+t < b :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_right hv t) h

private theorem tagMin {v t b : Nat} (h : b ≤ t) : ¬ v+t < b :=
  Nat.not_lt_of_ge (Nat.le_trans h (Nat.le_add_left ..))

-- One encoder step consumes exactly the bytes emitted for the scalar,
-- leaving the remaining stream in the initial decoder state.
private theorem nextChar (c : Char) (bs : List UInt8) :
    decode (String.utf8EncodeChar c ++ bs) = c :: decode bs := by
  have hn : c.val.toNat < 2097152 := by
    rcases c.valid with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le h (by decide)
    · exact Nat.lt_of_lt_of_le h (by decide)
  apply Eq.trans _ (congrArg (· :: decode bs) (Char.ofNat_toNat c))
  unfold String.utf8EncodeChar Char.toNat
  generalize c.val.toNat = n at hn ⊢
  have low := parts n 64 (by decide)
  have mid := parts (n/64) 64 (by decide)
  have high := parts (n/4096) 64 (by decide)
  have g₂ : n/4096 = n/64/64 := groupDiv n 64 64 (by decide) (by decide)
  have g₃ : n/262144 = n/4096/64 := groupDiv n 4096 64 (by decide) (by decide)
  change decodeFrom ((if n ≤ 127 then _ else if n ≤ 2047 then _ else if n ≤ 65535 then _ else _) ++ bs) .lead = _
  split
  · rename_i h
    simp only [List.cons_append, List.nil_append, decodeFrom, byteNat (Nat.lt_of_lt_of_le (show n < 128 from Nat.succ_le_succ h) (by decide : 128 ≤ 256)), ite_eq_left (show n < 128 from Nat.succ_le_succ h)]
    rfl

  · split
    · rename_i h
      have hb := divBound (k := 64) (d := 32) (by decide) (show n < 2048 from Nat.succ_le_succ h)
      simp only [smallMod hb, List.cons_append, List.nil_append, decodeFrom,
        byteNat (tagBound hb (by decide : 32+192 ≤ 256)), byteNat (tagBound low.1 (by decide : 64+128 ≤ 256)),
        ite_eq_right (tagMin (v := n/64) (by decide : 128 ≤ 192)),
        ite_eq_left (tagBound hb (by decide : 32+192 ≤ 224)), addSub, low.2]
      rfl
    · split
      · rename_i h
        have hb := divBound (k := 4096) (d := 16) (by decide) (show n < 65536 from Nat.succ_le_succ h)
        simp only [smallMod hb, List.cons_append, List.nil_append, decodeFrom,
          byteNat (tagBound hb (by decide : 16+224 ≤ 256)), byteNat (tagBound mid.1 (by decide : 64+128 ≤ 256)),
          byteNat (tagBound low.1 (by decide : 64+128 ≤ 256)),
          ite_eq_right (tagMin (v := n/4096) (by decide : 128 ≤ 224)),
          ite_eq_right (tagMin (v := n/4096) (by decide : 224 ≤ 224)),
          ite_eq_left (tagBound hb (by decide : 16+224 ≤ 240)), addSub]
        rw [g₂, mid.2, low.2]
        rfl
      · have hb := divBound (k := 262144) (d := 8) (by decide) hn
        simp only [smallMod hb, List.cons_append, List.nil_append, decodeFrom,
          byteNat (tagBound hb (by decide : 8+240 ≤ 256)), byteNat (tagBound high.1 (by decide : 64+128 ≤ 256)),
          byteNat (tagBound mid.1 (by decide : 64+128 ≤ 256)), byteNat (tagBound low.1 (by decide : 64+128 ≤ 256)),
          ite_eq_right (tagMin (v := n/262144) (by decide : 128 ≤ 240)),
          ite_eq_right (tagMin (v := n/262144) (by decide : 224 ≤ 240)),
          ite_eq_right (tagMin (v := n/262144) (by decide : 240 ≤ 240)), addSub]
        rw [g₃, high.2, g₂, mid.2, low.2]
        rfl


private theorem pushList (a : Array UInt8) (b : UInt8) :
    (a.push b).toList = a.toList ++ [b] := by
  cases a with
  | mk xs =>
    change xs.concat b = xs ++ [b]
    induction xs with
    | nil => rfl
    | cons x xs ih => exact congrArg (x :: ·) ih

private theorem appendCons (xs : List UInt8) (b : UInt8) (ys : List UInt8) :
    (xs ++ [b]) ++ ys = xs ++ b :: ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (x :: ·) ih

private theorem bytesList (xs : List UInt8) :
    xs.toByteArray.data.toList = xs := by
  suffices ∀ a : ByteArray, (List.toByteArray.loop xs a).data.toList = a.data.toList ++ xs from this .empty
  induction xs with
  | nil =>
    intro a
    change a.data.toList = a.data.toList ++ []
    induction a.data.toList with
    | nil => rfl
    | cons x xs ih => exact congrArg (x :: ·) ih
  | cons b bs ih =>
    intro a
    exact (ih (a.push b)).trans ((congrArg (· ++ bs) (pushList a.data b)).trans (appendCons _ _ _))

private theorem bytesAppendAssoc (xs ys zs : List UInt8) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (x :: ·) ih

private theorem encodeAppend (xs ys : List Char) :
    (xs ++ ys).flatMap String.utf8EncodeChar =
      xs.flatMap String.utf8EncodeChar ++ ys.flatMap String.utf8EncodeChar := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    exact (congrArg (String.utf8EncodeChar c ++ ·) ih).trans (bytesAppendAssoc ..).symm

private theorem bytesExt {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  exact congrArg (fun l => ByteArray.mk (Array.mk l)) h

private theorem encodeBytes (cs : List Char) :
    ByteArray.mk ⟨cs.flatMap String.utf8EncodeChar⟩ = cs.utf8Encode :=
  bytesExt (bytesList _).symm

/-- Construct the byte spine once. The logic of `List.toByteArray` appends
    each byte to the end of its accumulator, which is quadratic in the kernel. -/
@[implemented_by String.ofList]
def encode (cs : List Char) : String :=
  .ofByteArray ⟨⟨cs.flatMap String.utf8EncodeChar⟩⟩ ⟨cs, encodeBytes cs⟩

theorem encodeEq (cs : List Char) : encode cs = String.ofList cs := by
  have ext : ∀ {s t : String}, s.toByteArray = t.toByteArray → s = t
    | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
  exact ext (encodeBytes cs)

/-- A concatenation of two UTF-8 encodings encodes the concatenated scalar lists. -/
theorem validAppend {s t : ByteArray} (hs : s.IsValidUTF8) (ht : t.IsValidUTF8) :
    (s ++ t).IsValidUTF8 := by
  obtain ⟨xs, rfl⟩ := hs
  obtain ⟨ys, rfl⟩ := ht
  refine ⟨xs ++ ys, bytesExt ?_⟩
  change (xs.flatMap String.utf8EncodeChar).toByteArray.data.toList ++
    (ys.flatMap String.utf8EncodeChar).toByteArray.data.toList =
    ((xs ++ ys).flatMap String.utf8EncodeChar).toByteArray.data.toList
  rw [bytesList, bytesList, bytesList, encodeAppend]

theorem decodeOfList (cs : List Char) :
    decode (String.ofList cs).toByteArray.data.toList = cs := by
  change decode (cs.flatMap String.utf8EncodeChar).toByteArray.data.toList = cs
  rw [bytesList]
  induction cs with
  | nil => rfl
  | cons c cs ih => exact (nextChar c _).trans (congrArg (c :: ·) ih)

theorem encodeOfString (s : String) : String.ofList (decode s.toByteArray.data.toList) = s := by
  cases s with
  | ofByteArray bytes valid =>
    obtain ⟨cs, rfl⟩ := valid
    exact congrArg String.ofList (decodeOfList cs)

end AgdaMirror.Utf8
