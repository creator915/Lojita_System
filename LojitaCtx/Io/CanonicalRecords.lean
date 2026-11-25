import LojitaCtx.Io.DeviceCursor
import LojitaCtx.Io.KernelConfluence

namespace LojitaCtx.Io.CanonicalRecords
open LojitaCtx.Posix FsLib

/-- Each entry counts the bytes after the first byte of a nonempty record. -/
def lengths (rs : List Nat) := rs.map (·+1)

def volume (rs : List Nat) := (lengths rs).sum

def skip (n : Nat) : List Nat → List Nat
  | [] => []
  | k::ks => if n ≤ k then (k-n)::ks else skip (n-(k+1)) ks

private theorem skip_zero (rs : List Nat) : skip 0 rs = rs := by cases rs <;> simp [skip]

private theorem skip_add (rs : List Nat) (a b : Nat) : skip (a+b) rs = skip b (skip a rs) := by
  induction rs generalizing a b with
  | nil => simp [skip]
  | cons k ks ih =>
    by_cases h : a ≤ k
    · by_cases j : b ≤ k-a
      · simp [skip,h,j,show a+b ≤ k by omega, Nat.sub_sub]
      · simp [skip,h,j,show ¬ a+b ≤ k by omega]
        congr 1 <;> omega
    · simp [skip,h,show ¬ a+b ≤ k by omega,← ih]
      congr 1 <;> omega

private theorem volume_skip (rs : List Nat) (n : Nat) : volume (skip n rs) = volume rs - n := by
  induction rs generalizing n with
  | nil => simp [skip,volume,lengths]
  | cons k ks ih =>
    have cons (k : Nat) : volume (k::ks) = k+1 + volume ks := by simp [volume,lengths]
    by_cases h : n ≤ k
    · simp [skip,h,cons]; omega
    · simp [skip,h,cons,ih]; omega

/-- The base PTY contains the bytes and canonical records *after* VEOF. The
    cursor prepends the current transfer's remaining input and its record boundaries. -/
def withInput (p : PtyState) (pending : Bytes) (rs : List Nat) : PtyState :=
  {p with
    toSlave := {p.toSlave with pendingBytes := pending ++ p.toSlave.pendingBytes}
    records := lengths rs ++ 0::p.records}

def cursor (m : Machine) (id : PtyId) (p : PtyState) (bs : Bytes) (rs : List Nat) (off : Nat) :=
  m.setPty id (withInput p (bs.drop off) (skip off rs))

theorem initial (m : Machine) (id : Nat) (p : PtyState) (bs : Bytes) (rs : List Nat)
    (found : m.kernel.ptys[id]? = some (withInput p bs rs)) :
    cursor m id p bs rs 0 = m := by
  simp [cursor,skip_zero,Machine.setPty,table_restore _ _ _ found]

private theorem record_read (p : PtyState) (canonical : p.attrs.icanon = true) (x : UInt8)
    (xs : Bytes) (r k : Nat) (rs : List Nat) (fits : r ≤ xs.length)
    (sl : StepSlice) (awake : sl.intrBefore = false) (nb : Bool) :
    let t := min r k
    ptyRead {sl with maxBytes := k+1} nb false (withInput p (x::xs) (r::rs)) =
    (.ok (x::xs.take t), withInput p (xs.drop t) (skip (t+1) (r::rs))) := by
  intro t
  have bound : t ≤ xs.length := by dsimp [t]; omega
  have word : min (k+1) (r+1) = t+1 := by dsimp [t]; omega
  have take : (xs ++ p.toSlave.pendingBytes).take t = xs.take t := List.take_append_of_le_length bound
  have drop : (xs ++ p.toSlave.pendingBytes).drop t = xs.drop t ++ p.toSlave.pendingBytes := List.drop_append_of_le_length bound
  by_cases full : t = r
  · simp [ptyRead,withInput,canonical,awake,lengths,streamRead,word,
      List.length_take,full,skip,skip_zero,
      List.take_append_of_le_length fits,List.drop_append_of_le_length fits,
      show ¬ r+1 ≤ r by omega] <;> omega
  · have short : t+1 ≤ r := by dsimp [t] at *; omega
    have diff : r-t ≠ 0 := by omega
    simp [ptyRead,withInput,canonical,awake,lengths,streamRead,word,take,drop,
      List.length_take,Nat.min_eq_left bound,skip,short,diff]
    omega


/-- Every attempted read returns bytes, an interrupt, or the next VEOF. -/
theorem step_cases (m : Machine) (fd ofd id : Nat) (d : OpenFileDesc) (p : PtyState)
    (bytes : Bytes) (rs : List Nat) (aligned : volume rs = bytes.length)
    (backed : fdLinks m.proc m.kernel.ofds) (look : m.lookup fd = .ok (ofd,d))
    (target : d.target = .pty id false) (canRead : d.flags.access ≠ .writeOnly)
    (present : (m.kernel.ptys[id]?).isSome) (canonical : p.attrs.icanon = true)
    (off size : Nat) (sl : StepSlice) :
    let atOff := cursor m id p bytes rs
    let read := stepSyscall (atOff off) sl (.read fd (max 1 size))
    read = (.err .EINTR,atOff off) ∨
    (read = (.ok ([] : Bytes).toByteArray,m.setPty id p) ∧ bytes.drop off = []) ∨
    ∃ b xs, let endOff := off+(b::xs).length
            read = (.ok (b::xs).toByteArray,atOff endOff) ∧ (b::xs) ++ bytes.drop endOff = bytes.drop off := by
  dsimp only
  let here := cursor m id p bytes rs off
  let tty := withInput p (bytes.drop off) (skip off rs)
  have current : here.kernel.ptys[id]? = some tty := Std.TreeMap.getElem?_insert_self
  obtain ⟨orig,found⟩ := Option.isSome_iff_exists.mp present
  have set (v : PtyState) : here.setPty id v = m.setPty id v := by
    simp [here,cursor,Machine.setPty,table_overwrite _ _ orig _ _ found]
  rw [kernel_pty_read here fd ofd id size d tty sl backed look target canRead current]
  cases hi : sl.intrBefore
  · cases boundary : skip off rs with
    | nil =>
      right; left
      have size := volume_skip rs off
      rw [boundary,aligned] at size
      have empty : bytes.drop off = [] := List.drop_eq_nil_iff.mpr (by simp [volume,lengths] at size; omega)
      refine ⟨?_,empty⟩
      simp [tty,boundary,empty,withInput,lengths,ptyRead,canonical,set] <;> rfl
    | cons r rest =>
      right; right
      have fit := volume_skip rs off
      rw [boundary,aligned] at fit
      have enough : r + 1 ≤ (bytes.drop off).length := by
        simp [volume,lengths] at fit
        simp; omega
      cases dataAt : bytes.drop off with
      | nil => simp [dataAt] at enough
      | cons x xs =>
        have room : r ≤ xs.length := by simp [dataAt] at enough; omega
        let n := min (max 1 size) (max 1 sl.maxBytes)
        have pos : 0 < n := by dsimp [n]; omega
        obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
        have word : min (max 1 size) (max 1 sl.maxBytes) = k+1 := hk
        let t := min r k
        have bound : t ≤ xs.length := by dsimp [t]; omega
        have takeLen : (xs.take t).length = t := by simp [List.length_take,bound]
        have after : bytes.drop (off+(x::xs.take t).length) = xs.drop t := by
          rw [← List.drop_drop,dataAt]
          simp [takeLen]
        have boundaries : skip (off+(x::xs.take t).length) rs = skip (t+1) (r::rest) := by
          rw [skip_add,boundary]; simp [takeLen]
        have read := record_read p canonical x xs r k rest room sl hi d.flags.nonblock
        rw [hi] at read
        refine ⟨x,xs.take t,?_,?_⟩
        · simp only [tty,boundary,dataAt,word,read,set,cursor,after,boundaries]
          rfl
        · rw [after]
          simp
  · left
    simp [ptyRead,tty,withInput,canonical,set] <;> rfl


/-- Before the first VEOF, an arbitrary sequence of canonical records may
    cause early short reads. The original PTY suffix survives the consumed VEOF. -/
theorem finite_read_law (m : Machine) (fd ofd id : Nat) (d : OpenFileDesc) (p : PtyState)
    (bytes : Bytes) (rs : List Nat) (aligned : volume rs = bytes.length)
    (backed : fdLinks m.proc m.kernel.ofds) (look : m.lookup fd = .ok (ofd,d))
    (target : d.target = .pty id false) (canRead : d.flags.access ≠ .writeOnly)
    (present : (m.kernel.ptys[id]?).isSome) (canonical : p.attrs.icanon = true) :
    FiniteReadLaw bytes fd (cursor m id p bytes rs) (m.setPty id p) := by
  have casesAt := step_cases m fd ofd id d p bytes rs aligned backed look target canRead present canonical
  constructor
  · intro off size sl b bs next _ step
    rcases casesAt off size sl with intr | ⟨eof,_⟩ | ⟨x,xs,read,prefixEq⟩
    · simp [step] at intr
    · rw [step] at eof
      have empty := packed_bytes_injective (Ret.ok.inj (congrArg Prod.fst eof))
      cases empty
    · rw [step] at read
      have data := packed_bytes_injective (Ret.ok.inj (congrArg Prod.fst read))
      cases data
      exact ⟨prefixEq, congrArg Prod.snd read⟩
  · intro off size sl next _ step
    rcases casesAt off size sl with intr | ⟨eof,_⟩ | ⟨x,xs,read,_⟩
    · simpa [step] using intr
    · simp [step] at eof
    · simp [step] at read
  · intro off size sl next _ step
    rcases casesAt off size sl with intr | ⟨eof,empty⟩ | ⟨x,xs,read,_⟩
    · simp [step] at intr
    · exact ⟨empty,by simpa [step] using eof⟩
    · rw [step] at read
      have empty := packed_bytes_injective (Ret.ok.inj (congrArg Prod.fst read))
      cases empty

end LojitaCtx.Io.CanonicalRecords
