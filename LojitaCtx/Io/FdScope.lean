import LojitaCtx.Io.FsLib

namespace LojitaCtx.Io.FsLib
open LojitaCtx.Posix

variable {Δ : List Cap} {S A : Type}

def closePrefix (cap : .fdIoCap ∈ Δ) (fd : Fd) (value : Ret A) : Prefix Δ (Ret A) :=
  .ask (.close fd) cap fun closed => .done (afterClose value closed)

private theorem scopeRound (cap : .fdIoCap ∈ Δ) (fd : Fd) (r : FreeSys Δ (Sum S (Ret A)))
    (f : Sum S (Ret A) → Prefix Δ (Ret A))
    (g : Sum (Option (Fd × S)) (Ret A) → Prefix Δ (Ret A))
    (tail : ∀ x, Prefix.Extends ((f x).bind (closePrefix cap fd)) ((closeRound cap fd x).toPrefix g)) :
    Prefix.Extends ((r.toPrefix f).bind (closePrefix cap fd)) ((r.bind (closeRound cap fd)).toPrefix g) := by
  induction r with
  | pure x => exact tail x
  | step op h k ih => exact .ask _ _ _ _ ih

/-- A complete middle run can always be observed with one additional round for
    its closing call, including a middle program already finished at depth zero. -/
theorem withFd_body_extends (cap : .fdIoCap ∈ Δ) (acquire : FreeSys Δ (Ret Fd))
    (use : Fd → PosixMachine Δ S (Ret A)) (fd : Fd) (n : Nat) (s : S) :
    Prefix.Extends (((use fd).observeFrom n s).bind (closePrefix cap fd))
      ((withFd cap acquire use).observeFrom (n+1) (some (fd,s))) := by
  induction n generalizing s with
  | zero =>
    cases h : (use fd).step s with
    | pure result =>
      cases result with
      | inl t => simp only [PosixMachine.observeFrom,h,Prefix.bind]; exact .suspended _
      | inr a =>
        simp only [PosixMachine.observeFrom,h,withFd,FreeSys.bind,closeRound,FreeSys.toPrefix,Prefix.bind,closePrefix]
        exact .ask _ _ _ _ (fun _ => .done _)
    | step op allowed k =>
      simp only [PosixMachine.observeFrom,h,Prefix.bind]
      exact .suspended _
  | succ n ih =>
    simp only [PosixMachine.observeFrom]
    apply scopeRound cap fd ((use fd).step s)
    intro x
    cases x with
    | inl state => exact ih state
    | inr result => exact .ask _ _ _ _ (fun _ => .done _)

end LojitaCtx.Io.FsLib
