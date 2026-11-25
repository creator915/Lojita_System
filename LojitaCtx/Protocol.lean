namespace LojitaCtx.Protocol

/-! ## §1 Typed Dual Session Protocol (`Proto`, `dual`, `dual_involutive`) -/

inductive Proto (Tag : Type) : Type where
  | pEnd    : Proto Tag
  | pSend   : Tag → Proto Tag → Proto Tag
  | pRecv   : Tag → Proto Tag → Proto Tag
  | pSelect : Proto Tag → Proto Tag → Proto Tag
  | pOffer  : Proto Tag → Proto Tag → Proto Tag

-- The dependent endpoint matcher discriminates protocol constructors using
-- this kernel definition of the tag.
def Proto.ctorIdx {Tag : Type} : Proto Tag → Nat
  | .pEnd => 0
  | .pSend .. => 1
  | .pRecv .. => 2
  | .pSelect .. => 3
  | .pOffer .. => 4

def dual {Tag : Type} : Proto Tag → Proto Tag
  | .pEnd        => .pEnd
  | .pSend t P   => .pRecv t (dual P)
  | .pRecv t P   => .pSend t (dual P)
  | .pSelect P Q => .pOffer (dual P) (dual Q)
  | .pOffer P Q  => .pSelect (dual P) (dual Q)
termination_by structural P => P

theorem dual_involutive {Tag : Type} : (P : Proto Tag) → dual (dual P) = P
  | .pEnd => rfl
  | .pSend t P => congrArg (Proto.pSend t) (dual_involutive P)
  | .pRecv t P => congrArg (Proto.pRecv t) (dual_involutive P)
  | .pSelect P Q =>
    by change Proto.pSelect (dual (dual P)) (dual (dual Q)) = _; rw [dual_involutive P, dual_involutive Q]
  | .pOffer P Q =>
    by change Proto.pOffer (dual (dual P)) (dual (dual Q)) = _; rw [dual_involutive P, dual_involutive Q]
termination_by structural P => P

end LojitaCtx.Protocol
