module

public import Init

public section

namespace G1Fixture.Dep

private axiom hiddenAxiom : Nat
noncomputable def axiomRelay : Nat := hiddenAxiom

private theorem missingProof : True := by sorry
theorem proofRelay : True := missingProof

@[extern "lojita_g1_fixture_identity"]
private def hiddenExtern (n : Nat) : Nat := n
def externRelay : Nat → Nat := hiddenExtern

unsafe def markedUnsafe (n : Nat) : Nat := n

private def hiddenIO : Type := IO Unit
def effectRelay : Type := hiddenIO

partial def partialMarker (n : Nat) : Nat :=
  if n == 0 then 0 else partialMarker (n - 1)

-- Both definitions have a pure logical body. Reject the unreviewed compiler
-- edge even if its current target has no disallowed code of its own.
private def implTarget (n : Nat) : Nat := n
@[implemented_by implTarget] def withImpl (n : Nat) : Nat := n

@[expose] def logical (n : Nat) : Nat := n
@[expose] def replacement (n : Nat) : Nat := n
@[csimp] theorem fixtureRewrite : logical = replacement := rfl

end G1Fixture.Dep
