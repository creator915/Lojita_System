module

public import Test.G1.Dependencies

public section

namespace G1Fixture

def approvedBytes (xs : Array UInt8) : ByteArray := (ByteArray.mk xs).push 0
noncomputable def indirectAxiom : Nat := Dep.axiomRelay
noncomputable def taintedBytes (xs : ByteArray) : ByteArray :=
  xs.push (UInt8.ofNat Dep.axiomRelay)
theorem admittedTheorem : True := Dep.proofRelay
def indirectExtern : Nat → Nat := Dep.externRelay
unsafe def unsafeRoot : Nat → Nat := Dep.markedUnsafe
def effectOnlyInType : Type := Dep.effectRelay
def usesPartial : Nat → Nat := Dep.partialMarker
def usesImplementedBy : Nat → Nat := Dep.withImpl
def usesCSimp : Nat → Nat := Dep.logical
def outsideReviewedSet : Float → Float := Float.sin

def directPanic (message : String) : Nat := panic message
def directPanicCore (message : String) : Nat := panicCore message
theorem legitimateElimination (h : False) : True := False.elim h

end G1Fixture
