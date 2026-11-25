import Init

namespace G1Fixture

/-- error: (kernel) invalid declaration, it uses unsafe declaration 'lcProof' -/
#guard_msgs in
theorem cannotUseCompilerProof (p : Prop) : p := lcProof

end G1Fixture
