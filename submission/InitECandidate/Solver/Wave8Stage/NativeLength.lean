import InitECandidate.Proofs.LiteralFacts

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.Stage5

/-- The concrete image size is nonzero even after conversion to a machine word. -/
theorem nativeCode_length_word_ne_zero :
    BitVec.ofNat 64 InitECandidate.nativeCode.length ≠ 0 := by
  rw [InitECandidate.Proofs.LiteralFacts.nativeCode_length]
  decide


end InitECandidate.Solver.Wave8Stage.Stage5
