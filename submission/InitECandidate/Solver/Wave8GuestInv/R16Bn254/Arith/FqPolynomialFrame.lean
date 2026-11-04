import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulInvariant

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack

theorem polynomialDisjoint_symm (a b : BitVec 64) (h : PolynomialDisjoint a b) :
    PolynomialDisjoint b a := by
  intro j hj k hk x hx hxb
  exact h k hk j hj x hxb hx

/-- A polynomial memory frame preserves every represented disjoint buffer. -/
theorem polynomialFrame_preserves (before after : BitVec 64 → HolWordLab 64)
    (a b : BitVec 64) (B : Nat → Limbs256)
    (hf : PolynomialFrame before after a) (hsep : PolynomialDisjoint a b)
    (hm : MemoryPolynomial before b B) : MemoryPolynomial after b B := by
  intro k hk
  have he : ∀ x ∈ u256Addresses (coefficientAddress b k), after x = before x := by
    intro x hx
    exact hf x (fun j hj => hsep j hj k hk x hx)
  rcases hm k hk with ⟨h0,h1,h2,h3⟩
  refine ⟨?_,?_,?_,?_⟩
  all_goals rw [he _ (by simp [u256Addresses])]
  all_goals assumption

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
