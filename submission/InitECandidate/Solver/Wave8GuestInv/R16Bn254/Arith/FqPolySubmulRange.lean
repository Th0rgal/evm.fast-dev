import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulInvariant

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv

def SubmulRange (q : Limbs256) (shift first last : Nat)
    (A B C : Nat → Limbs256) : Prop :=
  (∀ j, j < shift+first ∨ shift+last < j → C j = A j) ∧
  (∀ k, first ≤ k → k ≤ last → SubmulCoefficient q (A (shift+k)) (B k) (C (shift+k)))

theorem submulRange_empty (q : Limbs256) (shift first last : Nat) (A B : Nat → Limbs256)
    (hempty : last < first) : SubmulRange q shift first last A B A := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro k hfirst hlast
  omega

theorem submulRange_step (q out : Limbs256) (shift first last : Nat) (A B C : Nat → Limbs256)
    (hindex : first ≤ last)
    (hstep : SubmulCoefficient q (A (shift+first)) (B first) out)
    (hrest : SubmulRange q shift (first+1) last
      (fun j => if j = shift+first then out else A j) B C) :
    SubmulRange q shift first last A B C := by
  constructor
  · intro j hj
    have hr := hrest.1 j (by rcases hj with h | h; exact Or.inl (by omega); exact Or.inr h)
    have hne : j ≠ shift+first := by rcases hj with h | h <;> omega
    simpa only [if_neg hne] using hr
  · intro k hk hlast
    by_cases he : k = first
    · subst k
      have hr := hrest.1 (shift+first) (Or.inl (by omega))
      simp only [ite_true] at hr
      rw [hr]
      exact hstep
    · have hr := hrest.2 k (by omega) hlast
      have hne : shift+k ≠ shift+first := by omega
      simpa only [if_neg hne] using hr

theorem polynomialFrame_refl (memory : BitVec 64 → Flapjack.HolWordLab 64) (base : BitVec 64) :
    PolynomialFrame memory memory base := fun _ _ => rfl

theorem polynomialFrame_trans (before middle after : BitVec 64 → Flapjack.HolWordLab 64)
    (base : BitVec 64) (hfirst : PolynomialFrame before middle base)
    (hsecond : PolynomialFrame middle after base) : PolynomialFrame before after base := by
  intro x hx
  exact (hsecond x hx).trans (hfirst x hx)

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
