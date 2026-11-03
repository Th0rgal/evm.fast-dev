import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryU256Eval

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack

def coefficientAddress (base : BitVec 64) (i : Nat) : BitVec 64 :=
  base + BitVec.ofNat 64 (32 * i)

/-- Distinct coefficients in a thirteen-coefficient buffer cannot alias, even
if the base address itself wraps around the machine address space. -/
theorem coefficientWord_index (base : BitVec 64) (i j u v : Nat)
    (hi : i < 13) (hj : j < 13) (hu : u < 32) (hv : v < 32)
    (he : coefficientAddress base i + BitVec.ofNat 64 u =
      coefficientAddress base j + BitVec.ofNat 64 v) : i = j := by
  simp only [coefficientAddress, BitVec.add_assoc, ← BitVec.ofNat_add,
    BitVec.add_right_inj] at he
  have hnat := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat] at hnat
  omega

theorem coefficientWords_member (base x : BitVec 64) (i : Nat)
    (hx : x ∈ u256Addresses (coefficientAddress base i)) :
    ∃ u : Nat, u < 32 ∧ x = coefficientAddress base i + BitVec.ofNat 64 u := by
  simp only [u256Addresses, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, by simp⟩
  · exact ⟨8, by decide, rfl⟩
  · exact ⟨16, by decide, rfl⟩
  · exact ⟨24, by decide, rfl⟩

theorem coefficientWords_disjoint (base : BitVec 64) (i j : Nat)
    (hi : i < 13) (hj : j < 13) (hne : i ≠ j) :
    ∀ x ∈ u256Addresses (coefficientAddress base j),
      x ∉ u256Addresses (coefficientAddress base i) := by
  intro x hxj hxi
  obtain ⟨u,hu,heiu⟩ := coefficientWords_member base x i hxi
  obtain ⟨v,hv,hejv⟩ := coefficientWords_member base x j hxj
  exact hne (coefficientWord_index base i j u v hi hj hu hv (heiu.symm.trans hejv))

/-- Pointwise representation of the thirteen words of a polynomial buffer. -/
def MemoryPolynomial (memory : BitVec 64 → HolWordLab 64) (base : BitVec 64)
    (coefficients : Nat → Limbs256) : Prop :=
  ∀ i, i < 13 → MemoryU256 memory (coefficientAddress base i) (coefficients i)

theorem writeCoefficient_polynomial (memory : BitVec 64 → HolWordLab 64)
    (base : BitVec 64) (coefficients : Nat → Limbs256) (i : Nat) (value : Limbs256)
    (hi : i < 13) (hm : MemoryPolynomial memory base coefficients) :
    MemoryPolynomial (writeU256 memory (coefficientAddress base i) value) base
      (fun j => if j = i then value else coefficients j) := by
  intro j hj
  by_cases he : j = i
  · subst j
    simp only [ite_true]
    exact writeU256_value memory _ value
  · simp only [if_neg he]
    exact writeU256_preserves memory _ _ value (coefficients j)
      (coefficientWords_disjoint base i j hi hj (Ne.symm he)) (hm j hj)

end InitECandidate.Solver.Wave8GuestInv.Arith
