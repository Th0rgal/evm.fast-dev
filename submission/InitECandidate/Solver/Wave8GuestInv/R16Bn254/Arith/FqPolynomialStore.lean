import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMemoryPure
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqCancellation
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryPolynomial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup

def CanonicalPolynomial (coefficients : Nat → Limbs256) : Prop :=
  ∀ i, i < 13 → (coefficients i).toNat < fqModulus.toNat

/-- All coefficients at or above this index vanish. This avoids assigning a
natural-number degree to the zero polynomial. -/
def PolynomialDegreeBelow (coefficients : Nat → Limbs256) (d : Nat) : Prop :=
  ∀ i, i < 13 → d ≤ i → (coefficients i).toNat = 0

theorem canonicalPolynomial_update (coefficients : Nat → Limbs256) (i : Nat) (value : Limbs256)
    (hc : CanonicalPolynomial coefficients) (hv : value.toNat < fqModulus.toNat) :
    CanonicalPolynomial (fun j => if j = i then value else coefficients j) := by
  intro j hj
  by_cases he : j = i
  · simp only [if_pos he]; exact hv
  · simp only [if_neg he]; exact hc j hj

theorem polynomialDegree_clear_lead (coefficients : Nat → Limbs256) (d : Nat) (value : Limbs256)
    (hd : PolynomialDegreeBelow coefficients (d + 1)) (hz : value.toNat = 0) :
    PolynomialDegreeBelow (fun j => if j = d then value else coefficients j) d := by
  intro j hj hge
  by_cases he : j = d
  · simp only [if_pos he]; exact hz
  · simp only [if_neg he]; exact hd j hj (by omega)

/-- A successful actual fq_sub followed by an actual U256 store clears a
canonical leading coefficient without disturbing the other coefficients.
This is the scalar/store fragment; polynomial-loop correspondence is separate. -/
theorem fqSub_store_clears_lead {F : Type}
    (s computed final : PanSemStateFiniteExact 64 F)
    (coefficients : Nat → Limbs256) (base : BitVec 64) (d : Nat)
    (product : Limbs256) (ret : ValueHOL 64) (destination source : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hd : d < 13)
    (hm : MemoryPolynomial s.memory base coefficients)
    (hcanon : CanonicalPolynomial coefficients)
    (hdegree : PolynomialDegreeBelow coefficients (d + 1))
    (hp : product.toNat < fqModulus.toNat) (heq : product.toNat = (coefficients d).toNat)
    (ha : s.locals.lookup (ofString "a") = some (coefficients d).toValue)
    (hb : s.locals.lookup (ofString "b") = some product.toValue)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_sub) =
      (some (.returned ret), computed))
    (hdomain : DomainU256 computed.memaddrs (coefficientAddress base d))
    (headdr : arithEval computed destination = some (.val (.word (coefficientAddress base d))))
    (hevalue : arithEval computed source = some ret)
    (hstore : evaluateHOLFiniteState computed (.store destination source) = (none, final)) :
    ∃ out : Limbs256, out.toNat = 0 ∧
      MemoryPolynomial final.memory base (fun j => if j = d then out else coefficients j) ∧
      CanonicalPolynomial (fun j => if j = d then out else coefficients j) ∧
      PolynomialDegreeBelow (fun j => if j = d then out else coefficients j) d := by
  obtain ⟨out, hret, hz⟩ := fqSub_returned_zero_of_equal_canonical
    (coefficients d) product ret hc ha hb (hcanon d hd) hp heq hr
  have hmem := fqSub_memoryPure s hc
  rw [hr] at hmem
  have hwrite := eval_store_u256 computed destination source (coefficientAddress base d) out
    headdr (hevalue.trans (congrArg some hret)) hdomain
  rw [hstore] at hwrite
  have hfinal := congrArg (fun pair => pair.2.memory) hwrite
  change final.memory = writeU256 computed.memory (coefficientAddress base d) out at hfinal
  rw [hmem] at hfinal
  refine ⟨out, hz, ?_, ?_, polynomialDegree_clear_lead coefficients d out hdegree hz⟩
  · rw [hfinal]
    exact writeCoefficient_polynomial s.memory base coefficients d out hd hm
  · exact canonicalPolynomial_update coefficients d out hcanon
      (by rw [hz]; exact Nat.lt_trans (by decide) fqModulus_gt_one)

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
