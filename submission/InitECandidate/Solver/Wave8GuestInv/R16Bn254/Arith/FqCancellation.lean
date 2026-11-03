import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInverseCorrect
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqSubSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- For canonical coefficients, a certified inverse and two Montgomery products
recover the exact leading coefficient, not just its congruence class. -/
theorem fqCanonical_product_eq_lead (lead divisor inverse quotient product : Nat)
    (hl : lead < fqModulus.toNat) (hp : product < fqModulus.toNat)
    (hinv : Nat.ModEq fqModulus.toNat (divisor * inverse) (2 ^ 256 * 2 ^ 256))
    (hquot : Nat.ModEq fqModulus.toNat (2 ^ 256 * quotient) (lead * inverse))
    (hprod : Nat.ModEq fqModulus.toNat (2 ^ 256 * product) (divisor * quotient)) :
    product = lead := by
  have hprod' : Nat.ModEq fqModulus.toNat (2 ^ 256 * product) (quotient * divisor) := by
    simpa only [Nat.mul_comm] using hprod
  exact (montInverse_cancel fqModulus.toNat (2 ^ 256) lead divisor inverse quotient product
    fqRadix_coprime hinv hquot hprod').eq_of_lt_of_lt hp hl

theorem fqCanonical_sub_eq_zero (lead product result : Nat)
    (hr : result < fqModulus.toNat) (hp : product = lead)
    (hsub : Nat.ModEq fqModulus.toNat (result + product) lead) : result = 0 := by
  have hzero : Nat.ModEq fqModulus.toNat result 0 :=
    Nat.ModEq.add_right_cancel' lead (by simpa only [hp, Nat.zero_add] using hsub)
  exact hzero.eq_of_lt_of_lt hr (Nat.lt_trans (by decide) fqModulus_gt_one)

/-- The scalar cancellation used by polynomial division. Canonicality of the
leading coefficient is essential; the recorded noncanonical cycle is excluded
by the explicit premise. Memory updates and degree decrease remain separate. -/
theorem fqPoly_leading_subtract_zero (lead divisor inverse quotient product result : Nat)
    (hl : lead < fqModulus.toNat) (hp : product < fqModulus.toNat) (hr : result < fqModulus.toNat)
    (hinv : Nat.ModEq fqModulus.toNat (divisor * inverse) (2 ^ 256 * 2 ^ 256))
    (hquot : Nat.ModEq fqModulus.toNat (2 ^ 256 * quotient) (lead * inverse))
    (hprod : Nat.ModEq fqModulus.toNat (2 ^ 256 * product) (divisor * quotient))
    (hsub : Nat.ModEq fqModulus.toNat (result + product) lead) : result = 0 :=
  fqCanonical_sub_eq_zero lead product result hr
    (fqCanonical_product_eq_lead lead divisor inverse quotient product hl hp hinv hquot hprod) hsub

/-- Actual fq_sub returns zero when its canonical operands have the same value. -/
theorem fqSub_returned_zero_of_equal_canonical {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hb : s.locals.lookup (ofString "b") = some b.toValue)
    (haCanon : a.toNat < fqModulus.toNat) (hbCanon : b.toNat < fqModulus.toNat)
    (heq : b.toNat = a.toNat)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_sub) =
      (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat = 0 := by
  obtain ⟨out, hret, hbound, hsub⟩ := fqSub_returned_canonical a b ret hc ha hb haCanon hbCanon hr
  exact ⟨out, hret, fqCanonical_sub_eq_zero a.toNat b.toNat out.toNat hbound heq hsub⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
