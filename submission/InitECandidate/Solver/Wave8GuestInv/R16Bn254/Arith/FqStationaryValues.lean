import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqStationaryScalar

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- Numeric equality determines every stored word, including noncanonical values. -/
theorem limbs256_toNat_injective : Function.Injective Limbs256.toNat := by
  intro a b he
  have ha0 := a.l0.isLt
  have ha1 := a.l1.isLt
  have ha2 := a.l2.isLt
  have ha3 := a.l3.isLt
  have hb0 := b.l0.isLt
  have hb1 := b.l1.isLt
  have hb2 := b.l2.isLt
  have hb3 := b.l3.isLt
  simp only [Limbs256.toNat] at he
  have h0 : a.l0 = b.l0 := BitVec.toNat_inj.mp (by omega)
  have h1 : a.l1 = b.l1 := BitVec.toNat_inj.mp (by omega)
  have h2 : a.l2 = b.l2 := BitVec.toNat_inj.mp (by omega)
  have h3 : a.l3 = b.l3 := BitVec.toNat_inj.mp (by omega)
  cases a; cases b; simp_all

def fqZeroLimbs : Limbs256 := ⟨0,0,0,0⟩

theorem limbs256_eq_zero (a : Limbs256) (ha : a.toNat = 0) : a = fqZeroLimbs :=
  limbs256_toNat_injective (ha.trans (by rfl))

theorem fqSub_zero_eq (a b : Limbs256) (hb : b.toNat = 0) :
    modSub256 a b fqModulus = a :=
  limbs256_toNat_injective (fqSub_zero_toNat a b hb)

/-- Actual successful fq_sub by zero returns the exact original value. -/
theorem fqSub_returned_zero_identity {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hb : s.locals.lookup (ofString "b") = some b.toValue) (hz : b.toNat = 0)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_sub) =
      (some (.returned ret),post)) : ret = a.toValue := by
  rw [fqSub_returned_exact a b ret hc ha hb hr,fqSub_zero_eq a b hz]

/-- Actual successful multiplication by a canonical zero returns four zero words. -/
theorem fqMul_returned_zero_right {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hb : s.locals.lookup (ofString "b") = some b.toValue) (hz : b.toNat = 0)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_mul) =
      (some (.returned ret),post)) : ret = fqZeroLimbs.toValue := by
  obtain ⟨out,hret,hout,hmul⟩ := fqMul_returned_canonical a b ret hc ha hb
    (by rw [hz]; exact Nat.lt_trans (by decide) fqModulus_gt_one) hr
  have he : Nat.ModEq fqModulus.toNat (2^256 * out.toNat) (2^256 * 0) := by
    simpa only [hz,Nat.mul_zero] using hmul
  have ho : out.toNat = 0 :=
    (Nat.ModEq.cancel_left_of_coprime fqRadix_coprime he).eq_of_lt_of_lt hout
      (Nat.lt_trans (by decide) fqModulus_gt_one)
  rw [hret,limbs256_eq_zero out ho]

/-- Actual quotient multiplication is exactly zero for a modulus-multiple top. -/
theorem fqMul_returned_multiple_zero {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hb : s.locals.lookup (ofString "b") = some b.toValue)
    (hz : a.toNat % fqModulus.toNat = 0) (hcanon : b.toNat < fqModulus.toNat)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_mul) =
      (some (.returned ret),post)) : ret = fqZeroLimbs.toValue := by
  obtain ⟨out,hret,hout,hmul⟩ := fqMul_returned_canonical a b ret hc ha hb hcanon hr
  rw [hret,limbs256_eq_zero out (fqMultiple_product_zero a.toNat b.toNat out.toNat hz hout hmul)]

end InitECandidate.Solver.Wave8GuestInv.Arith
