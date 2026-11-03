import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqCancellation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack
attribute [local irreducible] subCarry256

/-- Cancellation recovers the residue even when the dividend is noncanonical. -/
theorem fqProduct_eq_residue (lead divisor inverse quotient product : Nat)
    (hp : product < fqModulus.toNat)
    (hinv : Nat.ModEq fqModulus.toNat (divisor * inverse) (2^256 * 2^256))
    (hquot : Nat.ModEq fqModulus.toNat (2^256 * quotient) (lead * inverse))
    (hprod : Nat.ModEq fqModulus.toNat (2^256 * product) (divisor * quotient)) :
    product = lead % fqModulus.toNat := by
  have he := montInverse_cancel fqModulus.toNat (2^256) lead divisor inverse quotient product
    fqRadix_coprime hinv hquot (by simpa only [Nat.mul_comm] using hprod)
  exact (Nat.mod_eq_of_lt hp).symm.trans he

/-- The actual limb subtraction leaves the unreduced multiple of p. -/
theorem fqSub_residue_toNat (a b : Limbs256)
    (hb : b.toNat = a.toNat % fqModulus.toNat) :
    (modSub256 a b fqModulus).toNat = a.toNat - a.toNat % fqModulus.toNat := by
  have hle : b.toNat ≤ a.toNat := hb ▸ Nat.mod_le _ _
  rw [modSub256,if_neg (Nat.not_lt.mpr hle),subCarry256_no_borrow a b hle,hb]

theorem fqSub_residue_multiple (a b : Limbs256)
    (hb : b.toNat = a.toNat % fqModulus.toNat) :
    (modSub256 a b fqModulus).toNat % fqModulus.toNat = 0 := by
  rw [fqSub_residue_toNat a b hb]
  have he := Nat.mod_add_div a.toNat fqModulus.toNat
  have hx : a.toNat - a.toNat % fqModulus.toNat = fqModulus.toNat * (a.toNat / fqModulus.toNat) := by omega
  rw [hx,Nat.mul_mod_right]

/-- A canonical Montgomery product of a modulus multiple is zero. -/
theorem fqMultiple_product_zero (top inverse quotient : Nat)
    (ht : top % fqModulus.toNat = 0) (hq : quotient < fqModulus.toNat)
    (hm : Nat.ModEq fqModulus.toNat (2^256 * quotient) (top * inverse)) :
    quotient = 0 := by
  have hz : Nat.ModEq fqModulus.toNat top 0 := ht
  have he : Nat.ModEq fqModulus.toNat (2^256 * quotient) (2^256 * 0) := by
    simpa only [Nat.zero_mul,Nat.mul_zero] using hm.trans (hz.mul_right inverse)
  exact (Nat.ModEq.cancel_left_of_coprime fqRadix_coprime he).eq_of_lt_of_lt hq
    (Nat.lt_trans (by decide) fqModulus_gt_one)

/-- Subtracting zero does not even normalize a noncanonical coefficient. -/
theorem fqSub_zero_toNat (a b : Limbs256) (hb : b.toNat = 0) :
    (modSub256 a b fqModulus).toNat = a.toNat := by
  have hle : b.toNat ≤ a.toNat := by omega
  rw [modSub256,if_neg (Nat.not_lt.mpr hle),subCarry256_no_borrow a b hle,hb,Nat.sub_zero]

end InitECandidate.Solver.Wave8GuestInv.Arith
