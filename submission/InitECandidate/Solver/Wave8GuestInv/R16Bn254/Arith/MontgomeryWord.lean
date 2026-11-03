import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInverseSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith

/-- The actual fq_mul kernel splits machine words into radix-2^32 digits. -/
def montLow32 (x : BitVec 64) : BitVec 64 := x &&& 4294967295#64
def montHigh32 (x : BitVec 64) : BitVec 64 := x >>> (32 : Nat)

theorem montLow32_toNat (x : BitVec 64) : (montLow32 x).toNat = x.toNat % 2 ^ 32 := by
  rw [montLow32, BitVec.toNat_and]
  change x.toNat &&& (2 ^ 32 - 1) = x.toNat % 2 ^ 32
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem montHigh32_toNat (x : BitVec 64) : (montHigh32 x).toNat = x.toNat / 2 ^ 32 := by
  simp [montHigh32, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem montLow32_lt (x : BitVec 64) : (montLow32 x).toNat < 2 ^ 32 := by
  rw [montLow32_toNat]
  exact Nat.mod_lt _ (by decide)

theorem montHigh32_lt (x : BitVec 64) : (montHigh32 x).toNat < 2 ^ 32 := by
  rw [montHigh32_toNat]
  have h := x.isLt
  omega

theorem montWord_split (x : BitVec 64) :
    (montLow32 x).toNat + 2 ^ 32 * (montHigh32 x).toNat = x.toNat := by
  rw [montLow32_toNat, montHigh32_toNat]
  omega

theorem montDigit_mul_toNat (a b : BitVec 64)
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]
  apply Nat.mod_eq_of_lt
  nlinarith

theorem montDigit_product_split (a b : BitVec 64)
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (montLow32 (a * b)).toNat + 2 ^ 32 * (montHigh32 (a * b)).toNat = a.toNat * b.toNat := by
  rw [montWord_split, montDigit_mul_toNat a b ha hb]

theorem montDigit_product_high_le (a b : BitVec 64)
    (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (montHigh32 (a * b)).toNat ≤ 2 ^ 32 - 2 := by
  rw [montHigh32_toNat, montDigit_mul_toNat a b ha hb]
  have hprod : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- At most 16 products and the carry fit comfortably in a machine word. -/
theorem montAccumulator_add_toNat (a b : BitVec 64)
    (ha : a.toNat ≤ 16 * 2 ^ 32) (hb : b.toNat < 32 * 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]
  apply Nat.mod_eq_of_lt
  omega

theorem montPack32_toNat (lo hi : BitVec 64)
    (hlo : lo.toNat < 2 ^ 32) (hhi : hi.toNat < 2 ^ 32) :
    (lo ||| (hi <<< (32 : Nat))).toNat = lo.toNat + 2 ^ 32 * hi.toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hlt : hi.toNat * 2 ^ 32 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt, Nat.mul_comm hi.toNat, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt hlo hi.toNat]
  omega

end InitECandidate.Solver.Wave8GuestInv.Arith
