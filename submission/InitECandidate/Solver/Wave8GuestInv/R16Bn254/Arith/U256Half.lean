import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256Arithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 800000
namespace InitECandidate.Solver.Wave8GuestInv.Arith

/-- The cross-word shift used by the binary-inverse loop. -/
def halfWord256 (lo hi : BitVec 64) : BitVec 64 :=
  (lo >>> (1 : Nat)) ||| (hi <<< (63 : Nat))

theorem halfWord256_toNat (lo hi : BitVec 64) :
    (halfWord256 lo hi).toNat = lo.toNat / 2 + 9223372036854775808 * (hi.toNat % 2) := by
  have hlo := lo.isLt
  have hhi := hi.isLt
  have hsmall : lo.toNat / 2 < 2 ^ 63 := by omega
  have hmod : (hi.toNat * 2 ^ 63) % 2 ^ 64 = 2 ^ 63 * (hi.toNat % 2) := by omega
  simp only [halfWord256, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [hmod, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hsmall (hi.toNat % 2)]
  omega

def half256 (a : Limbs256) : Limbs256 :=
  ⟨halfWord256 a.l0 a.l1, halfWord256 a.l1 a.l2,
    halfWord256 a.l2 a.l3, a.l3 >>> (1 : Nat)⟩

theorem half256_toNat (a : Limbs256) : (half256 a).toNat = a.toNat / 2 := by
  dsimp only [Limbs256.toNat, half256]
  rw [halfWord256_toNat, halfWord256_toNat, halfWord256_toNat]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem half256_lt (a : Limbs256) (h : 0 < a.toNat) : (half256 a).toNat < a.toNat := by
  rw [half256_toNat]
  omega

theorem half256_zero (a : Limbs256) (h : a.toNat = 0) : (half256 a).toNat = 0 := by
  rw [half256_toNat, h]

end InitECandidate.Solver.Wave8GuestInv.Arith
