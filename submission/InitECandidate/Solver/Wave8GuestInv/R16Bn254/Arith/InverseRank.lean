import Mathlib.Data.Nat.Size
import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256Half

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv

/-- Sharp binary-inverse rank (`≤ 513` on 256-bit operands). Each normalization +
subtraction drops `u.size + v.size` by at least `1`, except an odd/odd step (`ku = 0 ∧ kv = 0`),
which transitions `odd&odd` (`1`) to `even` (`0`) without increasing `u.size + v.size`. -/
def inverseRank (u v : Nat) : Nat :=
  (u.size + v.size) + if u % 2 = 1 ∧ v % 2 = 1 then 1 else 0

def inverseSubtract (u v : Nat) : Nat × Nat :=
  if v ≤ u then (u - v, v) else (u, v - u)

theorem inverseRank_bound {u v width : Nat}
    (hu : u < 2 ^ width) (hv : v < 2 ^ width) :
    inverseRank u v ≤ 2 * width + 1 := by
  have hsu := Nat.size_le.mpr hu
  have hsv := Nat.size_le.mpr hv
  unfold inverseRank
  split <;> omega

theorem inverseSubtract_size (u v : Nat) :
    (inverseSubtract u v).1.size + (inverseSubtract u v).2.size ≤ u.size + v.size := by
  have hu := Nat.size_le_size (Nat.sub_le u v)
  have hv := Nat.size_le_size (Nat.sub_le v u)
  unfold inverseSubtract
  split <;> simp only [Prod.fst, Prod.snd] <;> omega

theorem inverseSubtract_even {u v : Nat} (hu : u % 2 = 1) (hv : v % 2 = 1) :
    ¬ ((inverseSubtract u v).1 % 2 = 1 ∧ (inverseSubtract u v).2 % 2 = 1) := by
  unfold inverseSubtract
  split <;> simp only [Prod.fst, Prod.snd] <;> omega

theorem size_mul_pow_two {a : Nat} (ha : a ≠ 0) (k : Nat) :
    (a * 2 ^ k).size = a.size + k := by
  simpa only [Nat.shiftLeft_eq] using Nat.size_shiftLeft ha k

/-- Any complete odd-normalization followed by the source subtraction strictly
reduces the rank, including the equal-input case producing a zero operand. -/
theorem inverseRank_normalize_subtract (a b ku kv : Nat)
    (ha : a % 2 = 1) (hb : b % 2 = 1) :
    inverseRank (inverseSubtract a b).1 (inverseSubtract a b).2 <
      inverseRank (a * 2 ^ ku) (b * 2 ^ kv) := by
  have hsz := inverseSubtract_size a b
  have heven := inverseSubtract_even ha hb
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  unfold inverseRank
  rw [if_neg heven, size_mul_pow_two ha0, size_mul_pow_two hb0]
  by_cases hk : ku = 0 ∧ kv = 0
  · obtain ⟨rfl, rfl⟩ := hk
    simp only [Nat.pow_zero, Nat.mul_one, ha, hb, and_self, ↓reduceIte]
    omega
  · split <;> omega

theorem half_size_lt {n : Nat} (hn : 0 < n) : (n / 2).size < n.size := by
  have hpos := Nat.size_pos.mpr hn
  have hnlt := Nat.lt_size_self n
  have hpow : 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
    conv_lhs => rw [show n.size = (n.size - 1) + 1 by omega]
    rw [Nat.pow_succ, Nat.mul_comm]
  have hhalf : n / 2 < 2 ^ (n.size - 1) := by
    rw [hpow] at hnlt
    omega
  have := Nat.size_le.mpr hhalf
  omega

theorem half256_size_lt (a : Limbs256) (h : 0 < a.toNat) :
    (half256 a).toNat.size < a.toNat.size := by
  rw [half256_toNat]
  exact half_size_lt h

theorem inverseRank_256_le (u v : Limbs256) : inverseRank u.toNat v.toNat ≤ 513 :=
  inverseRank_bound u.toNat_lt v.toNat_lt

theorem inverseRank_384_le {u v : Nat} (hu : u < 2 ^ 384) (hv : v < 2 ^ 384) :
    inverseRank u v ≤ 769 := inverseRank_bound hu hv

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
