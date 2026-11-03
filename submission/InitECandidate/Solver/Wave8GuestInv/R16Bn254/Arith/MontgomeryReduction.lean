import Mathlib.Data.Nat.ModEq
import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInverseSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith

def montFinalReduce (raw modulus : Nat) : Nat :=
  if raw < modulus then raw else raw - modulus

theorem montFinalReduce_lt (raw modulus : Nat) (hraw : raw < 2 * modulus) :
    montFinalReduce raw modulus < modulus := by
  unfold montFinalReduce
  split <;> omega

theorem montFinalReduce_modEq (raw modulus : Nat) :
    Nat.ModEq modulus (montFinalReduce raw modulus) raw := by
  unfold montFinalReduce
  split
  · exact Nat.ModEq.refl _
  · rename_i hn
    have he : raw - modulus + modulus = raw := Nat.sub_add_cancel (by omega)
    change (raw - modulus) % modulus = raw % modulus
    conv_rhs => rw [← he]
    simp

/-- One canonical operand is sufficient for the single final subtraction.
The other input and the correction integer may use the full radix range. -/
theorem montRaw_bound (radix modulus a b correction raw : Nat)
    (hr : 0 < radix) (hm : 0 < modulus)
    (ha : a < radix) (hb : b < modulus) (hk : correction < radix)
    (hidentity : radix * raw = a * b + correction * modulus) :
    raw < 2 * modulus := by
  have hab : a * b < radix * modulus :=
    (Nat.mul_le_mul_right b (Nat.le_of_lt ha)).trans_lt (Nat.mul_lt_mul_of_pos_left hb hr)
  have hkprod : correction * modulus < radix * modulus := Nat.mul_lt_mul_of_pos_right hk hm
  nlinarith

theorem montReduction_correct (radix modulus a b correction raw : Nat)
    (hr : 0 < radix) (hm : 0 < modulus)
    (ha : a < radix) (hb : b < modulus) (hk : correction < radix)
    (hidentity : radix * raw = a * b + correction * modulus) :
    montFinalReduce raw modulus < modulus ∧
      Nat.ModEq modulus (radix * montFinalReduce raw modulus) (a * b) := by
  refine ⟨montFinalReduce_lt _ _ (montRaw_bound _ _ _ _ _ _ hr hm ha hb hk hidentity), ?_⟩
  apply ((montFinalReduce_modEq raw modulus).mul_left radix).trans
  change (radix * raw) % modulus = (a*b) % modulus
  rw [hidentity]
  simp

theorem fqModulus_double_lt_radix : 2 * fqModulus.toNat < 2 ^ 256 := by decide

theorem fqMontReduction_correct (a b correction raw : Nat)
    (ha : a < 2 ^ 256) (hb : b < fqModulus.toNat) (hk : correction < 2 ^ 256)
    (hidentity : 2 ^ 256 * raw = a*b + correction*fqModulus.toNat) :
    raw < 2 ^ 256 ∧ montFinalReduce raw fqModulus.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * montFinalReduce raw fqModulus.toNat) (a*b) := by
  have hp : 0 < fqModulus.toNat := Nat.lt_trans (by decide) fqModulus_gt_one
  have hraw := montRaw_bound _ _ _ _ _ _ (by decide) hp ha hb hk hidentity
  exact ⟨hraw.trans fqModulus_double_lt_radix,
    montReduction_correct _ _ _ _ _ _ (by decide) hp ha hb hk hidentity⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
