import Mathlib.Data.Nat.ModEq
import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModularArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
namespace InitECandidate.Solver.Wave8GuestInv.Arith

/-- The coefficient relation maintained by the binary modular inverse. -/
def InverseCongruence (input modulus operand coefficient : Nat) : Prop :=
  Nat.ModEq modulus (input * coefficient) operand

theorem inverseCongruence_init (input modulus : Nat) :
    InverseCongruence input modulus input 1 ∧
      InverseCongruence input modulus modulus 0 := by
  simp [InverseCongruence, Nat.ModEq]

/-- Halving an even operand and modularly halving its coefficient preserves
its relation to the original input when the modulus is odd. -/
theorem inverseCongruence_half (input operand : Nat) (x m : Limbs256)
    (hm : m.toNat % 2 = 1) (hu : operand % 2 = 0)
    (hx : InverseCongruence input m.toNat operand x.toNat) :
    InverseCongruence input m.toNat (operand / 2) (modHalf256 x m).toNat := by
  have hcop : Nat.gcd m.toNat 2 = 1 := by
    simpa only [Nat.coprime_two_right] using (Nat.odd_iff.mpr hm)
  apply Nat.ModEq.cancel_left_of_coprime hcop
  have hc : Nat.ModEq m.toNat (2 * (modHalf256 x m).toNat) x.toNat :=
    modHalf256_double_mod x m hm
  have he : 2 * (operand / 2) = operand := by omega
  simpa only [Nat.mul_left_comm, he] using (hc.mul_left input).trans hx

/-- Subtracting one operand and its modular coefficient from another preserves
both the congruence and the canonical coefficient range. -/
theorem inverseCongruence_sub (input u v : Nat) (x y m : Limbs256)
    (huv : v ≤ u) (hx : x.toNat < m.toNat) (hy : y.toNat < m.toNat)
    (hxu : InverseCongruence input m.toNat u x.toNat)
    (hyv : InverseCongruence input m.toNat v y.toNat) :
    InverseCongruence input m.toNat (u - v) (modSub256 x y m).toNat ∧
      (modSub256 x y m).toNat < m.toNat := by
  refine ⟨?_, modSub256_lt_modulus x y m hx hy⟩
  have hs : Nat.ModEq m.toNat ((modSub256 x y m).toNat + y.toNat) x.toNat :=
    modSub256_add_mod x y m hx hy
  have he : (u - v) + v = u := Nat.sub_add_cancel huv
  apply Nat.ModEq.add_right_cancel hyv
  simpa only [Nat.mul_add, he] using (hs.mul_left input).trans hxu

theorem inverseCongruence_one (input modulus coefficient : Nat)
    (h : InverseCongruence input modulus 1 coefficient) :
    (input * coefficient) % modulus = 1 % modulus := h

end InitECandidate.Solver.Wave8GuestInv.Arith
