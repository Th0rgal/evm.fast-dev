import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256Arithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 800000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv

/-- Signed distance and a phase bit, with no restriction on the initial word. -/
def negativeCarryWordRank (c : BitVec 64) (r : Limbs256) : Nat :=
  negativeCarryRank (-c.toInt).toNat r

def positiveCarryWordRank (c : BitVec 64) (r : Limbs256) : Nat :=
  positiveCarryRank c.toInt.toNat r

theorem negativeCarryWordRank_bound (c : BitVec 64) (r : Limbs256) :
    negativeCarryWordRank c r ≤ 2 ^ 128 := by
  have hc := BitVec.le_toInt c
  unfold negativeCarryWordRank negativeCarryRank
  split_ifs <;> omega

theorem positiveCarryWordRank_bound (c : BitVec 64) (r : Limbs256) :
    positiveCarryWordRank c r ≤ 2 ^ 128 := by
  have hc := BitVec.toInt_le (x := c)
  unfold positiveCarryWordRank positiveCarryRank
  split_ifs <;> omega

theorem negativeCarryWordRank_decreases (c : BitVec 64) (r : Limbs256)
    (hc : c.toInt < 0) :
    negativeCarryWordRank (c + (addCarry256 r p256Modulus).2)
      (addCarry256 r p256Modulus).1 < negativeCarryWordRank c r := by
  have hb := addCarry256_bit r p256Modulus
  have hbit : (addCarry256 r p256Modulus).2.toNat ≤ 1 := by
    rcases hb with h | h <;> rw [h] <;> decide
  have hi : (addCarry256 r p256Modulus).2.toInt = (addCarry256 r p256Modulus).2.toNat := by
    rcases hb with h | h <;> rw [h] <;> decide
  have hmin := BitVec.le_toInt c
  have hnext : (c + (addCarry256 r p256Modulus).2).toInt =
      c.toInt + (addCarry256 r p256Modulus).2.toNat := by
    rw [BitVec.toInt_add, hi]
    apply Int.bmod_eq_of_le <;> omega
  have hd : (-(c.toInt + (addCarry256 r p256Modulus).2.toNat)).toNat =
      (-c.toInt).toNat - (addCarry256 r p256Modulus).2.toNat := by omega
  unfold negativeCarryWordRank
  rw [hnext, hd]
  exact negativeCarryRank_decreases _ r (by omega)

theorem positiveCarryWordRank_decreases (c : BitVec 64) (r : Limbs256)
    (hc : 0 < c.toInt) :
    positiveCarryWordRank (c - (if r.toNat < p256Modulus.toNat then 1 else 0))
      (subCarry256 r p256Modulus).1 < positiveCarryWordRank c r := by
  let borrow : BitVec 64 := if r.toNat < p256Modulus.toNat then 1 else 0
  have hbit : borrow.toNat ≤ 1 := by dsimp [borrow]; split_ifs <;> decide
  have hi : borrow.toInt = borrow.toNat := by dsimp [borrow]; split_ifs <;> decide
  have hn : borrow.toNat = if r.toNat < p256Modulus.toNat then 1 else 0 := by
    dsimp [borrow]; split_ifs <;> decide
  have hmax := BitVec.toInt_le (x := c)
  have hnext : (c - borrow).toInt = c.toInt - borrow.toNat := by
    rw [BitVec.toInt_sub, hi]
    apply Int.bmod_eq_of_le <;> omega
  have hd : (c.toInt - borrow.toNat).toNat = c.toInt.toNat - borrow.toNat := by omega
  change positiveCarryRank (c - borrow).toInt.toNat _ < positiveCarryRank c.toInt.toNat _
  rw [hnext, hd, hn]
  exact positiveCarryRank_decreases _ r (by omega)

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
