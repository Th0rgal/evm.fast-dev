import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.InverseRank

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Six arbitrary little-endian words; no field-normalization assumption. -/
structure Limbs384 where
  l0 : BitVec 64
  l1 : BitVec 64
  l2 : BitVec 64
  l3 : BitVec 64
  l4 : BitVec 64
  l5 : BitVec 64

def Limbs384.toNat (a : Limbs384) : Nat :=
  a.l0.toNat +
    18446744073709551616 * a.l1.toNat +
    340282366920938463463374607431768211456 * a.l2.toNat +
    6277101735386680763835789423207666416102355444464034512896 * a.l3.toNat +
    115792089237316195423570985008687907853269984665640564039457584007913129639936 * a.l4.toNat +
    2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 * a.l5.toNat

def Limbs384.toValue (a : Limbs384) : ValueHOL 64 :=
  .rStruct [.val (.word a.l0), .val (.word a.l1), .val (.word a.l2), .val (.word a.l3), .val (.word a.l4), .val (.word a.l5)]

theorem Limbs384.toNat_lt (a : Limbs384) : a.toNat < 2 ^ 384 := by
  have h0 := a.l0.isLt
  have h1 := a.l1.isLt
  have h2 := a.l2.isLt
  have h3 := a.l3.isLt
  have h4 := a.l4.isLt
  have h5 := a.l5.isLt
  dsimp only [Limbs384.toNat]
  omega

def half384 (a : Limbs384) : Limbs384 :=
  ⟨halfWord256 a.l0 a.l1, halfWord256 a.l1 a.l2, halfWord256 a.l2 a.l3,
    halfWord256 a.l3 a.l4, halfWord256 a.l4 a.l5, a.l5 >>> (1 : Nat)⟩

theorem half384_toNat (a : Limbs384) : (half384 a).toNat = a.toNat / 2 := by
  dsimp only [Limbs384.toNat, half384]
  rw [halfWord256_toNat, halfWord256_toNat, halfWord256_toNat, halfWord256_toNat, halfWord256_toNat]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem half384_size_lt (a : Limbs384) (ha : 0 < a.toNat) :
    (half384 a).toNat.size < a.toNat.size := by
  rw [half384_toNat]
  exact half_size_lt ha

theorem half384_positive_of_even (a : Limbs384) (ha : 0 < a.toNat)
    (he : a.toNat % 2 = 0) : 0 < (half384 a).toNat := by
  rw [half384_toNat]
  omega

private def blsCarryInput (c : BitVec 64) : Nat := if c == 0 then 0 else 1

private theorem bls_wordAddCarry_conserve (a b c : BitVec 64) :
    (wordAddCarryHOL a b c).1.toNat + 18446744073709551616 * (wordAddCarryHOL a b c).2.toNat =
      a.toNat + b.toNat + blsCarryInput c := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [wordAddCarryHOL, blsCarryInput]
  split_ifs <;> simp only [BitVec.toNat_ofNat] <;> omega

private theorem bls_wordAddCarry_carryInput (a b c : BitVec 64) :
    blsCarryInput (wordAddCarryHOL a b c).2 = (wordAddCarryHOL a b c).2.toNat := by
  rcases wordAddCarry_bit a b c with h | h <;> rw [h] <;> decide

attribute [local irreducible] wordAddCarryHOL

def addCarry384 (a b : Limbs384) : Limbs384 × BitVec 64 :=
  let t0 := wordAddCarryHOL a.l0 b.l0 0
  let t1 := wordAddCarryHOL a.l1 b.l1 t0.2
  let t2 := wordAddCarryHOL a.l2 b.l2 t1.2
  let t3 := wordAddCarryHOL a.l3 b.l3 t2.2
  let t4 := wordAddCarryHOL a.l4 b.l4 t3.2
  let t5 := wordAddCarryHOL a.l5 b.l5 t4.2
  (⟨t0.1, t1.1, t2.1, t3.1, t4.1, t5.1⟩, t5.2)

theorem addCarry384_bit (a b : Limbs384) :
    (addCarry384 a b).2 = 0 ∨ (addCarry384 a b).2 = 1 := wordAddCarry_bit _ _ _

theorem addCarry384_conserve (a b : Limbs384) :
    (addCarry384 a b).1.toNat + 2 ^ 384 * (addCarry384 a b).2.toNat = a.toNat + b.toNat := by
  let t0 := wordAddCarryHOL a.l0 b.l0 0
  let t1 := wordAddCarryHOL a.l1 b.l1 t0.2
  let t2 := wordAddCarryHOL a.l2 b.l2 t1.2
  let t3 := wordAddCarryHOL a.l3 b.l3 t2.2
  let t4 := wordAddCarryHOL a.l4 b.l4 t3.2
  let t5 := wordAddCarryHOL a.l5 b.l5 t4.2
  have h0 := bls_wordAddCarry_conserve a.l0 b.l0 0
  have h1 := bls_wordAddCarry_conserve a.l1 b.l1 t0.2
  have h2 := bls_wordAddCarry_conserve a.l2 b.l2 t1.2
  have h3 := bls_wordAddCarry_conserve a.l3 b.l3 t2.2
  have h4 := bls_wordAddCarry_conserve a.l4 b.l4 t3.2
  have h5 := bls_wordAddCarry_conserve a.l5 b.l5 t4.2
  have hc0 : blsCarryInput (0 : BitVec 64) = 0 := by decide
  rw [hc0] at h0
  rw [show blsCarryInput t0.2 = t0.2.toNat from bls_wordAddCarry_carryInput _ _ _] at h1
  rw [show blsCarryInput t1.2 = t1.2.toNat from bls_wordAddCarry_carryInput _ _ _] at h2
  rw [show blsCarryInput t2.2 = t2.2.toNat from bls_wordAddCarry_carryInput _ _ _] at h3
  rw [show blsCarryInput t3.2 = t3.2.toNat from bls_wordAddCarry_carryInput _ _ _] at h4
  rw [show blsCarryInput t4.2 = t4.2.toNat from bls_wordAddCarry_carryInput _ _ _] at h5
  change t0.1.toNat + 18446744073709551616 * t0.2.toNat = _ at h0
  change t1.1.toNat + 18446744073709551616 * t1.2.toNat = _ at h1
  change t2.1.toNat + 18446744073709551616 * t2.2.toNat = _ at h2
  change t3.1.toNat + 18446744073709551616 * t3.2.toNat = _ at h3
  change t4.1.toNat + 18446744073709551616 * t4.2.toNat = _ at h4
  change t5.1.toNat + 18446744073709551616 * t5.2.toNat = _ at h5
  change (⟨t0.1, t1.1, t2.1, t3.1, t4.1, t5.1⟩ : Limbs384).toNat + 2 ^ 384 * t5.2.toNat = _
  dsimp only [Limbs384.toNat]
  omega

def subCarry384 (a b : Limbs384) : Limbs384 × BitVec 64 :=
  let t0 := wordAddCarryHOL a.l0 (~~~b.l0) 1
  let t1 := wordAddCarryHOL a.l1 (~~~b.l1) t0.2
  let t2 := wordAddCarryHOL a.l2 (~~~b.l2) t1.2
  let t3 := wordAddCarryHOL a.l3 (~~~b.l3) t2.2
  let t4 := wordAddCarryHOL a.l4 (~~~b.l4) t3.2
  let t5 := wordAddCarryHOL a.l5 (~~~b.l5) t4.2
  (⟨t0.1, t1.1, t2.1, t3.1, t4.1, t5.1⟩, t5.2)

theorem subCarry384_bit (a b : Limbs384) :
    (subCarry384 a b).2 = 0 ∨ (subCarry384 a b).2 = 1 := wordAddCarry_bit _ _ _

theorem subCarry384_conserve (a b : Limbs384) :
    (subCarry384 a b).1.toNat + 2 ^ 384 * (subCarry384 a b).2.toNat = a.toNat + 2 ^ 384 - b.toNat := by
  let t0 := wordAddCarryHOL a.l0 (~~~b.l0) 1
  let t1 := wordAddCarryHOL a.l1 (~~~b.l1) t0.2
  let t2 := wordAddCarryHOL a.l2 (~~~b.l2) t1.2
  let t3 := wordAddCarryHOL a.l3 (~~~b.l3) t2.2
  let t4 := wordAddCarryHOL a.l4 (~~~b.l4) t3.2
  let t5 := wordAddCarryHOL a.l5 (~~~b.l5) t4.2
  have h0 := bls_wordAddCarry_conserve a.l0 (~~~b.l0) 1
  have h1 := bls_wordAddCarry_conserve a.l1 (~~~b.l1) t0.2
  have h2 := bls_wordAddCarry_conserve a.l2 (~~~b.l2) t1.2
  have h3 := bls_wordAddCarry_conserve a.l3 (~~~b.l3) t2.2
  have h4 := bls_wordAddCarry_conserve a.l4 (~~~b.l4) t3.2
  have h5 := bls_wordAddCarry_conserve a.l5 (~~~b.l5) t4.2
  have hc0 : blsCarryInput (1 : BitVec 64) = 1 := by decide
  rw [hc0] at h0
  rw [show blsCarryInput t0.2 = t0.2.toNat from bls_wordAddCarry_carryInput _ _ _] at h1
  rw [show blsCarryInput t1.2 = t1.2.toNat from bls_wordAddCarry_carryInput _ _ _] at h2
  rw [show blsCarryInput t2.2 = t2.2.toNat from bls_wordAddCarry_carryInput _ _ _] at h3
  rw [show blsCarryInput t3.2 = t3.2.toNat from bls_wordAddCarry_carryInput _ _ _] at h4
  rw [show blsCarryInput t4.2 = t4.2.toNat from bls_wordAddCarry_carryInput _ _ _] at h5
  change t0.1.toNat + 18446744073709551616 * t0.2.toNat = _ at h0
  change t1.1.toNat + 18446744073709551616 * t1.2.toNat = _ at h1
  change t2.1.toNat + 18446744073709551616 * t2.2.toNat = _ at h2
  change t3.1.toNat + 18446744073709551616 * t3.2.toNat = _ at h3
  change t4.1.toNat + 18446744073709551616 * t4.2.toNat = _ at h4
  change t5.1.toNat + 18446744073709551616 * t5.2.toNat = _ at h5
  change (⟨t0.1, t1.1, t2.1, t3.1, t4.1, t5.1⟩ : Limbs384).toNat + 2 ^ 384 * t5.2.toNat = _
  dsimp only [Limbs384.toNat]
  simp only [BitVec.toNat_not] at h0 h1 h2 h3 h4 h5
  have hb0 := b.l0.isLt
  have hb1 := b.l1.isLt
  have hb2 := b.l2.isLt
  have hb3 := b.l3.isLt
  have hb4 := b.l4.isLt
  have hb5 := b.l5.isLt
  omega

theorem subCarry384_no_borrow (a b : Limbs384) (h : b.toNat ≤ a.toNat) :
    (subCarry384 a b).1.toNat = a.toNat - b.toNat := by
  have hc := subCarry384_conserve a b
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hr := (subCarry384 a b).1.toNat_lt
  rcases subCarry384_bit a b with hz | ho
  · rw [hz] at hc
    have he : (0 : BitVec 64).toNat = 0 := by decide
    rw [he] at hc
    omega
  · rw [ho] at hc
    have he : (1 : BitVec 64).toNat = 1 := by decide
    rw [he] at hc
    omega


theorem inverseRank_limbs384_le (u v : Limbs384) : inverseRank u.toNat v.toNat ≤ 1537 :=
  Nat.le_trans (inverseRank_384_le u.toNat_lt v.toNat_lt) (by omega)

theorem tightInverseRank_limbs384_le (u v : Limbs384) : tightInverseRank u.toNat v.toNat ≤ 769 :=
  tightInverseRank_384_le u.toNat_lt v.toNat_lt
end InitECandidate.Solver.Wave8GuestInv.Arith
