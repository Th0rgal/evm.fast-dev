import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.Straight

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 800000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Four little-endian machine words, with no modular-normalization assumption. -/
structure Limbs256 where
  l0 : BitVec 64
  l1 : BitVec 64
  l2 : BitVec 64
  l3 : BitVec 64

def Limbs256.toNat (a : Limbs256) : Nat :=
  a.l0.toNat + 18446744073709551616 * a.l1.toNat +
    340282366920938463463374607431768211456 * a.l2.toNat +
    6277101735386680763835789423207666416102355444464034512896 * a.l3.toNat

def Limbs256.toValue (a : Limbs256) : ValueHOL 64 :=
  .rStruct [.val (.word a.l0), .val (.word a.l1), .val (.word a.l2), .val (.word a.l3)]

theorem Limbs256.toNat_lt (a : Limbs256) : a.toNat < 2 ^ 256 := by
  have h0 := a.l0.isLt
  have h1 := a.l1.isLt
  have h2 := a.l2.isLt
  have h3 := a.l3.isLt
  dsimp only [Limbs256.toNat]
  omega

private def carryInput (c : BitVec 64) : Nat := if c == 0 then 0 else 1

theorem wordAddCarry_conserve (a b c : BitVec 64) :
    (wordAddCarryHOL a b c).1.toNat + 18446744073709551616 * (wordAddCarryHOL a b c).2.toNat =
      a.toNat + b.toNat + carryInput c := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [wordAddCarryHOL, carryInput]
  split_ifs <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem wordAddCarry_bit (a b c : BitVec 64) :
    (wordAddCarryHOL a b c).2 = 0 ∨ (wordAddCarryHOL a b c).2 = 1 := by
  unfold wordAddCarryHOL
  split_ifs <;> simp <;> omega

private theorem wordAddCarry_carryInput (a b c : BitVec 64) :
    carryInput (wordAddCarryHOL a b c).2 = (wordAddCarryHOL a b c).2.toNat := by
  rcases wordAddCarry_bit a b c with h | h <;> rw [h] <;> decide

attribute [local irreducible] wordAddCarryHOL

/-- The exact chain of four source `wordAddCarryHOL` primitives. -/
def addCarry256 (a b : Limbs256) : Limbs256 × BitVec 64 :=
  let t0 := wordAddCarryHOL a.l0 b.l0 0
  let t1 := wordAddCarryHOL a.l1 b.l1 t0.2
  let t2 := wordAddCarryHOL a.l2 b.l2 t1.2
  let t3 := wordAddCarryHOL a.l3 b.l3 t2.2
  (⟨t0.1, t1.1, t2.1, t3.1⟩, t3.2)

theorem addCarry256_bit (a b : Limbs256) :
    (addCarry256 a b).2 = 0 ∨ (addCarry256 a b).2 = 1 :=
  wordAddCarry_bit _ _ _

theorem addCarry256_conserve (a b : Limbs256) :
    (addCarry256 a b).1.toNat + 2 ^ 256 * (addCarry256 a b).2.toNat = a.toNat + b.toNat := by
  let t0 := wordAddCarryHOL a.l0 b.l0 0
  let t1 := wordAddCarryHOL a.l1 b.l1 t0.2
  let t2 := wordAddCarryHOL a.l2 b.l2 t1.2
  let t3 := wordAddCarryHOL a.l3 b.l3 t2.2
  have h0 := wordAddCarry_conserve a.l0 b.l0 0
  have h1 := wordAddCarry_conserve a.l1 b.l1 t0.2
  have h2 := wordAddCarry_conserve a.l2 b.l2 t1.2
  have h3 := wordAddCarry_conserve a.l3 b.l3 t2.2
  have hc0 : carryInput (0 : BitVec 64) = 0 := by decide
  rw [hc0] at h0
  rw [show carryInput t0.2 = t0.2.toNat from wordAddCarry_carryInput _ _ _] at h1
  rw [show carryInput t1.2 = t1.2.toNat from wordAddCarry_carryInput _ _ _] at h2
  rw [show carryInput t2.2 = t2.2.toNat from wordAddCarry_carryInput _ _ _] at h3
  change t0.1.toNat + 18446744073709551616 * t0.2.toNat = _ at h0
  change t1.1.toNat + 18446744073709551616 * t1.2.toNat = _ at h1
  change t2.1.toNat + 18446744073709551616 * t2.2.toNat = _ at h2
  change t3.1.toNat + 18446744073709551616 * t3.2.toNat = _ at h3
  change (⟨t0.1, t1.1, t2.1, t3.1⟩ : Limbs256).toNat + 2 ^ 256 * t3.2.toNat = _
  dsimp only [Limbs256.toNat]
  omega

def p256Modulus : Limbs256 :=
  ⟨18446744073709551615, 4294967295, 0, 18446744069414584321⟩

theorem p256Modulus_large : 2 ^ 255 ≤ p256Modulus.toNat := by decide

theorem p256_add_no_carry_next (r : Limbs256) (h : (addCarry256 r p256Modulus).2 = 0) :
    (addCarry256 (addCarry256 r p256Modulus).1 p256Modulus).2 = 1 := by
  have hfirst := addCarry256_conserve r p256Modulus
  have hsecond := addCarry256_conserve (addCarry256 r p256Modulus).1 p256Modulus
  have hsmall := ((addCarry256 (addCarry256 r p256Modulus).1 p256Modulus).1).toNat_lt
  have hlarge := p256Modulus_large
  rcases addCarry256_bit (addCarry256 r p256Modulus).1 p256Modulus with hz | ho
  · rw [h] at hfirst
    rw [hz] at hsecond
    have hzero : (0 : BitVec 64).toNat = 0 := by decide
    rw [hzero] at hfirst hsecond
    omega
  · exact ho

/-- The complemented-limb addition used by the source subtraction helper. -/
def subCarry256 (a b : Limbs256) : Limbs256 × BitVec 64 :=
  let t0 := wordAddCarryHOL a.l0 (~~~b.l0) 1
  let t1 := wordAddCarryHOL a.l1 (~~~b.l1) t0.2
  let t2 := wordAddCarryHOL a.l2 (~~~b.l2) t1.2
  let t3 := wordAddCarryHOL a.l3 (~~~b.l3) t2.2
  (⟨t0.1, t1.1, t2.1, t3.1⟩, t3.2)

theorem subCarry256_bit (a b : Limbs256) :
    (subCarry256 a b).2 = 0 ∨ (subCarry256 a b).2 = 1 :=
  wordAddCarry_bit _ _ _

theorem subCarry256_conserve (a b : Limbs256) :
    (subCarry256 a b).1.toNat + 2 ^ 256 * (subCarry256 a b).2.toNat = a.toNat + 2 ^ 256 - b.toNat := by
  let t0 := wordAddCarryHOL a.l0 (~~~b.l0) 1
  let t1 := wordAddCarryHOL a.l1 (~~~b.l1) t0.2
  let t2 := wordAddCarryHOL a.l2 (~~~b.l2) t1.2
  let t3 := wordAddCarryHOL a.l3 (~~~b.l3) t2.2
  have h0 := wordAddCarry_conserve a.l0 (~~~b.l0) 1
  have h1 := wordAddCarry_conserve a.l1 (~~~b.l1) t0.2
  have h2 := wordAddCarry_conserve a.l2 (~~~b.l2) t1.2
  have h3 := wordAddCarry_conserve a.l3 (~~~b.l3) t2.2
  have hc0 : carryInput (1 : BitVec 64) = 1 := by decide
  rw [hc0] at h0
  rw [show carryInput t0.2 = t0.2.toNat from wordAddCarry_carryInput _ _ _] at h1
  rw [show carryInput t1.2 = t1.2.toNat from wordAddCarry_carryInput _ _ _] at h2
  rw [show carryInput t2.2 = t2.2.toNat from wordAddCarry_carryInput _ _ _] at h3
  change t0.1.toNat + 18446744073709551616 * t0.2.toNat = _ at h0
  change t1.1.toNat + 18446744073709551616 * t1.2.toNat = _ at h1
  change t2.1.toNat + 18446744073709551616 * t2.2.toNat = _ at h2
  change t3.1.toNat + 18446744073709551616 * t3.2.toNat = _ at h3
  change (⟨t0.1, t1.1, t2.1, t3.1⟩ : Limbs256).toNat + 2 ^ 256 * t3.2.toNat = _
  dsimp only [Limbs256.toNat]
  simp only [BitVec.toNat_not] at h0 h1 h2 h3
  have hb0 := b.l0.isLt
  have hb1 := b.l1.isLt
  have hb2 := b.l2.isLt
  have hb3 := b.l3.isLt
  omega

theorem subCarry256_no_borrow (a b : Limbs256) (h : b.toNat ≤ a.toNat) :
    (subCarry256 a b).1.toNat = a.toNat - b.toNat := by
  have hc := subCarry256_conserve a b
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hr := (subCarry256 a b).1.toNat_lt
  rcases subCarry256_bit a b with hz | ho
  · rw [hz] at hc
    have he : (0 : BitVec 64).toNat = 0 := by decide
    rw [he] at hc
    omega
  · rw [ho] at hc
    have he : (1 : BitVec 64).toNat = 1 := by decide
    rw [he] at hc
    omega

theorem p256_sub_no_borrow_next (r : Limbs256) (h : p256Modulus.toNat ≤ r.toNat) :
    (subCarry256 r p256Modulus).1.toNat < p256Modulus.toNat := by
  rw [subCarry256_no_borrow r p256Modulus h]
  have hr := r.toNat_lt
  have hp := p256Modulus_large
  omega

/-- A stalled carry step consumes the phase bit; a carry step reduces distance. -/
def negativeCarryRank (distance : Nat) (r : Limbs256) : Nat :=
  2 * distance + if (addCarry256 r p256Modulus).2 = 0 then 1 else 0

theorem negativeCarryRank_decreases (distance : Nat) (r : Limbs256)
    (hd : 0 < distance) :
    negativeCarryRank (distance - (addCarry256 r p256Modulus).2.toNat)
      (addCarry256 r p256Modulus).1 < negativeCarryRank distance r := by
  rcases addCarry256_bit r p256Modulus with hz | ho
  · have hn := p256_add_no_carry_next r hz
    simp [negativeCarryRank, hz, hn]
  · have hzero : (0 : BitVec 64).toNat = 0 := by decide
    have hone : (1 : BitVec 64).toNat = 1 := by decide
    unfold negativeCarryRank
    rw [ho, hone]
    split_ifs <;> simp_all <;> omega

def positiveCarryRank (distance : Nat) (r : Limbs256) : Nat :=
  2 * distance + if p256Modulus.toNat ≤ r.toNat then 1 else 0

theorem positiveCarryRank_decreases (distance : Nat) (r : Limbs256)
    (hd : 0 < distance) :
    positiveCarryRank (distance - if r.toNat < p256Modulus.toNat then 1 else 0)
      (subCarry256 r p256Modulus).1 < positiveCarryRank distance r := by
  by_cases h : p256Modulus.toNat ≤ r.toNat
  · have hn := p256_sub_no_borrow_next r h
    simp [positiveCarryRank, h, Nat.not_lt.mpr h, Nat.not_le.mpr hn]
  · unfold positiveCarryRank
    have hl : r.toNat < p256Modulus.toNat := Nat.lt_of_not_ge h
    rw [if_pos hl, if_neg h]
    split_ifs <;> omega

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
