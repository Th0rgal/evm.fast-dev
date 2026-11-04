import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModHalfSemantics

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
attribute [local irreducible] wordAddCarryHOL addCarry256 subCarry256

/-- Carry-aware halving includes the bit beyond the four-word representation. -/
theorem carryHalf256_toNat (a : Limbs256) (carry : BitVec 64)
    (hc : carry = 0 ∨ carry = 1) :
    (carryHalf256 a carry).toNat = (a.toNat + 2 ^ 256 * carry.toNat) / 2 := by
  dsimp only [Limbs256.toNat, carryHalf256]
  rw [halfWord256_toNat, halfWord256_toNat, halfWord256_toNat, halfWord256_toNat]
  rcases hc with rfl | rfl <;>
    simp only [show (0 : BitVec 64).toNat = 0 by decide, show (1 : BitVec 64).toNat = 1 by decide] <;> omega

theorem carryHalfAdd256_toNat (a m : Limbs256) :
    (carryHalf256 (addCarry256 a m).1 (addCarry256 a m).2).toNat = (a.toNat + m.toNat) / 2 := by
  rw [carryHalf256_toNat _ _ (addCarry256_bit a m), addCarry256_conserve]

/-- The numeric result of the two mod_half source branches. -/
def modHalf256 (a m : Limbs256) : Limbs256 :=
  if a.toNat % 2 = 0 then half256 a else carryHalf256 (addCarry256 a m).1 (addCarry256 a m).2

theorem modHalf256_toNat (a m : Limbs256) :
    (modHalf256 a m).toNat = if a.toNat % 2 = 0 then a.toNat / 2 else (a.toNat + m.toNat) / 2 := by
  unfold modHalf256
  split <;> simp only [half256_toNat, carryHalfAdd256_toNat]

theorem modHalf256_double (a m : Limbs256) (hm : m.toNat % 2 = 1) :
    2 * (modHalf256 a m).toNat = if a.toNat % 2 = 0 then a.toNat else a.toNat + m.toNat := by
  rw [modHalf256_toNat]
  split <;> omega

theorem modHalf256_lt_modulus (a m : Limbs256) (ha : a.toNat < m.toNat) :
    (modHalf256 a m).toNat < m.toNat := by
  rw [modHalf256_toNat]
  split <;> omega

theorem modHalf256_double_mod (a m : Limbs256) (hm : m.toNat % 2 = 1) :
    (2 * (modHalf256 a m).toNat) % m.toNat = a.toNat % m.toNat := by
  rw [modHalf256_double a m hm]
  split <;> simp

/-- The source's subtract-with-conditional-modulus-addition arithmetic. -/
def modSub256 (a b m : Limbs256) : Limbs256 :=
  if a.toNat < b.toNat then (addCarry256 (subCarry256 a b).1 m).1 else (subCarry256 a b).1

theorem modSub256_toNat (a b m : Limbs256)
    (ha : a.toNat < m.toNat) (hb : b.toNat < m.toNat) :
    (modSub256 a b m).toNat = if a.toNat < b.toNat then a.toNat + m.toNat - b.toNat else a.toNat - b.toNat := by
  unfold modSub256
  split
  · rename_i hlt
    have hs := subCarry256_conserve a b
    have ht := addCarry256_conserve (subCarry256 a b).1 m
    have has := a.toNat_lt
    have hbs := b.toNat_lt
    have hms := m.toNat_lt
    have hrs := (subCarry256 a b).1.toNat_lt
    have hrt := (addCarry256 (subCarry256 a b).1 m).1.toNat_lt
    rcases subCarry256_bit a b with hsc | hsc <;>
      rcases addCarry256_bit (subCarry256 a b).1 m with htc | htc <;>
      rw [hsc] at hs <;> rw [htc] at ht <;>
      norm_num only [BitVec.toNat_ofNat] at hs ht <;> omega
  · rename_i hge
    exact subCarry256_no_borrow a b (by omega)

theorem modSub256_add (a b m : Limbs256)
    (ha : a.toNat < m.toNat) (hb : b.toNat < m.toNat) :
    (modSub256 a b m).toNat + b.toNat =
      if a.toNat < b.toNat then a.toNat + m.toNat else a.toNat := by
  rw [modSub256_toNat a b m ha hb]
  split <;> omega

theorem modSub256_lt_modulus (a b m : Limbs256)
    (ha : a.toNat < m.toNat) (hb : b.toNat < m.toNat) :
    (modSub256 a b m).toNat < m.toNat := by
  rw [modSub256_toNat a b m ha hb]
  split <;> omega

theorem modSub256_add_mod (a b m : Limbs256)
    (ha : a.toNat < m.toNat) (hb : b.toNat < m.toNat) :
    ((modSub256 a b m).toNat + b.toNat) % m.toNat = a.toNat % m.toNat := by
  rw [modSub256_add a b m ha hb]
  split <;> simp

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
