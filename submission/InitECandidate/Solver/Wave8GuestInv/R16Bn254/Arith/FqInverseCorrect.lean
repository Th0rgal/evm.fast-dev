import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulCalls
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryInverseAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem fqInverseAdjustment_lt : fqInverseAdjustment.toNat < fqModulus.toNat := by
  rw [fqInverseAdjustment_eq]
  exact Nat.mod_lt _ (Nat.lt_trans (by decide) fqModulus_gt_one)

theorem fqInverseAdjustment_modEq :
    Nat.ModEq fqModulus.toNat fqInverseAdjustment.toNat (2 ^ 256 * 2 ^ 256 * 2 ^ 256) := by
  have hp : (2 ^ 256 : Nat) * 2 ^ 256 * 2 ^ 256 = 2 ^ 768 := by norm_num
  change fqInverseAdjustment.toNat % fqModulus.toNat = (2 ^ 256 * 2 ^ 256 * 2 ^ 256) % fqModulus.toNat
  rw [fqInverseAdjustment_eq, hp, Nat.mod_mod]

/-- Whole-source fq_inv value correctness. A successful return for nonzero
input is canonical and is its Montgomery inverse. No primality assumption is
needed: unsuccessful noninvertible cases do not satisfy the execution premise. -/
theorem fqInverse_returned_correct {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue) (ha0 : a.toNat ≠ 0)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_fq_inv) =
      (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (a.toNat * out.toNat) (2 ^ 256 * 2 ^ 256) := by
  obtain ⟨x, resumed, inner, hx, hinv, hlocals, hcode, htail⟩ :=
    fqInverse_returned_prefix a ret hc ha ha0 hr
  have hi : resumed.locals.lookup (ofString "i") = some x.toValue := by
    simp [hlocals, HolFiniteMapExact.lookup_update, FUPDATE]
  unfold fqInverseTail at htail
  obtain ⟨out, hret, hbound, hmul⟩ := fqMul_tailCall_returned (s := resumed)
    _ x fqInverseAdjustment ret (hcode.trans hc) fqInverseAdjustment_lt
    (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hi,
      limbs256ConstExpr, Limbs256.toValue]) htail
  have hinv' : Nat.ModEq fqModulus.toNat (a.toNat * x.toNat) 1 := by
    change (a.toNat * x.toNat) % fqModulus.toNat = 1 % fqModulus.toNat
    simpa only [Nat.mod_eq_of_lt fqModulus_gt_one] using hinv
  exact ⟨out, hret, hbound, montInverse_adjust fqModulus.toNat (2 ^ 256)
    a.toNat x.toNat fqInverseAdjustment.toNat out.toNat fqRadix_coprime hinv'
    fqInverseAdjustment_modEq hmul⟩

/-- A value satisfying the Montgomery inverse congruence cannot be zero. -/
theorem fqMontInverse_ne_zero (a inverse : Nat)
    (h : Nat.ModEq fqModulus.toNat (a * inverse) (2 ^ 256 * 2 ^ 256)) : inverse ≠ 0 := by
  have hradix : (2 ^ 256 * 2 ^ 256) % fqModulus.toNat ≠ 0 := by decide
  intro hz
  change (a * inverse) % fqModulus.toNat = (2 ^ 256 * 2 ^ 256) % fqModulus.toNat at h
  rw [hz, Nat.mul_zero, Nat.zero_mod] at h
  exact hradix h.symm

end InitECandidate.Solver.Wave8GuestInv.Arith
