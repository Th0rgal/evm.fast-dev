import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Composed

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.Arith

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

theorem ub_bls_fp_is_zero : TerminatingFunBounded (ofString "bls_fp_is_zero") K.«bls_fp_is_zero» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 697
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_fp_is_zero) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem ub_bls_fp_lt_raw : TerminatingFunBounded (ofString "bls_fp_lt_raw") K.«bls_fp_lt_raw» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 699
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_fp_lt_raw) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem ub_bls_fp_add_raw : TerminatingFunBounded (ofString "bls_fp_add_raw") K.«bls_fp_add_raw» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 700
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_fp_add_raw) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem ub_bls_fp_sub_raw : TerminatingFunBounded (ofString "bls_fp_sub_raw") K.«bls_fp_sub_raw» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 701
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_fp_sub_raw) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem ub_bls_fp_sub : TerminatingFunBounded (ofString "bls_fp_sub") K.«bls_fp_sub» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 703
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_fp_sub) rfl, ?_⟩
  exact (TerminatingProgBounded.decCall ub_bls_fp_sub_raw _ _ _ (TerminatingProgBounded.dec _ _ _ (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl) (TerminatingProgBounded.decCall ub_bls_fp_add_raw _ _ _ (TerminatingProgBounded.straight _ rfl)))))

theorem ub_bls_fp_shr1 : TerminatingFunBounded (ofString "bls_fp_shr1") K.«bls_fp_shr1» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 710
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_fp_shr1) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem ub_bls_fp_half_can : TerminatingFunBounded (ofString "bls_fp_half_can") K.«bls_fp_half_can» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 711
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_fp_half_can) rfl, ?_⟩
  exact (TerminatingProgBounded.seq (TerminatingProgBounded.ite (TerminatingProgBounded.tailCall ub_bls_fp_shr1 _) (TerminatingProgBounded.straight _ rfl)) (TerminatingProgBounded.decCall ub_bls_fp_add_raw _ _ _ (TerminatingProgBounded.straight _ rfl)))

end InitECandidate.Solver.Wave8GuestInv.Arith
