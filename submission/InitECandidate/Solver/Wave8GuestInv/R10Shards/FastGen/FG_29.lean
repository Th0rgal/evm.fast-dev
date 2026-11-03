import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_06
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_12
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_13
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_14
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_15
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_22
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_23
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_24
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_26
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_28

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FastGen

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestBoundBlockTxBal
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.FastGen

local syntax "fg_auto" : tactic
local macro_rules
  | `(tactic| fg_auto) => `(tactic| fg_step_auto)

local syntax "fg_auto_loops" : tactic
local macro_rules
  | `(tactic| fg_auto_loops) => `(tactic| fg_step_loops)

local syntax "fg_prove " num ident ident : tactic
local macro_rules
  | `(tactic| fg_prove $idx $fn $k) => `(tactic|
      (fg_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fg_auto
       · fg_arith $k))

theorem fb_g2_mul :
    TerminatingFunBoundedOn GuestInv (ofString "g2_mul") K.g2_mul := by
  have _ := fb_g2_set_inf
  have _ := fb_g2_double
  have _ := fb_g2_add
  have _ := fb_g2_copy
  fg_unfold 776 Guest.Software.guestFn_g2_mul
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_down_unsigned_guestInv (ofString "i")
      · fg_auto
      · refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.sub_one _
  · fg_arith K.g2_mul

theorem fb_secp256k1_recover_of
    (h_ec_mul2 : TerminatingFunBoundedOn GuestInv (ofString "ec_mul2") K.ec_mul2)
    (h_ec_to_affine : TerminatingFunBoundedOn GuestInv (ofString "ec_to_affine") K.ec_to_affine)
    (h_fn_inv : TerminatingFunBoundedOn GuestInv (ofString "fn_inv") K.fn_inv)
    (h_fn_mul : TerminatingFunBoundedOn GuestInv (ofString "fn_mul") K.fn_mul)
    (h_secp256k1_decompress_r : TerminatingFunBoundedOn GuestInv (ofString "secp256k1_decompress_r") K.secp256k1_decompress_r) :
    TerminatingFunBoundedOn GuestInv (ofString "secp256k1_recover") K.secp256k1_recover := by
  have _ := h_secp256k1_decompress_r
  have _ := h_fn_inv
  have _ := h_fn_mul
  have _ := h_ec_mul2
  have _ := h_ec_to_affine
  fg_prove 178 Guest.Software.guestFn_secp256k1_recover K.secp256k1_recover

theorem fb_ecp_add_of
    (h_ecp_double : TerminatingFunBoundedOn GuestInv (ofString "ecp_double") K.ecp_double)
    (h_fe_eq : TerminatingFunBoundedOn GuestInv (ofString "fe_eq") K.fe_eq)
    (h_fe_mul : TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.fe_mul)
    (h_fe_mul_small : TerminatingFunBoundedOn GuestInv (ofString "fe_mul_small") K.fe_mul_small)
    (h_fe_sqr : TerminatingFunBoundedOn GuestInv (ofString "fe_sqr") K.fe_sqr)
    (h_fe_sub : TerminatingFunBoundedOn GuestInv (ofString "fe_sub") K.fe_sub) :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_add") K.ecp_add := by
  have _ := fb_fe_is_zero
  have _ := h_fe_mul
  have _ := h_fe_eq
  have _ := h_ecp_double
  have _ := fb_ecp_set_inf
  have _ := h_fe_sub
  have _ := h_fe_sqr
  have _ := h_fe_mul_small
  fg_prove 674 Guest.Software.guestFn_ecp_add K.ecp_add

theorem fb_bls_g2_add_exec_of
    (h_g2_encode : TerminatingFunBoundedOn GuestInv (ofString "g2_encode") K.g2_encode) :
    TerminatingFunBoundedOn GuestInv (ofString "bls_g2_add_exec") K.bls_g2_add_exec := by
  have _ := fb_g2_decode
  have _ := fb_g2_add
  have _ := h_g2_encode
  fg_prove 804 Guest.Software.guestFn_bls_g2_add_exec K.bls_g2_add_exec

theorem fb_g1_subgroup_check :
    TerminatingFunBoundedOn GuestInv (ofString "g1_subgroup_check") K.g1_subgroup_check := by
  have _ := fb_g1_mul
  have _ := fb_g1_is_inf
  fg_prove 769 Guest.Software.guestFn_g1_subgroup_check K.g1_subgroup_check

theorem fb_map_fp_to_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "map_fp_to_g1") K.map_fp_to_g1 := by
  have _ := fb_swu_g1
  have _ := fb_iso_map_g1
  have _ := fb_g1_mul
  fg_prove 791 Guest.Software.guestFn_map_fp_to_g1 K.map_fp_to_g1

theorem fb_fp12_final_exp_of
    (h_fp12_exp_x : TerminatingFunBoundedOn GuestInv (ofString "fp12_exp_x") K.fp12_exp_x)
    (h_fp12_inv : TerminatingFunBoundedOn GuestInv (ofString "fp12_inv") K.fp12_inv) :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_final_exp") K.fp12_final_exp := by
  have _ := h_fp12_inv
  have _ := fb_fp12_conj
  have _ := fb_fp12_mul
  have _ := fb_fp12_frob
  have _ := h_fp12_exp_x
  fg_prove 757 Guest.Software.guestFn_fp12_final_exp K.fp12_final_exp

theorem fb_g2_subgroup_check :
    TerminatingFunBoundedOn GuestInv (ofString "g2_subgroup_check") K.g2_subgroup_check := by
  have _ := fb_g2_mul
  have _ := fb_g2_is_inf
  fg_prove 781 Guest.Software.guestFn_g2_subgroup_check K.g2_subgroup_check

end InitECandidate.Solver.Wave8GuestInv.FastGen
