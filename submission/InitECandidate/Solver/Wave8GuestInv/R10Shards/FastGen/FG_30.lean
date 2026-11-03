import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_03
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_04
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_06
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_07
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_10
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_12
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_19
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_20
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_22
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_23
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_25
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_26
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_28
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_29

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

theorem fb_map_fp2_to_g2 :
    TerminatingFunBoundedOn GuestInv (ofString "map_fp2_to_g2") K.map_fp2_to_g2 := by
  have _ := fb_swu_g2
  have _ := fb_iso_map_g2
  have _ := fb_g2_mul
  fg_prove 796 Guest.Software.guestFn_map_fp2_to_g2 K.map_fp2_to_g2

theorem fb_secp256k1_ecrecover_of
    (h_secp256k1_recover : TerminatingFunBoundedOn GuestInv (ofString "secp256k1_recover") K.secp256k1_recover) :
    TerminatingFunBoundedOn GuestInv (ofString "secp256k1_ecrecover") K.secp256k1_ecrecover := by
  have _ := h_secp256k1_recover
  have _ := fb_secp256k1_address_of_point
  fg_prove 180 Guest.Software.guestFn_secp256k1_ecrecover K.secp256k1_ecrecover

theorem fb_bn254_g1_add_of
    (h_bn254_g1_to_bytes : TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_to_bytes") K.bn254_g1_to_bytes)
    (h_ecp_add : TerminatingFunBoundedOn GuestInv (ofString "ecp_add") K.ecp_add) :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_add") K.bn254_g1_add := by
  have _ := fb_bn254_parse_g1
  have _ := h_ecp_add
  have _ := h_bn254_g1_to_bytes
  fg_prove 689 Guest.Software.guestFn_bn254_g1_add K.bn254_g1_add

theorem fb_kzg_load_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "kzg_load_g1") K.kzg_load_g1 := by
  have _ := fb_is_zero_bytes
  have _ := fb_g1_set_inf
  have _ := fb_kzg_decompress_g1
  have _ := fb_g1_is_inf
  have _ := fb_g1_subgroup_check
  fg_prove 798 Guest.Software.guestFn_kzg_load_g1 K.kzg_load_g1

theorem fb_bls_map_fp_to_g1_exec_of
    (h_g1_encode : TerminatingFunBoundedOn GuestInv (ofString "g1_encode") K.g1_encode) :
    TerminatingFunBoundedOn GuestInv (ofString "bls_map_fp_to_g1_exec") K.bls_map_fp_to_g1_exec := by
  have _ := fb_bls_fp_decode64
  have _ := fb_map_fp_to_g1
  have _ := h_g1_encode
  fg_prove 807 Guest.Software.guestFn_bls_map_fp_to_g1_exec K.bls_map_fp_to_g1_exec

theorem fb_kzg_verify_of
    (h_fp12_final_exp : TerminatingFunBoundedOn GuestInv (ofString "fp12_final_exp") K.fp12_final_exp)
    (h_fp12_is_one : TerminatingFunBoundedOn GuestInv (ofString "fp12_is_one") K.fp12_is_one)
    (h_pair_accumulate : TerminatingFunBoundedOn GuestInv (ofString "pair_accumulate") K.pair_accumulate) :
    TerminatingFunBoundedOn GuestInv (ofString "kzg_verify") K.kzg_verify := by
  have _ := fb_fp2_copy
  have _ := fb_fp2_set_one
  have _ := fb_kzg_neg_scalar
  have _ := fb_g2_mul
  have _ := fb_g2_add
  have _ := fb_g1_mul
  have _ := fb_g1_add
  have _ := fb_g2_neg
  have _ := fb_fp12_set_one
  have _ := h_pair_accumulate
  have _ := h_fp12_final_exp
  have _ := h_fp12_is_one
  fg_prove 800 Guest.Software.guestFn_kzg_verify K.kzg_verify

theorem fb_bls_map_fp2_to_g2_exec_of
    (h_g2_encode : TerminatingFunBoundedOn GuestInv (ofString "g2_encode") K.g2_encode) :
    TerminatingFunBoundedOn GuestInv (ofString "bls_map_fp2_to_g2_exec") K.bls_map_fp2_to_g2_exec := by
  have _ := fb_bls_fp_decode64
  have _ := fb_map_fp2_to_g2
  have _ := h_g2_encode
  fg_prove 808 Guest.Software.guestFn_bls_map_fp2_to_g2_exec K.bls_map_fp2_to_g2_exec

theorem fb_kzg_point_evaluation_exec_of
    (h_kzg_verify : TerminatingFunBoundedOn GuestInv (ofString "kzg_verify") K.kzg_verify)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.memeq) :
    TerminatingFunBoundedOn GuestInv (ofString "kzg_point_evaluation_exec") K.kzg_point_evaluation_exec := by
  have _ := h_memeq
  have _ := fb_kzg_load_g1
  have _ := h_kzg_verify
  fg_prove 809 Guest.Software.guestFn_kzg_point_evaluation_exec K.kzg_point_evaluation_exec

end InitECandidate.Solver.Wave8GuestInv.FastGen
