import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_05
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_06
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_09
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_13
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_14
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_15
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_16

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

theorem fb_bn254_g1_to_bytes_of
    (h_fq_inv : TerminatingFunBoundedOn GuestInv (ofString "fq_inv") K.fq_inv) :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_to_bytes") K.bn254_g1_to_bytes := by
  have _ := h_fq_inv
  have _ := fb_fq_mul
  have _ := fb_fq_from_mont
  fg_prove 688 Guest.Software.guestFn_bn254_g1_to_bytes K.bn254_g1_to_bytes

theorem fb_bn254_parse_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_parse_g1") K.bn254_parse_g1 := by
  have _ := fb_ecp_set_inf
  have _ := fb_fq_to_mont
  have _ := fb_fq_mul
  have _ := fb_fq_add
  fg_prove 686 Guest.Software.guestFn_bn254_parse_g1 K.bn254_parse_g1

theorem fb_bn254_parse_g2_of
    (h_fe_add : TerminatingFunBoundedOn GuestInv (ofString "fe_add") K.fe_add)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.memeq) :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_parse_g2") K.bn254_parse_g2 := by
  have _ := fb_is_zero_bytes
  have _ := fb_ecp_set_inf
  have _ := fb_fq_to_mont
  have _ := fb_fq2_mul
  have _ := h_fe_add
  have _ := h_memeq
  fg_prove 687 Guest.Software.guestFn_bn254_parse_g2 K.bn254_parse_g2

theorem fb_fe_mul_of
    (h_fq12_mul : TerminatingFunBoundedOn GuestInv (ofString "fq12_mul") K.fq12_mul) :
    TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.fe_mul := by
  have _ := fb_fq_mul
  have _ := fb_fq2_mul
  have _ := h_fq12_mul
  fg_prove 661 Guest.Software.guestFn_fe_mul K.fe_mul

theorem fb_decode_header_of
    (h_hdr_bytes_field : TerminatingFunBoundedOn GuestInv (ofString "hdr_bytes_field") K.hdr_bytes_field)
    (h_hdr_raw_field : TerminatingFunBoundedOn GuestInv (ofString "hdr_raw_field") K.hdr_raw_field)
    (h_hdr_u256_field : TerminatingFunBoundedOn GuestInv (ofString "hdr_u256_field") K.hdr_u256_field)
    (h_hdr_uint_field : TerminatingFunBoundedOn GuestInv (ofString "hdr_uint_field") K.hdr_uint_field)
    (h_hdr_word_field : TerminatingFunBoundedOn GuestInv (ofString "hdr_word_field") K.hdr_word_field)
    (h_rlp_decode_fully : TerminatingFunBoundedOn GuestInv (ofString "rlp_decode_fully") K.rlp_decode_fully)
    (h_rlp_list_to_slices : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_to_slices") K.rlp_list_to_slices) :
    TerminatingFunBoundedOn GuestInv (ofString "decode_header") K.decode_header := by
  have _ := h_rlp_decode_fully
  have _ := h_rlp_list_to_slices
  have _ := h_hdr_bytes_field
  have _ := h_hdr_u256_field
  have _ := h_hdr_word_field
  have _ := h_hdr_uint_field
  have _ := h_hdr_raw_field
  fg_prove 227 Guest.Software.guestFn_decode_header K.decode_header

theorem fb_ecp_is_inf :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_is_inf") K.ecp_is_inf := by
  have _ := fb_fe_is_zero
  fg_prove 672 Guest.Software.guestFn_ecp_is_inf K.ecp_is_inf

theorem fb_generic_call_of
    (h_credit_state_gas_refund : TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.credit_state_gas_refund)
    (h_frame_mem_mark : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_mark") K.frame_mem_mark)
    (h_scratch_mark : TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.scratch_mark)
    (h_set_retdata : TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.set_retdata)
    (h_start_child : TerminatingFunBoundedOn GuestInv (ofString "start_child") K.start_child) :
    TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.generic_call := by
  have _ := h_set_retdata
  have _ := h_credit_state_gas_refund
  have _ := h_scratch_mark
  have _ := h_frame_mem_mark
  have _ := fb_child_message
  have _ := h_start_child
  fg_prove 601 Guest.Software.guestFn_generic_call K.generic_call

theorem fb_p256_ec_add_affine_of
    (h_p256_ec_double : TerminatingFunBoundedOn GuestInv (ofString "p256_ec_double") K.p256_ec_double)
    (h_p256_fp_mul : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_mul") K.p256_fp_mul)
    (h_p256_fp_sqr : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_sqr") K.p256_fp_sqr) :
    TerminatingFunBoundedOn GuestInv (ofString "p256_ec_add_affine") K.p256_ec_add_affine := by
  have _ := fb_p256_set_affine
  have _ := h_p256_fp_sqr
  have _ := h_p256_fp_mul
  have _ := fb_p256_fp_add
  have _ := fb_p256_set_infinity
  have _ := h_p256_ec_double
  have _ := fb_p256_fp_sub
  fg_prove 640 Guest.Software.guestFn_p256_ec_add_affine K.p256_ec_add_affine

end InitECandidate.Solver.Wave8GuestInv.FastGen
