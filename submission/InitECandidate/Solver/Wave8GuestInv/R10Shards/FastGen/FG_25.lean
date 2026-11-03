import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_00
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_01
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_06
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_12
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_13
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_14
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_17
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_18
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_19
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_21
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_22

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

theorem fb_decode_transaction_rlp_of
    (h_decode_access_list : TerminatingFunBoundedOn GuestInv (ofString "decode_access_list") K.decode_access_list)
    (h_decode_authorizations : TerminatingFunBoundedOn GuestInv (ofString "decode_authorizations") K.decode_authorizations)
    (h_decode_blob_hashes : TerminatingFunBoundedOn GuestInv (ofString "decode_blob_hashes") K.decode_blob_hashes)
    (h_rlp_decode_fully : TerminatingFunBoundedOn GuestInv (ofString "rlp_decode_fully") K.rlp_decode_fully)
    (h_rlp_list_to_slices : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_to_slices") K.rlp_list_to_slices)
    (h_tx_bytes_item : TerminatingFunBoundedOn GuestInv (ofString "tx_bytes_item") K.tx_bytes_item)
    (h_tx_fixed_bytes : TerminatingFunBoundedOn GuestInv (ofString "tx_fixed_bytes") K.tx_fixed_bytes)
    (h_tx_list_item : TerminatingFunBoundedOn GuestInv (ofString "tx_list_item") K.tx_list_item)
    (h_tx_scalar_u256 : TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_u256") K.tx_scalar_u256)
    (h_tx_scalar_word : TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_word") K.tx_scalar_word)
    (h_tx_to_item : TerminatingFunBoundedOn GuestInv (ofString "tx_to_item") K.tx_to_item) :
    TerminatingFunBoundedOn GuestInv (ofString "decode_transaction_rlp") K.decode_transaction_rlp := by
  have _ := h_rlp_decode_fully
  have _ := h_rlp_list_to_slices
  have _ := h_tx_scalar_word
  have _ := h_tx_scalar_u256
  have _ := h_tx_fixed_bytes
  have _ := h_tx_to_item
  have _ := h_tx_bytes_item
  have _ := h_tx_list_item
  have _ := h_decode_access_list
  have _ := h_decode_blob_hashes
  have _ := h_decode_authorizations
  fg_prove 306 Guest.Software.guestFn_decode_transaction_rlp K.decode_transaction_rlp

theorem fb_calculate_delegation_cost_of
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.ext_code_of)
    (h_is_valid_delegation : TerminatingFunBoundedOn GuestInv (ofString "is_valid_delegation") K.is_valid_delegation)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.is_warm_address) :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.calculate_delegation_cost := by
  have _ := h_ext_code_of
  have _ := h_is_valid_delegation
  have _ := h_is_warm_address
  fg_prove 573 Guest.Software.guestFn_calculate_delegation_cost K.calculate_delegation_cost

theorem fb_kzg_decompress_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "kzg_decompress_g1") K.kzg_decompress_g1 := by
  have _ := fb_bls_fp_from_be48
  have _ := fb_bls_fp_is_zero
  have _ := fb_g1_set_inf
  have _ := fb_bls_fp_lt_raw
  have _ := fb_bls_fp_to_mont
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_pow
  have _ := fb_bls_fp_eq
  have _ := fb_bls_fp_is_high
  have _ := fb_bls_fp_neg
  fg_prove 797 Guest.Software.guestFn_kzg_decompress_g1 K.kzg_decompress_g1

theorem fb_fp2_sgn0 :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_sgn0") K.fp2_sgn0 := by
  have _ := fb_bls_fp_sgn0
  have _ := fb_bls_fp_is_zero
  fg_prove 737 Guest.Software.guestFn_fp2_sgn0 K.fp2_sgn0

theorem fb_g1_encode_of
    (h_g1_normalize : TerminatingFunBoundedOn GuestInv (ofString "g1_normalize") K.g1_normalize) :
    TerminatingFunBoundedOn GuestInv (ofString "g1_encode") K.g1_encode := by
  have _ := h_g1_normalize
  have _ := fb_bls_fp_encode64
  fg_prove 768 Guest.Software.guestFn_g1_encode K.g1_encode

theorem fb_fp6_inv_of
    (h_fp2_inv : TerminatingFunBoundedOn GuestInv (ofString "fp2_inv") K.fp2_inv) :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_inv") K.fp6_inv := by
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_fp2_mul_xi
  have _ := fb_fp2_sub
  have _ := fb_fp2_add
  have _ := h_fp2_inv
  fg_prove 746 Guest.Software.guestFn_fp6_inv K.fp6_inv

theorem fb_g2_normalize_of
    (h_fp2_inv : TerminatingFunBoundedOn GuestInv (ofString "fp2_inv") K.fp2_inv) :
    TerminatingFunBoundedOn GuestInv (ofString "g2_normalize") K.g2_normalize := by
  have _ := fb_g2_is_inf
  have _ := h_fp2_inv
  have _ := fb_fp2_mul
  fg_prove 777 Guest.Software.guestFn_g2_normalize K.g2_normalize

theorem fb_g1_add :
    TerminatingFunBoundedOn GuestInv (ofString "g1_add") K.g1_add := by
  have _ := fb_bls_fp_is_zero
  have _ := fb_g1_copy
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_eq
  have _ := fb_g1_double
  have _ := fb_g1_set_inf
  have _ := fb_bls_fp_sub
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_add
  fg_prove 763 Guest.Software.guestFn_g1_add K.g1_add

end InitECandidate.Solver.Wave8GuestInv.FastGen
