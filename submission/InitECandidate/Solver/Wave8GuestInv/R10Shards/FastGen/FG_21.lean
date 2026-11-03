import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_01
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_17

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

theorem fb_build_block_access_list_rlp
    (h_add_storage_read : TerminatingFunBoundedOn GuestInv (ofString "add_storage_read") K.add_storage_read)
    (h_add_touched_account : TerminatingFunBoundedOn GuestInv (ofString "add_touched_account") K.add_touched_account)
    (h_bal_encode_account : TerminatingFunBoundedOn GuestInv (ofString "bal_encode_account") K.bal_encode_account)
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.htab_get)
    (h_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.htab_item)
    (h_htab_keys : TerminatingFunBoundedOn GuestInv (ofString "htab_keys") K.htab_keys)
    (h_rlp_encode_list_header : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.rlp_encode_list_header)
    (h_rlp_list_header_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.rlp_list_header_len)
    (h_sort_elems : TerminatingFunBoundedOn GuestInv (ofString "sort_elems") K.sort_elems) :
    TerminatingFunBoundedOn GuestInv (ofString "build_block_access_list_rlp") K.build_block_access_list_rlp := by
  have _ := h_htab_item
  have _ := h_add_storage_read
  have _ := h_add_touched_account
  have _ := h_htab_keys
  have _ := h_sort_elems
  have _ := h_htab_get
  have _ := h_bal_encode_account
  have _ := h_rlp_list_header_len
  have _ := h_rlp_encode_list_header
  fg_unfold 433 Guest.Software.guestFn_build_block_access_list_rlp
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_counter_guestInv_step .less (Or.inl rfl) (ofString "i") (ofString "cap")
      · fg_auto
      · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
    · apply while_counter_guestInv_step .less (Or.inl rfl) (ofString "i") (ofString "cap")
      · fg_auto
      · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
    · apply while_up_exp_guestInv .less (Or.inl rfl) (ofString "i") _
      · fg_auto_loops
        · apply while_counter_guestInv_step .less (Or.inl rfl) (ofString "j") (ofString "scap")
          · fg_auto
          · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
          · rfl
          · rfl
        · apply while_counter_guestInv_step .less (Or.inl rfl) (ofString "j") (ofString "cn")
          · fg_auto
          · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
          · rfl
          · rfl
      · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
    · apply while_up_exp_guestInv .less (Or.inl rfl) (ofString "i") _
      · fg_auto
      · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
  · fg_arith K.build_block_access_list_rlp

theorem fb_decode_authorizations_of
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item)
    (h_rlp_list_to_slices : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_to_slices") K.rlp_list_to_slices)
    (h_tx_fixed_bytes : TerminatingFunBoundedOn GuestInv (ofString "tx_fixed_bytes") K.tx_fixed_bytes)
    (h_tx_scalar_u256 : TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_u256") K.tx_scalar_u256)
    (h_tx_scalar_word : TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_word") K.tx_scalar_word) :
    TerminatingFunBoundedOn GuestInv (ofString "decode_authorizations") K.decode_authorizations := by
  have _ := h_rlp_list_to_slices
  have _ := h_rlp_item
  have _ := h_tx_scalar_u256
  have _ := h_tx_fixed_bytes
  have _ := h_tx_scalar_word
  fg_unfold 305 Guest.Software.guestFn_decode_authorizations
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "i") _
      · fg_auto
      · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
  · fg_arith K.decode_authorizations

theorem fb_op_sdiv :
    TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.op_sdiv := by
  have _ := fb_u256_sdiv
  fg_prove 479 Guest.Software.guestFn_op_sdiv K.op_sdiv

theorem fb_ext_code_of_of
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.get_account)
    (h_get_code : TerminatingFunBoundedOn GuestInv (ofString "get_code") K.get_code) :
    TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.ext_code_of := by
  have _ := h_get_account
  have _ := h_get_code
  fg_prove 543 Guest.Software.guestFn_ext_code_of K.ext_code_of

theorem fb_fp6_add :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_add") K.fp6_add := by
  have _ := fb_fp2_add
  fg_prove 741 Guest.Software.guestFn_fp6_add K.fp6_add

theorem fb_bls_fp_encode64 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_encode64") K.bls_fp_encode64 := by
  have _ := fb_bls_fp_from_mont
  have _ := fb_bls_fp_to_be48
  fg_prove 720 Guest.Software.guestFn_bls_fp_encode64 K.bls_fp_encode64

theorem fb_bls_fp_is_high :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_is_high") K.bls_fp_is_high := by
  have _ := fb_bls_fp_from_mont
  have _ := fb_bls_fp_lt_raw
  fg_prove 716 Guest.Software.guestFn_bls_fp_is_high K.bls_fp_is_high

theorem fb_bls_fp_sgn0 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sgn0") K.bls_fp_sgn0 := by
  have _ := fb_bls_fp_from_mont
  fg_prove 715 Guest.Software.guestFn_bls_fp_sgn0 K.bls_fp_sgn0

end InitECandidate.Solver.Wave8GuestInv.FastGen
