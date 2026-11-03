import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_07
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_09
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_10

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

theorem fb_child_message :
    TerminatingFunBoundedOn GuestInv (ofString "child_message") K.child_message := by
  have _ := fb_msg_new_scratch
  fg_prove 594 Guest.Software.guestFn_child_message K.child_message

theorem fb_p256_on_curve_of
    (h_p256_fp_mul : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_mul") K.p256_fp_mul)
    (h_p256_fp_sqr : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_sqr") K.p256_fp_sqr) :
    TerminatingFunBoundedOn GuestInv (ofString "p256_on_curve") K.p256_on_curve := by
  have _ := h_p256_fp_sqr
  have _ := h_p256_fp_mul
  have _ := fb_p256_fp_add
  have _ := fb_p256_fp_sub
  fg_prove 643 Guest.Software.guestFn_p256_on_curve K.p256_on_curve

theorem fb_p256_ec_double_of
    (h_p256_fp_mul : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_mul") K.p256_fp_mul)
    (h_p256_fp_sqr : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_sqr") K.p256_fp_sqr) :
    TerminatingFunBoundedOn GuestInv (ofString "p256_ec_double") K.p256_ec_double := by
  have _ := fb_p256_set_infinity
  have _ := h_p256_fp_sqr
  have _ := h_p256_fp_mul
  have _ := fb_p256_fp_sub
  have _ := fb_p256_fp_add
  fg_prove 639 Guest.Software.guestFn_p256_ec_double K.p256_ec_double

theorem fb_ripemd160_block :
    TerminatingFunBoundedOn GuestInv (ofString "ripemd160_block") K.ripemd160_block := by
  have _ := fb_rmd_f
  have _ := fb_rmd_k
  have _ := fb_rmd_kp
  fg_unfold 616 Guest.Software.guestFn_ripemd160_block
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_signed_const_guestInv (ofString "i") 1#64 (BitVec.ofNat 64 16)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · decide
      · decide
    · apply while_up_signed_const_guestInv (ofString "j") 1#64 (BitVec.ofNat 64 80)
      · fg_auto
      · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · decide
      · decide
  · fg_arith K.ripemd160_block

theorem fb_bal_encode_account_of
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.htab_get)
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.htab_has)
    (h_htab_keys : TerminatingFunBoundedOn GuestInv (ofString "htab_keys") K.htab_keys)
    (h_rlp_encode_bytes : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.rlp_encode_bytes)
    (h_rlp_encode_list_header : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.rlp_encode_list_header)
    (h_rlp_encode_word : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.rlp_encode_word)
    (h_rlp_list_header_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.rlp_list_header_len)
    (h_rlp_put_u256 : TerminatingFunBoundedOn GuestInv (ofString "rlp_put_u256") K.rlp_put_u256)
    (h_sort_elems : TerminatingFunBoundedOn GuestInv (ofString "sort_elems") K.sort_elems)
    (h_sorted_keys32 : TerminatingFunBoundedOn GuestInv (ofString "sorted_keys32") K.sorted_keys32) :
    TerminatingFunBoundedOn GuestInv (ofString "bal_encode_account") K.bal_encode_account := by
  have _ := h_rlp_encode_bytes
  have _ := h_sorted_keys32
  have _ := h_htab_get
  have _ := h_sort_elems
  have _ := h_rlp_put_u256
  have _ := h_rlp_encode_word
  have _ := h_rlp_list_header_len
  have _ := h_rlp_encode_list_header
  have _ := h_htab_keys
  have _ := h_htab_has
  fg_unfold 432 Guest.Software.guestFn_bal_encode_account
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_exp_guestInv .less (Or.inl rfl) (ofString "i") _
      · fg_auto_loops
        · apply while_counter_guestInv_step .less (Or.inl rfl) (ofString "j") (ofString "n")
          · fg_auto
          · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
          · rfl
          · rfl
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
    · apply while_up_exp_guestInv .less (Or.inl rfl) (ofString "i") _
      · fg_auto
      · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
    · apply while_counter_guestInv_step .less (Or.inl rfl) (ofString "i") (ofString "kept")
      · fg_auto
      · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
    · apply while_counter_guestInv_step .less (Or.inl rfl) (ofString "i") (ofString "n2")
      · fg_auto
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
    · apply while_counter_guestInv_step .less (Or.inl rfl) (ofString "i") (ofString "n3")
      · fg_auto
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
    · apply while_counter_guestInv_step .less (Or.inl rfl) (ofString "i") (ofString "n4")
      · fg_auto
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
  · fg_arith K.bal_encode_account

theorem fb_decode_blob_hashes_of
    (h_rlp_list_to_slices : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_to_slices") K.rlp_list_to_slices)
    (h_tx_fixed_bytes : TerminatingFunBoundedOn GuestInv (ofString "tx_fixed_bytes") K.tx_fixed_bytes) :
    TerminatingFunBoundedOn GuestInv (ofString "decode_blob_hashes") K.decode_blob_hashes := by
  have _ := h_rlp_list_to_slices
  have _ := h_tx_fixed_bytes
  fg_unfold 304 Guest.Software.guestFn_decode_blob_hashes
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "i") _
      · fg_auto
      · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
  · fg_arith K.decode_blob_hashes

theorem fb_decode_access_list_of
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item)
    (h_rlp_list_to_slices : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_to_slices") K.rlp_list_to_slices)
    (h_tx_fixed_bytes : TerminatingFunBoundedOn GuestInv (ofString "tx_fixed_bytes") K.tx_fixed_bytes)
    (h_tx_list_item : TerminatingFunBoundedOn GuestInv (ofString "tx_list_item") K.tx_list_item) :
    TerminatingFunBoundedOn GuestInv (ofString "decode_access_list") K.decode_access_list := by
  have _ := h_rlp_list_to_slices
  have _ := h_rlp_item
  have _ := h_tx_fixed_bytes
  have _ := h_tx_list_item
  fg_unfold 303 Guest.Software.guestFn_decode_access_list
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "i") _
      · fg_auto_loops
        · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "j") _
          · fg_auto
          · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
          · rfl
      · refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
  · fg_arith K.decode_access_list

theorem fb_tx_encode_generic_of
    (h_rlp_encode_bytes : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.rlp_encode_bytes)
    (h_rlp_encode_list_header : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.rlp_encode_list_header)
    (h_rlp_encode_word : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.rlp_encode_word)
    (h_rlp_list_header_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.rlp_list_header_len)
    (h_tx_encode_bound : TerminatingFunBoundedOn GuestInv (ofString "tx_encode_bound") K.tx_encode_bound)
    (h_tx_put_access_list : TerminatingFunBoundedOn GuestInv (ofString "tx_put_access_list") K.tx_put_access_list)
    (h_tx_put_authorizations : TerminatingFunBoundedOn GuestInv (ofString "tx_put_authorizations") K.tx_put_authorizations)
    (h_tx_put_blob_hashes : TerminatingFunBoundedOn GuestInv (ofString "tx_put_blob_hashes") K.tx_put_blob_hashes)
    (h_tx_put_to : TerminatingFunBoundedOn GuestInv (ofString "tx_put_to") K.tx_put_to)
    (h_tx_put_u256 : TerminatingFunBoundedOn GuestInv (ofString "tx_put_u256") K.tx_put_u256) :
    TerminatingFunBoundedOn GuestInv (ofString "tx_encode_generic") K.tx_encode_generic := by
  have _ := h_tx_encode_bound
  have _ := h_rlp_encode_word
  have _ := h_tx_put_u256
  have _ := h_tx_put_to
  have _ := h_rlp_encode_bytes
  have _ := h_tx_put_access_list
  have _ := h_tx_put_blob_hashes
  have _ := h_tx_put_authorizations
  have _ := h_rlp_list_header_len
  have _ := h_rlp_encode_list_header
  fg_prove 328 Guest.Software.guestFn_tx_encode_generic K.tx_encode_generic

end InitECandidate.Solver.Wave8GuestInv.FastGen
