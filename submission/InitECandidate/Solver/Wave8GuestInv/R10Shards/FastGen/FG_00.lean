import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon


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
  | `(tactic| fg_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · fg_auto
         · fg_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · fg_auto
         · fg_auto)
      | (apply dec_guestInv; fg_auto)
      | (apply call_guestInv'; exact_fb_hyp)
      | (apply decCall_guestInv'
         · exact_fb_hyp
         · fg_auto)
      | (apply callHandle_guestInv'
         · exact_fb_hyp
         · fg_auto)
      | (apply tailCall_guestInv'; exact_fb_hyp))

local syntax "fg_auto_loops" : tactic
local macro_rules
  | `(tactic| fg_auto_loops) => `(tactic| first
      | fg_auto
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · fg_auto_loops
         · fg_auto_loops)
      | (apply TerminatingProgBoundedOn.ite_on
         · fg_auto_loops
         · fg_auto_loops)
      | (apply dec_guestInv; fg_auto_loops)
      | (apply decCall_guestInv'
         · exact_fb_hyp
         · fg_auto_loops)
      | (apply callHandle_guestInv'
         · exact_fb_hyp
         · fg_auto_loops)
      | skip)

local syntax "fg_prove " num ident ident : tactic
local macro_rules
  | `(tactic| fg_prove $idx $fn $k) => `(tactic|
      (fg_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fg_auto
       · fg_arith $k))

theorem fb__decode_step_of
    (h_compact_to_nibbles : TerminatingFunBoundedOn GuestInv (ofString "compact_to_nibbles") K.compact_to_nibbles)
    (h_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.mpt_fail)
    (h_node_new_leaf : TerminatingFunBoundedOn GuestInv (ofString "node_new_leaf") K.node_new_leaf)
    (h_rlp_decode_fully : TerminatingFunBoundedOn GuestInv (ofString "rlp_decode_fully") K.rlp_decode_fully)
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item)
    (h_rlp_list_to_slices : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_to_slices") K.rlp_list_to_slices) :
    TerminatingFunBoundedOn GuestInv (ofString "_decode_step") K.«_decode_step» := by
  have _ := h_rlp_decode_fully
  have _ := h_mpt_fail
  have _ := h_rlp_list_to_slices
  have _ := h_rlp_item
  have _ := h_compact_to_nibbles
  have _ := h_node_new_leaf
  fg_prove 261 Guest.Software.guestFn__decode_step K.«_decode_step»

theorem fb_bal_init_of
    (h_htab_new : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.htab_new) :
    TerminatingFunBoundedOn GuestInv (ofString "bal_init") K.bal_init := by
  have _ := h_htab_new
  fg_prove 411 Guest.Software.guestFn_bal_init K.bal_init

theorem fb_bal_sort_gt :
    TerminatingFunBoundedOn GuestInv (ofString "bal_sort_gt") K.bal_sort_gt := by
  fg_unfold 429 Guest.Software.guestFn_bal_sort_gt
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_counter_guestInv_step .less (Or.inl rfl) (ofString "k") (ofString "len")
      · fg_auto
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
  · fg_arith K.bal_sort_gt

theorem fb_be_top_bit :
    TerminatingFunBoundedOn GuestInv (ofString "be_top_bit") K.be_top_bit := by
  fg_unfold 629 Guest.Software.guestFn_be_top_bit
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_counter_guestInv_step .lower (Or.inr rfl) (ofString "i") (ofString "nbytes")
      · fg_auto
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
  · fg_arith K.be_top_bit

theorem fb_blake2_g :
    TerminatingFunBoundedOn GuestInv (ofString "blake2_g") K.blake2_g := by
  fg_prove 622 Guest.Software.guestFn_blake2_g K.blake2_g

theorem fb_bls_consts_init :
    TerminatingFunBoundedOn GuestInv (ofString "bls_consts_init") K.bls_consts_init := by
  fg_prove 696 Guest.Software.guestFn_bls_consts_init K.bls_consts_init

theorem fb_bls_fp_add_raw :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_add_raw") K.bls_fp_add_raw := by
  fg_prove 700 Guest.Software.guestFn_bls_fp_add_raw K.bls_fp_add_raw

theorem fb_bls_fp_eq :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_eq") K.bls_fp_eq := by
  fg_prove 698 Guest.Software.guestFn_bls_fp_eq K.bls_fp_eq

end InitECandidate.Solver.Wave8GuestInv.FastGen
