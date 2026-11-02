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

theorem fb_tx_fixed_bytes_of
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item) :
    TerminatingFunBoundedOn GuestInv (ofString "tx_fixed_bytes") K.tx_fixed_bytes := by
  have _ := h_rlp_item
  fg_prove 300 Guest.Software.guestFn_tx_fixed_bytes K.tx_fixed_bytes

theorem fb_tx_list_item_of
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item) :
    TerminatingFunBoundedOn GuestInv (ofString "tx_list_item") K.tx_list_item := by
  have _ := h_rlp_item
  fg_prove 302 Guest.Software.guestFn_tx_list_item K.tx_list_item

theorem fb_tx_put_authorizations_of
    (h_auth_list_payload_len : TerminatingFunBoundedOn GuestInv (ofString "auth_list_payload_len") K.auth_list_payload_len)
    (h_auth_payload_len : TerminatingFunBoundedOn GuestInv (ofString "auth_payload_len") K.auth_payload_len)
    (h_rlp_encode_bytes : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.rlp_encode_bytes)
    (h_rlp_encode_list_header : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.rlp_encode_list_header)
    (h_rlp_encode_word : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.rlp_encode_word)
    (h_tx_put_u256 : TerminatingFunBoundedOn GuestInv (ofString "tx_put_u256") K.tx_put_u256) :
    TerminatingFunBoundedOn GuestInv (ofString "tx_put_authorizations") K.tx_put_authorizations := by
  have _ := h_auth_list_payload_len
  have _ := h_rlp_encode_list_header
  have _ := h_auth_payload_len
  have _ := h_tx_put_u256
  have _ := h_rlp_encode_bytes
  have _ := h_rlp_encode_word
  fg_unfold 326 Guest.Software.guestFn_tx_put_authorizations
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_counter_guestInv_step .lower (Or.inr rfl) (ofString "i") (ofString "n")
      · fg_auto
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
  · fg_arith K.tx_put_authorizations

theorem fb_tx_scalar_item_of
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item) :
    TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_item") K.tx_scalar_item := by
  have _ := h_rlp_item
  fg_prove 296 Guest.Software.guestFn_tx_scalar_item K.tx_scalar_item

theorem fb_tx_to_item_of
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item) :
    TerminatingFunBoundedOn GuestInv (ofString "tx_to_item") K.tx_to_item := by
  have _ := h_rlp_item
  fg_prove 301 Guest.Software.guestFn_tx_to_item K.tx_to_item

theorem fb_u256_and :
    TerminatingFunBoundedOn GuestInv (ofString "u256_and") K.u256_and := by
  fg_prove 52 Guest.Software.guestFn_u256_and K.u256_and

theorem fb_u256_div :
    TerminatingFunBoundedOn GuestInv (ofString "u256_div") K.u256_div := by
  fg_prove 70 Guest.Software.guestFn_u256_div K.u256_div

theorem fb_u256_not :
    TerminatingFunBoundedOn GuestInv (ofString "u256_not") K.u256_not := by
  fg_prove 51 Guest.Software.guestFn_u256_not K.u256_not

end InitECandidate.Solver.Wave8GuestInv.FastGen
