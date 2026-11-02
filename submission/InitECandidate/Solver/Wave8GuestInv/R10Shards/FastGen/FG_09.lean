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

theorem fb_op_or :
    TerminatingFunBoundedOn GuestInv (ofString "op_or") K.op_or := by
  fg_prove 493 Guest.Software.guestFn_op_or K.op_or

theorem fb_op_selfbalance_of
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.get_account) :
    TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.op_selfbalance := by
  have _ := h_get_account
  fg_prove 549 Guest.Software.guestFn_op_selfbalance K.op_selfbalance

theorem fb_op_selfdestruct_of
    (h_charge_state_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.charge_state_gas)
    (h_emit_transfer_log : TerminatingFunBoundedOn GuestInv (ofString "emit_transfer_log") K.emit_transfer_log)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.get_account)
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.htab_has)
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.htab_set)
    (h_is_account_alive : TerminatingFunBoundedOn GuestInv (ofString "is_account_alive") K.is_account_alive)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.is_warm_address)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.memeq)
    (h_move_ether : TerminatingFunBoundedOn GuestInv (ofString "move_ether") K.move_ether)
    (h_to_address_masked : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.to_address_masked)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.warm_address) :
    TerminatingFunBoundedOn GuestInv (ofString "op_selfdestruct") K.op_selfdestruct := by
  have _ := h_to_address_masked
  have _ := h_is_warm_address
  have _ := h_warm_address
  have _ := h_is_account_alive
  have _ := h_get_account
  have _ := h_charge_state_gas
  have _ := h_move_ether
  have _ := h_memeq
  have _ := h_emit_transfer_log
  have _ := h_htab_has
  have _ := h_htab_set
  fg_prove 570 Guest.Software.guestFn_op_selfdestruct K.op_selfdestruct

theorem fb_p256_fp_add :
    TerminatingFunBoundedOn GuestInv (ofString "p256_fp_add") K.p256_fp_add := by
  fg_prove 631 Guest.Software.guestFn_p256_fp_add K.p256_fp_add

theorem fb_p256_fp_reduce :
    TerminatingFunBoundedOn GuestInv (ofString "p256_fp_reduce") K.p256_fp_reduce := by
  fg_prove 633 Guest.Software.guestFn_p256_fp_reduce K.p256_fp_reduce

theorem fb_p256_fp_sub :
    TerminatingFunBoundedOn GuestInv (ofString "p256_fp_sub") K.p256_fp_sub := by
  fg_prove 632 Guest.Software.guestFn_p256_fp_sub K.p256_fp_sub

theorem fb_p256_set_affine :
    TerminatingFunBoundedOn GuestInv (ofString "p256_set_affine") K.p256_set_affine := by
  fg_prove 638 Guest.Software.guestFn_p256_set_affine K.p256_set_affine

theorem fb_p256_set_infinity :
    TerminatingFunBoundedOn GuestInv (ofString "p256_set_infinity") K.p256_set_infinity := by
  fg_prove 637 Guest.Software.guestFn_p256_set_infinity K.p256_set_infinity

end InitECandidate.Solver.Wave8GuestInv.FastGen
