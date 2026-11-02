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

theorem fb_kzg_neg_scalar :
    TerminatingFunBoundedOn GuestInv (ofString "kzg_neg_scalar") K.kzg_neg_scalar := by
  fg_prove 799 Guest.Software.guestFn_kzg_neg_scalar K.kzg_neg_scalar

theorem fb_mod_half :
    TerminatingFunBoundedOn GuestInv (ofString "mod_half") K.mod_half := by
  fg_prove 158 Guest.Software.guestFn_mod_half K.mod_half

theorem fb_mod_sub :
    TerminatingFunBoundedOn GuestInv (ofString "mod_sub") K.mod_sub := by
  fg_prove 159 Guest.Software.guestFn_mod_sub K.mod_sub

theorem fb_modexp_gas :
    TerminatingFunBoundedOn GuestInv (ofString "modexp_gas") K.modexp_gas := by
  fg_prove 828 Guest.Software.guestFn_modexp_gas K.modexp_gas

theorem fb_mpt_nibble_key_of
    (h_key_to_nibbles : TerminatingFunBoundedOn GuestInv (ofString "key_to_nibbles") K.key_to_nibbles) :
    TerminatingFunBoundedOn GuestInv (ofString "mpt_nibble_key") K.mpt_nibble_key := by
  have _ := h_key_to_nibbles
  fg_prove 270 Guest.Software.guestFn_mpt_nibble_key K.mpt_nibble_key

theorem fb_msg_new_scratch :
    TerminatingFunBoundedOn GuestInv (ofString "msg_new_scratch") K.msg_new_scratch := by
  fg_prove 466 Guest.Software.guestFn_msg_new_scratch K.msg_new_scratch

theorem fb_op_byte :
    TerminatingFunBoundedOn GuestInv (ofString "op_byte") K.op_byte := by
  fg_prove 496 Guest.Software.guestFn_op_byte K.op_byte

theorem fb_op_calldatacopy_of
    (h_copy_from_buffer : TerminatingFunBoundedOn GuestInv (ofString "copy_from_buffer") K.copy_from_buffer) :
    TerminatingFunBoundedOn GuestInv (ofString "op_calldatacopy") K.op_calldatacopy := by
  have _ := h_copy_from_buffer
  fg_prove 539 Guest.Software.guestFn_op_calldatacopy K.op_calldatacopy

end InitECandidate.Solver.Wave8GuestInv.FastGen
