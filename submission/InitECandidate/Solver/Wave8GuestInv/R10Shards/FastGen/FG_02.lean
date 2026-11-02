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

theorem fb_bn_from_be :
    TerminatingFunBoundedOn GuestInv (ofString "bn_from_be") K.bn_from_be := by
  fg_unfold 624 Guest.Software.guestFn_bn_from_be
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_counter_guestInv_step .lower (Or.inr rfl) (ofString "i") (ofString "nd")
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
    · apply while_counter_guestInv_step .lower (Or.inr rfl) (ofString "i") (ofString "nbytes")
      · fg_auto
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
  · fg_arith K.bn_from_be

theorem fb_bn_mod_of
    (h_bn_divmnu : TerminatingFunBoundedOn GuestInv (ofString "bn_divmnu") K.bn_divmnu) :
    TerminatingFunBoundedOn GuestInv (ofString "bn_mod") K.bn_mod := by
  have _ := h_bn_divmnu
  fg_prove 628 Guest.Software.guestFn_bn_mod K.bn_mod

theorem fb_bn_to_be :
    TerminatingFunBoundedOn GuestInv (ofString "bn_to_be") K.bn_to_be := by
  fg_unfold 625 Guest.Software.guestFn_bn_to_be
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_counter_guestInv_step .lower (Or.inr rfl) (ofString "i") (ofString "nbytes")
      · fg_auto
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
  · fg_arith K.bn_to_be

theorem fb_cache_get_root_of
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.htab_has)
    (h_ws_storage_root_of : TerminatingFunBoundedOn GuestInv (ofString "ws_storage_root_of") K.ws_storage_root_of) :
    TerminatingFunBoundedOn GuestInv (ofString "cache_get_root") K.cache_get_root := by
  have _ := h_htab_has
  have _ := h_ws_storage_root_of
  fg_prove 842 Guest.Software.guestFn_cache_get_root K.cache_get_root

theorem fb_check_gas_limit :
    TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.check_gas_limit := by
  fg_prove 235 Guest.Software.guestFn_check_gas_limit K.check_gas_limit

theorem fb_digits_divmod_of
    (h_divmnu : TerminatingFunBoundedOn GuestInv (ofString "divmnu") K.divmnu) :
    TerminatingFunBoundedOn GuestInv (ofString "digits_divmod") K.digits_divmod := by
  have _ := h_divmnu
  fg_unfold 68 Guest.Software.guestFn_digits_divmod
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_unsigned_const_guestInv (ofString "i") (BitVec.ofNat 64 16)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
    · apply while_up_unsigned_const_guestInv (ofString "i") (BitVec.ofNat 64 8)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
  · fg_arith K.digits_divmod

theorem fb_ec_is_infinity :
    TerminatingFunBoundedOn GuestInv (ofString "ec_is_infinity") K.ec_is_infinity := by
  fg_prove 169 Guest.Software.guestFn_ec_is_infinity K.ec_is_infinity

theorem fb_ec_set_affine :
    TerminatingFunBoundedOn GuestInv (ofString "ec_set_affine") K.ec_set_affine := by
  fg_prove 168 Guest.Software.guestFn_ec_set_affine K.ec_set_affine

end InitECandidate.Solver.Wave8GuestInv.FastGen
