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

theorem fb_fp2_is_zero :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_is_zero") K.fp2_is_zero := by
  fg_prove 724 Guest.Software.guestFn_fp2_is_zero K.fp2_is_zero

theorem fb_fp2_set_one :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_set_one") K.fp2_set_one := by
  fg_prove 723 Guest.Software.guestFn_fp2_set_one K.fp2_set_one

theorem fb_fp2_set_zero :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_set_zero") K.fp2_set_zero := by
  fg_prove 722 Guest.Software.guestFn_fp2_set_zero K.fp2_set_zero

theorem fb_fp6_copy :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_copy") K.fp6_copy := by
  fg_prove 738 Guest.Software.guestFn_fp6_copy K.fp6_copy

theorem fb_fp6_set_zero :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_set_zero") K.fp6_set_zero := by
  fg_prove 739 Guest.Software.guestFn_fp6_set_zero K.fp6_set_zero

theorem fb_fp_add :
    TerminatingFunBoundedOn GuestInv (ofString "fp_add") K.fp_add := by
  fg_prove 149 Guest.Software.guestFn_fp_add K.fp_add

theorem fb_fp_inv_of
    (h_modinv_bin : TerminatingFunBoundedOn GuestInv (ofString "modinv_bin") K.modinv_bin) :
    TerminatingFunBoundedOn GuestInv (ofString "fp_inv") K.fp_inv := by
  have _ := h_modinv_bin
  fg_prove 160 Guest.Software.guestFn_fp_inv K.fp_inv

theorem fb_fp_neg :
    TerminatingFunBoundedOn GuestInv (ofString "fp_neg") K.fp_neg := by
  fg_prove 151 Guest.Software.guestFn_fp_neg K.fp_neg

end InitECandidate.Solver.Wave8GuestInv.FastGen
