import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_03
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_04
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_12
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_17
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_18
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_19

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

theorem fb_g2_neg :
    TerminatingFunBoundedOn GuestInv (ofString "g2_neg") K.g2_neg := by
  have _ := fb_fp2_copy
  have _ := fb_fp2_neg
  fg_prove 773 Guest.Software.guestFn_g2_neg K.g2_neg

theorem fb_fp12_frob :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_frob") K.fp12_frob := by
  have _ := fb_fp2_conj
  have _ := fb_fp2_mul
  fg_prove 754 Guest.Software.guestFn_fp12_frob K.fp12_frob

theorem fb_iso_horner_fp2 :
    TerminatingFunBoundedOn GuestInv (ofString "iso_horner_fp2") K.iso_horner_fp2 := by
  have _ := fb_fp2_copy
  have _ := fb_fp2_mul
  have _ := fb_fp2_add
  fg_unfold 794 Guest.Software.guestFn_iso_horner_fp2
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_unsigned_const_guestInv (ofString "j") (BitVec.ofNat 64 1)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
  · fg_arith K.iso_horner_fp2

theorem fb_fp6_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_mul") K.fp6_mul := by
  have _ := fb_fp2_mul
  have _ := fb_fp2_add
  have _ := fb_fp2_mul_xi
  fg_prove 744 Guest.Software.guestFn_fp6_mul K.fp6_mul

theorem fb_fp6_mul_v :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_mul_v") K.fp6_mul_v := by
  have _ := fb_fp2_mul_xi
  have _ := fb_fp2_copy
  fg_prove 745 Guest.Software.guestFn_fp6_mul_v K.fp6_mul_v

theorem fb_fp2_pow :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_pow") K.fp2_pow := by
  have _ := fb_fp2_copy
  have _ := fb_fp2_set_one
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  fg_unfold 736 Guest.Software.guestFn_fp2_pow
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_down_unsigned_guestInv (ofString "i")
      · fg_auto
      · refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.sub_one _
  · fg_arith K.fp2_pow

theorem fb_g2_on_curve :
    TerminatingFunBoundedOn GuestInv (ofString "g2_on_curve") K.g2_on_curve := by
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_fp2_add
  have _ := fb_fp2_eq
  fg_prove 778 Guest.Software.guestFn_g2_on_curve K.g2_on_curve

theorem fb_fp6_sub :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_sub") K.fp6_sub := by
  have _ := fb_fp2_sub
  fg_prove 742 Guest.Software.guestFn_fp6_sub K.fp6_sub

end InitECandidate.Solver.Wave8GuestInv.FastGen
