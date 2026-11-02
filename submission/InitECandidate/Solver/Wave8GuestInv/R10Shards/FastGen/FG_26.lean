import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_01
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_03
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_04
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_06
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_12
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_13
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_14
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_17
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_18
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_19
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_21
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_22
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_23
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_24

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

theorem fb_swu_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "swu_g1") K.swu_g1 := by
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_neg
  have _ := fb_bls_fp_is_zero
  have _ := fb_swu_sqrt_division_fp
  have _ := fb_bls_fp_sgn0
  fg_prove 788 Guest.Software.guestFn_swu_g1 K.swu_g1

theorem fb_g1_decode :
    TerminatingFunBoundedOn GuestInv (ofString "g1_decode") K.g1_decode := by
  have _ := fb_bls_fp_decode64
  have _ := fb_bls_fp_is_zero
  have _ := fb_g1_on_curve
  fg_prove 767 Guest.Software.guestFn_g1_decode K.g1_decode

theorem fb_fp12_conj :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_conj") K.fp12_conj := by
  have _ := fb_fp6_copy
  have _ := fb_fp6_neg
  fg_prove 752 Guest.Software.guestFn_fp12_conj K.fp12_conj

theorem fb_iso_map_g2 :
    TerminatingFunBoundedOn GuestInv (ofString "iso_map_g2") K.iso_map_g2 := by
  have _ := fb_fp2_copy
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_iso_horner_fp2
  have _ := fb_g2_copy
  fg_prove 795 Guest.Software.guestFn_iso_map_g2 K.iso_map_g2

theorem fb_swu_sqrt_division_fp2 :
    TerminatingFunBoundedOn GuestInv (ofString "swu_sqrt_division_fp2") K.swu_sqrt_division_fp2 := by
  have _ := fb_fp2_copy
  have _ := fb_fp2_mul
  have _ := fb_fp2_pow
  have _ := fb_fp2_sqr
  have _ := fb_fp2_sub
  have _ := fb_fp2_is_zero
  fg_unfold 792 Guest.Software.guestFn_swu_sqrt_division_fp2
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_unsigned_const_guestInv (ofString "i") (BitVec.ofNat 64 6)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
    · apply while_up_unsigned_const_guestInv (ofString "i") (BitVec.ofNat 64 4)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
  · fg_arith K.swu_sqrt_division_fp2

theorem fb_g2_decode :
    TerminatingFunBoundedOn GuestInv (ofString "g2_decode") K.g2_decode := by
  have _ := fb_bls_fp_decode64
  have _ := fb_fp2_is_zero
  have _ := fb_fp2_set_zero
  have _ := fb_fp2_set_one
  have _ := fb_g2_on_curve
  fg_prove 779 Guest.Software.guestFn_g2_decode K.g2_decode

theorem fb_fp12_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_mul") K.fp12_mul := by
  have _ := fb_fp6_mul
  have _ := fb_fp6_add
  have _ := fb_fp6_sub
  have _ := fb_fp6_mul_v
  fg_prove 750 Guest.Software.guestFn_fp12_mul K.fp12_mul

theorem fb_g2_add :
    TerminatingFunBoundedOn GuestInv (ofString "g2_add") K.g2_add := by
  have _ := fb_g2_is_inf
  have _ := fb_g2_copy
  have _ := fb_fp2_mul
  have _ := fb_fp2_eq
  have _ := fb_g2_double
  have _ := fb_g2_set_inf
  have _ := fb_fp2_sub
  have _ := fb_fp2_sqr
  have _ := fb_fp2_add
  have _ := fb_fp2_copy
  fg_prove 775 Guest.Software.guestFn_g2_add K.g2_add

end InitECandidate.Solver.Wave8GuestInv.FastGen
