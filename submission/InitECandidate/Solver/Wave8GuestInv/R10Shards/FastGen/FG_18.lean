import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_12
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_13

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

theorem fb_bls_fp_sqr :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sqr") K.bls_fp_sqr := by
  have _ := fb_bls_fp_mul
  fg_prove 707 Guest.Software.guestFn_bls_fp_sqr K.bls_fp_sqr

theorem fb_bls_fp_to_mont :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_to_mont") K.bls_fp_to_mont := by
  have _ := fb_bls_fp_mul
  fg_prove 708 Guest.Software.guestFn_bls_fp_to_mont K.bls_fp_to_mont

theorem fb_fp2_scale :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_scale") K.fp2_scale := by
  have _ := fb_bls_fp_mul
  fg_prove 734 Guest.Software.guestFn_fp2_scale K.fp2_scale

theorem fb_iso_horner_fp :
    TerminatingFunBoundedOn GuestInv (ofString "iso_horner_fp") K.iso_horner_fp := by
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_add
  fg_unfold 789 Guest.Software.guestFn_iso_horner_fp
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_unsigned_const_guestInv (ofString "j") (BitVec.ofNat 64 1)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
  · fg_arith K.iso_horner_fp

theorem fb_fp2_conj :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_conj") K.fp2_conj := by
  have _ := fb_bls_fp_neg
  fg_prove 730 Guest.Software.guestFn_fp2_conj K.fp2_conj

theorem fb_fp2_neg :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_neg") K.fp2_neg := by
  have _ := fb_bls_fp_neg
  fg_prove 728 Guest.Software.guestFn_fp2_neg K.fp2_neg

theorem fb_fp2_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_mul") K.fp2_mul := by
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_sub
  fg_prove 731 Guest.Software.guestFn_fp2_mul K.fp2_mul

theorem fb_fp2_mul_xi :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_mul_xi") K.fp2_mul_xi := by
  have _ := fb_bls_fp_sub
  have _ := fb_bls_fp_add
  fg_prove 733 Guest.Software.guestFn_fp2_mul_xi K.fp2_mul_xi

end InitECandidate.Solver.Wave8GuestInv.FastGen
