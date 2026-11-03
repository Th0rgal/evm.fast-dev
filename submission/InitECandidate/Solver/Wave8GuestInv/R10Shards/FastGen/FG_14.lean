import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_04
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_05

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

theorem fb_g2_is_inf :
    TerminatingFunBoundedOn GuestInv (ofString "g2_is_inf") K.g2_is_inf := by
  have _ := fb_fp2_is_zero
  fg_prove 771 Guest.Software.guestFn_g2_is_inf K.g2_is_inf

theorem fb_fp6_set_one :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_set_one") K.fp6_set_one := by
  have _ := fb_fp2_set_one
  have _ := fb_fp2_set_zero
  fg_prove 740 Guest.Software.guestFn_fp6_set_one K.fp6_set_one

theorem fb_g2_set_inf :
    TerminatingFunBoundedOn GuestInv (ofString "g2_set_inf") K.g2_set_inf := by
  have _ := fb_fp2_set_one
  have _ := fb_fp2_set_zero
  fg_prove 770 Guest.Software.guestFn_g2_set_inf K.g2_set_inf

theorem fb_fp_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fp_mul") K.fp_mul := by
  have _ := fb_fp_reduce
  fg_prove 153 Guest.Software.guestFn_fp_mul K.fp_mul

theorem fb_fp_sqr :
    TerminatingFunBoundedOn GuestInv (ofString "fp_sqr") K.fp_sqr := by
  have _ := fb_fp_reduce
  fg_prove 154 Guest.Software.guestFn_fp_sqr K.fp_sqr

theorem fb_fq_from_mont :
    TerminatingFunBoundedOn GuestInv (ofString "fq_from_mont") K.fq_from_mont := by
  have _ := fb_fq_mul
  fg_prove 654 Guest.Software.guestFn_fq_from_mont K.fq_from_mont

theorem fb_fq_inv_of
    (h_modinv_bin : TerminatingFunBoundedOn GuestInv (ofString "modinv_bin") K.modinv_bin) :
    TerminatingFunBoundedOn GuestInv (ofString "fq_inv") K.fq_inv := by
  have _ := h_modinv_bin
  have _ := fb_fq_mul
  fg_prove 655 Guest.Software.guestFn_fq_inv K.fq_inv

theorem fb_fq_to_mont :
    TerminatingFunBoundedOn GuestInv (ofString "fq_to_mont") K.fq_to_mont := by
  have _ := fb_fq_mul
  fg_prove 653 Guest.Software.guestFn_fq_to_mont K.fq_to_mont

end InitECandidate.Solver.Wave8GuestInv.FastGen
