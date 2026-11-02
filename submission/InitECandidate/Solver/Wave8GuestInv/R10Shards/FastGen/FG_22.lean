import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_00
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_01
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_06
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_12
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_13
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_17
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_18

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

theorem fb_g1_normalize_of
    (h_bls_fp_inv : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_inv") K.bls_fp_inv) :
    TerminatingFunBoundedOn GuestInv (ofString "g1_normalize") K.g1_normalize := by
  have _ := h_bls_fp_inv
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_is_zero
  fg_prove 765 Guest.Software.guestFn_g1_normalize K.g1_normalize

theorem fb_fp2_inv_of
    (h_bls_fp_inv : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_inv") K.bls_fp_inv) :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_inv") K.fp2_inv := by
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_add
  have _ := h_bls_fp_inv
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_neg
  fg_prove 735 Guest.Software.guestFn_fp2_inv K.fp2_inv

theorem fb_g1_double :
    TerminatingFunBoundedOn GuestInv (ofString "g1_double") K.g1_double := by
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_sub
  fg_prove 762 Guest.Software.guestFn_g1_double K.g1_double

theorem fb_g1_on_curve :
    TerminatingFunBoundedOn GuestInv (ofString "g1_on_curve") K.g1_on_curve := by
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_eq
  fg_prove 766 Guest.Software.guestFn_g1_on_curve K.g1_on_curve

theorem fb_swu_sqrt_division_fp :
    TerminatingFunBoundedOn GuestInv (ofString "swu_sqrt_division_fp") K.swu_sqrt_division_fp := by
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_pow
  have _ := fb_bls_fp_sub
  have _ := fb_bls_fp_is_zero
  fg_prove 787 Guest.Software.guestFn_swu_sqrt_division_fp K.swu_sqrt_division_fp

theorem fb_bls_fp_decode64 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_decode64") K.bls_fp_decode64 := by
  have _ := fb_is_zero_bytes
  have _ := fb_bls_fp_from_be48
  have _ := fb_bls_fp_lt_raw
  have _ := fb_bls_fp_to_mont
  fg_prove 719 Guest.Software.guestFn_bls_fp_decode64 K.bls_fp_decode64

theorem fb_iso_map_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "iso_map_g1") K.iso_map_g1 := by
  have _ := fb_bls_fp_mul
  have _ := fb_iso_horner_fp
  fg_unfold 790 Guest.Software.guestFn_iso_map_g1
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_unsigned_const_guestInv (ofString "j") (BitVec.ofNat 64 15)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
  · fg_arith K.iso_map_g1

theorem fb_fp6_neg :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_neg") K.fp6_neg := by
  have _ := fb_fp2_neg
  fg_prove 743 Guest.Software.guestFn_fp6_neg K.fp6_neg

end InitECandidate.Solver.Wave8GuestInv.FastGen
