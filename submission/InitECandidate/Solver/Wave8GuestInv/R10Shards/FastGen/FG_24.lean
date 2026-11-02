import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_02
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_03
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_04
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_05
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_09
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_14
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_17
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_18
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_19
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_20

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

theorem fb_g2_double :
    TerminatingFunBoundedOn GuestInv (ofString "g2_double") K.g2_double := by
  have _ := fb_fp2_sqr
  have _ := fb_fp2_add
  have _ := fb_fp2_mul
  have _ := fb_fp2_sub
  have _ := fb_fp2_copy
  fg_prove 774 Guest.Software.guestFn_g2_double K.g2_double

theorem fb_pair_addition_step :
    TerminatingFunBoundedOn GuestInv (ofString "pair_addition_step") K.pair_addition_step := by
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_fp2_add
  have _ := fb_fp2_sub
  have _ := fb_fp2_copy
  have _ := fb_fp2_neg
  fg_prove 783 Guest.Software.guestFn_pair_addition_step K.pair_addition_step

theorem fb_pair_doubling_step :
    TerminatingFunBoundedOn GuestInv (ofString "pair_doubling_step") K.pair_doubling_step := by
  have _ := fb_fp2_sqr
  have _ := fb_fp2_add
  have _ := fb_fp2_sub
  have _ := fb_fp2_mul
  have _ := fb_fp2_copy
  have _ := fb_fp2_neg
  fg_prove 782 Guest.Software.guestFn_pair_doubling_step K.pair_doubling_step

theorem fb_fp12_is_one_of
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.memeq) :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_is_one") K.fp12_is_one := by
  have _ := fb_fp12_set_one
  have _ := h_memeq
  fg_prove 749 Guest.Software.guestFn_fp12_is_one K.fp12_is_one

theorem fb_ec_add_affine :
    TerminatingFunBoundedOn GuestInv (ofString "ec_add_affine") K.ec_add_affine := by
  have _ := fb_ec_set_affine
  have _ := fb_fp_sqr
  have _ := fb_fp_mul
  have _ := fb_fp_add
  have _ := fb_ec_set_infinity
  have _ := fb_ec_double
  have _ := fb_fp_sub
  fg_prove 171 Guest.Software.guestFn_ec_add_affine K.ec_add_affine

theorem fb_bn254_g1_mul_of
    (h_bn254_g1_to_bytes : TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_to_bytes") K.bn254_g1_to_bytes)
    (h_ecp_mul : TerminatingFunBoundedOn GuestInv (ofString "ecp_mul") K.ecp_mul) :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_mul") K.bn254_g1_mul := by
  have _ := fb_bn254_parse_g1
  have _ := h_ecp_mul
  have _ := h_bn254_g1_to_bytes
  fg_prove 690 Guest.Software.guestFn_bn254_g1_mul K.bn254_g1_mul

theorem fb_fe_sqr_of
    (h_fe_mul : TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.fe_mul)
    (h_fq12_sqr : TerminatingFunBoundedOn GuestInv (ofString "fq12_sqr") K.fq12_sqr) :
    TerminatingFunBoundedOn GuestInv (ofString "fe_sqr") K.fe_sqr := by
  have _ := h_fq12_sqr
  have _ := h_fe_mul
  fg_prove 662 Guest.Software.guestFn_fe_sqr K.fe_sqr

theorem fb_p256_ec_mul2_of
    (h_p256_ec_add_affine : TerminatingFunBoundedOn GuestInv (ofString "p256_ec_add_affine") K.p256_ec_add_affine)
    (h_p256_ec_double : TerminatingFunBoundedOn GuestInv (ofString "p256_ec_double") K.p256_ec_double) :
    TerminatingFunBoundedOn GuestInv (ofString "p256_ec_mul2") K.p256_ec_mul2 := by
  have _ := fb_p256_set_infinity
  have _ := h_p256_ec_double
  have _ := h_p256_ec_add_affine
  fg_unfold 641 Guest.Software.guestFn_p256_ec_mul2
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_down_unsigned_guestInv (ofString "i")
      · fg_auto
      · refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.sub_one _
  · fg_arith K.p256_ec_mul2

end InitECandidate.Solver.Wave8GuestInv.FastGen
