import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_03
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_04
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_06
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_12
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_14
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_17
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_18
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_19
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_21
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_22
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_23
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_25
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_26

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

theorem fb_fp12_inv_of
    (h_fp6_inv : TerminatingFunBoundedOn GuestInv (ofString "fp6_inv") K.fp6_inv) :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_inv") K.fp12_inv := by
  have _ := fb_fp6_mul
  have _ := fb_fp6_mul_v
  have _ := fb_fp6_sub
  have _ := h_fp6_inv
  have _ := fb_fp6_neg
  fg_prove 753 Guest.Software.guestFn_fp12_inv K.fp12_inv

theorem fb_g2_encode_of
    (h_g2_normalize : TerminatingFunBoundedOn GuestInv (ofString "g2_normalize") K.g2_normalize) :
    TerminatingFunBoundedOn GuestInv (ofString "g2_encode") K.g2_encode := by
  have _ := h_g2_normalize
  have _ := fb_bls_fp_encode64
  fg_prove 780 Guest.Software.guestFn_g2_encode K.g2_encode

theorem fb_g1_mul :
    TerminatingFunBoundedOn GuestInv (ofString "g1_mul") K.g1_mul := by
  have _ := fb_g1_copy
  have _ := fb_g1_set_inf
  have _ := fb_g1_double
  have _ := fb_g1_add
  fg_unfold 764 Guest.Software.guestFn_g1_mul
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_down_unsigned_guestInv (ofString "i")
      · fg_auto
      · refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.sub_one _
  · fg_arith K.g1_mul

theorem fb_bls_g1_add_exec_of
    (h_g1_encode : TerminatingFunBoundedOn GuestInv (ofString "g1_encode") K.g1_encode) :
    TerminatingFunBoundedOn GuestInv (ofString "bls_g1_add_exec") K.bls_g1_add_exec := by
  have _ := fb_g1_decode
  have _ := fb_g1_add
  have _ := h_g1_encode
  fg_prove 802 Guest.Software.guestFn_bls_g1_add_exec K.bls_g1_add_exec

theorem fb_fp12_exp_x_of
    (h_fp12_pow_absx : TerminatingFunBoundedOn GuestInv (ofString "fp12_pow_absx") K.fp12_pow_absx) :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_exp_x") K.fp12_exp_x := by
  have _ := h_fp12_pow_absx
  have _ := fb_fp12_conj
  fg_prove 756 Guest.Software.guestFn_fp12_exp_x K.fp12_exp_x

theorem fb_swu_g2 :
    TerminatingFunBoundedOn GuestInv (ofString "swu_g2") K.swu_g2 := by
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_fp2_add
  have _ := fb_fp2_neg
  have _ := fb_fp2_set_one
  have _ := fb_fp2_is_zero
  have _ := fb_swu_sqrt_division_fp2
  have _ := fb_fp2_sub
  have _ := fb_fp2_copy
  have _ := fb_fp2_sgn0
  fg_unfold 793 Guest.Software.guestFn_swu_g2
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_unsigned_const_guestInv (ofString "i") (BitVec.ofNat 64 4)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
  · fg_arith K.swu_g2

theorem fb_pair_accumulate_of
    (h_g1_normalize : TerminatingFunBoundedOn GuestInv (ofString "g1_normalize") K.g1_normalize)
    (h_g2_normalize : TerminatingFunBoundedOn GuestInv (ofString "g2_normalize") K.g2_normalize)
    (h_pair_miller_loop : TerminatingFunBoundedOn GuestInv (ofString "pair_miller_loop") K.pair_miller_loop) :
    TerminatingFunBoundedOn GuestInv (ofString "pair_accumulate") K.pair_accumulate := by
  have _ := fb_g1_is_inf
  have _ := fb_g2_is_inf
  have _ := h_g1_normalize
  have _ := h_g2_normalize
  have _ := h_pair_miller_loop
  have _ := fb_fp12_mul
  fg_prove 786 Guest.Software.guestFn_pair_accumulate K.pair_accumulate

theorem fb_pair_ell :
    TerminatingFunBoundedOn GuestInv (ofString "pair_ell") K.pair_ell := by
  have _ := fb_fp2_copy
  have _ := fb_fp2_scale
  have _ := fb_fp12_mul
  fg_prove 784 Guest.Software.guestFn_pair_ell K.pair_ell

end InitECandidate.Solver.Wave8GuestInv.FastGen
