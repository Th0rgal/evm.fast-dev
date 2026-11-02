import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_02
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_03
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_04
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_05
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_12
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_13
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_14

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

theorem fb_fp2_sqr :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_sqr") K.fp2_sqr := by
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_sub
  have _ := fb_bls_fp_mul
  fg_prove 732 Guest.Software.guestFn_fp2_sqr K.fp2_sqr

theorem fb_fp2_sub :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_sub") K.fp2_sub := by
  have _ := fb_bls_fp_sub
  fg_prove 727 Guest.Software.guestFn_fp2_sub K.fp2_sub

theorem fb_fn_mul_of
    (h_u256_mulmod : TerminatingFunBoundedOn GuestInv (ofString "u256_mulmod") K.u256_mulmod) :
    TerminatingFunBoundedOn GuestInv (ofString "fn_mul") K.fn_mul := by
  have _ := h_u256_mulmod
  fg_prove 162 Guest.Software.guestFn_fn_mul K.fn_mul

theorem fb_op_mulmod_of
    (h_u256_mulmod : TerminatingFunBoundedOn GuestInv (ofString "u256_mulmod") K.u256_mulmod) :
    TerminatingFunBoundedOn GuestInv (ofString "op_mulmod") K.op_mulmod := by
  have _ := h_u256_mulmod
  fg_prove 483 Guest.Software.guestFn_op_mulmod K.op_mulmod

theorem fb_fp12_set_one :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_set_one") K.fp12_set_one := by
  have _ := fb_fp6_set_one
  have _ := fb_fp6_set_zero
  fg_prove 748 Guest.Software.guestFn_fp12_set_one K.fp12_set_one

theorem fb_ec_double :
    TerminatingFunBoundedOn GuestInv (ofString "ec_double") K.ec_double := by
  have _ := fb_ec_set_infinity
  have _ := fb_fp_sqr
  have _ := fb_fp_mul
  have _ := fb_fp_add
  have _ := fb_fp_sub
  fg_prove 170 Guest.Software.guestFn_ec_double K.ec_double

theorem fb_ec_to_affine_of
    (h_fp_inv : TerminatingFunBoundedOn GuestInv (ofString "fp_inv") K.fp_inv) :
    TerminatingFunBoundedOn GuestInv (ofString "ec_to_affine") K.ec_to_affine := by
  have _ := h_fp_inv
  have _ := fb_fp_sqr
  have _ := fb_fp_mul
  have _ := fb_ec_set_affine
  fg_prove 175 Guest.Software.guestFn_ec_to_affine K.ec_to_affine

theorem fb_secp256k1_decompress_r_of
    (h_fp_sqrt : TerminatingFunBoundedOn GuestInv (ofString "fp_sqrt") K.fp_sqrt) :
    TerminatingFunBoundedOn GuestInv (ofString "secp256k1_decompress_r") K.secp256k1_decompress_r := by
  have _ := fb_fp_sqr
  have _ := fb_fp_mul
  have _ := fb_fp_add
  have _ := h_fp_sqrt
  have _ := fb_fp_neg
  have _ := fb_ec_set_affine
  fg_prove 177 Guest.Software.guestFn_secp256k1_decompress_r K.secp256k1_decompress_r

end InitECandidate.Solver.Wave8GuestInv.FastGen
