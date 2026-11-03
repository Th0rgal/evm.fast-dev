import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_00
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_01
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_02
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_03

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

theorem fb_bls_fp_mul :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_mul") K.bls_fp_mul := by
  have _ := fb_bls_fp_sub_raw
  fg_prove 706 Guest.Software.guestFn_bls_fp_mul K.bls_fp_mul

theorem fb_bls_fp_neg :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_neg") K.bls_fp_neg := by
  have _ := fb_bls_fp_is_zero
  have _ := fb_bls_fp_sub_raw
  fg_prove 704 Guest.Software.guestFn_bls_fp_neg K.bls_fp_neg

theorem fb_bls_fp_sub :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sub") K.bls_fp_sub := by
  have _ := fb_bls_fp_sub_raw
  have _ := fb_bls_fp_add_raw
  fg_prove 703 Guest.Software.guestFn_bls_fp_sub K.bls_fp_sub

theorem fb_modexp_of
    (h_bn_mod : TerminatingFunBoundedOn GuestInv (ofString "bn_mod") K.bn_mod)
    (h_bn_mul : TerminatingFunBoundedOn GuestInv (ofString "bn_mul") K.bn_mul) :
    TerminatingFunBoundedOn GuestInv (ofString "modexp") K.modexp := by
  have _ := fb_bn_from_be
  have _ := h_bn_mod
  have _ := fb_be_top_bit
  have _ := h_bn_mul
  have _ := fb_bn_to_be
  fg_unfold 630 Guest.Software.guestFn_modexp
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_down_signed_guestInv (ofString "t")
      · fg_auto
      · refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.sub_one _
  · fg_arith K.modexp

theorem fb_u256_addmod_of
    (h_digits_divmod : TerminatingFunBoundedOn GuestInv (ofString "digits_divmod") K.digits_divmod) :
    TerminatingFunBoundedOn GuestInv (ofString "u256_addmod") K.u256_addmod := by
  have _ := h_digits_divmod
  fg_prove 75 Guest.Software.guestFn_u256_addmod K.u256_addmod

theorem fb_u256_mulmod_of
    (h_digits_divmod : TerminatingFunBoundedOn GuestInv (ofString "digits_divmod") K.digits_divmod) :
    TerminatingFunBoundedOn GuestInv (ofString "u256_mulmod") K.u256_mulmod := by
  have _ := h_digits_divmod
  fg_prove 76 Guest.Software.guestFn_u256_mulmod K.u256_mulmod

theorem fb_fq12_pow_words_of
    (h_fq12_mul : TerminatingFunBoundedOn GuestInv (ofString "fq12_mul") K.fq12_mul)
    (h_fq12_sqr : TerminatingFunBoundedOn GuestInv (ofString "fq12_sqr") K.fq12_sqr) :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_pow_words") K.fq12_pow_words := by
  have _ := fb_fe_set_one
  have _ := h_fq12_sqr
  have _ := h_fq12_mul
  fg_unfold 683 Guest.Software.guestFn_fq12_pow_words
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_down_unsigned_guestInv (ofString "i")
      · fg_auto
      · refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.sub_one _
  · fg_arith K.fq12_pow_words

theorem fb_ecp_set_inf :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_set_inf") K.ecp_set_inf := by
  have _ := fb_fe_set_one
  have _ := fb_fe_set_zero
  fg_prove 671 Guest.Software.guestFn_ecp_set_inf K.ecp_set_inf

end InitECandidate.Solver.Wave8GuestInv.FastGen
