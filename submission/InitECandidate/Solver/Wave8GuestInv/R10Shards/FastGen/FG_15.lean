import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_05
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_06

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

theorem fb_fq12_frob_of
    (h_fq_mul_small : TerminatingFunBoundedOn GuestInv (ofString "fq_mul_small") K.fq_mul_small) :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_frob") K.fq12_frob := by
  have _ := h_fq_mul_small
  have _ := fb_fq_add
  have _ := fb_fq_neg
  have _ := fb_fq_mul
  have _ := fb_fq_sub
  fg_unfold 679 Guest.Software.guestFn_fq12_frob
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_unsigned_const_guestInv (ofString "k") (BitVec.ofNat 64 6)
      · fg_auto
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
  · fg_arith K.fq12_frob

theorem fb_fq12_twist_of
    (h_fq_mul_small : TerminatingFunBoundedOn GuestInv (ofString "fq_mul_small") K.fq_mul_small) :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_twist") K.fq12_twist := by
  have _ := h_fq_mul_small
  have _ := fb_fq_sub
  fg_unfold 677 Guest.Software.guestFn_fq12_twist
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_unsigned_const_guestInv (ofString "j") (BitVec.ofNat 64 3)
      · fg_auto
      · refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.decCall _ _ _ _ _ _ (by decide) ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.dec _ _ _ _ _ (by decide) ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
  · fg_arith K.fq12_twist

theorem fb_fq2_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fq2_mul") K.fq2_mul := by
  have _ := fb_fq_mul
  have _ := fb_fq_sub
  have _ := fb_fq_add
  fg_prove 657 Guest.Software.guestFn_fq2_mul K.fq2_mul

theorem fb_hdr_u256_field_of
    (h_hdr_uint_field : TerminatingFunBoundedOn GuestInv (ofString "hdr_uint_field") K.hdr_uint_field) :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_u256_field") K.hdr_u256_field := by
  have _ := h_hdr_uint_field
  fg_prove 224 Guest.Software.guestFn_hdr_u256_field K.hdr_u256_field

theorem fb_hdr_word_field_of
    (h_hdr_uint_field : TerminatingFunBoundedOn GuestInv (ofString "hdr_uint_field") K.hdr_uint_field) :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_word_field") K.hdr_word_field := by
  have _ := h_hdr_uint_field
  fg_unfold 223 Guest.Software.guestFn_hdr_word_field
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "j") _
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
  · fg_arith K.hdr_word_field

theorem fb_extract_deposit_data_of
    (h_ld_be64 : TerminatingFunBoundedOn GuestInv (ofString "ld_be64") K.ld_be64) :
    TerminatingFunBoundedOn GuestInv (ofString "extract_deposit_data") K.extract_deposit_data := by
  have _ := fb_is_zero_bytes
  have _ := h_ld_be64
  fg_prove 841 Guest.Software.guestFn_extract_deposit_data K.extract_deposit_data

theorem fb_fe_is_zero :
    TerminatingFunBoundedOn GuestInv (ofString "fe_is_zero") K.fe_is_zero := by
  have _ := fb_is_zero_bytes
  fg_prove 667 Guest.Software.guestFn_fe_is_zero K.fe_is_zero

theorem fb_fq_poly_deg :
    TerminatingFunBoundedOn GuestInv (ofString "fq_poly_deg") K.fq_poly_deg := by
  have _ := fb_is_zero_bytes
  fg_unfold 680 Guest.Software.guestFn_fq_poly_deg
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_down_unsigned_guestInv (ofString "i")
      · fg_auto
      · refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.sub_one _
  · fg_arith K.fq_poly_deg

end InitECandidate.Solver.Wave8GuestInv.FastGen
