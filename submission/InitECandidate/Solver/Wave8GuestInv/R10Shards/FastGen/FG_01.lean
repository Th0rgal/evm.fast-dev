import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon


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

theorem fb_bls_fp_from_be48 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_from_be48") K.bls_fp_from_be48 := by
  fg_prove 717 Guest.Software.guestFn_bls_fp_from_be48 K.bls_fp_from_be48

theorem fb_bls_fp_is_zero :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_is_zero") K.bls_fp_is_zero := by
  fg_prove 697 Guest.Software.guestFn_bls_fp_is_zero K.bls_fp_is_zero

theorem fb_bls_fp_lt_raw :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_lt_raw") K.bls_fp_lt_raw := by
  fg_prove 699 Guest.Software.guestFn_bls_fp_lt_raw K.bls_fp_lt_raw

theorem fb_bls_fp_shr1 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_shr1") K.bls_fp_shr1 := by
  fg_prove 710 Guest.Software.guestFn_bls_fp_shr1 K.bls_fp_shr1

theorem fb_bls_fp_sub_raw :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sub_raw") K.bls_fp_sub_raw := by
  fg_prove 701 Guest.Software.guestFn_bls_fp_sub_raw K.bls_fp_sub_raw

theorem fb_bls_fp_to_be48 :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_to_be48") K.bls_fp_to_be48 := by
  fg_prove 718 Guest.Software.guestFn_bls_fp_to_be48 K.bls_fp_to_be48

theorem fb_bls_g1_msm_discount :
    TerminatingFunBoundedOn GuestInv (ofString "bls_g1_msm_discount") K.bls_g1_msm_discount := by
  fg_prove 812 Guest.Software.guestFn_bls_g1_msm_discount K.bls_g1_msm_discount

theorem fb_bls_g2_msm_discount :
    TerminatingFunBoundedOn GuestInv (ofString "bls_g2_msm_discount") K.bls_g2_msm_discount := by
  fg_prove 813 Guest.Software.guestFn_bls_g2_msm_discount K.bls_g2_msm_discount

end InitECandidate.Solver.Wave8GuestInv.FastGen
