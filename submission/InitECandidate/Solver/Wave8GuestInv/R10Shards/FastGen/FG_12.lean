import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_00
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_01

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

theorem fb_u256_or :
    TerminatingFunBoundedOn GuestInv (ofString "u256_or") K.u256_or := by
  fg_prove 53 Guest.Software.guestFn_u256_or K.u256_or

theorem fb_ws_get_code_of
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.memeq)
    (h_nodedb_lookup : TerminatingFunBoundedOn GuestInv (ofString "nodedb_lookup") K.nodedb_lookup) :
    TerminatingFunBoundedOn GuestInv (ofString "ws_get_code") K.ws_get_code := by
  have _ := h_memeq
  have _ := h_nodedb_lookup
  fg_prove 370 Guest.Software.guestFn_ws_get_code K.ws_get_code

theorem fb_blake2b_f :
    TerminatingFunBoundedOn GuestInv (ofString "blake2b_f") K.blake2b_f := by
  have _ := fb_blake2_g
  fg_unfold 623 Guest.Software.guestFn_blake2b_f
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_counter_guestInv_step .lower (Or.inr rfl) (ofString "r") (ofString "rounds")
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.seq _ _ _ rfl rfl ?_; refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
    · apply while_up_signed_const_guestInv (ofString "i") 1#64 (BitVec.ofNat 64 8)
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · decide
      · decide
  · fg_arith K.blake2b_f

theorem fb_bls_lib_init :
    TerminatingFunBoundedOn GuestInv (ofString "bls_lib_init") K.bls_lib_init := by
  have _ := fb_bls_consts_init
  fg_prove 801 Guest.Software.guestFn_bls_lib_init K.bls_lib_init

theorem fb_fp2_eq :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_eq") K.fp2_eq := by
  have _ := fb_bls_fp_eq
  fg_prove 725 Guest.Software.guestFn_fp2_eq K.fp2_eq

theorem fb_g1_is_inf :
    TerminatingFunBoundedOn GuestInv (ofString "g1_is_inf") K.g1_is_inf := by
  have _ := fb_bls_fp_is_zero
  fg_prove 759 Guest.Software.guestFn_g1_is_inf K.g1_is_inf

theorem fb_bls_fp_half_can :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_half_can") K.bls_fp_half_can := by
  have _ := fb_bls_fp_shr1
  have _ := fb_bls_fp_add_raw
  fg_prove 711 Guest.Software.guestFn_bls_fp_half_can K.bls_fp_half_can

theorem fb_bls_fp_add :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_add") K.bls_fp_add := by
  have _ := fb_bls_fp_add_raw
  have _ := fb_bls_fp_sub_raw
  fg_prove 702 Guest.Software.guestFn_bls_fp_add K.bls_fp_add

end InitECandidate.Solver.Wave8GuestInv.FastGen
