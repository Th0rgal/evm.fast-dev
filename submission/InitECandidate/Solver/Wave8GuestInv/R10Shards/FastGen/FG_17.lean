import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FGCommon
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_11
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

theorem fb_tx_scalar_u256_of
    (h_tx_scalar_item : TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_item") K.tx_scalar_item) :
    TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_u256") K.tx_scalar_u256 := by
  have _ := h_tx_scalar_item
  fg_prove 297 Guest.Software.guestFn_tx_scalar_u256 K.tx_scalar_u256

theorem fb_tx_scalar_word_of
    (h_tx_scalar_item : TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_item") K.tx_scalar_item) :
    TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_word") K.tx_scalar_word := by
  have _ := h_tx_scalar_item
  fg_unfold 298 Guest.Software.guestFn_tx_scalar_word
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "j") _
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
  · fg_arith K.tx_scalar_word

theorem fb_u256_sdiv :
    TerminatingFunBoundedOn GuestInv (ofString "u256_sdiv") K.u256_sdiv := by
  have _ := fb_u256_div
  fg_prove 73 Guest.Software.guestFn_u256_sdiv K.u256_sdiv

theorem fb_get_code_of
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.htab_get)
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.htab_set)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.memeq)
    (h_ws_get_code : TerminatingFunBoundedOn GuestInv (ofString "ws_get_code") K.ws_get_code) :
    TerminatingFunBoundedOn GuestInv (ofString "get_code") K.get_code := by
  have _ := h_memeq
  have _ := h_htab_get
  have _ := h_htab_set
  have _ := h_ws_get_code
  fg_prove 376 Guest.Software.guestFn_get_code K.get_code

theorem fb_fp2_add :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_add") K.fp2_add := by
  have _ := fb_bls_fp_add
  fg_prove 726 Guest.Software.guestFn_fp2_add K.fp2_add

theorem fb_bls_fp_from_mont :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_from_mont") K.bls_fp_from_mont := by
  have _ := fb_bls_fp_mul
  fg_prove 709 Guest.Software.guestFn_bls_fp_from_mont K.bls_fp_from_mont

theorem fb_bls_fp_inv_of
    (h_bls_fp_inv_raw : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_inv_raw") K.bls_fp_inv_raw) :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_inv") K.bls_fp_inv := by
  have _ := h_bls_fp_inv_raw
  have _ := fb_bls_fp_mul
  fg_prove 713 Guest.Software.guestFn_bls_fp_inv K.bls_fp_inv

theorem fb_bls_fp_pow :
    TerminatingFunBoundedOn GuestInv (ofString "bls_fp_pow") K.bls_fp_pow := by
  have _ := fb_bls_fp_mul
  fg_unfold 714 Guest.Software.guestFn_bls_fp_pow
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_down_unsigned_guestInv (ofString "i")
      · fg_auto
      · refine CounterStep.suffix _ _ _ ?_ rfl; exact CounterStep.sub_one _
  · fg_arith K.bls_fp_pow

end InitECandidate.Solver.Wave8GuestInv.FastGen
