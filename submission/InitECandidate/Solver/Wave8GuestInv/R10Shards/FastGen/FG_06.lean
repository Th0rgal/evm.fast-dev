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

theorem fb_g1_copy :
    TerminatingFunBoundedOn GuestInv (ofString "g1_copy") K.g1_copy := by
  fg_prove 760 Guest.Software.guestFn_g1_copy K.g1_copy

theorem fb_g1_set_inf :
    TerminatingFunBoundedOn GuestInv (ofString "g1_set_inf") K.g1_set_inf := by
  fg_prove 758 Guest.Software.guestFn_g1_set_inf K.g1_set_inf

theorem fb_g2_copy :
    TerminatingFunBoundedOn GuestInv (ofString "g2_copy") K.g2_copy := by
  fg_prove 772 Guest.Software.guestFn_g2_copy K.g2_copy

theorem fb_hdr_bytes_field_of
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item) :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_bytes_field") K.hdr_bytes_field := by
  have _ := h_rlp_item
  fg_prove 225 Guest.Software.guestFn_hdr_bytes_field K.hdr_bytes_field

theorem fb_hdr_raw_field_of
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item) :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_raw_field") K.hdr_raw_field := by
  have _ := h_rlp_item
  fg_prove 226 Guest.Software.guestFn_hdr_raw_field K.hdr_raw_field

theorem fb_hdr_uint_field_of
    (h_rlp_item : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.rlp_item) :
    TerminatingFunBoundedOn GuestInv (ofString "hdr_uint_field") K.hdr_uint_field := by
  have _ := h_rlp_item
  fg_prove 222 Guest.Software.guestFn_hdr_uint_field K.hdr_uint_field

theorem fb_is_warm_storage_key_of
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.htab_has) :
    TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.is_warm_storage_key := by
  have _ := h_htab_has
  fg_prove 525 Guest.Software.guestFn_is_warm_storage_key K.is_warm_storage_key

theorem fb_is_zero_bytes :
    TerminatingFunBoundedOn GuestInv (ofString "is_zero_bytes") K.is_zero_bytes := by
  fg_unfold 19 Guest.Software.guestFn_is_zero_bytes
  apply TerminatingProgBoundedOn.weaken'
  · fg_auto_loops
    · apply while_counter_guestInv_step .lower (Or.inr rfl) (ofString "i") (ofString "n")
      · fg_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_; exact CounterStep.assign _ 1#64
      · rfl
      · rfl
  · fg_arith K.is_zero_bytes

end InitECandidate.Solver.Wave8GuestInv.FastGen
