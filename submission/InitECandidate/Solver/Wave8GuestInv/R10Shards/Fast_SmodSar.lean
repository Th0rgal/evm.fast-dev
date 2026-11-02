import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13DivMod

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FastSmodSar

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod

theorem fb_u256_neg : TerminatingFunBoundedOn GuestInv (ofString "u256_neg") K.«u256_neg» := by
  fb_prove 58 Guest.Software.guestFn_u256_neg K.«u256_neg»

theorem fb_u256_abs : TerminatingFunBoundedOn GuestInv (ofString "u256_abs") K.«u256_abs» := by
  have _ := fb_u256_neg
  fb_prove 72 Guest.Software.guestFn_u256_abs K.«u256_abs»

theorem fb_u256_smod : TerminatingFunBoundedOn GuestInv (ofString "u256_smod") K.«u256_smod» := by
  have _ := fb_u256_abs
  have _ := fb_u256_mod
  have _ := fb_u256_neg
  fb_prove 74 Guest.Software.guestFn_u256_smod K.«u256_smod»

theorem fb_op_smod : TerminatingFunBoundedOn GuestInv (ofString "op_smod") K.«op_smod» := by
  have _ := fb_charge_gas
  have _ := fb_pc_add
  have _ := fb_stack_pop
  have _ := fb_stack_push
  have _ := fb_u256_smod
  fb_prove 481 Guest.Software.guestFn_op_smod K.«op_smod»

theorem fb_u256_sar : TerminatingFunBoundedOn GuestInv (ofString "u256_sar") K.«u256_sar» := by
  have h_u256_or : TerminatingFunBoundedOn GuestInv (ofString "u256_or") K.«u256_or» := by
    fb_prove 53 Guest.Software.guestFn_u256_or K.«u256_or»
  have h_u256_shl : TerminatingFunBoundedOn GuestInv (ofString "u256_shl") K.«u256_shl» := by
    fb_prove 81 Guest.Software.guestFn_u256_shl K.«u256_shl»
  have h_u256_shr : TerminatingFunBoundedOn GuestInv (ofString "u256_shr") K.«u256_shr» := by
    fb_prove 82 Guest.Software.guestFn_u256_shr K.«u256_shr»
  fb_prove 83 Guest.Software.guestFn_u256_sar K.«u256_sar»

theorem fb_op_sar : TerminatingFunBoundedOn GuestInv (ofString "op_sar") K.«op_sar» := by
  have _ := fb_charge_gas
  have _ := fb_pc_add
  have _ := fb_sat_word
  have _ := fb_stack_pop
  have _ := fb_stack_push
  have _ := fb_u256_sar
  fb_prove 499 Guest.Software.guestFn_op_sar K.«op_sar»

theorem fb_u256_signextend : TerminatingFunBoundedOn GuestInv (ofString "u256_signextend") K.«u256_signextend» := by
  have h_u256_limb : TerminatingFunBoundedOn GuestInv (ofString "u256_limb") K.«u256_limb» := by
    fb_prove 43 Guest.Software.guestFn_u256_limb K.«u256_limb»
  have h_u256_bit : TerminatingFunBoundedOn GuestInv (ofString "u256_bit") K.«u256_bit» := by
    fb_prove 44 Guest.Software.guestFn_u256_bit K.«u256_bit»
  have h_u256_not : TerminatingFunBoundedOn GuestInv (ofString "u256_not") K.«u256_not» := by
    fb_prove 51 Guest.Software.guestFn_u256_not K.«u256_not»
  have h_u256_and : TerminatingFunBoundedOn GuestInv (ofString "u256_and") K.«u256_and» := by
    fb_prove 52 Guest.Software.guestFn_u256_and K.«u256_and»
  have h_u256_or : TerminatingFunBoundedOn GuestInv (ofString "u256_or") K.«u256_or» := by
    fb_prove 53 Guest.Software.guestFn_u256_or K.«u256_or»
  have h_u256_shl : TerminatingFunBoundedOn GuestInv (ofString "u256_shl") K.«u256_shl» := by
    fb_prove 81 Guest.Software.guestFn_u256_shl K.«u256_shl»
  fb_prove 84 Guest.Software.guestFn_u256_signextend K.«u256_signextend»

theorem fb_op_signextend : TerminatingFunBoundedOn GuestInv (ofString "op_signextend") K.«op_signextend» := by
  have _ := fb_charge_gas
  have _ := fb_pc_add
  have _ := fb_sat_word
  have _ := fb_stack_pop
  have _ := fb_stack_push
  have _ := fb_u256_signextend
  fb_prove 485 Guest.Software.guestFn_op_signextend K.«op_signextend»

end InitECandidate.Solver.Wave8GuestInv.FastSmodSar
