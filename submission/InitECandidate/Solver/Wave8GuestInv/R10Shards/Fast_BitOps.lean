import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FastBitOps

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

theorem fb_u256_slt : TerminatingFunBoundedOn GuestInv (ofString "u256_slt") K.«u256_slt» := by
  fb_prove 48 Guest.Software.guestFn_u256_slt K.«u256_slt»

theorem fb_u256_sgt : TerminatingFunBoundedOn GuestInv (ofString "u256_sgt") K.«u256_sgt» := by
  have _ := fb_u256_slt
  fb_prove 49 Guest.Software.guestFn_u256_sgt K.«u256_sgt»

theorem fb_u256_shl : TerminatingFunBoundedOn GuestInv (ofString "u256_shl") K.«u256_shl» := by
  fb_prove 81 Guest.Software.guestFn_u256_shl K.«u256_shl»

theorem fb_u256_shr : TerminatingFunBoundedOn GuestInv (ofString "u256_shr") K.«u256_shr» := by
  fb_prove 82 Guest.Software.guestFn_u256_shr K.«u256_shr»

theorem fb_op_slt : TerminatingFunBoundedOn GuestInv (ofString "op_slt") K.«op_slt» := by
  have _ := fb_charge_gas
  have _ := fb_pc_add
  have _ := fb_stack_pop
  have _ := fb_stack_push_bool
  have _ := fb_u256_slt
  fb_prove 488 Guest.Software.guestFn_op_slt K.«op_slt»

theorem fb_op_sgt : TerminatingFunBoundedOn GuestInv (ofString "op_sgt") K.«op_sgt» := by
  have _ := fb_charge_gas
  have _ := fb_pc_add
  have _ := fb_stack_pop
  have _ := fb_stack_push_bool
  have _ := fb_u256_sgt
  fb_prove 489 Guest.Software.guestFn_op_sgt K.«op_sgt»

theorem fb_op_shl : TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl» := by
  have _ := fb_charge_gas
  have _ := fb_pc_add
  have _ := fb_sat_word
  have _ := fb_stack_pop
  have _ := fb_stack_push
  have _ := fb_u256_shl
  fb_prove 497 Guest.Software.guestFn_op_shl K.«op_shl»

theorem fb_op_shr : TerminatingFunBoundedOn GuestInv (ofString "op_shr") K.«op_shr» := by
  have _ := fb_charge_gas
  have _ := fb_pc_add
  have _ := fb_sat_word
  have _ := fb_stack_pop
  have _ := fb_stack_push
  have _ := fb_u256_shr
  fb_prove 498 Guest.Software.guestFn_op_shr K.«op_shr»

end InitECandidate.Solver.Wave8GuestInv.FastBitOps
