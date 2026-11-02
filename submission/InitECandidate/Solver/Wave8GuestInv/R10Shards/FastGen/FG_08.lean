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

theorem fb_op_calldataload :
    TerminatingFunBoundedOn GuestInv (ofString "op_calldataload") K.op_calldataload := by
  fg_prove 536 Guest.Software.guestFn_op_calldataload K.op_calldataload

theorem fb_op_calldatasize :
    TerminatingFunBoundedOn GuestInv (ofString "op_calldatasize") K.op_calldatasize := by
  fg_prove 537 Guest.Software.guestFn_op_calldatasize K.op_calldatasize

theorem fb_op_caller :
    TerminatingFunBoundedOn GuestInv (ofString "op_caller") K.op_caller := by
  fg_prove 534 Guest.Software.guestFn_op_caller K.op_caller

theorem fb_op_mstore :
    TerminatingFunBoundedOn GuestInv (ofString "op_mstore") K.op_mstore := by
  fg_prove 508 Guest.Software.guestFn_op_mstore K.op_mstore

theorem fb_op_mstore8 :
    TerminatingFunBoundedOn GuestInv (ofString "op_mstore8") K.op_mstore8 := by
  fg_prove 509 Guest.Software.guestFn_op_mstore8 K.op_mstore8

theorem fb_op_mul :
    TerminatingFunBoundedOn GuestInv (ofString "op_mul") K.op_mul := by
  fg_prove 476 Guest.Software.guestFn_op_mul K.op_mul

theorem fb_op_not :
    TerminatingFunBoundedOn GuestInv (ofString "op_not") K.op_not := by
  fg_prove 495 Guest.Software.guestFn_op_not K.op_not

theorem fb_op_number :
    TerminatingFunBoundedOn GuestInv (ofString "op_number") K.op_number := by
  fg_prove 557 Guest.Software.guestFn_op_number K.op_number

end InitECandidate.Solver.Wave8GuestInv.FastGen
