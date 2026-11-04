import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.CalldataloadSpecs

/-! # OpHandlerSpec Group 04 (`OpHandlers-A`): environment & calldata opcodes -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA

theorem op_address_spec : OpHandlerSpec (ofString "op_address") := by
  refine opHandlerSpec_of_run 531 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_address rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_address, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_address_to_u256
        (HandlerRun.seq_call_simple eps_stack_push
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_origin_spec : OpHandlerSpec (ofString "op_origin") := by
  refine opHandlerSpec_of_run 533 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_origin rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_origin, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.dec_simple
        (HandlerRun.decCall_simple eps_address_to_u256
          (HandlerRun.seq_call_simple eps_stack_push
            (HandlerRun.seq_call_simple eps_pc_add
              (HandlerRun.ret _)))))

theorem op_caller_spec : OpHandlerSpec (ofString "op_caller") := by
  refine opHandlerSpec_of_run 534 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_caller rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_caller, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_address_to_u256
        (HandlerRun.seq_call_simple eps_stack_push
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_callvalue_spec : OpHandlerSpec (ofString "op_callvalue") := by
  refine opHandlerSpec_of_run 535 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_callvalue rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_callvalue, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.seq_call_simple eps_stack_push
        (HandlerRun.seq_call_simple eps_pc_add
          (HandlerRun.ret _)))

theorem op_calldatasize_spec : OpHandlerSpec (ofString "op_calldatasize") := by
  refine opHandlerSpec_of_run 537 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_calldatasize rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_calldatasize, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.seq_call_simple eps_stack_push_word
        (HandlerRun.seq_call_simple eps_pc_add
          (HandlerRun.ret _)))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
