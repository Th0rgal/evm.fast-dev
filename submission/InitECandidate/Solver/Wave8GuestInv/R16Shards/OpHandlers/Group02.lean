import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush

/-! # OpHandlerSpec Group 02: comparison opcodes (`op_lt`, `op_gt`, `op_slt`, `op_sgt`, `op_eq`, `op_iszero`) -/

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

theorem op_lt_spec : OpHandlerSpec (ofString "op_lt") := by
  refine opHandlerSpec_of_run 486 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_lt rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_lt, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_lt
            (HandlerRun.seq_call_simple eps_stack_push_bool
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_gt_spec : OpHandlerSpec (ofString "op_gt") := by
  refine opHandlerSpec_of_run 487 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_gt rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_gt, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_gt
            (HandlerRun.seq_call_simple eps_stack_push_bool
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_slt_spec : OpHandlerSpec (ofString "op_slt") := by
  refine opHandlerSpec_of_run 488 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_slt rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_slt, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_slt
            (HandlerRun.seq_call_simple eps_stack_push_bool
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_sgt_spec : OpHandlerSpec (ofString "op_sgt") := by
  refine opHandlerSpec_of_run 489 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_sgt rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_sgt, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_sgt
            (HandlerRun.seq_call_simple eps_stack_push_bool
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_eq_spec : OpHandlerSpec (ofString "op_eq") := by
  refine opHandlerSpec_of_run 490 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_eq rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_eq, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_eq
            (HandlerRun.seq_call_simple eps_stack_push_bool
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_iszero_spec : OpHandlerSpec (ofString "op_iszero") := by
  refine opHandlerSpec_of_run 491 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_iszero rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_iszero, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.seq_charge_gas_const (by decide)
        (HandlerRun.decCall_simple eps_u256_is_zero
          (HandlerRun.seq_call_simple eps_stack_push_bool
            (HandlerRun.seq_call_simple eps_pc_add
              (HandlerRun.ret _)))))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
