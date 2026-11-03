import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush

/-! # OpHandlerSpec Group 03: bitwise & shift opcodes (`op_and`, `op_or`, `op_xor`, `op_not`, `op_byte`, `op_shl`, `op_shr`, `op_sar`, `op_clz`) -/

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

theorem op_and_spec : OpHandlerSpec (ofString "op_and") := by
  refine opHandlerSpec_of_run 492 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_and rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_and, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.seq_call_simple eps_stack_push
            (HandlerRun.seq_call_simple eps_pc_add
              (HandlerRun.ret _)))))

theorem op_or_spec : OpHandlerSpec (ofString "op_or") := by
  refine opHandlerSpec_of_run 493 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_or rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_or, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.seq_call_simple eps_stack_push
            (HandlerRun.seq_call_simple eps_pc_add
              (HandlerRun.ret _)))))

theorem op_xor_spec : OpHandlerSpec (ofString "op_xor") := by
  refine opHandlerSpec_of_run 494 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_xor rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_xor, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.seq_call_simple eps_stack_push
            (HandlerRun.seq_call_simple eps_pc_add
              (HandlerRun.ret _)))))

theorem op_not_spec : OpHandlerSpec (ofString "op_not") := by
  refine opHandlerSpec_of_run 495 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_not rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_not, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.seq_charge_gas_const (by decide)
        (HandlerRun.seq_call_simple eps_stack_push
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_byte_spec : OpHandlerSpec (ofString "op_byte") := by
  refine opHandlerSpec_of_run 496 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_byte rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_byte, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_sat_word
            (HandlerRun.decCall_simple eps_u256_byte
              (HandlerRun.seq_call_simple eps_stack_push_word
                (HandlerRun.seq_call_simple eps_pc_add
                  (HandlerRun.ret _)))))))

theorem op_shl_spec : OpHandlerSpec (ofString "op_shl") := by
  refine opHandlerSpec_of_run 497 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_shl rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_shl, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_sat_word
            (HandlerRun.decCall_simple eps_u256_shl
              (HandlerRun.seq_call_simple eps_stack_push
                (HandlerRun.seq_call_simple eps_pc_add
                  (HandlerRun.ret _)))))))

theorem op_shr_spec : OpHandlerSpec (ofString "op_shr") := by
  refine opHandlerSpec_of_run 498 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_shr rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_shr, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_sat_word
            (HandlerRun.decCall_simple eps_u256_shr
              (HandlerRun.seq_call_simple eps_stack_push
                (HandlerRun.seq_call_simple eps_pc_add
                  (HandlerRun.ret _)))))))

theorem op_sar_spec : OpHandlerSpec (ofString "op_sar") := by
  refine opHandlerSpec_of_run 499 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_sar rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_sar, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_sat_word
            (HandlerRun.decCall_simple eps_u256_sar
              (HandlerRun.seq_call_simple eps_stack_push
                (HandlerRun.seq_call_simple eps_pc_add
                  (HandlerRun.ret _)))))))

theorem op_clz_spec : OpHandlerSpec (ofString "op_clz") := by
  refine opHandlerSpec_of_run 500 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_clz rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_clz, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.seq_charge_gas_const (by decide)
        (HandlerRun.decCall_simple eps_u256_bit_length
          (HandlerRun.seq_call_simple eps_stack_push_word
            (HandlerRun.seq_call_simple eps_pc_add
              (HandlerRun.ret _)))))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
