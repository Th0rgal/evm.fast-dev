import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05bEnv4
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05bEnv5

/-! # OpHandlerSpec Group 05bEnv (`OpHandlers-A`): remaining 6 block/env opcodes & full re-export -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

theorem op_gaslimit_spec : OpHandlerSpec (ofString "op_gaslimit") := by
  refine opHandlerSpec_of_run 558 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_gaslimit rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_gaslimit, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_block_env
        (HandlerRun.seq_call_simple eps_stack_push_word
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_chainid_spec : OpHandlerSpec (ofString "op_chainid") := by
  refine opHandlerSpec_of_run 559 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_chainid rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_chainid, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_block_env
        (HandlerRun.seq_call_simple eps_stack_push_word
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_basefee_spec : OpHandlerSpec (ofString "op_basefee") := by
  refine opHandlerSpec_of_run 551 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_basefee rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_basefee, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_block_env
        (HandlerRun.seq_call_simple eps_stack_push
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_blobhash_spec : OpHandlerSpec (ofString "op_blobhash") := by
  refine opHandlerSpec_of_run 552 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_blobhash rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_blobhash, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.seq_charge_gas_const (by decide)
        (HandlerRun.dec_simple
          (HandlerRun.dec_simple
            (HandlerRun.decCall_simple eps_sat_word
              (HandlerRun.seq_ite_simple
                (HandlerRun.seq_decCall_call_simple eps_u256_from_be eps_stack_push
                  (HandlerRun.seq_call_simple eps_pc_add
                    (HandlerRun.ret _)))
                (HandlerRun.seq_call_simple eps_stack_push
                  (HandlerRun.seq_call_simple eps_pc_add
                    (HandlerRun.ret _))))))))

theorem op_blobbasefee_spec : OpHandlerSpec (ofString "op_blobbasefee") := by
  refine opHandlerSpec_of_run 553 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_blobbasefee rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_blobbasefee, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_block_env
        (HandlerRun.decCall_simple eps_calculate_blob_gas_price
          (HandlerRun.seq_call_simple eps_stack_push
            (HandlerRun.seq_call_simple eps_pc_add
              (HandlerRun.ret _)))))

theorem op_slotnum_spec : OpHandlerSpec (ofString "op_slotnum") := by
  refine opHandlerSpec_of_run 561 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_slotnum rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_slotnum, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_block_env
        (HandlerRun.seq_call_simple eps_stack_push_word
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
