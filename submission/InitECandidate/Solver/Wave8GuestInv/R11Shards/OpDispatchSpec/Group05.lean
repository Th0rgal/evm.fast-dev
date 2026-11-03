import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Walk

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem opDispatchSpecGroup05
    (h_op_codesize : OpHandlerSpec (ofString "op_codesize"))
    (h_op_codecopy : OpHandlerSpec (ofString "op_codecopy"))
    (h_op_gasprice : OpHandlerSpec (ofString "op_gasprice"))
    (h_op_extcodesize : OpHandlerSpec (ofString "op_extcodesize"))
    (h_op_extcodecopy : OpHandlerSpec (ofString "op_extcodecopy"))
    (h_op_returndatasize : OpHandlerSpec (ofString "op_returndatasize"))
    (h_op_returndatacopy : OpHandlerSpec (ofString "op_returndatacopy"))
    (h_op_extcodehash : OpHandlerSpec (ofString "op_extcodehash")) :
    DispatchSpecWalk dispatchGroup05 := by
  exact
    DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_codesize _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_codecopy _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_gasprice _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_extcodesize _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_extcodecopy _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_returndatasize _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_returndatacopy _) DispatchSpecWalk.skip)
      (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_extcodehash _) DispatchSpecWalk.skip)))))))

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
