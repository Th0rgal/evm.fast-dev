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

theorem opDispatchSpecGroup07
    (h_op_pop : OpHandlerSpec (ofString "op_pop"))
    (h_op_mload : OpHandlerSpec (ofString "op_mload"))
    (h_op_mstore : OpHandlerSpec (ofString "op_mstore"))
    (h_op_mstore8 : OpHandlerSpec (ofString "op_mstore8"))
    (h_op_sload : OpHandlerSpec (ofString "op_sload"))
    (h_op_sstore : OpHandlerSpec (ofString "op_sstore"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalk tail) :
    DispatchSpecWalk (dispatchGroup07 tail) := by
  exact
    DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_pop _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_mload _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_mstore _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_mstore8 _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_sload _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_sstore _) DispatchSpecWalk.skip)
      ht)))))

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
