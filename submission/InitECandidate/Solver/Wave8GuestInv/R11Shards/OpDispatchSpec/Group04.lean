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

theorem opDispatchSpecGroup04
    (h_op_keccak : OpHandlerSpec (ofString "op_keccak"))
    (h_op_address : OpHandlerSpec (ofString "op_address"))
    (h_op_balance : OpHandlerSpec (ofString "op_balance"))
    (h_op_origin : OpHandlerSpec (ofString "op_origin"))
    (h_op_caller : OpHandlerSpec (ofString "op_caller"))
    (h_op_callvalue : OpHandlerSpec (ofString "op_callvalue"))
    (h_op_calldataload : OpHandlerSpec (ofString "op_calldataload"))
    (h_op_calldatasize : OpHandlerSpec (ofString "op_calldatasize"))
    (h_op_calldatacopy : OpHandlerSpec (ofString "op_calldatacopy"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalk tail) :
    DispatchSpecWalk (dispatchGroup04 tail) := by
  exact
    DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_keccak _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_address _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_balance _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_origin _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_caller _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_callvalue _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_calldataload _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_calldatasize _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_calldatacopy _) DispatchSpecWalk.skip)
      ht))))))))

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
