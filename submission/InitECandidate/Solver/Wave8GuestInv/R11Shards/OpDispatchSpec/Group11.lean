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

theorem opDispatchSpecGroup11
    (h_op_create : OpHandlerSpec (ofString "op_create"))
    (h_op_call : OpHandlerSpec (ofString "op_call"))
    (h_op_callcode : OpHandlerSpec (ofString "op_callcode"))
    (h_op_return : OpHandlerSpec (ofString "op_return"))
    (h_op_delegatecall : OpHandlerSpec (ofString "op_delegatecall"))
    (h_op_create2 : OpHandlerSpec (ofString "op_create2"))
    (h_op_staticcall : OpHandlerSpec (ofString "op_staticcall"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalk tail) :
    DispatchSpecWalk (dispatchGroup11 tail) := by
  exact
    DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_create _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_call _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_callcode _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_return _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_delegatecall _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_create2 _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_staticcall _) DispatchSpecWalk.skip)
      ht))))))

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
