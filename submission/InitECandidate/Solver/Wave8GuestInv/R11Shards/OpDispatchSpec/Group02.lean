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

theorem opDispatchSpecGroup02
    (h_op_lt : OpHandlerSpec (ofString "op_lt"))
    (h_op_gt : OpHandlerSpec (ofString "op_gt"))
    (h_op_slt : OpHandlerSpec (ofString "op_slt"))
    (h_op_sgt : OpHandlerSpec (ofString "op_sgt"))
    (h_op_eq : OpHandlerSpec (ofString "op_eq"))
    (h_op_iszero : OpHandlerSpec (ofString "op_iszero"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalk tail) :
    DispatchSpecWalk (dispatchGroup02 tail) := by
  exact
    DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_lt _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_gt _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_slt _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_sgt _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_eq _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_iszero _) DispatchSpecWalk.skip)
      ht)))))

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
