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

theorem opDispatchSpecGroup09
    (h_op_push : OpHandlerSpec (ofString "op_push"))
    (h_op_dup : OpHandlerSpec (ofString "op_dup"))
    (h_op_swap : OpHandlerSpec (ofString "op_swap"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalk tail) :
    DispatchSpecWalk (dispatchGroup09 tail) := by
  exact
    DispatchSpecWalk.seq
      (DispatchSpecWalk.ite _
        (DispatchSpecWalk.seq
          (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_push _) DispatchSpecWalk.skip)
          (DispatchSpecWalk.seq
            (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_dup _) DispatchSpecWalk.skip)
            (DispatchSpecWalk.callReturn h_op_swap _)))
        DispatchSpecWalk.skip)
      ht

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
