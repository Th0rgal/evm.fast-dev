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

theorem opDispatchSpecGroup01
    (h_op_stop : OpHandlerSpec (ofString "op_stop"))
    (h_op_add : OpHandlerSpec (ofString "op_add"))
    (h_op_mul : OpHandlerSpec (ofString "op_mul"))
    (h_op_sub : OpHandlerSpec (ofString "op_sub"))
    (h_op_div : OpHandlerSpec (ofString "op_div"))
    (h_op_sdiv : OpHandlerSpec (ofString "op_sdiv"))
    (h_op_mod : OpHandlerSpec (ofString "op_mod"))
    (h_op_smod : OpHandlerSpec (ofString "op_smod"))
    (h_op_addmod : OpHandlerSpec (ofString "op_addmod"))
    (h_op_mulmod : OpHandlerSpec (ofString "op_mulmod"))
    (h_op_exp : OpHandlerSpec (ofString "op_exp"))
    (h_op_signextend : OpHandlerSpec (ofString "op_signextend")) :
    DispatchSpecWalk dispatchGroup01 := by
  exact
    DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_stop _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_add _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_mul _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_sub _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_div _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_sdiv _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_mod _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_smod _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_addmod _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_mulmod _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_exp _) DispatchSpecWalk.skip)
      (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_signextend _) DispatchSpecWalk.skip)))))))))))

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
