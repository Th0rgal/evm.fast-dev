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

theorem opDispatchSpecGroup08
    (h_op_jump : OpHandlerSpec (ofString "op_jump"))
    (h_op_jumpi : OpHandlerSpec (ofString "op_jumpi"))
    (h_op_pc : OpHandlerSpec (ofString "op_pc"))
    (h_op_msize : OpHandlerSpec (ofString "op_msize"))
    (h_op_gas : OpHandlerSpec (ofString "op_gas"))
    (h_op_jumpdest : OpHandlerSpec (ofString "op_jumpdest"))
    (h_op_tload : OpHandlerSpec (ofString "op_tload"))
    (h_op_tstore : OpHandlerSpec (ofString "op_tstore"))
    (h_op_mcopy : OpHandlerSpec (ofString "op_mcopy"))
    (h_op_push : OpHandlerSpec (ofString "op_push")) :
    DispatchSpecWalk dispatchGroup08 := by
  exact
    DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_jump _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_jumpi _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_pc _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_msize _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_gas _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_jumpdest _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_tload _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_tstore _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_mcopy _) DispatchSpecWalk.skip)
      (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_push _) DispatchSpecWalk.skip)))))))))

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
