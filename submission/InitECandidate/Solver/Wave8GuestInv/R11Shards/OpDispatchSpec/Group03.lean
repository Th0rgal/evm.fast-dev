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

theorem opDispatchSpecGroup03
    (h_op_and : OpHandlerSpec (ofString "op_and"))
    (h_op_or : OpHandlerSpec (ofString "op_or"))
    (h_op_xor : OpHandlerSpec (ofString "op_xor"))
    (h_op_not : OpHandlerSpec (ofString "op_not"))
    (h_op_byte : OpHandlerSpec (ofString "op_byte"))
    (h_op_shl : OpHandlerSpec (ofString "op_shl"))
    (h_op_shr : OpHandlerSpec (ofString "op_shr"))
    (h_op_sar : OpHandlerSpec (ofString "op_sar"))
    (h_op_clz : OpHandlerSpec (ofString "op_clz")) :
    DispatchSpecWalk dispatchGroup03 := by
  exact
    DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_and _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_or _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_xor _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_not _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_byte _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_shl _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_shr _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_sar _) DispatchSpecWalk.skip)
      (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_clz _) DispatchSpecWalk.skip))))))))

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
