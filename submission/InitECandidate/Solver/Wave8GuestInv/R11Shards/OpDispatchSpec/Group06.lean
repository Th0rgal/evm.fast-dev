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

theorem opDispatchSpecGroup06
    (h_op_blockhash : OpHandlerSpec (ofString "op_blockhash"))
    (h_op_coinbase : OpHandlerSpec (ofString "op_coinbase"))
    (h_op_timestamp : OpHandlerSpec (ofString "op_timestamp"))
    (h_op_number : OpHandlerSpec (ofString "op_number"))
    (h_op_prevrandao : OpHandlerSpec (ofString "op_prevrandao"))
    (h_op_gaslimit : OpHandlerSpec (ofString "op_gaslimit"))
    (h_op_chainid : OpHandlerSpec (ofString "op_chainid"))
    (h_op_selfbalance : OpHandlerSpec (ofString "op_selfbalance"))
    (h_op_basefee : OpHandlerSpec (ofString "op_basefee"))
    (h_op_blobhash : OpHandlerSpec (ofString "op_blobhash"))
    (h_op_blobbasefee : OpHandlerSpec (ofString "op_blobbasefee"))
    (h_op_slotnum : OpHandlerSpec (ofString "op_slotnum"))
    {tail : ProgHOL 64} (ht : DispatchSpecWalk tail) :
    DispatchSpecWalk (dispatchGroup06 tail) := by
  exact
    DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_blockhash _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_coinbase _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_timestamp _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_number _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_prevrandao _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_gaslimit _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_chainid _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_selfbalance _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_basefee _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_blobhash _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_blobbasefee _) DispatchSpecWalk.skip)
    (DispatchSpecWalk.seq (DispatchSpecWalk.ite _ (DispatchSpecWalk.callReturn h_op_slotnum _) DispatchSpecWalk.skip)
      ht)))))))))))

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
