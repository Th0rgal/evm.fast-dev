import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchDefs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv.RunFramesRace

/-- Literal opcode branches; salvaged from race-gbody-runframes-sol. -/
theorem opDispatchGroup07
    (h_op_pop : TerminatingFunBoundedOn GuestInv (ofString "op_pop") K.op_pop)
    (h_op_mload : TerminatingFunBoundedOn GuestInv (ofString "op_mload") K.op_mload)
    (h_op_mstore : TerminatingFunBoundedOn GuestInv (ofString "op_mstore") K.op_mstore)
    (h_op_mstore8 : TerminatingFunBoundedOn GuestInv (ofString "op_mstore8") K.op_mstore8)
    (h_op_sload : TerminatingFunBoundedOn EvmRun (ofString "op_sload") K.op_sload)
    (h_op_sstore : TerminatingFunBoundedOn EvmRun (ofString "op_sstore") K.op_sstore)
    {tail : ProgHOL 64} {b : Nat} (ht : DispatchWalk tail b) :
    DispatchWalk (dispatchGroup07 tail) (dispatchCost07 b) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_pop
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_mload
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_mstore
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_mstore8
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_sload
_
_
(dispatchEntry_run
_
_))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_sstore
_
_
(dispatchEntry_run
_
_))
DispatchWalk.skip)
ht))))))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
