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
theorem opDispatchGroup04
    (h_op_keccak : TerminatingFunBoundedOn GuestInv (ofString "op_keccak") K.op_keccak)
    (h_op_address : TerminatingFunBoundedOn GuestInv (ofString "op_address") K.op_address)
    (h_op_balance : TerminatingFunBoundedOn GuestInv (ofString "op_balance") K.op_balance)
    (h_op_origin : TerminatingFunBoundedOn GuestInv (ofString "op_origin") K.op_origin)
    (h_op_caller : TerminatingFunBoundedOn GuestInv (ofString "op_caller") K.op_caller)
    (h_op_callvalue : TerminatingFunBoundedOn GuestInv (ofString "op_callvalue") K.op_callvalue)
    (h_op_calldataload : TerminatingFunBoundedOn GuestInv (ofString "op_calldataload") K.op_calldataload)
    (h_op_calldatasize : TerminatingFunBoundedOn GuestInv (ofString "op_calldatasize") K.op_calldatasize)
    (h_op_calldatacopy : TerminatingFunBoundedOn GuestInv (ofString "op_calldatacopy") K.op_calldatacopy)
    {tail : ProgHOL 64} {b : Nat} (ht : DispatchWalk tail b) :
    DispatchWalk (dispatchGroup04 tail) (dispatchCost04 b) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_keccak
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
h_op_address
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
h_op_balance
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
h_op_origin
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
h_op_caller
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
h_op_callvalue
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
h_op_calldataload
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
h_op_calldatasize
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
h_op_calldatacopy
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
ht)))))))))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
