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
theorem opDispatchGroup11
    (h_op_create : TerminatingFunBoundedOn GuestInv (ofString "op_create") K.op_create)
    (h_op_call : TerminatingFunBoundedOn GuestInv (ofString "op_call") K.op_call)
    (h_op_callcode : TerminatingFunBoundedOn GuestInv (ofString "op_callcode") K.op_callcode)
    (h_op_return : TerminatingFunBoundedOn GuestInv (ofString "op_return") K.op_return)
    (h_op_delegatecall : TerminatingFunBoundedOn GuestInv (ofString "op_delegatecall") K.op_delegatecall)
    (h_op_create2 : TerminatingFunBoundedOn GuestInv (ofString "op_create2") K.op_create2)
    (h_op_staticcall : TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.op_staticcall)
    {tail : ProgHOL 64} {b : Nat} (ht : DispatchWalk tail b) :
    DispatchWalk (dispatchGroup11 tail) (dispatchCost11 b) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_create
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
h_op_call
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
h_op_callcode
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
h_op_return
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
h_op_delegatecall
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
h_op_create2
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
h_op_staticcall
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
ht)))))))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
