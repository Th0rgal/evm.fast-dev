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
theorem opDispatchGroup02
    (h_op_lt : TerminatingFunBoundedOn GuestInv (ofString "op_lt") K.op_lt)
    (h_op_gt : TerminatingFunBoundedOn GuestInv (ofString "op_gt") K.op_gt)
    (h_op_slt : TerminatingFunBoundedOn GuestInv (ofString "op_slt") K.op_slt)
    (h_op_sgt : TerminatingFunBoundedOn GuestInv (ofString "op_sgt") K.op_sgt)
    (h_op_eq : TerminatingFunBoundedOn GuestInv (ofString "op_eq") K.op_eq)
    (h_op_iszero : TerminatingFunBoundedOn GuestInv (ofString "op_iszero") K.op_iszero)
    {tail : ProgHOL 64} {b : Nat} (ht : DispatchWalk tail b) :
    DispatchWalk (dispatchGroup02 tail) (dispatchCost02 b) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_lt
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
h_op_gt
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
h_op_slt
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
h_op_sgt
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
h_op_eq
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
h_op_iszero
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
ht))))))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
