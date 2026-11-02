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
theorem opDispatchGroup09
    (h_op_push : TerminatingFunBoundedOn GuestInv (ofString "op_push") K.op_push)
    (h_op_dup : TerminatingFunBoundedOn GuestInv (ofString "op_dup") K.op_dup)
    (h_op_swap : TerminatingFunBoundedOn GuestInv (ofString "op_swap") K.op_swap)
    {tail : ProgHOL 64} {b : Nat} (ht : DispatchWalk tail b) :
    DispatchWalk (dispatchGroup09 tail) (dispatchCost09 b) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_push
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
h_op_dup
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
(DispatchWalk.callReturn
h_op_swap
_
_
(dispatchEntry_guest
_
_))))
DispatchWalk.skip)
ht)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
