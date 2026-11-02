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
theorem opDispatchGroup10
    (h_op_log : TerminatingFunBoundedOn GuestInv (ofString "op_log") K.op_log)
    (h_op_dupn : TerminatingFunBoundedOn GuestInv (ofString "op_dupn") K.op_dupn)
    (h_op_swapn : TerminatingFunBoundedOn GuestInv (ofString "op_swapn") K.op_swapn)
    (h_op_exchange : TerminatingFunBoundedOn GuestInv (ofString "op_exchange") K.op_exchange)
    {tail : ProgHOL 64} {b : Nat} (ht : DispatchWalk tail b) :
    DispatchWalk (dispatchGroup10 tail) (dispatchCost10 b) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_log
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
h_op_dupn
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
h_op_swapn
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
h_op_exchange
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
ht))))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
