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
theorem opDispatchGroup05
    (h_op_codesize : TerminatingFunBoundedOn GuestInv (ofString "op_codesize") K.op_codesize)
    (h_op_codecopy : TerminatingFunBoundedOn GuestInv (ofString "op_codecopy") K.op_codecopy)
    (h_op_gasprice : TerminatingFunBoundedOn GuestInv (ofString "op_gasprice") K.op_gasprice)
    (h_op_extcodesize : TerminatingFunBoundedOn GuestInv (ofString "op_extcodesize") K.op_extcodesize)
    (h_op_extcodecopy : TerminatingFunBoundedOn GuestInv (ofString "op_extcodecopy") K.op_extcodecopy)
    (h_op_returndatasize : TerminatingFunBoundedOn GuestInv (ofString "op_returndatasize") K.op_returndatasize)
    (h_op_returndatacopy : TerminatingFunBoundedOn GuestInv (ofString "op_returndatacopy") K.op_returndatacopy)
    (h_op_extcodehash : TerminatingFunBoundedOn GuestInv (ofString "op_extcodehash") K.op_extcodehash)
    :
    DispatchWalk (dispatchGroup05) (dispatchCost05) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_codesize
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
h_op_codecopy
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
h_op_gasprice
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
h_op_extcodesize
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
h_op_extcodecopy
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
h_op_returndatasize
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
h_op_returndatacopy
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_extcodehash
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip))))))))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
