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
theorem opDispatchGroup03
    (h_op_and : TerminatingFunBoundedOn GuestInv (ofString "op_and") K.op_and)
    (h_op_or : TerminatingFunBoundedOn GuestInv (ofString "op_or") K.op_or)
    (h_op_xor : TerminatingFunBoundedOn GuestInv (ofString "op_xor") K.op_xor)
    (h_op_not : TerminatingFunBoundedOn GuestInv (ofString "op_not") K.op_not)
    (h_op_byte : TerminatingFunBoundedOn GuestInv (ofString "op_byte") K.op_byte)
    (h_op_shl : TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.op_shl)
    (h_op_shr : TerminatingFunBoundedOn GuestInv (ofString "op_shr") K.op_shr)
    (h_op_sar : TerminatingFunBoundedOn GuestInv (ofString "op_sar") K.op_sar)
    (h_op_clz : TerminatingFunBoundedOn GuestInv (ofString "op_clz") K.op_clz)
    :
    DispatchWalk (dispatchGroup03) (dispatchCost03) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_and
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
h_op_or
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
h_op_xor
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
h_op_not
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
h_op_byte
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
h_op_shl
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
h_op_shr
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
h_op_sar
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_clz
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)))))))))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
