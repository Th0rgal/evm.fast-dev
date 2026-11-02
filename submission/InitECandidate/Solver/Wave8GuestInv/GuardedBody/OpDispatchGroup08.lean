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
theorem opDispatchGroup08
    (h_op_jump : TerminatingFunBoundedOn GuestInv (ofString "op_jump") K.op_jump)
    (h_op_jumpi : TerminatingFunBoundedOn GuestInv (ofString "op_jumpi") K.op_jumpi)
    (h_op_pc : TerminatingFunBoundedOn GuestInv (ofString "op_pc") K.op_pc)
    (h_op_msize : TerminatingFunBoundedOn GuestInv (ofString "op_msize") K.op_msize)
    (h_op_gas : TerminatingFunBoundedOn GuestInv (ofString "op_gas") K.op_gas)
    (h_op_jumpdest : TerminatingFunBoundedOn GuestInv (ofString "op_jumpdest") K.op_jumpdest)
    (h_op_tload : TerminatingFunBoundedOn GuestInv (ofString "op_tload") K.op_tload)
    (h_op_tstore : TerminatingFunBoundedOn GuestInv (ofString "op_tstore") K.op_tstore)
    (h_op_mcopy : TerminatingFunBoundedOn GuestInv (ofString "op_mcopy") K.op_mcopy)
    (h_op_push : TerminatingFunBoundedOn GuestInv (ofString "op_push") K.op_push)
    :
    DispatchWalk (dispatchGroup08) (dispatchCost08) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_jump
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
h_op_jumpi
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
h_op_pc
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
h_op_msize
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
h_op_gas
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
h_op_jumpdest
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
h_op_tload
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
h_op_tstore
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
h_op_mcopy
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_push
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip))))))))))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
