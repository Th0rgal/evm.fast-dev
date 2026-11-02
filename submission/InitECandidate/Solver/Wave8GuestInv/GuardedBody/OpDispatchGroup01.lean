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
theorem opDispatchGroup01
    (h_op_stop : TerminatingFunBoundedOn GuestInv (ofString "op_stop") K.op_stop)
    (h_op_add : TerminatingFunBoundedOn GuestInv (ofString "op_add") K.op_add)
    (h_op_mul : TerminatingFunBoundedOn GuestInv (ofString "op_mul") K.op_mul)
    (h_op_sub : TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.op_sub)
    (h_op_div : TerminatingFunBoundedOn GuestInv (ofString "op_div") K.op_div)
    (h_op_sdiv : TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.op_sdiv)
    (h_op_mod : TerminatingFunBoundedOn GuestInv (ofString "op_mod") K.op_mod)
    (h_op_smod : TerminatingFunBoundedOn GuestInv (ofString "op_smod") K.op_smod)
    (h_op_addmod : TerminatingFunBoundedOn GuestInv (ofString "op_addmod") K.op_addmod)
    (h_op_mulmod : TerminatingFunBoundedOn GuestInv (ofString "op_mulmod") K.op_mulmod)
    (h_op_exp : TerminatingFunBoundedOn GuestInv (ofString "op_exp") K.op_exp)
    (h_op_signextend : TerminatingFunBoundedOn GuestInv (ofString "op_signextend") K.op_signextend)
    :
    DispatchWalk (dispatchGroup01) (dispatchCost01) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_stop
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
h_op_add
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
h_op_mul
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
h_op_sub
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
h_op_div
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
h_op_sdiv
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
h_op_mod
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
h_op_smod
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
h_op_addmod
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
h_op_mulmod
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
h_op_exp
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_signextend
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip))))))))))))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
