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
theorem opDispatchGroup06
    (h_op_blockhash : TerminatingFunBoundedOn GuestInv (ofString "op_blockhash") K.op_blockhash)
    (h_op_coinbase : TerminatingFunBoundedOn GuestInv (ofString "op_coinbase") K.op_coinbase)
    (h_op_timestamp : TerminatingFunBoundedOn GuestInv (ofString "op_timestamp") K.op_timestamp)
    (h_op_number : TerminatingFunBoundedOn GuestInv (ofString "op_number") K.op_number)
    (h_op_prevrandao : TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.op_prevrandao)
    (h_op_gaslimit : TerminatingFunBoundedOn GuestInv (ofString "op_gaslimit") K.op_gaslimit)
    (h_op_chainid : TerminatingFunBoundedOn GuestInv (ofString "op_chainid") K.op_chainid)
    (h_op_selfbalance : TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.op_selfbalance)
    (h_op_basefee : TerminatingFunBoundedOn GuestInv (ofString "op_basefee") K.op_basefee)
    (h_op_blobhash : TerminatingFunBoundedOn GuestInv (ofString "op_blobhash") K.op_blobhash)
    (h_op_blobbasefee : TerminatingFunBoundedOn GuestInv (ofString "op_blobbasefee") K.op_blobbasefee)
    (h_op_slotnum : TerminatingFunBoundedOn GuestInv (ofString "op_slotnum") K.op_slotnum)
    {tail : ProgHOL 64} {b : Nat} (ht : DispatchWalk tail b) :
    DispatchWalk (dispatchGroup06 tail) (dispatchCost06 b) := by
  exact (DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.callReturn
h_op_blockhash
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
h_op_coinbase
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
h_op_timestamp
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
h_op_number
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
h_op_prevrandao
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
h_op_gaslimit
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
h_op_chainid
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
h_op_selfbalance
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
h_op_basefee
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
h_op_blobhash
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
h_op_blobbasefee
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
h_op_slotnum
_
_
(dispatchEntry_guest
_
_))
DispatchWalk.skip)
ht))))))))))))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
