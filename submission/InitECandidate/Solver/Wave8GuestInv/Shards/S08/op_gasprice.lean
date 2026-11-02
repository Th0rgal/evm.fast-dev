import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_gasprice
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_gasprice") K.«op_gasprice» := by
  fb_prove 542 Guest.Software.guestFn_op_gasprice K.«op_gasprice»

example :
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_gasprice» :=
  fb_op_gasprice

end InitECandidate.Solver.Wave8Leaves.S08
