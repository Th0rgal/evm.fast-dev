import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_exp
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_u256_byte_length : TerminatingFunBoundedOn GuestInv (ofString "u256_byte_length") K.«u256_byte_length»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_u256_exp : TerminatingFunBoundedOn GuestInv (ofString "u256_exp") K.«u256_exp»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_exp") K.«op_exp» := by
  fb_prove 484 Guest.Software.guestFn_op_exp K.«op_exp»

example :
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_u256_byte_length» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_u256_exp» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_exp» :=
  fb_op_exp

end InitECandidate.Solver.Wave8Leaves.S08
