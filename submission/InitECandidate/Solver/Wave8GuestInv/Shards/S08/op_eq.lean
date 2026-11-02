import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.stack_push_bool

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_eq
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_u256_eq : TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq»)
    (h_stack_push_bool : TerminatingFunBoundedOn GuestInv (ofString "stack_push_bool") K.«stack_push_bool»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_eq") K.«op_eq» := by
  fb_prove 490 Guest.Software.guestFn_op_eq K.«op_eq»

theorem fb_op_eq_of
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_u256_eq : TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_eq") K.«op_eq» :=
  fb_op_eq h_stack_pop h_charge_gas h_u256_eq (fb_stack_push_bool h_stack_push) h_pc_add

example :
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_u256_eq» →
    type_of% Wave8GuestInv.«fb_stack_push_bool» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_eq» :=
  fb_op_eq

example :
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_u256_eq» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_eq» :=
  fb_op_eq_of

end InitECandidate.Solver.Wave8Leaves.S08
