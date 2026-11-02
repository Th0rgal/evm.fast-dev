import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_extcodehash
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_to_address_masked : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked»)
    (h_access_gas_cost : TerminatingFunBoundedOn GuestInv (ofString "access_gas_cost") K.«access_gas_cost»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_warm_after_charge : TerminatingFunBoundedOn GuestInv (ofString "warm_after_charge") K.«warm_after_charge»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_acct_is_empty : TerminatingFunBoundedOn GuestInv (ofString "acct_is_empty") K.«acct_is_empty»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_u256_from_be : TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_extcodehash") K.«op_extcodehash» := by
  fb_prove 548 Guest.Software.guestFn_op_extcodehash K.«op_extcodehash»

example :
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_to_address_masked» →
    type_of% Wave8GuestInv.«fb_access_gas_cost» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_warm_after_charge» →
    type_of% Wave8GuestInv.«fb_get_account» →
    type_of% Wave8GuestInv.«fb_acct_is_empty» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_u256_from_be» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_extcodehash» :=
  fb_op_extcodehash

end InitECandidate.Solver.Wave8Leaves.S08
