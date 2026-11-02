import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_extcodesize
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_to_address_masked : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked»)
    (h_access_gas_cost : TerminatingFunBoundedOn GuestInv (ofString "access_gas_cost") K.«access_gas_cost»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_warm_after_charge : TerminatingFunBoundedOn GuestInv (ofString "warm_after_charge") K.«warm_after_charge»)
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»)
    (h_stack_push_word : TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_extcodesize") K.«op_extcodesize» := by
  fb_prove 544 Guest.Software.guestFn_op_extcodesize K.«op_extcodesize»

example :
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_to_address_masked» →
    type_of% Wave8GuestInv.«fb_access_gas_cost» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_warm_after_charge» →
    type_of% Wave8GuestInv.«fb_ext_code_of» →
    type_of% Wave8GuestInv.«fb_stack_push_word» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_extcodesize» :=
  fb_op_extcodesize

end InitECandidate.Solver.Wave8Leaves.S08
