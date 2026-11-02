import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_delegatecall
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_to_address_masked : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked»)
    (h_extend_memory_cost2 : TerminatingFunBoundedOn GuestInv (ofString "extend_memory_cost2") K.«extend_memory_cost2»)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address»)
    (h_add_sat : TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address»)
    (h_calculate_delegation_cost : TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.«calculate_delegation_cost»)
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»)
    (h_sat_word : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word»)
    (h_calculate_message_call_gas : TerminatingFunBoundedOn GuestInv (ofString "calculate_message_call_gas") K.«calculate_message_call_gas»)
    (h_extend_memory : TerminatingFunBoundedOn GuestInv (ofString "extend_memory") K.«extend_memory»)
    (h_generic_call : TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.«generic_call»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_delegatecall") K.«op_delegatecall» := by
  fb_prove 605 Guest.Software.guestFn_op_delegatecall K.«op_delegatecall»

example :
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_to_address_masked» →
    type_of% Wave8GuestInv.«fb_extend_memory_cost2» →
    type_of% Wave8GuestInv.«fb_is_warm_address» →
    type_of% Wave8GuestInv.«fb_add_sat» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_warm_address» →
    type_of% Wave8GuestInv.«fb_calculate_delegation_cost» →
    type_of% Wave8GuestInv.«fb_ext_code_of» →
    type_of% Wave8GuestInv.«fb_sat_word» →
    type_of% Wave8GuestInv.«fb_calculate_message_call_gas» →
    type_of% Wave8GuestInv.«fb_extend_memory» →
    type_of% Wave8GuestInv.«fb_generic_call» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_delegatecall» :=
  fb_op_delegatecall

end InitECandidate.Solver.Wave8Leaves.S08
