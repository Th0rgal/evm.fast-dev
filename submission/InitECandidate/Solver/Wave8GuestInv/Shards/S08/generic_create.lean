import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_generic_create
    (h_set_retdata : TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.«set_retdata»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_u256_lt : TerminatingFunBoundedOn GuestInv (ofString "u256_lt") K.«u256_lt»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address»)
    (h_is_account_alive : TerminatingFunBoundedOn GuestInv (ofString "is_account_alive") K.«is_account_alive»)
    (h_charge_state_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas»)
    (h_account_deployable : TerminatingFunBoundedOn GuestInv (ofString "account_deployable") K.«account_deployable»)
    (h_increment_nonce : TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce»)
    (h_credit_state_gas_refund : TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.«credit_state_gas_refund»)
    (h_scratch_mark : TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark»)
    (h_frame_mem_mark : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_mark") K.«frame_mem_mark»)
    (h_child_message : TerminatingFunBoundedOn GuestInv (ofString "child_message") K.«child_message»)
    (h_start_child : TerminatingFunBoundedOn GuestInv (ofString "start_child") K.«start_child») :
    TerminatingFunBoundedOn GuestInv (ofString "generic_create") K.«generic_create» := by
  fb_prove 598 Guest.Software.guestFn_generic_create K.«generic_create»

theorem fb_generic_create_of
    (h_set_retdata : TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.«set_retdata»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_u256_lt : TerminatingFunBoundedOn GuestInv (ofString "u256_lt") K.«u256_lt»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address»)
    (h_is_account_alive : TerminatingFunBoundedOn GuestInv (ofString "is_account_alive") K.«is_account_alive»)
    (h_charge_state_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas»)
    (h_account_deployable : TerminatingFunBoundedOn GuestInv (ofString "account_deployable") K.«account_deployable»)
    (h_increment_nonce : TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce»)
    (h_credit_state_gas_refund : TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.«credit_state_gas_refund»)
    (h_child_message : TerminatingFunBoundedOn GuestInv (ofString "child_message") K.«child_message»)
    (h_start_child : TerminatingFunBoundedOn GuestInv (ofString "start_child") K.«start_child») :
    TerminatingFunBoundedOn GuestInv (ofString "generic_create") K.«generic_create» :=
  fb_generic_create h_set_retdata h_get_account h_u256_lt h_stack_push
    h_warm_address h_is_account_alive h_charge_state_gas h_account_deployable
    h_increment_nonce h_credit_state_gas_refund on_scratch_mark on_frame_mem_mark
    h_child_message h_start_child

example :
    type_of% Wave8GuestInv.«fb_set_retdata» →
    type_of% Wave8GuestInv.«fb_get_account» →
    type_of% Wave8GuestInv.«fb_u256_lt» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_warm_address» →
    type_of% Wave8GuestInv.«fb_is_account_alive» →
    type_of% Wave8GuestInv.«fb_charge_state_gas» →
    type_of% Wave8GuestInv.«fb_account_deployable» →
    type_of% Wave8GuestInv.«fb_increment_nonce» →
    type_of% Wave8GuestInv.«fb_credit_state_gas_refund» →
    type_of% Wave8GuestInv.«fb_scratch_mark» →
    type_of% Wave8GuestInv.«fb_frame_mem_mark» →
    type_of% Wave8GuestInv.«fb_child_message» →
    type_of% Wave8GuestInv.«fb_start_child» →
    type_of% Wave8GuestInv.«fb_generic_create» :=
  fb_generic_create

example :
    type_of% Wave8GuestInv.«fb_set_retdata» →
    type_of% Wave8GuestInv.«fb_get_account» →
    type_of% Wave8GuestInv.«fb_u256_lt» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_warm_address» →
    type_of% Wave8GuestInv.«fb_is_account_alive» →
    type_of% Wave8GuestInv.«fb_charge_state_gas» →
    type_of% Wave8GuestInv.«fb_account_deployable» →
    type_of% Wave8GuestInv.«fb_increment_nonce» →
    type_of% Wave8GuestInv.«fb_credit_state_gas_refund» →
    type_of% Wave8GuestInv.«fb_child_message» →
    type_of% Wave8GuestInv.«fb_start_child» →
    type_of% Wave8GuestInv.«fb_generic_create» :=
  fb_generic_create_of

end InitECandidate.Solver.Wave8Leaves.S08
