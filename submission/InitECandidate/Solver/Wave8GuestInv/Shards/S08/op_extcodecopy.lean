import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_extcodecopy
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_to_address_masked : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked»)
    (h_sat_word : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word»)
    (h_words_of : TerminatingFunBoundedOn GuestInv (ofString "words_of") K.«words_of»)
    (h_extend_memory_cost1 : TerminatingFunBoundedOn GuestInv (ofString "extend_memory_cost1") K.«extend_memory_cost1»)
    (h_access_gas_cost : TerminatingFunBoundedOn GuestInv (ofString "access_gas_cost") K.«access_gas_cost»)
    (h_add_sat : TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_warm_after_charge : TerminatingFunBoundedOn GuestInv (ofString "warm_after_charge") K.«warm_after_charge»)
    (h_extend_memory : TerminatingFunBoundedOn GuestInv (ofString "extend_memory") K.«extend_memory»)
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»)
    (h_buffer_read : TerminatingFunBoundedOn GuestInv (ofString "buffer_read") K.«buffer_read»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_extcodecopy") K.«op_extcodecopy» := by
  fb_prove 545 Guest.Software.guestFn_op_extcodecopy K.«op_extcodecopy»

example :
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_to_address_masked» →
    type_of% Wave8GuestInv.«fb_sat_word» →
    type_of% Wave8GuestInv.«fb_words_of» →
    type_of% Wave8GuestInv.«fb_extend_memory_cost1» →
    type_of% Wave8GuestInv.«fb_access_gas_cost» →
    type_of% Wave8GuestInv.«fb_add_sat» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_warm_after_charge» →
    type_of% Wave8GuestInv.«fb_extend_memory» →
    type_of% Wave8GuestInv.«fb_ext_code_of» →
    type_of% Wave8GuestInv.«fb_buffer_read» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_extcodecopy» :=
  fb_op_extcodecopy

end InitECandidate.Solver.Wave8Leaves.S08
