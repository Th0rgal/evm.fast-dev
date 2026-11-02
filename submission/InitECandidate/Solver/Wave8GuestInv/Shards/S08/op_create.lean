import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.require_not_static

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_create
    (h_require_not_static : TerminatingFunBoundedOn GuestInv (ofString "require_not_static") K.«require_not_static»)
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_sat_word : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word»)
    (h_extend_memory_cost1 : TerminatingFunBoundedOn GuestInv (ofString "extend_memory_cost1") K.«extend_memory_cost1»)
    (h_words_of : TerminatingFunBoundedOn GuestInv (ofString "words_of") K.«words_of»)
    (h_add_sat : TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_extend_memory : TerminatingFunBoundedOn GuestInv (ofString "extend_memory") K.«extend_memory»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_compute_contract_address : TerminatingFunBoundedOn GuestInv (ofString "compute_contract_address") K.«compute_contract_address»)
    (h_generic_create : TerminatingFunBoundedOn GuestInv (ofString "generic_create") K.«generic_create»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_create") K.«op_create» := by
  fb_prove 599 Guest.Software.guestFn_op_create K.«op_create»

theorem fb_op_create_of
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_sat_word : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word»)
    (h_extend_memory_cost1 : TerminatingFunBoundedOn GuestInv (ofString "extend_memory_cost1") K.«extend_memory_cost1»)
    (h_words_of : TerminatingFunBoundedOn GuestInv (ofString "words_of") K.«words_of»)
    (h_add_sat : TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_extend_memory : TerminatingFunBoundedOn GuestInv (ofString "extend_memory") K.«extend_memory»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_compute_contract_address : TerminatingFunBoundedOn GuestInv (ofString "compute_contract_address") K.«compute_contract_address»)
    (h_generic_create : TerminatingFunBoundedOn GuestInv (ofString "generic_create") K.«generic_create»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_create") K.«op_create» :=
  fb_op_create fb_require_not_static h_stack_pop h_sat_word h_extend_memory_cost1
    h_words_of h_add_sat h_charge_gas h_extend_memory h_get_account on_alloc
    h_compute_contract_address h_generic_create h_pc_add

example :
    type_of% Wave8GuestInv.«fb_require_not_static» →
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_sat_word» →
    type_of% Wave8GuestInv.«fb_extend_memory_cost1» →
    type_of% Wave8GuestInv.«fb_words_of» →
    type_of% Wave8GuestInv.«fb_add_sat» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_extend_memory» →
    type_of% Wave8GuestInv.«fb_get_account» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_compute_contract_address» →
    type_of% Wave8GuestInv.«fb_generic_create» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_create» :=
  fb_op_create

example :
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_sat_word» →
    type_of% Wave8GuestInv.«fb_extend_memory_cost1» →
    type_of% Wave8GuestInv.«fb_words_of» →
    type_of% Wave8GuestInv.«fb_add_sat» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_extend_memory» →
    type_of% Wave8GuestInv.«fb_get_account» →
    type_of% Wave8GuestInv.«fb_compute_contract_address» →
    type_of% Wave8GuestInv.«fb_generic_create» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_create» :=
  fb_op_create_of

end InitECandidate.Solver.Wave8Leaves.S08
