import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_coinbase
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_block_env : TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env»)
    (h_address_to_u256 : TerminatingFunBoundedOn GuestInv (ofString "address_to_u256") K.«address_to_u256»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_coinbase") K.«op_coinbase» := by
  fb_prove 555 Guest.Software.guestFn_op_coinbase K.«op_coinbase»

example :
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_block_env» →
    type_of% Wave8GuestInv.«fb_address_to_u256» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_coinbase» :=
  fb_op_coinbase

end InitECandidate.Solver.Wave8Leaves.S08
