import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.code_imm
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.stack_swap_positions

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_exchange
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_code_imm : TerminatingFunBoundedOn GuestInv (ofString "code_imm") K.«code_imm»)
    (h_max : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max»)
    (h_stack_swap_positions : TerminatingFunBoundedOn GuestInv (ofString "stack_swap_positions") K.«stack_swap_positions»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_exchange") K.«op_exchange» := by
  fb_prove 522 Guest.Software.guestFn_op_exchange K.«op_exchange»

theorem fb_op_exchange_of
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_max : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_exchange") K.«op_exchange» :=
  fb_op_exchange h_charge_gas fb_code_imm h_max fb_stack_swap_positions h_pc_add

example :
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_code_imm» →
    type_of% Wave8GuestInv.«fb_max» →
    type_of% Wave8GuestInv.«fb_stack_swap_positions» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_exchange» :=
  fb_op_exchange

example :
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_max» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_exchange» :=
  fb_op_exchange_of

end InitECandidate.Solver.Wave8Leaves.S08
