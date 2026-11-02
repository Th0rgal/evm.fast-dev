import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.code_imm
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.decode_single

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_op_dupn
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_code_imm : TerminatingFunBoundedOn GuestInv (ofString "code_imm") K.«code_imm»)
    (h_decode_single : TerminatingFunBoundedOn GuestInv (ofString "decode_single") K.«decode_single»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_dupn") K.«op_dupn» := by
  fb_prove 520 Guest.Software.guestFn_op_dupn K.«op_dupn»

theorem fb_op_dupn_of
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») :
    TerminatingFunBoundedOn GuestInv (ofString "op_dupn") K.«op_dupn» :=
  fb_op_dupn h_charge_gas fb_code_imm fb_decode_single h_stack_push h_pc_add

example :
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_code_imm» →
    type_of% Wave8GuestInv.«fb_decode_single» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_dupn» :=
  fb_op_dupn

example :
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_dupn» :=
  fb_op_dupn_of

end InitECandidate.Solver.Wave8Leaves.S08
