import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure3
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_10
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_16
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P11

/-! Closed 0-sorry adapters for `start_child`, `generic_call`, `op_staticcall`,
`op_call`, and `op_callcode` with zero `LeafStatements` helper arguments. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Adapters.StaticCall

open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.FastGen

theorem «fb_start_child» :
    TerminatingFunBoundedOn GuestInv (ofString "start_child") K.«start_child» :=
  FastGen.fb_start_child_of
    Merged.fb_destroy_storage
    Merged.fb_frame_open
    Merged.fb_frame_start
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_increment_nonce»
    Merged.fb_mark_account_created

theorem «fb_generic_call» :
    TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.«generic_call» := by
  have _ := Merged.fb_set_retdata
  have _ := Merged.fb_credit_state_gas_refund
  have _ := Merged.fb_scratch_mark
  have _ := Merged.fb_frame_mem_mark
  have _ := FastGen.fb_child_message
  have _ := «fb_start_child»
  fg_unfold 601 Guest.Software.guestFn_generic_call
  apply TerminatingProgBoundedOn.weaken'
  · fg_step_auto
  · fg_arith K.generic_call

theorem «fb_op_staticcall» :
    TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.«op_staticcall» :=
  R10Shards.Fast_RemoteLeavesB2.fb_op_staticcall_of
    Merged.fb_htab_has
    Merged.fb_htab_set
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ext_code_of»
    «fb_generic_call»

theorem «fb_op_call» :
    TerminatingFunBoundedOn GuestInv (ofString "op_call") K.«op_call» :=
  R10Shards.P11.fb_op_call
    Merged.fb_stack_pop
    Merged.fb_to_address_masked
    P12_P15.Callees.fb_extend_memory_cost2
    Merged.fb_is_warm_address
    P12_P15.Callees.fb_u256_is_zero
    P12_P15.Callees.fb_add_sat
    P12_P15.Callees.fb_charge_gas
    Merged.fb_warm_address
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_delegation_cost»
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ext_code_of»
    Merged.fb_sat_word
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_message_call_gas»
    P12_P15.Callees.fb_extend_memory
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account»
    P12_P15.Callees.fb_u256_lt
    Merged.fb_stack_push
    Merged.fb_set_retdata
    Merged.fb_credit_state_gas_refund
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_is_account_alive»
    Merged.fb_charge_state_gas
    «fb_generic_call»
    Merged.fb_pc_add

theorem «fb_op_callcode» :
    TerminatingFunBoundedOn GuestInv (ofString "op_callcode") K.«op_callcode» :=
  R10Shards.P11.fb_op_callcode
    Merged.fb_stack_pop
    Merged.fb_to_address_masked
    P12_P15.Callees.fb_extend_memory_cost2
    Merged.fb_is_warm_address
    P12_P15.Callees.fb_u256_is_zero
    P12_P15.Callees.fb_add_sat
    P12_P15.Callees.fb_charge_gas
    Merged.fb_warm_address
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_delegation_cost»
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_ext_code_of»
    Merged.fb_sat_word
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_calculate_message_call_gas»
    P12_P15.Callees.fb_extend_memory
    InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_get_account»
    P12_P15.Callees.fb_u256_lt
    Merged.fb_stack_push
    Merged.fb_set_retdata
    «fb_generic_call»
    Merged.fb_pc_add

end InitECandidate.Solver.Wave8GuestInv.R11Adapters.StaticCall
