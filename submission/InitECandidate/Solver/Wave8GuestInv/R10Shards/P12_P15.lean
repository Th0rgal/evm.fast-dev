import InitECandidate.Solver.Wave8GuestInv.R10Shards.P12_P15Callees

/-! Shards P12 + P15: unconditional R11 `TerminatingFunBoundedOn GuestInv` proofs for all 14 opcode
fields:
- Shard P12: `fb_op_callvalue`, `fb_op_chainid`, `fb_op_clz`, `fb_op_codecopy`, `fb_op_codesize`,
  `fb_op_jumpdest`, `fb_op_jumpi`
- Shard P15: `fb_op_origin`, `fb_op_pc`, `fb_op_pop`, `fb_op_push`, `fb_op_return`,
  `fb_op_returndatacopy`, `fb_op_revert`
Discharges every transitive `fb_*` callee without referencing `LeafStatements.lean`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.P12_P15

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P12_P15.Common

theorem fb_copy_from_buffer :
    TerminatingFunBoundedOn GuestInv (ofString "copy_from_buffer") K.«copy_from_buffer» := by
  have _ := Callees.fb_add_sat
  have _ := Callees.fb_buffer_read
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_extend_memory
  have _ := Callees.fb_extend_memory_cost1
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_sat_word
  have _ := Callees.fb_stack_pop
  have _ := Callees.fb_words_of
  fb_prove 538 Guest.Software.guestFn_copy_from_buffer K.«copy_from_buffer»

/-! ### Shard P12 (7 fields) -/

theorem fb_op_callvalue :
    TerminatingFunBoundedOn GuestInv (ofString "op_callvalue") K.«op_callvalue» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_push
  fb_prove 535 Guest.Software.guestFn_op_callvalue K.«op_callvalue»

theorem fb_op_chainid :
    TerminatingFunBoundedOn GuestInv (ofString "op_chainid") K.«op_chainid» := by
  have _ := Callees.fb_block_env
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_push_word
  fb_prove 559 Guest.Software.guestFn_op_chainid K.«op_chainid»

theorem fb_op_clz :
    TerminatingFunBoundedOn GuestInv (ofString "op_clz") K.«op_clz» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_pop
  have _ := Callees.fb_stack_push_word
  have _ := Callees.fb_u256_bit_length
  fb_prove 500 Guest.Software.guestFn_op_clz K.«op_clz»

theorem fb_op_codecopy :
    TerminatingFunBoundedOn GuestInv (ofString "op_codecopy") K.«op_codecopy» := by
  have _ := fb_copy_from_buffer
  fb_prove 541 Guest.Software.guestFn_op_codecopy K.«op_codecopy»

theorem fb_op_codesize :
    TerminatingFunBoundedOn GuestInv (ofString "op_codesize") K.«op_codesize» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_push_word
  fb_prove 540 Guest.Software.guestFn_op_codesize K.«op_codesize»

theorem fb_op_jumpdest :
    TerminatingFunBoundedOn GuestInv (ofString "op_jumpdest") K.«op_jumpdest» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  fb_prove 507 Guest.Software.guestFn_op_jumpdest K.«op_jumpdest»

theorem fb_op_jumpi :
    TerminatingFunBoundedOn GuestInv (ofString "op_jumpi") K.«op_jumpi» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_is_valid_jumpdest
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_pop
  have _ := Callees.fb_u256_is_zero
  fb_prove 504 Guest.Software.guestFn_op_jumpi K.«op_jumpi»

/-! ### Shard P15 (7 fields) -/

theorem fb_op_origin :
    TerminatingFunBoundedOn GuestInv (ofString "op_origin") K.«op_origin» := by
  have _ := Callees.fb_address_to_u256
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_push
  fb_prove 533 Guest.Software.guestFn_op_origin K.«op_origin»

theorem fb_op_pc :
    TerminatingFunBoundedOn GuestInv (ofString "op_pc") K.«op_pc» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_push_word
  fb_prove 505 Guest.Software.guestFn_op_pc K.«op_pc»

theorem fb_op_pop :
    TerminatingFunBoundedOn GuestInv (ofString "op_pop") K.«op_pop» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_pop
  fb_prove 513 Guest.Software.guestFn_op_pop K.«op_pop»

theorem fb_op_push :
    TerminatingFunBoundedOn GuestInv (ofString "op_push") K.«op_push» := by
  have _ := Callees.fb_alloc
  have _ := Callees.fb_buffer_read
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_heap_mark
  have _ := Callees.fb_heap_release
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_push
  have _ := Callees.fb_u256_from_be
  fb_prove 514 Guest.Software.guestFn_op_push K.«op_push»

theorem fb_op_return :
    TerminatingFunBoundedOn GuestInv (ofString "op_return") K.«op_return» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_extend_memory
  have _ := Callees.fb_extend_memory_cost1
  have _ := Callees.fb_sat_word
  have _ := Callees.fb_stack_pop
  fb_prove 568 Guest.Software.guestFn_op_return K.«op_return»

theorem fb_op_returndatacopy :
    TerminatingFunBoundedOn GuestInv (ofString "op_returndatacopy") K.«op_returndatacopy» := by
  have _ := Callees.fb_add_sat
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_extend_memory
  have _ := Callees.fb_extend_memory_cost1
  have _ := Callees.fb_memcpy
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_sat_word
  have _ := Callees.fb_stack_pop
  have _ := Callees.fb_words_of
  fb_prove 547 Guest.Software.guestFn_op_returndatacopy K.«op_returndatacopy»

theorem fb_op_revert :
    TerminatingFunBoundedOn GuestInv (ofString "op_revert") K.«op_revert» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_extend_memory
  have _ := Callees.fb_extend_memory_cost1
  have _ := Callees.fb_sat_word
  have _ := Callees.fb_stack_pop
  fb_prove 569 Guest.Software.guestFn_op_revert K.«op_revert»

end InitECandidate.Solver.Wave8GuestInv.P12_P15
