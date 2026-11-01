import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13DivMod

/-! Shard P13: unconditional R11 `TerminatingFunBoundedOn GuestInv` proofs for all 7 opcode fields
(`fb_op_keccak`, `fb_op_log`, `fb_op_lt`, `fb_op_mcopy`, `fb_op_mload`, `fb_op_mod`, `fb_op_msize`),
discharging every transitive `fb_*` callee without referencing `LeafStatements.lean`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.P13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common

theorem fb_op_keccak : TerminatingFunBoundedOn GuestInv (ofString "op_keccak") K.«op_keccak» := by
  have _ := Callees.fb_add_sat
  have _ := Callees.fb_alloc
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_extend_memory
  have _ := Callees.fb_extend_memory_cost1
  have _ := Callees.fb_heap_mark
  have _ := Callees.fb_heap_release
  have _ := Callees.fb_keccak256
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_sat_word
  have _ := Callees.fb_stack_pop
  have _ := Callees.fb_stack_push
  have _ := Callees.fb_u256_from_be
  have _ := Callees.fb_words_of
  fb_prove 501 Guest.Software.guestFn_op_keccak K.«op_keccak»

theorem fb_op_log : TerminatingFunBoundedOn GuestInv (ofString "op_log") K.«op_log» := by
  have _ := Callees.fb_add_sat
  have _ := Callees.fb_alloc
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_extend_memory
  have _ := Callees.fb_extend_memory_cost1
  have _ := Callees.fb_log_append
  have _ := Callees.fb_memcpy
  have _ := Callees.fb_mul64x64
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_require_not_static
  have _ := Callees.fb_sat_word
  have _ := Callees.fb_stack_pop
  have _ := Callees.fb_u256_to_be32
  fb_prove 524 Guest.Software.guestFn_op_log K.«op_log»

theorem fb_op_lt : TerminatingFunBoundedOn GuestInv (ofString "op_lt") K.«op_lt» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_pop
  have _ := Callees.fb_stack_push_bool
  have _ := Callees.fb_u256_lt
  fb_prove 486 Guest.Software.guestFn_op_lt K.«op_lt»

theorem fb_op_mcopy : TerminatingFunBoundedOn GuestInv (ofString "op_mcopy") K.«op_mcopy» := by
  have _ := Callees.fb_add_sat
  have _ := Callees.fb_alloc
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_extend_memory
  have _ := Callees.fb_extend_memory_cost2
  have _ := Callees.fb_heap_mark
  have _ := Callees.fb_heap_release
  have _ := Callees.fb_memcpy
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_sat_word
  have _ := Callees.fb_stack_pop
  have _ := Callees.fb_words_of
  fb_prove 512 Guest.Software.guestFn_op_mcopy K.«op_mcopy»

theorem fb_op_mload : TerminatingFunBoundedOn GuestInv (ofString "op_mload") K.«op_mload» := by
  have _ := Callees.fb_charge_with_memory
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_sat_word
  have _ := Callees.fb_stack_pop
  have _ := Callees.fb_stack_push
  have _ := Callees.fb_u256_from_be
  fb_prove 510 Guest.Software.guestFn_op_mload K.«op_mload»

theorem fb_op_mod : TerminatingFunBoundedOn GuestInv (ofString "op_mod") K.«op_mod» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_pop
  have _ := Callees.fb_stack_push
  have _ := DivMod.fb_u256_mod
  fb_prove 480 Guest.Software.guestFn_op_mod K.«op_mod»

theorem fb_op_msize : TerminatingFunBoundedOn GuestInv (ofString "op_msize") K.«op_msize» := by
  have _ := Callees.fb_charge_gas
  have _ := Callees.fb_pc_add
  have _ := Callees.fb_stack_push_word
  fb_prove 511 Guest.Software.guestFn_op_msize K.«op_msize»

end InitECandidate.Solver.Wave8GuestInv.P13
