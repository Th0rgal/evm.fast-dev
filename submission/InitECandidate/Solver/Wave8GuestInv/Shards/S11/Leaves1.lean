import InitECandidate.Solver.Wave8GuestInv.Shards.S11.Core

/-! Loop-free leaves batch 1 (10 leaves) for Wave 8 shard s11 (`wave8/leaves-s11`).
Imports only the light cone via `campaign.leaves.s11.Core`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S11

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem fb_op_swap_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_charge_gas K_stack_swap_positions K_pc_add : Nat}
    (h_charge_gas : TerminatingFunBoundedOn P (ofString "charge_gas") K_charge_gas)
    (h_stack_swap_positions : TerminatingFunBoundedOn P (ofString "stack_swap_positions") K_stack_swap_positions)
    (h_pc_add : TerminatingFunBoundedOn P (ofString "pc_add") K_pc_add) :
    TerminatingFunBoundedOn P (ofString "op_swap")
      ((K_charge_gas + 1) + (K_stack_swap_positions + 1) + (K_pc_add + 1)) := by
  fb_prove hP 517 Guest.Software.guestFn_op_swap

theorem fb_op_swapn_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_charge_gas K_code_imm K_decode_single K_stack_swap_positions K_pc_add : Nat}
    (h_charge_gas : TerminatingFunBoundedOn P (ofString "charge_gas") K_charge_gas)
    (h_code_imm : TerminatingFunBoundedOn P (ofString "code_imm") K_code_imm)
    (h_decode_single : TerminatingFunBoundedOn P (ofString "decode_single") K_decode_single)
    (h_stack_swap_positions : TerminatingFunBoundedOn P (ofString "stack_swap_positions") K_stack_swap_positions)
    (h_pc_add : TerminatingFunBoundedOn P (ofString "pc_add") K_pc_add) :
    TerminatingFunBoundedOn P (ofString "op_swapn")
      ((K_charge_gas + 1) + (K_code_imm + 1) + (K_decode_single + 1) + (K_stack_swap_positions + 1) + (K_pc_add + 1)) := by
  fb_prove hP 521 Guest.Software.guestFn_op_swapn

theorem fb_op_timestamp_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_charge_gas K_block_env K_stack_push_word K_pc_add : Nat}
    (h_charge_gas : TerminatingFunBoundedOn P (ofString "charge_gas") K_charge_gas)
    (h_block_env : TerminatingFunBoundedOn P (ofString "block_env") K_block_env)
    (h_stack_push_word : TerminatingFunBoundedOn P (ofString "stack_push_word") K_stack_push_word)
    (h_pc_add : TerminatingFunBoundedOn P (ofString "pc_add") K_pc_add) :
    TerminatingFunBoundedOn P (ofString "op_timestamp")
      ((K_charge_gas + 1) + (K_block_env + 1) + (K_stack_push_word + 1) + (K_pc_add + 1)) := by
  fb_prove hP 556 Guest.Software.guestFn_op_timestamp

theorem fb_get_transient_storage_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_sk_make K_htab_get : Nat}
    (h_sk_make : TerminatingFunBoundedOn P (ofString "sk_make") K_sk_make)
    (h_htab_get : TerminatingFunBoundedOn P (ofString "htab_get") K_htab_get) :
    TerminatingFunBoundedOn P (ofString "get_transient_storage")
      ((K_sk_make + 1) + (K_htab_get + 1)) := by
  fb_prove hP 380 Guest.Software.guestFn_get_transient_storage

theorem fb_op_tload_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_stack_pop K_charge_gas K_u256_to_be32 K_get_transient_storage K_stack_push K_pc_add : Nat}
    (h_stack_pop : TerminatingFunBoundedOn P (ofString "stack_pop") K_stack_pop)
    (h_charge_gas : TerminatingFunBoundedOn P (ofString "charge_gas") K_charge_gas)
    (h_u256_to_be32 : TerminatingFunBoundedOn P (ofString "u256_to_be32") K_u256_to_be32)
    (h_get_transient_storage : TerminatingFunBoundedOn P (ofString "get_transient_storage") K_get_transient_storage)
    (h_stack_push : TerminatingFunBoundedOn P (ofString "stack_push") K_stack_push)
    (h_pc_add : TerminatingFunBoundedOn P (ofString "pc_add") K_pc_add) :
    TerminatingFunBoundedOn P (ofString "op_tload")
      ((K_stack_pop + 1) + (K_charge_gas + 1) + (K_u256_to_be32 + 1) + (K_get_transient_storage + 1) + (K_stack_push + 1) + (K_pc_add + 1)) := by
  fb_prove hP 529 Guest.Software.guestFn_op_tload

theorem fb_set_transient_storage_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_sk_make K_u256_is_zero K_jdel K_alloc K_jset : Nat}
    (h_sk_make : TerminatingFunBoundedOn P (ofString "sk_make") K_sk_make)
    (h_u256_is_zero : TerminatingFunBoundedOn P (ofString "u256_is_zero") K_u256_is_zero)
    (h_jdel : TerminatingFunBoundedOn P (ofString "jdel") K_jdel)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_jset : TerminatingFunBoundedOn P (ofString "jset") K_jset) :
    TerminatingFunBoundedOn P (ofString "set_transient_storage")
      ((K_sk_make + 1) + (K_u256_is_zero + 1) + Nat.max ((K_jdel + 1)) (0) + (K_alloc + 1) + (K_jset + 1)) := by
  fb_prove hP 394 Guest.Software.guestFn_set_transient_storage

theorem fb_op_tstore_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_require_not_static K_stack_pop K_charge_gas K_u256_to_be32 K_set_transient_storage K_pc_add : Nat}
    (h_require_not_static : TerminatingFunBoundedOn P (ofString "require_not_static") K_require_not_static)
    (h_stack_pop : TerminatingFunBoundedOn P (ofString "stack_pop") K_stack_pop)
    (h_charge_gas : TerminatingFunBoundedOn P (ofString "charge_gas") K_charge_gas)
    (h_u256_to_be32 : TerminatingFunBoundedOn P (ofString "u256_to_be32") K_u256_to_be32)
    (h_set_transient_storage : TerminatingFunBoundedOn P (ofString "set_transient_storage") K_set_transient_storage)
    (h_pc_add : TerminatingFunBoundedOn P (ofString "pc_add") K_pc_add) :
    TerminatingFunBoundedOn P (ofString "op_tstore")
      ((K_require_not_static + 1) + (K_stack_pop + 1) + (K_stack_pop + 1) + (K_charge_gas + 1) + (K_u256_to_be32 + 1) + (K_set_transient_storage + 1) + (K_pc_add + 1)) := by
  fb_prove hP 530 Guest.Software.guestFn_op_tstore

theorem fb_op_xor_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_stack_pop K_charge_gas K_stack_push K_pc_add : Nat}
    (h_stack_pop : TerminatingFunBoundedOn P (ofString "stack_pop") K_stack_pop)
    (h_charge_gas : TerminatingFunBoundedOn P (ofString "charge_gas") K_charge_gas)
    (h_stack_push : TerminatingFunBoundedOn P (ofString "stack_push") K_stack_push)
    (h_pc_add : TerminatingFunBoundedOn P (ofString "pc_add") K_pc_add) :
    TerminatingFunBoundedOn P (ofString "op_xor")
      ((K_stack_pop + 1) + (K_stack_pop + 1) + (K_charge_gas + 1) + (K_stack_push + 1) + (K_pc_add + 1)) := by
  fb_prove hP 494 Guest.Software.guestFn_op_xor

theorem fb_state_fresh_tx_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_alloc K_htab_new : Nat}
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_htab_new : TerminatingFunBoundedOn P (ofString "htab_new") K_htab_new) :
    TerminatingFunBoundedOn P (ofString "state_fresh_tx")
      ((K_alloc + 1) + (K_htab_new + 1) + (K_htab_new + 1) + (K_htab_new + 1) + (K_htab_new + 1) + (K_htab_new + 1) + (K_htab_new + 1) + (K_htab_new + 1) + (K_htab_new + 1)) := by
  fb_prove hP 355 Guest.Software.guestFn_state_fresh_tx

theorem fb_te_new_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_alloc K_memzero : Nat}
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_memzero : TerminatingFunBoundedOn P (ofString "memzero") K_memzero) :
    TerminatingFunBoundedOn P (ofString "te_new")
      ((K_alloc + 1) + (K_memzero + 1)) := by
  fb_prove hP 869 Guest.Software.guestFn_te_new

end InitECandidate.Solver.Wave8Leaves.S11
