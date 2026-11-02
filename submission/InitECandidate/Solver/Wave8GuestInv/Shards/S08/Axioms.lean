import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_coinbase
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.compute_contract_address
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.generic_create
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.require_not_static
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_create
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.compute_create2_contract_address
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_create2
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_delegatecall
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_div
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_dup
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.code_imm
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.decode_single
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_dupn
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.stack_push_bool
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_eq
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.stack_swap_positions
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_exchange
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_exp
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_extcodecopy
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_extcodehash
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_extcodesize
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_gas
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_gaslimit
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.op_gasprice

/-! Axiom and exact statement checks for all 24 leaves in shard s08 (`wave8/leaves-s08`).
Every `example : (type_of% @...) = ... := rfl` checks syntactic equality against the spec statement
in `InitECandidate.Solver.Wave8GuestInv` (modulo explicit callee hypotheses).
Every theorem must depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Leaves.S08

/-! ### exact statement checks -/

-- 1. fb_op_coinbase
example : (type_of% @fb_op_coinbase) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_block_env) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_address_to_u256) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_coinbase)) := rfl

-- 2. fb_compute_contract_address
example : (type_of% @fb_compute_contract_address) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_heap_mark) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_bytes) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_list_header_len) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_list_header) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_keccak256) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_heap_release) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_compute_contract_address)) := rfl

example : (type_of% @fb_compute_contract_address_of) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_bytes) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_list_header_len) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_list_header) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_keccak256) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_compute_contract_address)) := rfl

-- 3. fb_generic_create
example : (type_of% @fb_generic_create) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_set_retdata) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_get_account) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_u256_lt) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_warm_address) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_is_account_alive) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_state_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_account_deployable) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_increment_nonce) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_credit_state_gas_refund) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_scratch_mark) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_frame_mem_mark) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_child_message) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_start_child) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_generic_create)) := rfl

example : (type_of% @fb_generic_create_of) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_set_retdata) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_get_account) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_u256_lt) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_warm_address) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_is_account_alive) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_state_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_account_deployable) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_increment_nonce) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_credit_state_gas_refund) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_child_message) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_start_child) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_generic_create)) := rfl

-- 4. fb_require_not_static
example : (type_of% @fb_require_not_static) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_require_not_static) := rfl

-- 5. fb_op_create
example : (type_of% @fb_op_create) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_require_not_static) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_sat_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory_cost1) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_words_of) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_add_sat) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_get_account) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_compute_contract_address) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_generic_create) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_create)) := rfl

example : (type_of% @fb_op_create_of) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_sat_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory_cost1) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_words_of) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_add_sat) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_get_account) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_compute_contract_address) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_generic_create) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_create)) := rfl

-- 6. fb_compute_create2_contract_address
example : (type_of% @fb_compute_create2_contract_address) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_heap_mark) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_keccak256) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_heap_release) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_compute_create2_contract_address)) := rfl

example : (type_of% @fb_compute_create2_contract_address_of) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_keccak256) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_compute_create2_contract_address)) := rfl

-- 7. fb_op_create2
example : (type_of% @fb_op_create2) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_require_not_static) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_sat_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory_cost1) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_words_of) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_add_sat) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_u256_to_be32) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_compute_create2_contract_address) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_generic_create) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_create2)) := rfl

example : (type_of% @fb_op_create2_of) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_sat_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory_cost1) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_words_of) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_add_sat) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_u256_to_be32) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_compute_create2_contract_address) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_generic_create) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_create2)) := rfl

-- 8. fb_op_delegatecall
example : (type_of% @fb_op_delegatecall) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_to_address_masked) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory_cost2) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_is_warm_address) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_add_sat) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_warm_address) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_calculate_delegation_cost) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_ext_code_of) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_sat_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_calculate_message_call_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_generic_call) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_delegatecall)) := rfl

-- 9. fb_op_div
example : (type_of% @fb_op_div) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_u256_div) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_div)) := rfl

-- 10. fb_op_dup
example : (type_of% @fb_op_dup) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_dup)) := rfl

-- 11. fb_code_imm
example : (type_of% @fb_code_imm) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_code_imm) := rfl

-- 12. fb_decode_single
example : (type_of% @fb_decode_single) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_decode_single) := rfl

-- 13. fb_op_dupn
example : (type_of% @fb_op_dupn) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_code_imm) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_decode_single) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_dupn)) := rfl

example : (type_of% @fb_op_dupn_of) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_dupn)) := rfl

-- 14. fb_stack_push_bool
example : (type_of% @fb_stack_push_bool) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push_bool)) := rfl

-- 15. fb_op_eq
example : (type_of% @fb_op_eq) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_u256_eq) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push_bool) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_eq)) := rfl

example : (type_of% @fb_op_eq_of) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_u256_eq) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_eq)) := rfl

-- 16. fb_stack_swap_positions
example : (type_of% @fb_stack_swap_positions) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_swap_positions) := rfl

-- 17. fb_op_exchange
example : (type_of% @fb_op_exchange) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_code_imm) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_max) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_swap_positions) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_exchange)) := rfl

example : (type_of% @fb_op_exchange_of) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_max) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_exchange)) := rfl

-- 18. fb_op_exp
example : (type_of% @fb_op_exp) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_u256_byte_length) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_u256_exp) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_exp)) := rfl

-- 19. fb_op_extcodecopy
example : (type_of% @fb_op_extcodecopy) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_to_address_masked) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_sat_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_words_of) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory_cost1) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_access_gas_cost) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_add_sat) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_warm_after_charge) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_extend_memory) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_ext_code_of) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_buffer_read) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_extcodecopy)) := rfl

-- 20. fb_op_extcodehash
example : (type_of% @fb_op_extcodehash) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_to_address_masked) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_access_gas_cost) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_warm_after_charge) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_get_account) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_acct_is_empty) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_u256_from_be) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_extcodehash)) := rfl

-- 21. fb_op_extcodesize
example : (type_of% @fb_op_extcodesize) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_pop) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_to_address_masked) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_access_gas_cost) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_warm_after_charge) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_ext_code_of) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_extcodesize)) := rfl

-- 22. fb_op_gas
example : (type_of% @fb_op_gas) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_gas)) := rfl

-- 23. fb_op_gaslimit
example : (type_of% @fb_op_gaslimit) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_block_env) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push_word) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_gaslimit)) := rfl

-- 24. fb_op_gasprice
example : (type_of% @fb_op_gasprice) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stack_push) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_pc_add) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_op_gasprice)) := rfl

/-! ### axiom audit -/


end InitECandidate.Solver.Wave8Leaves.S08
