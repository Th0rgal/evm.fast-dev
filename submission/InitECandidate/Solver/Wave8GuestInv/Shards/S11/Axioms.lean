import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S11.Leaves1
import InitECandidate.Solver.Wave8GuestInv.Shards.S11.Leaves2
import InitECandidate.Solver.Wave8GuestInv.Shards.S11.Loops

/-! Axioms and `type_of%` evidence for shard s11 (`wave8/leaves-s11`).

Each `example` checks that the proved theorem has the exact spec statement
(`type_of% Wave8GuestInv.«fb_f»`), taking as explicit hypotheses the spec statements of any
callee leaves it requires.
Every `#print axioms` line must show only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.S11

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Leaves.S11

theorem metadataInv_guestInv : MetadataInv (@Wave8GuestInv.GuestInv) :=
  fun hcode hmem hsh hbase h => Wave8GuestInv.guestInv_congr hcode hmem hsh hbase h

-- 1. fb_op_swap (idx 517)
theorem fb_op_swap_of :
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_stack_swap_positions» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_swap» :=
  fb_op_swap_on metadataInv_guestInv

example : type_of% @fb_op_swap_of =
    (type_of% Wave8GuestInv.«fb_charge_gas» →
     type_of% Wave8GuestInv.«fb_stack_swap_positions» →
     type_of% Wave8GuestInv.«fb_pc_add» →
     type_of% Wave8GuestInv.«fb_op_swap») := rfl

-- 2. fb_op_swapn (idx 521)
theorem fb_op_swapn_of :
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_code_imm» →
    type_of% Wave8GuestInv.«fb_decode_single» →
    type_of% Wave8GuestInv.«fb_stack_swap_positions» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_swapn» :=
  fb_op_swapn_on metadataInv_guestInv

example : type_of% @fb_op_swapn_of =
    (type_of% Wave8GuestInv.«fb_charge_gas» →
     type_of% Wave8GuestInv.«fb_code_imm» →
     type_of% Wave8GuestInv.«fb_decode_single» →
     type_of% Wave8GuestInv.«fb_stack_swap_positions» →
     type_of% Wave8GuestInv.«fb_pc_add» →
     type_of% Wave8GuestInv.«fb_op_swapn») := rfl

-- 3. fb_op_timestamp (idx 556)
theorem fb_op_timestamp_of :
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_block_env» →
    type_of% Wave8GuestInv.«fb_stack_push_word» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_timestamp» :=
  fb_op_timestamp_on metadataInv_guestInv

example : type_of% @fb_op_timestamp_of =
    (type_of% Wave8GuestInv.«fb_charge_gas» →
     type_of% Wave8GuestInv.«fb_block_env» →
     type_of% Wave8GuestInv.«fb_stack_push_word» →
     type_of% Wave8GuestInv.«fb_pc_add» →
     type_of% Wave8GuestInv.«fb_op_timestamp») := rfl

-- 4. fb_get_transient_storage (idx 380)
theorem fb_get_transient_storage_of :
    type_of% Wave8GuestInv.«fb_sk_make» →
    type_of% Wave8GuestInv.«fb_htab_get» →
    type_of% Wave8GuestInv.«fb_get_transient_storage» :=
  fb_get_transient_storage_on metadataInv_guestInv

example : type_of% @fb_get_transient_storage_of =
    (type_of% Wave8GuestInv.«fb_sk_make» →
     type_of% Wave8GuestInv.«fb_htab_get» →
     type_of% Wave8GuestInv.«fb_get_transient_storage») := rfl

-- 5. fb_op_tload (idx 529)
theorem fb_op_tload_of :
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_u256_to_be32» →
    type_of% Wave8GuestInv.«fb_get_transient_storage» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_tload» :=
  fb_op_tload_on metadataInv_guestInv

example : type_of% @fb_op_tload_of =
    (type_of% Wave8GuestInv.«fb_stack_pop» →
     type_of% Wave8GuestInv.«fb_charge_gas» →
     type_of% Wave8GuestInv.«fb_u256_to_be32» →
     type_of% Wave8GuestInv.«fb_get_transient_storage» →
     type_of% Wave8GuestInv.«fb_stack_push» →
     type_of% Wave8GuestInv.«fb_pc_add» →
     type_of% Wave8GuestInv.«fb_op_tload») := rfl

-- 6. fb_set_transient_storage (idx 394)
theorem fb_set_transient_storage_of :
    type_of% Wave8GuestInv.«fb_sk_make» →
    type_of% Wave8GuestInv.«fb_u256_is_zero» →
    type_of% Wave8GuestInv.«fb_jdel» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_jset» →
    type_of% Wave8GuestInv.«fb_set_transient_storage» :=
  fb_set_transient_storage_on metadataInv_guestInv

example : type_of% @fb_set_transient_storage_of =
    (type_of% Wave8GuestInv.«fb_sk_make» →
     type_of% Wave8GuestInv.«fb_u256_is_zero» →
     type_of% Wave8GuestInv.«fb_jdel» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_jset» →
     type_of% Wave8GuestInv.«fb_set_transient_storage») := rfl

-- 7. fb_op_tstore (idx 530)
theorem fb_op_tstore_of :
    type_of% Wave8GuestInv.«fb_require_not_static» →
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_u256_to_be32» →
    type_of% Wave8GuestInv.«fb_set_transient_storage» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_tstore» :=
  fb_op_tstore_on metadataInv_guestInv

example : type_of% @fb_op_tstore_of =
    (type_of% Wave8GuestInv.«fb_require_not_static» →
     type_of% Wave8GuestInv.«fb_stack_pop» →
     type_of% Wave8GuestInv.«fb_charge_gas» →
     type_of% Wave8GuestInv.«fb_u256_to_be32» →
     type_of% Wave8GuestInv.«fb_set_transient_storage» →
     type_of% Wave8GuestInv.«fb_pc_add» →
     type_of% Wave8GuestInv.«fb_op_tstore») := rfl

-- 8. fb_op_xor (idx 494)
theorem fb_op_xor_of :
    type_of% Wave8GuestInv.«fb_stack_pop» →
    type_of% Wave8GuestInv.«fb_charge_gas» →
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_pc_add» →
    type_of% Wave8GuestInv.«fb_op_xor» :=
  fb_op_xor_on metadataInv_guestInv

example : type_of% @fb_op_xor_of =
    (type_of% Wave8GuestInv.«fb_stack_pop» →
     type_of% Wave8GuestInv.«fb_charge_gas» →
     type_of% Wave8GuestInv.«fb_stack_push» →
     type_of% Wave8GuestInv.«fb_pc_add» →
     type_of% Wave8GuestInv.«fb_op_xor») := rfl

-- 9. fb_state_fresh_tx (idx 355)
theorem fb_state_fresh_tx_of :
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_htab_new» →
    type_of% Wave8GuestInv.«fb_state_fresh_tx» :=
  fb_state_fresh_tx_on metadataInv_guestInv

example : type_of% @fb_state_fresh_tx_of =
    (type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_htab_new» →
     type_of% Wave8GuestInv.«fb_state_fresh_tx») := rfl

-- 10. fb_te_new (idx 869)
theorem fb_te_new_of :
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_memzero» →
    type_of% Wave8GuestInv.«fb_te_new» :=
  fb_te_new_on metadataInv_guestInv

example : type_of% @fb_te_new_of =
    (type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_memzero» →
     type_of% Wave8GuestInv.«fb_te_new») := rfl

-- 11. fb_requests_append (idx 876)
theorem fb_requests_append_of :
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_requests_append» :=
  fb_requests_append_on metadataInv_guestInv

example : type_of% @fb_requests_append_of =
    (type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_requests_append») := rfl

-- 12. fb_calculate_total_blob_gas (idx 317)
theorem fb_calculate_total_blob_gas :
    type_of% Wave8GuestInv.«fb_calculate_total_blob_gas» :=
  fb_calculate_total_blob_gas_on metadataInv_guestInv

example : type_of% @fb_calculate_total_blob_gas =
    type_of% Wave8GuestInv.«fb_calculate_total_blob_gas» := rfl

-- 13. fb_fee_mul (idx 867)
theorem fb_fee_mul_of :
    type_of% Wave8GuestInv.«fb_u256_mul_full» →
    type_of% Wave8GuestInv.«fb_fee_mul» :=
  fb_fee_mul_on metadataInv_guestInv

example : type_of% @fb_fee_mul_of =
    (type_of% Wave8GuestInv.«fb_u256_mul_full» →
     type_of% Wave8GuestInv.«fb_fee_mul») := rfl

-- 14. fb_check_transaction (idx 872)
theorem fb_check_transaction_of :
    type_of% Wave8GuestInv.«fb_min» →
    type_of% Wave8GuestInv.«fb_calculate_total_blob_gas» →
    type_of% Wave8GuestInv.«fb_get_account» →
    type_of% Wave8GuestInv.«fb_u256_lt» →
    type_of% Wave8GuestInv.«fb_u256_sub» →
    type_of% Wave8GuestInv.«fb_u256_add» →
    type_of% Wave8GuestInv.«fb_fee_mul» →
    type_of% Wave8GuestInv.«fb_calculate_blob_gas_price» →
    type_of% Wave8GuestInv.«fb_u256_add_carry» →
    type_of% Wave8GuestInv.«fb_u256_fits_word» →
    type_of% Wave8GuestInv.«fb_get_code» →
    type_of% Wave8GuestInv.«fb_memeq» →
    type_of% Wave8GuestInv.«fb_is_valid_delegation» →
    type_of% Wave8GuestInv.«fb_check_transaction» :=
  fb_check_transaction_on metadataInv_guestInv

example : type_of% @fb_check_transaction_of =
    (type_of% Wave8GuestInv.«fb_min» →
     type_of% Wave8GuestInv.«fb_calculate_total_blob_gas» →
     type_of% Wave8GuestInv.«fb_get_account» →
     type_of% Wave8GuestInv.«fb_u256_lt» →
     type_of% Wave8GuestInv.«fb_u256_sub» →
     type_of% Wave8GuestInv.«fb_u256_add» →
     type_of% Wave8GuestInv.«fb_fee_mul» →
     type_of% Wave8GuestInv.«fb_calculate_blob_gas_price» →
     type_of% Wave8GuestInv.«fb_u256_add_carry» →
     type_of% Wave8GuestInv.«fb_u256_fits_word» →
     type_of% Wave8GuestInv.«fb_get_code» →
     type_of% Wave8GuestInv.«fb_memeq» →
     type_of% Wave8GuestInv.«fb_is_valid_delegation» →
     type_of% Wave8GuestInv.«fb_check_transaction») := rfl

-- 15. fb_clear_account_preserving_balance (idx 392)
theorem fb_clear_account_preserving_balance_of :
    type_of% Wave8GuestInv.«fb_destroy_storage» →
    type_of% Wave8GuestInv.«fb_get_account» →
    type_of% Wave8GuestInv.«fb_acct_copy» →
    type_of% Wave8GuestInv.«fb_modify_state_commit» →
    type_of% Wave8GuestInv.«fb_clear_account_preserving_balance» :=
  fb_clear_account_preserving_balance_on metadataInv_guestInv

example : type_of% @fb_clear_account_preserving_balance_of =
    (type_of% Wave8GuestInv.«fb_destroy_storage» →
     type_of% Wave8GuestInv.«fb_get_account» →
     type_of% Wave8GuestInv.«fb_acct_copy» →
     type_of% Wave8GuestInv.«fb_modify_state_commit» →
     type_of% Wave8GuestInv.«fb_clear_account_preserving_balance») := rfl

-- 16. fb_create_ether (idx 396)
theorem fb_create_ether_of :
    type_of% Wave8GuestInv.«fb_get_account» →
    type_of% Wave8GuestInv.«fb_acct_copy» →
    type_of% Wave8GuestInv.«fb_u256_add» →
    type_of% Wave8GuestInv.«fb_modify_state_commit» →
    type_of% Wave8GuestInv.«fb_create_ether» :=
  fb_create_ether_on metadataInv_guestInv

example : type_of% @fb_create_ether_of =
    (type_of% Wave8GuestInv.«fb_get_account» →
     type_of% Wave8GuestInv.«fb_acct_copy» →
     type_of% Wave8GuestInv.«fb_u256_add» →
     type_of% Wave8GuestInv.«fb_modify_state_commit» →
     type_of% Wave8GuestInv.«fb_create_ether») := rfl

-- 17. fb_encode_logs (idx 835)
theorem fb_encode_logs_of :
    type_of% Wave8GuestInv.«fb_rlp_encode_bytes» →
    type_of% Wave8GuestInv.«fb_rlp_finish_list» →
    type_of% Wave8GuestInv.«fb_encode_logs» :=
  fb_encode_logs_on metadataInv_guestInv

example : type_of% @fb_encode_logs_of =
    (type_of% Wave8GuestInv.«fb_rlp_encode_bytes» →
     type_of% Wave8GuestInv.«fb_rlp_finish_list» →
     type_of% Wave8GuestInv.«fb_encode_logs») := rfl

-- 18. fb_logs_encoded_bound (idx 834)
theorem fb_logs_encoded_bound :
    type_of% Wave8GuestInv.«fb_logs_encoded_bound» :=
  fb_logs_encoded_bound_on metadataInv_guestInv

example : type_of% @fb_logs_encoded_bound =
    type_of% Wave8GuestInv.«fb_logs_encoded_bound» := rfl

-- 19. fb_encode_receipt (idx 836)
theorem fb_encode_receipt_of :
    type_of% Wave8GuestInv.«fb_logs_encoded_bound» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_rlp_encode_word» →
    type_of% Wave8GuestInv.«fb_logs_bloom» →
    type_of% Wave8GuestInv.«fb_rlp_encode_bytes» →
    type_of% Wave8GuestInv.«fb_encode_logs» →
    type_of% Wave8GuestInv.«fb_rlp_finish_list» →
    type_of% Wave8GuestInv.«fb_encode_receipt» :=
  fb_encode_receipt_on metadataInv_guestInv

example : type_of% @fb_encode_receipt_of =
    (type_of% Wave8GuestInv.«fb_logs_encoded_bound» →
     type_of% Wave8GuestInv.«fb_alloc» →
     type_of% Wave8GuestInv.«fb_rlp_encode_word» →
     type_of% Wave8GuestInv.«fb_logs_bloom» →
     type_of% Wave8GuestInv.«fb_rlp_encode_bytes» →
     type_of% Wave8GuestInv.«fb_encode_logs» →
     type_of% Wave8GuestInv.«fb_rlp_finish_list» →
     type_of% Wave8GuestInv.«fb_encode_receipt») := rfl

-- 20. fb_tx_u256_encoded_len (idx 319)
theorem fb_tx_u256_encoded_len_of :
    type_of% Wave8GuestInv.«fb_u256_byte_length» →
    type_of% Wave8GuestInv.«fb_tx_u256_encoded_len» :=
  fb_tx_u256_encoded_len_on metadataInv_guestInv

example : type_of% @fb_tx_u256_encoded_len_of =
    (type_of% Wave8GuestInv.«fb_u256_byte_length» →
     type_of% Wave8GuestInv.«fb_tx_u256_encoded_len») := rfl

-- 21. fb_auth_payload_len (idx 324)
theorem fb_auth_payload_len_of :
    type_of% Wave8GuestInv.«fb_tx_u256_encoded_len» →
    type_of% Wave8GuestInv.«fb_rlp_word_encoded_len» →
    type_of% Wave8GuestInv.«fb_auth_payload_len» :=
  fb_auth_payload_len_on metadataInv_guestInv

example : type_of% @fb_auth_payload_len_of =
    (type_of% Wave8GuestInv.«fb_tx_u256_encoded_len» →
     type_of% Wave8GuestInv.«fb_rlp_word_encoded_len» →
     type_of% Wave8GuestInv.«fb_auth_payload_len») := rfl

-- 22. fb_auth_list_payload_len (idx 325)
theorem fb_auth_list_payload_len_of :
    type_of% Wave8GuestInv.«fb_auth_payload_len» →
    type_of% Wave8GuestInv.«fb_rlp_list_header_len» →
    type_of% Wave8GuestInv.«fb_auth_list_payload_len» :=
  fb_auth_list_payload_len_on metadataInv_guestInv

example : type_of% @fb_auth_list_payload_len_of =
    (type_of% Wave8GuestInv.«fb_auth_payload_len» →
     type_of% Wave8GuestInv.«fb_rlp_list_header_len» →
     type_of% Wave8GuestInv.«fb_auth_list_payload_len») := rfl

-- 23. fb_tx_encode_bound (idx 327)
theorem fb_tx_encode_bound_of :
    type_of% Wave8GuestInv.«fb_access_list_payload_len» →
    type_of% Wave8GuestInv.«fb_auth_list_payload_len» →
    type_of% Wave8GuestInv.«fb_tx_encode_bound» :=
  fb_tx_encode_bound_on metadataInv_guestInv

example : type_of% @fb_tx_encode_bound_of =
    (type_of% Wave8GuestInv.«fb_access_list_payload_len» →
     type_of% Wave8GuestInv.«fb_auth_list_payload_len» →
     type_of% Wave8GuestInv.«fb_tx_encode_bound») := rfl

-- 24. fb_tx_put_access_list (idx 322)
theorem fb_tx_put_access_list_of :
    type_of% Wave8GuestInv.«fb_access_list_payload_len» →
    type_of% Wave8GuestInv.«fb_rlp_encode_list_header» →
    type_of% Wave8GuestInv.«fb_rlp_list_header_len» →
    type_of% Wave8GuestInv.«fb_rlp_encode_bytes» →
    type_of% Wave8GuestInv.«fb_tx_put_access_list» :=
  fb_tx_put_access_list_on metadataInv_guestInv

example : type_of% @fb_tx_put_access_list_of =
    (type_of% Wave8GuestInv.«fb_access_list_payload_len» →
     type_of% Wave8GuestInv.«fb_rlp_encode_list_header» →
     type_of% Wave8GuestInv.«fb_rlp_list_header_len» →
     type_of% Wave8GuestInv.«fb_rlp_encode_bytes» →
     type_of% Wave8GuestInv.«fb_tx_put_access_list») := rfl


end InitECandidate.Solver.Wave8GuestInv.S11
