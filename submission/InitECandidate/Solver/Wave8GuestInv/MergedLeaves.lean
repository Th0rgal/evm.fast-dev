import InitECandidate.Solver.Wave8GuestInv.Contracts
import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M05.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M12.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.R10Ports.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Axioms
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M21.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M28.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.IndividualAudit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.Axioms
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.DelSpecs
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.TruncateSpec
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbCore
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbHtab
import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbRlp
import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmFrameSpecs
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Compatibility
import InitECandidate.Solver.Wave8GuestInv.Shards.S01.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S02.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S03.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S05.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S06.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S09.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S11.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Axioms
import InitECandidate.Solver.Wave8GuestInv.Shards.S15.Axioms

namespace InitECandidate.Solver.Wave8GuestInv.Merged

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.style.nameCheck false

instance : InitECandidate.Solver.Wave8GuestInv.S01.IsGuestInv (@InitECandidate.Solver.Wave8GuestInv.GuestInv) where
  eval s prog h := InitECandidate.Solver.Wave8GuestInv.guestInv_evaluate s prog h
  congr hc hm hs hb h := InitECandidate.Solver.Wave8GuestInv.guestInv_congr hc hm hs hb h

theorem dm_encode_withdrawal_rlp : type_of% InitECandidate.Solver.Wave8GuestInv.«dm_encode_withdrawal_rlp» :=
  InitECandidate.Solver.Wave8GuestInv.M21.dm_encode_withdrawal_rlp

theorem dm_memcpy : type_of% InitECandidate.Solver.Wave8GuestInv.«dm_memcpy» :=
  InitECandidate.Solver.Wave8GuestInv.M21.dm_memcpy

theorem ek_charge_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«ek_charge_gas» :=
  InitECandidate.Solver.Wave8GuestInv.M21.ek_charge_gas

theorem ek_is_warm_storage_key : type_of% InitECandidate.Solver.Wave8GuestInv.«ek_is_warm_storage_key» :=
  InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs.ek_is_warm_storage_key

theorem ek_stack_pop : type_of% InitECandidate.Solver.Wave8GuestInv.«ek_stack_pop» :=
  InitECandidate.Solver.Wave8Contracts.M23.ek_stack_pop

theorem ek_u256_to_be32 : type_of% InitECandidate.Solver.Wave8GuestInv.«ek_u256_to_be32» :=
  InitECandidate.Solver.Wave8Contracts.M23.ek_u256_to_be32

theorem fb_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_alloc» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_alloc

theorem fb_mpt_fail : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_mpt_fail» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_mpt_fail

theorem fb_nibbles_concat : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_nibbles_concat» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_nibbles_concat

theorem fb_node_new_ext : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_node_new_ext» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_node_new_ext fb_alloc

theorem fb__collapse_branch : type_of% InitECandidate.Solver.Wave8GuestInv.«fb__collapse_branch» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb__collapse_branch fb_alloc fb_mpt_fail fb_nibbles_concat fb_node_new_ext InitECandidate.Solver.Wave8GuestInv.«fb_node_new_leaf»

theorem fb__create_branch_from_two_leaves : type_of% InitECandidate.Solver.Wave8GuestInv.«fb__create_branch_from_two_leaves» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb__create_branch_from_two_leaves InitECandidate.Solver.Wave8GuestInv.«fb_node_new_branch» InitECandidate.Solver.Wave8GuestInv.«fb_node_new_leaf»

theorem fb__delete_ext_finish : type_of% InitECandidate.Solver.Wave8GuestInv.«fb__delete_ext_finish» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb__delete_ext_finish fb_mpt_fail fb_nibbles_concat fb_node_new_ext InitECandidate.Solver.Wave8GuestInv.«fb_node_new_leaf»

theorem fb_common_prefix_length : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_common_prefix_length» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_common_prefix_length InitECandidate.Solver.Wave8GuestInv.«fb_min»

theorem fb_memeq : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_memeq» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_memeq

theorem fb__insert_into_leaf : type_of% InitECandidate.Solver.Wave8GuestInv.«fb__insert_into_leaf» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb__insert_into_leaf fb__create_branch_from_two_leaves fb_common_prefix_length fb_memeq fb_node_new_ext

theorem fb__node_needs_rlp : type_of% InitECandidate.Solver.Wave8GuestInv.«fb__node_needs_rlp» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb__node_needs_rlp

theorem fb_nibble_list_to_compact : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_nibble_list_to_compact» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_nibble_list_to_compact

theorem fb_rlp_bytes_encoded_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_bytes_encoded_len» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_bytes_encoded_len

theorem fb_rlp_value_encoded_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_value_encoded_len» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_value_encoded_len

theorem fb__node_rlp_begin : type_of% InitECandidate.Solver.Wave8GuestInv.«fb__node_rlp_begin» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb__node_rlp_begin fb_alloc fb_nibble_list_to_compact fb_rlp_bytes_encoded_len fb_rlp_value_encoded_len

theorem fb_node_ref_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_node_ref_len» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_node_ref_len fb_mpt_fail

theorem fb_memcpy : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_memcpy» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_memcpy

theorem fb_node_hash_cached : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_node_hash_cached» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_node_hash_cached fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» fb_mpt_fail

theorem fb_node_write_ref : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_node_write_ref» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_node_write_ref fb_memcpy fb_mpt_fail fb_node_hash_cached

theorem fb_rlp_encode_bytes : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_encode_bytes» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_encode_bytes

theorem fb_rlp_encode_list_header : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_encode_list_header» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_encode_list_header

theorem fb_rlp_list_header_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_list_header_len» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_list_header_len

theorem fb__node_rlp_finish : type_of% InitECandidate.Solver.Wave8GuestInv.«fb__node_rlp_finish» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb__node_rlp_finish fb_alloc fb_node_ref_len fb_node_write_ref fb_rlp_encode_bytes fb_rlp_encode_list_header fb_rlp_list_header_len fb_rlp_value_encoded_len

theorem fb_node_new_hashed : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_node_new_hashed» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_node_new_hashed fb_alloc

theorem fb_htab_get : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_get» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_get_of fb_memeq

theorem fb_nodedb_lookup : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_nodedb_lookup» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_nodedb_lookup fb_htab_get

theorem fb__resolve_step : type_of% InitECandidate.Solver.Wave8GuestInv.«fb__resolve_step» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb__resolve_step fb_mpt_fail fb_node_new_hashed fb_nodedb_lookup InitECandidate.Solver.Wave8GuestInv.«fb_rlp_item»

theorem fb__rlp_validate_items_body : type_of% InitECandidate.Solver.Wave8GuestInv.«fb__rlp_validate_items_body» :=
  InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb__rlp_validate_items_body

theorem fb__split_extension : type_of% InitECandidate.Solver.Wave8GuestInv.«fb__split_extension» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb__split_extension fb_mpt_fail InitECandidate.Solver.Wave8GuestInv.«fb_node_new_branch» fb_node_new_ext InitECandidate.Solver.Wave8GuestInv.«fb_node_new_leaf»

theorem fb_htab_has : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_has» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_has_of fb_memeq

theorem fb_is_warm_address : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_is_warm_address» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_is_warm_address fb_htab_has

theorem fb_access_gas_cost : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_access_gas_cost» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_access_gas_cost fb_is_warm_address

theorem fb_access_list_payload_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_access_list_payload_len» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_access_list_payload_len fb_rlp_list_header_len

theorem fb_htab_set : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_set» :=
  InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_htab_set

theorem fb_record_pre_state_read : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_record_pre_state_read» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_record_pre_state_read fb_htab_set

theorem fb_key_to_nibbles : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_key_to_nibbles» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_key_to_nibbles

theorem fb_trie_walk : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_trie_walk» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_trie_walk fb_memeq fb_mpt_fail

theorem fb_trie_lookup : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_trie_lookup» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_trie_lookup fb_key_to_nibbles fb_trie_walk

theorem fb_ws_account_leaf : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ws_account_leaf» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_ws_account_leaf_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» fb_trie_lookup

theorem fb_ws_get_account_optional : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ws_get_account_optional» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_ws_get_account_optional_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_ws_account_leaf InitECandidate.Solver.Wave8GuestInv.«fb_decode_account_from_leaf»

theorem fb_get_pre_state_account_optional : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_get_pre_state_account_optional» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_get_pre_state_account_optional_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_htab_set fb_htab_get fb_record_pre_state_read fb_ws_get_account_optional

theorem fb_get_account_optional : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_get_account_optional» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_get_account_optional_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_htab_set fb_htab_get fb_get_pre_state_account_optional

theorem fb_get_account : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_get_account» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_get_account_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_get_account_optional

theorem fb_ws_storage_root_of : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ws_storage_root_of» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_ws_storage_root_of_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_ws_get_account_optional

theorem fb_ws_account_has_storage : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ws_account_has_storage» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_ws_account_has_storage_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_ws_storage_root_of fb_memeq

theorem fb_account_has_storage : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_account_has_storage» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_account_has_storage_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_htab_get fb_record_pre_state_read fb_ws_account_has_storage

theorem fb_account_deployable : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_account_deployable» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_account_deployable_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_get_account fb_memeq fb_account_has_storage

theorem fb_account_exists : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_account_exists» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_account_exists_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_get_account_optional

theorem fb_acct_copy : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_acct_copy» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_acct_copy_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_memcpy

theorem fb_acct_empty : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_acct_empty» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_acct_empty (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_acct_is_empty : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_acct_is_empty» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_acct_is_empty_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_memeq

theorem fb_acct_new : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_acct_new» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_acct_new (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_bal_ensure_account : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_bal_ensure_account» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_bal_ensure_account_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_htab_get fb_htab_set

theorem fb_lst_upsert_idx : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_lst_upsert_idx» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_lst_upsert_idx_of fb_memcpy

theorem fb_add_balance_change : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_add_balance_change» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_add_balance_change_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_bal_ensure_account fb_lst_upsert_idx

theorem fb_add_code_change : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_add_code_change» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_add_code_change_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_bal_ensure_account fb_lst_upsert_idx

theorem fb_lst_push : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_lst_push» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_lst_push_of fb_memcpy

theorem fb_add_nonce_change : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_add_nonce_change» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_add_nonce_change_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_bal_ensure_account fb_lst_push

theorem fb_add_sat : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_add_sat» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_add_sat (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_add_storage_read : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_add_storage_read» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_add_storage_read_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_bal_ensure_account fb_htab_set

theorem fb_add_storage_write : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_add_storage_write» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_add_storage_write_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_bal_ensure_account fb_htab_get fb_htab_set fb_lst_upsert_idx

theorem fb_add_to_bloom : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_add_to_bloom» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_add_to_bloom_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.«fb_keccak256»

theorem fb_add_touched_account : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_add_touched_account» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_add_touched_account_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_bal_ensure_account

theorem fb_addr_from_words : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_addr_from_words» :=
  InitECandidate.Solver.Wave8GuestInv.S01.fb_addr_from_words (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_address_to_u256 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_address_to_u256» :=
  InitECandidate.Solver.Wave8GuestInv.S02.fb_address_to_u256 InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_be»

theorem fb_tx_u256_encoded_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_u256_encoded_len» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_tx_u256_encoded_len_of InitECandidate.Solver.Wave8GuestInv.«fb_u256_byte_length»

theorem fb_rlp_word_encoded_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_word_encoded_len» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_word_encoded_len

theorem fb_auth_payload_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_auth_payload_len» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_auth_payload_len_of fb_tx_u256_encoded_len fb_rlp_word_encoded_len

theorem fb_auth_list_payload_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_auth_list_payload_len» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_auth_list_payload_len_of fb_auth_payload_len fb_rlp_list_header_len

theorem fb_bal_list_remove_idx : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_bal_list_remove_idx» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_bal_list_remove_idx fb_memcpy

theorem fb_bal_remove_change : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_bal_remove_change» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_bal_remove_change fb_bal_list_remove_idx fb_htab_get

theorem fb_block_env : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_block_env» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_block_env (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_rlp_encode_word : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_encode_word» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_encode_word

theorem fb_rlp_put_u256 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_put_u256» :=
  InitECandidate.Solver.Wave8GuestInv.S02.fb_rlp_put_u256 InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_u256_to_be_min» fb_rlp_encode_bytes InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_encode_header : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_encode_header» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_encode_header fb_alloc fb_rlp_encode_bytes fb_rlp_encode_list_header fb_rlp_encode_word fb_rlp_list_header_len fb_rlp_put_u256

theorem fb_withdrawal_rlp_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_withdrawal_rlp_len» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_withdrawal_rlp_len

theorem fb_block_rlp_length : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_block_rlp_length» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_block_rlp_length fb_encode_header InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» fb_rlp_bytes_encoded_len fb_rlp_list_header_len fb_withdrawal_rlp_len

theorem fb_memzero : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_memzero» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_memzero

theorem fb_buffer_read : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_buffer_read» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_buffer_read fb_memcpy fb_memzero

theorem fb_calculate_base_fee_per_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_calculate_base_fee_per_gas» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_calculate_base_fee_per_gas InitECandidate.Solver.Wave8GuestInv.«fb_check_gas_limit» InitECandidate.Solver.Wave8GuestInv.«fb_u256_add» InitECandidate.Solver.Wave8GuestInv.«fb_u256_div» InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_word» InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero» InitECandidate.Solver.Wave8GuestInv.«fb_u256_mul» InitECandidate.Solver.Wave8GuestInv.«fb_u256_sub»

theorem fb_trap_with : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_trap_with» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_trap_with

theorem fb_taylor_exponential : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_taylor_exponential» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_taylor_exponential_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_word» InitECandidate.Solver.Wave8GuestInv.«fb_u256_mul» InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero» InitECandidate.Solver.Wave8GuestInv.«fb_u256_add» InitECandidate.Solver.Wave8GuestInv.«fb_u256_mul_full» fb_trap_with InitECandidate.Solver.Wave8GuestInv.«fb_u256_div»

theorem fb_calculate_blob_gas_price : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_calculate_blob_gas_price» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_calculate_blob_gas_price_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_taylor_exponential

theorem fb_calculate_excess_blob_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_calculate_excess_blob_gas» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_calculate_excess_blob_gas fb_calculate_blob_gas_price InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_word» InitECandidate.Solver.Wave8GuestInv.«fb_u256_gt» InitECandidate.Solver.Wave8GuestInv.«fb_u256_mul» InitECandidate.Solver.Wave8GuestInv.«fb_udiv»

theorem fb_count_tokens_in_data : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_count_tokens_in_data» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_count_tokens_in_data

theorem fb_calculate_intrinsic_cost : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_calculate_intrinsic_cost» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_calculate_intrinsic_cost fb_count_tokens_in_data fb_memeq InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero»

theorem fb_calculate_total_blob_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_calculate_total_blob_gas» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_calculate_total_blob_gas

theorem fb_ceil32 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ceil32» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_ceil32 fb_add_sat

theorem fb_ceil_log2 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ceil_log2» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_ceil_log2

theorem fb_charge_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_charge_gas» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_charge_gas

theorem fb_charge_state_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_charge_state_gas» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_charge_state_gas fb_add_sat

theorem fb_check_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_check_gas» :=
  InitECandidate.Solver.Wave8Leaves.S10.fb_check_gas

theorem fb_fee_mul : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_fee_mul» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_fee_mul_of InitECandidate.Solver.Wave8GuestInv.«fb_u256_mul_full»

theorem fb_is_valid_delegation : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_is_valid_delegation» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_is_valid_delegation

theorem fb_check_transaction : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_check_transaction» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_check_transaction_of InitECandidate.Solver.Wave8GuestInv.«fb_min» fb_calculate_total_blob_gas fb_get_account InitECandidate.Solver.Wave8GuestInv.«fb_u256_lt» InitECandidate.Solver.Wave8GuestInv.«fb_u256_sub» InitECandidate.Solver.Wave8GuestInv.«fb_u256_add» fb_fee_mul fb_calculate_blob_gas_price InitECandidate.Solver.Wave8GuestInv.«fb_u256_add_carry» InitECandidate.Solver.Wave8GuestInv.«fb_u256_fits_word» InitECandidate.Solver.Wave8GuestInv.«fb_get_code» fb_memeq fb_is_valid_delegation

theorem fb_htab_item : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_item» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_item

theorem fb_htab_del : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_del» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_del_of fb_memeq

theorem fb_jdel : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_jdel» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_jdel fb_alloc fb_htab_del fb_htab_get fb_memcpy fb_trap_with

theorem fb_destroy_storage : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_destroy_storage» :=
  InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_destroy_storage

theorem fb_jset : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_jset» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_jset fb_alloc fb_htab_get fb_htab_set fb_memcpy fb_trap_with

theorem fb_set_account : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_set_account» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_set_account fb_jset

theorem fb_destroy_account : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_destroy_account» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_destroy_account fb_destroy_storage fb_set_account

theorem fb_modify_state_commit : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_modify_state_commit» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_modify_state_commit fb_acct_is_empty fb_destroy_account fb_set_account

theorem fb_clear_account_preserving_balance : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_clear_account_preserving_balance» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_clear_account_preserving_balance_of fb_destroy_storage fb_get_account fb_acct_copy fb_modify_state_commit

theorem fb_code_imm : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_code_imm» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_code_imm

theorem fb_compact_to_nibbles : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_compact_to_nibbles» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_compact_to_nibbles

theorem fb_compute_contract_address : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_compute_contract_address» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_compute_contract_address_of fb_rlp_encode_bytes fb_rlp_encode_word fb_rlp_list_header_len fb_rlp_encode_list_header InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» fb_memcpy

theorem fb_compute_create2_contract_address : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_compute_create2_contract_address» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_compute_create2_contract_address_of fb_memcpy InitECandidate.Solver.Wave8GuestInv.«fb_keccak256»

theorem fb_scratch_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_scratch_alloc» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_scratch_alloc

theorem fb_compute_jumpdests : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_compute_jumpdests» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_compute_jumpdests fb_memzero fb_scratch_alloc

theorem fb_create_ether : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_create_ether» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_create_ether_of fb_get_account fb_acct_copy InitECandidate.Solver.Wave8GuestInv.«fb_u256_add» fb_modify_state_commit

theorem fb_set_code : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_set_code» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_set_code fb_acct_copy fb_alloc fb_get_account fb_jset InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» fb_memeq fb_modify_state_commit

theorem fb_words_of : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_words_of» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_words_of fb_ceil32

theorem fb_create_finish : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_create_finish» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_create_finish fb_alloc fb_charge_gas fb_charge_state_gas fb_memcpy fb_set_code fb_words_of

theorem fb_credit_state_gas_refund : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_credit_state_gas_refund» :=
  Campaign.Leaves.S05.fb_credit_state_gas_refund (P := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_ssz_split_var_list : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ssz_split_var_list» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_ssz_split_var_list fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_ssz_fail»

theorem fb_decode_bytes_list : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_decode_bytes_list» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_decode_bytes_list InitECandidate.Solver.Wave8GuestInv.«fb_ssz_fail» fb_ssz_split_var_list

theorem fb_ssz_check_offsets : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ssz_check_offsets» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_ssz_check_offsets InitECandidate.Solver.Wave8GuestInv.«fb_ssz_fail»

theorem fb_ssz_fixed_list_count : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ssz_fixed_list_count» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_ssz_fixed_list_count InitECandidate.Solver.Wave8GuestInv.«fb_ssz_fail» InitECandidate.Solver.Wave8GuestInv.«fb_udivmod»

theorem fb_decode_payload : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_decode_payload» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_decode_payload fb_alloc fb_ssz_check_offsets InitECandidate.Solver.Wave8GuestInv.«fb_ssz_fail» fb_ssz_fixed_list_count fb_ssz_split_var_list

theorem fb_decode_requests : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_decode_requests» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_decode_requests fb_alloc fb_ssz_check_offsets InitECandidate.Solver.Wave8GuestInv.«fb_ssz_fail» fb_ssz_fixed_list_count

theorem fb_decode_stateless_input : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_decode_stateless_input» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_decode_stateless_input fb_alloc fb_decode_bytes_list fb_decode_payload fb_decode_requests fb_ssz_check_offsets InitECandidate.Solver.Wave8GuestInv.«fb_ssz_fail» fb_ssz_fixed_list_count

theorem fb_input_blob : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_input_blob» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_input_blob fb_alloc fb_trap_with

theorem fb_precheck_host_ssz_header : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_precheck_host_ssz_header» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_precheck_host_ssz_header InitECandidate.Solver.Wave8GuestInv.«fb_host_input_byte» InitECandidate.Solver.Wave8GuestInv.«fb_host_input_le32» fb_ssz_check_offsets InitECandidate.Solver.Wave8GuestInv.«fb_ssz_fail»

theorem fb_decode_host_input : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_decode_host_input» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_decode_host_input fb_decode_stateless_input fb_input_blob fb_precheck_host_ssz_header

theorem fb_decode_single : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_decode_single» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_decode_single

theorem fb_frame_state_gas_used : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_state_gas_used» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_frame_state_gas_used

theorem fb_get_delegated_code_address : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_get_delegated_code_address» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_get_delegated_code_address fb_is_valid_delegation

theorem fb_get_pre_state_account : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_get_pre_state_account» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_get_pre_state_account fb_acct_empty fb_get_pre_state_account_optional

theorem fb_is_account_alive : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_is_account_alive» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_is_account_alive fb_acct_is_empty fb_get_account_optional

theorem fb_warm_address : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_warm_address» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_warm_address fb_htab_set

theorem fb_prepare_dispatch : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_prepare_dispatch» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_prepare_dispatch fb_acct_is_empty fb_alloc fb_charge_gas fb_charge_state_gas fb_compute_jumpdests InitECandidate.Solver.Wave8GuestInv.«fb_ext_code_of» fb_get_delegated_code_address fb_get_pre_state_account fb_is_account_alive fb_is_warm_address fb_memcpy InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero» fb_warm_address

theorem fb_htab_new : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_new» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_new

theorem fb_increment_nonce : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_increment_nonce» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_increment_nonce fb_acct_copy fb_get_account fb_modify_state_commit

theorem fb_recover_authority : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_recover_authority» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_recover_authority fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» fb_memcpy fb_rlp_encode_bytes fb_rlp_encode_list_header fb_rlp_encode_word fb_rlp_list_header_len fb_rlp_put_u256 InitECandidate.Solver.Wave8GuestInv.«fb_secp256k1_recover» InitECandidate.Solver.Wave8GuestInv.«fb_u256_gt» InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero» InitECandidate.Solver.Wave8GuestInv.«fb_u256_lt»

theorem fb_validate_authorization_checks : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_validate_authorization_checks» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_validate_authorization_checks fb_get_account InitECandidate.Solver.Wave8GuestInv.«fb_get_code» fb_is_valid_delegation

theorem fb_set_delegation : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_set_delegation» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_set_delegation fb_account_exists fb_alloc fb_charge_gas fb_charge_state_gas InitECandidate.Solver.Wave8GuestInv.«fb_get_code» fb_get_pre_state_account fb_htab_has fb_htab_new fb_htab_set fb_increment_nonce fb_is_valid_delegation fb_memcpy fb_memeq fb_recover_authority fb_set_code InitECandidate.Solver.Wave8GuestInv.«fb_u256_fits_word» InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero» fb_validate_authorization_checks fb_warm_address

theorem fb_depth0_prepare : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_depth0_prepare» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_depth0_prepare fb_frame_state_gas_used fb_prepare_dispatch fb_set_delegation

theorem fb_log_append : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_log_append» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_log_append fb_lst_push

theorem fb_emit_transfer_log : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_emit_transfer_log» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_emit_transfer_log fb_alloc fb_log_append fb_memcpy fb_memzero InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero» InitECandidate.Solver.Wave8GuestInv.«fb_u256_to_be32»

theorem fb_encode_execution_requests : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_encode_execution_requests» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_encode_execution_requests fb_alloc fb_memcpy

theorem fb_rlp_finish_list : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_finish_list» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_finish_list

theorem fb_encode_logs : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_encode_logs» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_encode_logs_of fb_rlp_encode_bytes fb_rlp_finish_list

theorem fb_logs_encoded_bound : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_logs_encoded_bound» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_logs_encoded_bound

theorem fb_encode_receipt : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_encode_receipt» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_encode_receipt_of fb_logs_encoded_bound fb_alloc fb_rlp_encode_word InitECandidate.Solver.Wave8GuestInv.«fb_logs_bloom» fb_rlp_encode_bytes fb_encode_logs fb_rlp_finish_list

theorem fb_encode_transaction : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_encode_transaction» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_encode_transaction InitECandidate.Solver.Wave8GuestInv.«fb_tx_encode_generic»

theorem fb_encode_withdrawal_rlp : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_encode_withdrawal_rlp» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_encode_withdrawal_rlp

theorem fb_evm_init : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_evm_init» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_evm_init_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» fb_memzero

theorem fb_fork_init : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_fork_init» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_fork_init_of fb_alloc fb_memzero fb_addr_from_words InitECandidate.Solver.Wave8GuestInv.«fb_st_be64»

theorem fb_state_restore : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_state_restore» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_state_restore_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_htab_set fb_htab_del

theorem fb_frame_epilogue : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_epilogue» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_frame_epilogue_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_state_restore

theorem fb_frame_halt : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_halt» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_frame_halt

theorem fb_refill_frame_state_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_refill_frame_state_gas» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_refill_frame_state_gas

theorem fb_frame_exception : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_exception» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_frame_exception fb_frame_halt fb_refill_frame_state_gas

theorem fb_frame_mem_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_mem_alloc» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_frame_mem_alloc fb_trap_with

theorem fb_frame_mem_mark : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_mem_mark» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_frame_mem_mark

theorem fb_frame_mem_release : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_mem_release» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_frame_mem_release

theorem fb_htab_count : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_count» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_count

theorem fb_htab_new_scratch : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_new_scratch» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_new_scratch

theorem fb_lst_new_scratch : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_lst_new_scratch» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_lst_new_scratch

theorem fb_scratch_mark : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_scratch_mark» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_scratch_mark

theorem fb_frame_new : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_new» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_frame_new fb_compute_jumpdests fb_frame_mem_alloc fb_frame_mem_mark fb_htab_count fb_htab_new_scratch fb_lst_new_scratch fb_memzero fb_scratch_alloc fb_scratch_mark

theorem fb_frame_open : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_open» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_frame_open fb_frame_new fb_memzero fb_scratch_alloc

theorem fb_move_ether : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_move_ether» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_move_ether fb_acct_copy fb_get_account fb_modify_state_commit InitECandidate.Solver.Wave8GuestInv.«fb_u256_add» InitECandidate.Solver.Wave8GuestInv.«fb_u256_lt» InitECandidate.Solver.Wave8GuestInv.«fb_u256_sub»

theorem fb_precompile_index : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_precompile_index» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_precompile_index InitECandidate.Solver.Wave8GuestInv.«fb_is_zero_bytes»

theorem fb_pre_ecrecover : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_ecrecover» :=
  Campaign.Leaves.S05.fb_pre_ecrecover fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_buffer_read InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_be» InitECandidate.Solver.Wave8GuestInv.«fb_u256_fits_word» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» InitECandidate.Solver.Wave8GuestInv.«fb_secp256k1_ecrecover» fb_memzero

theorem fb_pre_sha256 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_sha256» :=
  Campaign.Leaves.S05.fb_pre_sha256 fb_words_of fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_sha256»

theorem fb_pre_ripemd160 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_ripemd160» :=
  Campaign.Leaves.S05.fb_pre_ripemd160 fb_words_of fb_charge_gas fb_alloc fb_memzero InitECandidate.Solver.Wave8GuestInv.«fb_ripemd160»

theorem fb_pre_identity : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_identity» :=
  Campaign.Leaves.S05.fb_pre_identity (P := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_pre_alt_bn128_add : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_alt_bn128_add» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_pre_alt_bn128_add fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_bn254_g1_add» fb_buffer_read fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_pre_alt_bn128_mul : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_alt_bn128_mul» :=
  Campaign.Leaves.S05.fb_pre_alt_bn128_mul fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_bn254_g1_mul» fb_buffer_read fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_pre_alt_bn128_pairing_check : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_alt_bn128_pairing_check» :=
  Campaign.Leaves.S05.fb_pre_alt_bn128_pairing_check InitECandidate.Solver.Wave8GuestInv.«fb_udivmod» fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_bn254_pairing_check» fb_alloc fb_memzero

theorem fb_sat_word : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_sat_word» :=
  Campaign.Leaves.S05.fb_sat_word (P := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_pre_modexp : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_modexp» :=
  Campaign.Leaves.S05.fb_pre_modexp fb_buffer_read InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_be» fb_sat_word InitECandidate.Solver.Wave8GuestInv.«fb_min» InitECandidate.Solver.Wave8GuestInv.«fb_modexp_gas» fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.«fb_modexp» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_st_le64 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_st_le64» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_st_le64

theorem fb_pre_blake2f : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_blake2f» :=
  Campaign.Leaves.S05.fb_pre_blake2f fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.«fb_blake2b_f» fb_st_le64 InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_pre_kzg_point_evaluation : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_kzg_point_evaluation» :=
  Campaign.Leaves.S05.fb_pre_kzg_point_evaluation fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_kzg_point_evaluation_exec»

theorem fb_pre_bls_g1_add : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_bls_g1_add» :=
  Campaign.Leaves.S05.fb_pre_bls_g1_add fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_bls_g1_add_exec»

theorem fb_pre_bls_g1_msm : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_bls_g1_msm» :=
  Campaign.Leaves.S05.fb_pre_bls_g1_msm InitECandidate.Solver.Wave8GuestInv.«fb_udivmod» InitECandidate.Solver.Wave8GuestInv.«fb_bls_g1_msm_discount» fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_bls_g1_msm_exec»

theorem fb_pre_bls_g2_add : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_bls_g2_add» :=
  Campaign.Leaves.S05.fb_pre_bls_g2_add fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_bls_g2_add_exec»

theorem fb_pre_bls_g2_msm : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_bls_g2_msm» :=
  Campaign.Leaves.S05.fb_pre_bls_g2_msm InitECandidate.Solver.Wave8GuestInv.«fb_udivmod» InitECandidate.Solver.Wave8GuestInv.«fb_bls_g2_msm_discount» fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_bls_g2_msm_exec»

theorem fb_pre_bls_pairing : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_bls_pairing» :=
  Campaign.Leaves.S05.fb_pre_bls_pairing InitECandidate.Solver.Wave8GuestInv.«fb_udivmod» fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_bls_pairing_exec»

theorem fb_pre_bls_map_fp_to_g1 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_bls_map_fp_to_g1» :=
  Campaign.Leaves.S05.fb_pre_bls_map_fp_to_g1 fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_bls_map_fp_to_g1_exec»

theorem fb_pre_bls_map_fp2_to_g2 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_bls_map_fp2_to_g2» :=
  Campaign.Leaves.S05.fb_pre_bls_map_fp2_to_g2 fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_bls_map_fp2_to_g2_exec»

theorem fb_pre_p256verify : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pre_p256verify» :=
  Campaign.Leaves.S05.fb_pre_p256verify fb_charge_gas fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_be» InitECandidate.Solver.Wave8GuestInv.«fb_p256_verify» fb_memzero

theorem fb_run_precompile : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_run_precompile» :=
  Campaign.Leaves.S05.fb_run_precompile fb_pre_ecrecover fb_pre_sha256 fb_pre_ripemd160 fb_pre_identity fb_pre_alt_bn128_add fb_pre_alt_bn128_mul fb_pre_alt_bn128_pairing_check fb_pre_modexp fb_pre_blake2f fb_pre_kzg_point_evaluation fb_pre_bls_g1_add fb_pre_bls_g1_msm fb_pre_bls_g2_add fb_pre_bls_g2_msm fb_pre_bls_pairing fb_pre_bls_map_fp_to_g1 fb_pre_bls_map_fp2_to_g2 fb_pre_p256verify

theorem fb_frame_prologue : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_prologue» :=
  Campaign.Leaves.S05.fb_frame_prologue InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero» fb_move_ether fb_memeq fb_emit_transfer_log fb_precompile_index fb_run_precompile

theorem fb_frame_start : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_frame_start» :=
  Campaign.Leaves.S05.fb_frame_start fb_frame_prologue fb_frame_exception

theorem fb_set_retdata : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_set_retdata» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_set_retdata_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_memcpy

theorem fb_stack_push : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_stack_push» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_stack_push_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_memcpy

theorem fb_generic_create : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_generic_create» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_generic_create_of fb_set_retdata fb_get_account InitECandidate.Solver.Wave8GuestInv.«fb_u256_lt» fb_stack_push fb_warm_address fb_is_account_alive fb_charge_state_gas fb_account_deployable fb_increment_nonce fb_credit_state_gas_refund InitECandidate.Solver.Wave8GuestInv.«fb_child_message» InitECandidate.Solver.Wave8GuestInv.«fb_start_child»

theorem fb_get_pre_tx_account : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_get_pre_tx_account» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_get_pre_tx_account fb_htab_get fb_record_pre_state_read fb_ws_get_account_optional

theorem fb_get_transient_storage : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_get_transient_storage» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_get_transient_storage_of InitECandidate.Solver.Wave8GuestInv.«fb_sk_make» fb_htab_get

theorem fb_header_hash : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_header_hash» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_header_hash fb_encode_header InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» InitECandidate.Solver.Wave8GuestInv.«fb_keccak256»

theorem fb_header_init : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_header_init» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_header_init_of fb_alloc fb_memzero

theorem fb_htab_copy : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_copy» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_copy_of fb_memcpy

theorem fb_htab_find_leaf : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_find_leaf» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_find_leaf

theorem fb_htab_first_diff : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_first_diff» :=
  InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_htab_first_diff

theorem fb_htab_grow : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_grow» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_grow_of fb_memcpy

theorem fb_htab_keys : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_keys» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_keys_of fb_memcpy

theorem fb_htab_new_internal : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_new_internal» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_new_internal_of fb_memcpy

theorem fb_htab_new_leaf : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_new_leaf» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_new_leaf_of fb_memcpy

theorem fb_htab_new_node : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_new_node» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_new_node_of fb_memcpy

theorem fb_htab_union_into : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htab_union_into» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_htab_union_into_of fb_memcpy fb_htab_set

theorem fb_pack_bytes : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pack_bytes» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_pack_bytes

theorem fb_merkleize : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_merkleize» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_merkleize_of fb_ceil_log2 InitECandidate.Solver.Wave8GuestInv.«fb_max» fb_memcpy InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_memzero InitECandidate.Solver.Wave8GuestInv.«fb_sha256_pair» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_bytes_vector : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_bytes_vector» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_bytes_vector_of fb_memzero fb_memcpy InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_pack_bytes fb_merkleize InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_u64_at : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_u64_at» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_u64_at_of fb_memzero fb_memcpy

theorem fb_htr_bdep : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_bdep» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_bdep_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_htr_bytes_vector fb_memcpy fb_htr_u64_at fb_merkleize InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_bexit : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_bexit» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_bexit_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_htr_bytes_vector fb_merkleize InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_mix_in_length : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_mix_in_length» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_mix_in_length_of fb_memzero fb_st_le64 InitECandidate.Solver.Wave8GuestInv.«fb_sha256_pair»

theorem fb_htr_bytes_list : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_bytes_list» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_bytes_list_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_pack_bytes fb_merkleize InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» fb_mix_in_length

theorem fb_htr_cons : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_cons» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_cons_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_htr_bytes_vector fb_merkleize InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_deposit : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_deposit» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_deposit_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_htr_bytes_vector fb_memcpy fb_htr_u64_at fb_merkleize InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_merkleize_progressive : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_merkleize_progressive» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_merkleize_progressive_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_merkleize fb_memzero InitECandidate.Solver.Wave8GuestInv.«fb_sha256_pair» fb_memcpy InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_plist_chunks : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_plist_chunks» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_plist_chunks_of fb_merkleize_progressive fb_mix_in_length

theorem fb_htr_pbytes : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_pbytes» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_pbytes_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_pack_bytes fb_htr_plist_chunks InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_withdrawal : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_withdrawal» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_withdrawal_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_htr_u64_at fb_htr_bytes_vector fb_merkleize InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_pcontainer : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_pcontainer» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_pcontainer_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_merkleize_progressive fb_memzero InitECandidate.Solver.Wave8GuestInv.«fb_sha256_pair» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_payload : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_payload» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_payload_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_memcpy fb_htr_bytes_vector fb_htr_u64_at fb_htr_bytes_list fb_htr_pbytes fb_htr_plist_chunks InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» fb_htr_withdrawal fb_htr_pcontainer

theorem fb_htr_wdreq : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_wdreq» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_wdreq_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_htr_bytes_vector fb_htr_u64_at fb_merkleize InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_request_list : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_request_list» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_request_list_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_htr_deposit fb_htr_wdreq fb_htr_cons fb_htr_bdep fb_htr_bexit fb_htr_plist_chunks InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_requests : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_requests» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_requests_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_htr_request_list fb_htr_pcontainer InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_htr_new_payload_request : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_htr_new_payload_request» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_htr_new_payload_request_of InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_htr_payload fb_htr_plist_chunks fb_memcpy fb_htr_requests fb_merkleize InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_idx_start_account : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_idx_start_account» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_idx_start_account fb_alloc fb_get_pre_tx_account fb_htab_get fb_htab_set fb_memcpy fb_memzero fb_st_le64

theorem fb_incorporate_child_on_error : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_incorporate_child_on_error» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_incorporate_child_on_error (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_incorporate_child_on_success : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_incorporate_child_on_success» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_incorporate_child_on_success_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_incorporate_child_on_error fb_log_append fb_htab_union_into

theorem fb_is_valid_jumpdest : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_is_valid_jumpdest» :=
  InitECandidate.Solver.Wave8Leaves.S09.fb_is_valid_jumpdest (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_tx_is_blob : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_is_blob» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_tx_is_blob

theorem fb_is_valid_versioned_hashes : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_is_valid_versioned_hashes» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_is_valid_versioned_hashes InitECandidate.Solver.Wave8GuestInv.«fb_decode_transaction» fb_memeq fb_tx_is_blob

theorem fb_ld_be64 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ld_be64» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_ld_be64

theorem fb_lst_new : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_lst_new» :=
  InitECandidate.Solver.Wave8GuestInv.Htab.fb_lst_new

theorem fb_mark_account_created : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_mark_account_created» :=
  InitECandidate.Solver.Wave8Leaves.S04.Verified.fb_mark_account_created fb_htab_set

theorem fb_mem_init : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_mem_init» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_mem_init_of

theorem fb_merge_tx_into_block : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_merge_tx_into_block» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_merge_tx_into_block fb_htab_get fb_htab_item fb_htab_new fb_htab_set fb_htab_union_into

theorem fb_mpt_init : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_mpt_init» :=
  InitECandidate.Solver.Wave8GuestInv.S14.fb_mpt_init_of fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_keccak256»

theorem fb_msg_new : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_msg_new» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_msg_new fb_alloc fb_memzero

theorem fb_node_invalidate : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_node_invalidate» :=
  InitECandidate.Solver.Wave8Leaves.S00Verified.fb_node_invalidate

theorem fb_nodedb_build : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_nodedb_build» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_nodedb_build fb_htab_new fb_htab_set InitECandidate.Solver.Wave8GuestInv.«fb_keccak256»

theorem fb_stack_pop : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_stack_pop» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_stack_pop (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_pc_add : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_pc_add» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_pc_add (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_op_add : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_add» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_op_add_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_charge_gas fb_stack_pop InitECandidate.Solver.Wave8GuestInv.«fb_u256_add» fb_stack_push fb_pc_add

theorem fb_op_addmod : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_addmod» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_op_addmod_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_charge_gas fb_stack_pop InitECandidate.Solver.Wave8GuestInv.«fb_u256_addmod» fb_stack_push fb_pc_add

theorem fb_op_address : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_address» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_op_address_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_charge_gas fb_address_to_u256 fb_stack_push fb_pc_add

theorem fb_op_and : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_and» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_op_and_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_charge_gas fb_stack_pop fb_stack_push fb_pc_add

theorem fb_to_address_masked : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_to_address_masked» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_to_address_masked (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_warm_after_charge : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_warm_after_charge» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_warm_after_charge_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_warm_address

theorem fb_op_balance : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_balance» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_op_balance_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_stack_pop fb_to_address_masked fb_access_gas_cost fb_charge_gas fb_warm_after_charge fb_get_account fb_stack_push fb_pc_add

theorem fb_op_basefee : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_basefee» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_op_basefee_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_charge_gas fb_block_env fb_stack_push fb_pc_add

theorem fb_op_blobbasefee : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_blobbasefee» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_op_blobbasefee_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_charge_gas fb_block_env fb_calculate_blob_gas_price fb_stack_push fb_pc_add

theorem fb_op_blobhash : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_blobhash» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_op_blobhash_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_charge_gas fb_stack_pop fb_sat_word InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_be» fb_stack_push fb_pc_add

theorem fb_track_ancestor_access : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_track_ancestor_access» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_track_ancestor_access (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv)

theorem fb_op_blockhash : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_blockhash» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_op_blockhash_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_stack_pop fb_charge_gas fb_block_env fb_sat_word InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_be» fb_track_ancestor_access fb_stack_push fb_pc_add

theorem fb_op_coinbase : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_coinbase» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_coinbase fb_charge_gas fb_block_env fb_address_to_u256 fb_stack_push fb_pc_add

theorem fb_op_create : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_create» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_create_of fb_stack_pop fb_sat_word InitECandidate.Solver.Wave8GuestInv.«fb_extend_memory_cost1» fb_words_of fb_add_sat fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_extend_memory» fb_get_account fb_compute_contract_address fb_generic_create fb_pc_add

theorem fb_op_create2 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_create2» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_create2_of fb_stack_pop fb_sat_word InitECandidate.Solver.Wave8GuestInv.«fb_extend_memory_cost1» fb_words_of fb_add_sat fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_u256_to_be32» InitECandidate.Solver.Wave8GuestInv.«fb_extend_memory» fb_compute_create2_contract_address fb_generic_create fb_pc_add

theorem fb_op_delegatecall : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_delegatecall» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_delegatecall fb_stack_pop fb_to_address_masked InitECandidate.Solver.Wave8GuestInv.«fb_extend_memory_cost2» fb_is_warm_address fb_add_sat fb_charge_gas fb_warm_address InitECandidate.Solver.Wave8GuestInv.«fb_calculate_delegation_cost» InitECandidate.Solver.Wave8GuestInv.«fb_ext_code_of» fb_sat_word InitECandidate.Solver.Wave8GuestInv.«fb_calculate_message_call_gas» InitECandidate.Solver.Wave8GuestInv.«fb_extend_memory» InitECandidate.Solver.Wave8GuestInv.«fb_generic_call» fb_pc_add

theorem fb_op_div : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_div» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_div fb_stack_pop fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_u256_div» fb_stack_push fb_pc_add

theorem fb_op_dup : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_dup» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_dup fb_charge_gas fb_stack_push fb_pc_add

theorem fb_op_dupn : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_dupn» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_dupn_of fb_charge_gas fb_stack_push fb_pc_add

theorem fb_op_eq : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_eq» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_eq_of fb_stack_pop fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_u256_eq» fb_stack_push fb_pc_add

theorem fb_op_exchange : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_exchange» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_exchange_of fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_max» fb_pc_add

theorem fb_op_exp : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_exp» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_exp fb_stack_pop InitECandidate.Solver.Wave8GuestInv.«fb_u256_byte_length» fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_u256_exp» fb_stack_push fb_pc_add

theorem fb_op_extcodecopy : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_extcodecopy» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_extcodecopy fb_stack_pop fb_to_address_masked fb_sat_word fb_words_of InitECandidate.Solver.Wave8GuestInv.«fb_extend_memory_cost1» fb_access_gas_cost fb_add_sat fb_charge_gas fb_warm_after_charge InitECandidate.Solver.Wave8GuestInv.«fb_extend_memory» InitECandidate.Solver.Wave8GuestInv.«fb_ext_code_of» fb_buffer_read fb_pc_add

theorem fb_op_extcodehash : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_extcodehash» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_extcodehash fb_stack_pop fb_to_address_masked fb_access_gas_cost fb_charge_gas fb_warm_after_charge fb_get_account fb_acct_is_empty fb_stack_push InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_be» fb_pc_add

theorem fb_stack_push_word : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_stack_push_word» :=
  InitECandidate.Solver.Wave8GuestInv.S06.fb_stack_push_word_of (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_stack_push

theorem fb_op_extcodesize : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_extcodesize» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_extcodesize fb_stack_pop fb_to_address_masked fb_access_gas_cost fb_charge_gas fb_warm_after_charge InitECandidate.Solver.Wave8GuestInv.«fb_ext_code_of» fb_stack_push_word fb_pc_add

theorem fb_op_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_gas» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_gas fb_charge_gas fb_stack_push_word fb_pc_add

theorem fb_op_gaslimit : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_gaslimit» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_gaslimit fb_charge_gas fb_block_env fb_stack_push_word fb_pc_add

theorem fb_op_gasprice : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_gasprice» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_op_gasprice fb_charge_gas fb_stack_push fb_pc_add

theorem fb_stack_push_bool : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_stack_push_bool» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_stack_push_bool fb_stack_push

theorem fb_op_gt : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_gt» :=
  InitECandidate.Solver.Wave8Leaves.S09.fb_op_gt (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_charge_gas fb_pc_add fb_stack_pop fb_stack_push_bool InitECandidate.Solver.Wave8GuestInv.«fb_u256_gt»

theorem fb_op_iszero : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_iszero» :=
  InitECandidate.Solver.Wave8Leaves.S09.fb_op_iszero (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_charge_gas fb_pc_add fb_stack_pop fb_stack_push_bool InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero»

theorem fb_op_jump : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_jump» :=
  InitECandidate.Solver.Wave8Leaves.S09.fb_op_jump (GuestInv := @InitECandidate.Solver.Wave8GuestInv.GuestInv) fb_charge_gas fb_is_valid_jumpdest fb_stack_pop

theorem fb_op_prevrandao : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_prevrandao» :=
  InitECandidate.Solver.Wave8Leaves.S10.fb_op_prevrandao fb_charge_gas fb_block_env InitECandidate.Solver.Wave8GuestInv.«fb_u256_from_be» fb_stack_push fb_pc_add

theorem fb_op_returndatasize : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_returndatasize» :=
  InitECandidate.Solver.Wave8Leaves.S10.fb_op_returndatasize fb_charge_gas fb_stack_push_word fb_pc_add

theorem fb_op_shl : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_shl» :=
  InitECandidate.Solver.Wave8Leaves.S10.fb_op_shl fb_stack_pop fb_charge_gas fb_sat_word InitECandidate.Solver.Wave8GuestInv.«fb_u256_shl» fb_stack_push fb_pc_add

theorem fb_op_slotnum : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_slotnum» :=
  InitECandidate.Solver.Wave8Leaves.S10.fb_op_slotnum fb_charge_gas fb_block_env fb_stack_push_word fb_pc_add

theorem fb_op_stop : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_stop» :=
  InitECandidate.Solver.Wave8Leaves.S10.fb_op_stop fb_pc_add

theorem fb_op_sub : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_sub» :=
  InitECandidate.Solver.Wave8Leaves.S10.fb_op_sub fb_stack_pop fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_u256_sub» fb_stack_push fb_pc_add

theorem fb_stack_swap_positions : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_stack_swap_positions» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_stack_swap_positions

theorem fb_op_swap : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_swap» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_op_swap_of fb_charge_gas fb_stack_swap_positions fb_pc_add

theorem fb_op_swapn : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_swapn» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_op_swapn_of fb_charge_gas fb_code_imm fb_decode_single fb_stack_swap_positions fb_pc_add

theorem fb_op_timestamp : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_timestamp» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_op_timestamp_of fb_charge_gas fb_block_env fb_stack_push_word fb_pc_add

theorem fb_op_tload : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_tload» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_op_tload_of fb_stack_pop fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_u256_to_be32» fb_get_transient_storage fb_stack_push fb_pc_add

theorem fb_require_not_static : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_require_not_static» :=
  InitECandidate.Solver.Wave8Leaves.S08.fb_require_not_static

theorem fb_set_transient_storage : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_set_transient_storage» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_set_transient_storage_of InitECandidate.Solver.Wave8GuestInv.«fb_sk_make» InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero» fb_jdel fb_alloc fb_jset

theorem fb_op_tstore : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_tstore» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_op_tstore_of fb_require_not_static fb_stack_pop fb_charge_gas InitECandidate.Solver.Wave8GuestInv.«fb_u256_to_be32» fb_set_transient_storage fb_pc_add

theorem fb_op_xor : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_op_xor» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_op_xor_of fb_stack_pop fb_charge_gas fb_stack_push fb_pc_add

theorem fb_output_write : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_output_write» :=
  InitECandidate.Solver.Wave8GuestInv.S15.fb_output_write_of

theorem fb_recover_transaction_public_key : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_recover_transaction_public_key» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_recover_transaction_public_key InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_signature_recovery_parameters» InitECandidate.Solver.Wave8GuestInv.«fb_secp256k1_recover» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_sender_address_from_public_key : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_sender_address_from_public_key» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_sender_address_from_public_key InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» fb_memcpy InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_recover_sender_with_chain_id : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_recover_sender_with_chain_id» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_recover_sender_with_chain_id InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc fb_recover_transaction_public_key fb_sender_address_from_public_key InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_remove_storage_write : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_remove_storage_write» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_remove_storage_write fb_bal_list_remove_idx fb_htab_del fb_htab_get

theorem fb_requests_append : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_requests_append» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_requests_append_of fb_alloc fb_memcpy

theorem fb_rlp_be_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_be_len» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_be_len

theorem fb_rlp_fail : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_fail» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_fail

theorem fb_rlp_header_len : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_header_len» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_header_len

theorem fb_rlp_item_header : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_item_header» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_item_header

theorem fb_rlp_item_total : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_item_total» :=
  InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_rlp_item_total

theorem fb_rlp_item_total_unchecked : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_item_total_unchecked» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_item_total_unchecked

theorem fb_rlp_put_be : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_put_be» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_put_be

theorem fb_rlp_read_length : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_read_length» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_read_length

theorem fb_rlp_validate_items : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_validate_items» :=
  InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.fb_rlp_validate_items

theorem fb_rlp_write_header : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_write_header» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_rlp_write_header

theorem fb_scratch_release : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_scratch_release» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_scratch_release

theorem fb_serialize_result : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_serialize_result» :=
  InitECandidate.Solver.Wave8GuestInv.S15.fb_serialize_result_of fb_memcpy fb_st_le64

theorem fb_set_account_balance : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_set_account_balance» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_set_account_balance fb_get_account fb_acct_copy fb_modify_state_commit

theorem fb_tx_signing_hash_mode : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_signing_hash_mode» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_tx_signing_hash_mode InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.«fb_tx_encode_generic» InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_signing_hash_155 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_155» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_signing_hash_155 fb_tx_signing_hash_mode

theorem fb_signing_hash_1559 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_1559» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_signing_hash_1559 fb_tx_signing_hash_mode

theorem fb_signing_hash_2930 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_2930» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_signing_hash_2930 fb_tx_signing_hash_mode

theorem fb_signing_hash_4844 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_4844» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_signing_hash_4844 fb_tx_signing_hash_mode

theorem fb_signing_hash_7702 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_7702» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_signing_hash_7702 fb_tx_signing_hash_mode

theorem fb_signing_hash_pre155 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_pre155» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_signing_hash_pre155 fb_tx_signing_hash_mode

theorem fb_ssz_init : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_ssz_init» :=
  InitECandidate.Solver.Wave8GuestInv.S15.fb_ssz_init_of fb_alloc

theorem fb_st_le32 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_st_le32» :=
  InitECandidate.Solver.Wave8Leaves.Rlp.fb_st_le32

theorem fb_state_fresh_tx : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_state_fresh_tx» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_state_fresh_tx_of fb_alloc fb_htab_new

theorem fb_stor_lookup : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_stor_lookup» :=
  InitECandidate.Solver.Wave8Leaves.S03.fb_stor_lookup fb_htab_get

theorem fb_te_new : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_te_new» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_te_new_of fb_alloc fb_memzero

theorem fb_tx_chain_id : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_chain_id» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_tx_chain_id InitECandidate.Solver.Wave8GuestInv.«fb_u256_fits_word» InitECandidate.Solver.Wave8GuestInv.«fb_u256_sub» InitECandidate.Solver.Wave8GuestInv.«fb_u256_shr»

theorem fb_tx_encode_bound : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_encode_bound» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_tx_encode_bound_of fb_access_list_payload_len fb_auth_list_payload_len

theorem fb_tx_has_access_list : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_has_access_list» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_tx_has_access_list

theorem fb_tx_is_setcode : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_is_setcode» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_tx_is_setcode

theorem fb_tx_put_access_list : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_put_access_list» :=
  InitECandidate.Solver.Wave8GuestInv.S11.fb_tx_put_access_list_of fb_access_list_payload_len fb_rlp_encode_list_header fb_rlp_list_header_len fb_rlp_encode_bytes

theorem fb_tx_put_blob_hashes : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_put_blob_hashes» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_tx_put_blob_hashes fb_rlp_encode_list_header fb_rlp_encode_bytes

theorem fb_tx_put_to : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_put_to» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_tx_put_to fb_rlp_encode_bytes

theorem fb_tx_put_u256 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_put_u256» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_tx_put_u256 InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_u256_to_be_min» fb_rlp_encode_bytes InitECandidate.Solver.Wave8GuestInv.«fb_heap_release»

theorem fb_udiv_small5 : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_udiv_small5» :=
  InitECandidate.Solver.Wave8Leaves.S12.fb_udiv_small5 InitECandidate.Solver.Wave8GuestInv.«fb_udiv»

theorem fb_validate_block_access_list_gas_limit : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_validate_block_access_list_gas_limit» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_validate_block_access_list_gas_limit fb_htab_has fb_htab_item InitECandidate.Solver.Wave8GuestInv.«fb_udiv»

theorem fb_validate_header : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_validate_header» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_validate_header fb_alloc fb_calculate_base_fee_per_gas fb_calculate_excess_blob_gas fb_header_hash InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» fb_memeq InitECandidate.Solver.Wave8GuestInv.«fb_u256_eq» InitECandidate.Solver.Wave8GuestInv.«fb_u256_is_zero»

theorem fb_validate_headers : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_validate_headers» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_validate_headers fb_alloc InitECandidate.Solver.Wave8GuestInv.«fb_decode_header» InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» fb_memeq

theorem fb_validate_transaction : type_of% InitECandidate.Solver.Wave8GuestInv.«fb_validate_transaction» :=
  InitECandidate.Solver.Wave8Leaves.S13.certified_fb_validate_transaction fb_calculate_intrinsic_cost InitECandidate.Solver.Wave8GuestInv.«fb_u256_fits_word»

theorem gbody_op_dispatch : type_of% InitECandidate.Solver.Wave8GuestInv.«gbody_op_dispatch» :=
  InitECandidate.Solver.Wave8GuestInv.RunFramesRace.gbody_op_dispatch

theorem gbody_run_frames : type_of% InitECandidate.Solver.Wave8GuestInv.«gbody_run_frames» :=
  InitECandidate.Solver.Wave8GuestInv.RunFramesRace.gbody_run_frames

theorem htab_del_progress_spec : type_of% InitECandidate.Solver.Wave8GuestInv.«htab_del_progress_spec» :=
  InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.htab_del_progress_spec

theorem htab_del_spec : type_of% InitECandidate.Solver.Wave8GuestInv.«htab_del_spec» :=
  InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.htab_del_spec

theorem htab_truncate_spec : type_of% InitECandidate.Solver.Wave8GuestInv.«htab_truncate_spec» :=
  InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.htab_truncate_spec

theorem iz_node_invalidate : type_of% InitECandidate.Solver.Wave8GuestInv.«iz_node_invalidate» :=
  InitECandidate.Solver.Wave8Contracts.M23.iz_node_invalidate

theorem nf_node_invalidate : type_of% InitECandidate.Solver.Wave8GuestInv.«nf_node_invalidate» :=
  InitECandidate.Solver.Wave8Contracts.M25.nf_node_invalidate

theorem nz_htab_set : type_of% InitECandidate.Solver.Wave8GuestInv.«nz_htab_set» :=
  InitECandidate.Solver.Wave8Contracts.M25.nz_htab_set

theorem ro_calculate_total_blob_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_calculate_total_blob_gas» :=
  InitECandidate.Solver.Wave8GuestInv.R10Ports.ro_calculate_total_blob_gas

theorem ro_check_gas : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_check_gas» :=
  InitECandidate.Solver.Wave8GuestInv.R10Ports.ro_check_gas

theorem ro_check_gas_limit : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_check_gas_limit» :=
  InitECandidate.Solver.Wave8GuestInv.R10Ports.ro_check_gas_limit

theorem ro_common_prefix_length : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_common_prefix_length» :=
  InitECandidate.Solver.Wave8GuestInv.R10Ports.ro_common_prefix_length

theorem ro_fee_mul : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_fee_mul» :=
  InitECandidate.Solver.Wave8GuestInv.R10Ports.ro_fee_mul

theorem ro_heap_mark : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_heap_mark» :=
  InitECandidate.Solver.Wave8GuestInv.R10Ports.ro_heap_mark

theorem ro_htab_get : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_htab_get» :=
  InitECandidate.Solver.Wave8Contracts.M15.ro_htab_get

theorem ro_htab_has : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_htab_has» :=
  InitECandidate.Solver.Wave8Contracts.M15.ro_htab_has

theorem ro_htab_item : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_htab_item» :=
  InitECandidate.Solver.Wave8Contracts.M15.ro_htab_item

theorem ro_max : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_max» :=
  InitECandidate.Solver.Wave8Contracts.M15.ro_max

theorem ro_memeq : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_memeq» :=
  InitECandidate.Solver.Wave8Contracts.M15.ro_memeq

theorem ro_min : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_min» :=
  InitECandidate.Solver.Wave8Contracts.M15.ro_min

theorem ro_stor_lookup : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_stor_lookup» :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_stor_lookup

theorem ro_tx_chain_id : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_tx_chain_id» :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_tx_chain_id

theorem ro_tx_has_access_list : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_tx_has_access_list» :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_tx_has_access_list

theorem ro_tx_is_blob : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_tx_is_blob» :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_tx_is_blob

theorem ro_tx_is_setcode : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_tx_is_setcode» :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_tx_is_setcode

theorem ro_u256_eq : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_u256_eq» :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_u256_eq

theorem ro_u256_is_zero : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_u256_is_zero» :=
  InitECandidate.Solver.Wave8Contracts.M18.ro_u256_is_zero

theorem ro_u256_mul : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_u256_mul» :=
  InitECandidate.Solver.Wave8Contracts.M18.ro_u256_mul

theorem ro_u256_sub : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_u256_sub» :=
  InitECandidate.Solver.Wave8Contracts.M18.ro_u256_sub

theorem ro_udiv_small5 : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_udiv_small5» :=
  InitECandidate.Solver.Wave8Contracts.M18.ro_udiv_small5

theorem ro_validate_block_access_list_gas_limit : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_validate_block_access_list_gas_limit» :=
  InitECandidate.Solver.Wave8Contracts.M18.ro_validate_block_access_list_gas_limit

theorem ro_validate_transaction : type_of% InitECandidate.Solver.Wave8GuestInv.«ro_validate_transaction» :=
  InitECandidate.Solver.Wave8Contracts.M18.ro_validate_transaction

theorem rt_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.«rt_alloc» :=
  InitECandidate.Solver.Wave8Contracts.M25.rt_alloc

theorem rt_lst_new : type_of% InitECandidate.Solver.Wave8GuestInv.«rt_lst_new» :=
  InitECandidate.Solver.Wave8Contracts.M26.rt_lst_new

theorem rt_msg_new : type_of% InitECandidate.Solver.Wave8GuestInv.«rt_msg_new» :=
  InitECandidate.Solver.Wave8Contracts.M26.rt_msg_new

theorem rt_node_new_ext : type_of% InitECandidate.Solver.Wave8GuestInv.«rt_node_new_ext» :=
  InitECandidate.Solver.Wave8Contracts.M26.rt_node_new_ext

theorem rt_scratch_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.«rt_scratch_alloc» :=
  InitECandidate.Solver.Wave8Contracts.M26.rt_scratch_alloc

theorem rt_te_new : type_of% InitECandidate.Solver.Wave8GuestInv.«rt_te_new» :=
  InitECandidate.Solver.Wave8Contracts.M27.rt_te_new

theorem rv_common_prefix_length : type_of% InitECandidate.Solver.Wave8GuestInv.«rv_common_prefix_length» :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_common_prefix_length

theorem rv_min : type_of% InitECandidate.Solver.Wave8GuestInv.«rv_min» :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_min

theorem rv_rlp_encode_bytes : type_of% InitECandidate.Solver.Wave8GuestInv.«rv_rlp_encode_bytes» :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_rlp_encode_bytes

theorem rv_u256_to_be_min : type_of% InitECandidate.Solver.Wave8GuestInv.«rv_u256_to_be_min» :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_u256_to_be_min

theorem rv_validate_transaction : type_of% InitECandidate.Solver.Wave8GuestInv.«rv_validate_transaction» :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_validate_transaction

theorem wk_extract_deposit_data : type_of% InitECandidate.Solver.Wave8GuestInv.«wk_extract_deposit_data» :=
  InitECandidate.Solver.Wave8Contracts.M05.wk_extract_deposit_data

theorem wk_memcpy : type_of% InitECandidate.Solver.Wave8GuestInv.«wk_memcpy» :=
  InitECandidate.Solver.Wave8Contracts.M08.wk_memcpy

theorem wk_memzero : type_of% InitECandidate.Solver.Wave8GuestInv.«wk_memzero» :=
  InitECandidate.Solver.Wave8Contracts.M08.wk_memzero

theorem wk_rlp_encode_bytes : type_of% InitECandidate.Solver.Wave8GuestInv.«wk_rlp_encode_bytes» :=
  InitECandidate.Solver.Wave8GuestInv.M11.wk_rlp_encode_bytes

theorem wk_rlp_encode_word : type_of% InitECandidate.Solver.Wave8GuestInv.«wk_rlp_encode_word» :=
  InitECandidate.Solver.Wave8GuestInv.M11.wk_rlp_encode_word

theorem wk_sk_make : type_of% InitECandidate.Solver.Wave8GuestInv.«wk_sk_make» :=
  InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs.wk_sk_make

theorem wk_st_le64 : type_of% InitECandidate.Solver.Wave8GuestInv.«wk_st_le64» :=
  InitECandidate.Solver.Wave8Contracts.M12.wk_st_le64

theorem wk_u256_to_be_min : type_of% InitECandidate.Solver.Wave8GuestInv.«wk_u256_to_be_min» :=
  InitECandidate.Solver.Wave8GuestInv.M13.wk_u256_to_be_min

theorem ww_memzero : type_of% InitECandidate.Solver.Wave8GuestInv.«ww_memzero» :=
  InitECandidate.Solver.Wave8Contracts.M28.ww_memzero

theorem zv_memzero : type_of% InitECandidate.Solver.Wave8GuestInv.«zv_memzero» :=
  InitECandidate.Solver.Wave8Contracts.M29.zv_memzero

end InitECandidate.Solver.Wave8GuestInv.Merged
