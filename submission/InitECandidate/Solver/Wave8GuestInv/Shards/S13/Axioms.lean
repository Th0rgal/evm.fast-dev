import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.calculate_intrinsic_cost
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.validate_transaction
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.validate_block_access_list_gas_limit
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.encode_header
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.header_hash
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.is_valid_versioned_hashes
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.nodedb_build
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.block_rlp_length
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.encode_execution_requests
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.calculate_base_fee_per_gas
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.calculate_excess_blob_gas
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.validate_header
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.validate_headers
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.ceil_log2
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.ssz_split_var_list
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.decode_bytes_list
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.ssz_check_offsets
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.ssz_fixed_list_count
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.decode_payload
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.decode_requests
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.decode_stateless_input
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.input_blob
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.precheck_host_ssz_header
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.decode_host_input

/- Exact spec equality and axiom audit, following s01 at 9bd58bb2e. -/
namespace InitECandidate.Solver.Wave8Leaves.S13
open Spec

instance : IsGuestInv (@Wave8GuestInv.GuestInv) where
  eval s p h := Wave8GuestInv.guestInv_evaluate s p h
  congr hc hm hs hb h := Wave8GuestInv.guestInv_congr hc hm hs hb h

instance : HasOrdinaryDomain (@Wave8GuestInv.GuestInv) where
  memaddrs _ h := h.memaddrs

example : type_of% (fb_calculate_intrinsic_cost (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_count_tokens_in_data» →
    type_of% Wave8GuestInv.«fb_memeq» →
    type_of% Wave8GuestInv.«fb_u256_is_zero» →
    type_of% Wave8GuestInv.«fb_calculate_intrinsic_cost») := rfl

theorem certified_fb_calculate_intrinsic_cost : (type_of% Wave8GuestInv.«fb_count_tokens_in_data» →
    type_of% Wave8GuestInv.«fb_memeq» →
    type_of% Wave8GuestInv.«fb_u256_is_zero» →
    type_of% Wave8GuestInv.«fb_calculate_intrinsic_cost») :=
  fb_calculate_intrinsic_cost (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_validate_transaction (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_calculate_intrinsic_cost» →
    type_of% Wave8GuestInv.«fb_u256_fits_word» →
    type_of% Wave8GuestInv.«fb_validate_transaction») := rfl

theorem certified_fb_validate_transaction : (type_of% Wave8GuestInv.«fb_calculate_intrinsic_cost» →
    type_of% Wave8GuestInv.«fb_u256_fits_word» →
    type_of% Wave8GuestInv.«fb_validate_transaction») :=
  fb_validate_transaction (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_validate_block_access_list_gas_limit (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_htab_has» →
    type_of% Wave8GuestInv.«fb_htab_item» →
    type_of% Wave8GuestInv.«fb_udiv» →
    type_of% Wave8GuestInv.«fb_validate_block_access_list_gas_limit») := rfl

theorem certified_fb_validate_block_access_list_gas_limit : (type_of% Wave8GuestInv.«fb_htab_has» →
    type_of% Wave8GuestInv.«fb_htab_item» →
    type_of% Wave8GuestInv.«fb_udiv» →
    type_of% Wave8GuestInv.«fb_validate_block_access_list_gas_limit») :=
  fb_validate_block_access_list_gas_limit (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_encode_header (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_rlp_encode_bytes» →
    type_of% Wave8GuestInv.«fb_rlp_encode_list_header» →
    type_of% Wave8GuestInv.«fb_rlp_encode_word» →
    type_of% Wave8GuestInv.«fb_rlp_list_header_len» →
    type_of% Wave8GuestInv.«fb_rlp_put_u256» →
    type_of% Wave8GuestInv.«fb_encode_header») := rfl

theorem certified_fb_encode_header : (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_rlp_encode_bytes» →
    type_of% Wave8GuestInv.«fb_rlp_encode_list_header» →
    type_of% Wave8GuestInv.«fb_rlp_encode_word» →
    type_of% Wave8GuestInv.«fb_rlp_list_header_len» →
    type_of% Wave8GuestInv.«fb_rlp_put_u256» →
    type_of% Wave8GuestInv.«fb_encode_header») :=
  fb_encode_header (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_header_hash (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_encode_header» →
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_header_hash») := rfl

theorem certified_fb_header_hash : (type_of% Wave8GuestInv.«fb_encode_header» →
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_header_hash») :=
  fb_header_hash (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_is_valid_versioned_hashes (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_decode_transaction» →
    type_of% Wave8GuestInv.«fb_memeq» →
    type_of% Wave8GuestInv.«fb_tx_is_blob» →
    type_of% Wave8GuestInv.«fb_is_valid_versioned_hashes») := rfl

theorem certified_fb_is_valid_versioned_hashes : (type_of% Wave8GuestInv.«fb_decode_transaction» →
    type_of% Wave8GuestInv.«fb_memeq» →
    type_of% Wave8GuestInv.«fb_tx_is_blob» →
    type_of% Wave8GuestInv.«fb_is_valid_versioned_hashes») :=
  fb_is_valid_versioned_hashes (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_nodedb_build (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_htab_new» →
    type_of% Wave8GuestInv.«fb_htab_set» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_nodedb_build») := rfl

theorem certified_fb_nodedb_build : (type_of% Wave8GuestInv.«fb_htab_new» →
    type_of% Wave8GuestInv.«fb_htab_set» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_nodedb_build») :=
  fb_nodedb_build (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_block_rlp_length (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_encode_header» →
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_rlp_bytes_encoded_len» →
    type_of% Wave8GuestInv.«fb_rlp_list_header_len» →
    type_of% Wave8GuestInv.«fb_withdrawal_rlp_len» →
    type_of% Wave8GuestInv.«fb_block_rlp_length») := rfl

theorem certified_fb_block_rlp_length : (type_of% Wave8GuestInv.«fb_encode_header» →
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_rlp_bytes_encoded_len» →
    type_of% Wave8GuestInv.«fb_rlp_list_header_len» →
    type_of% Wave8GuestInv.«fb_withdrawal_rlp_len» →
    type_of% Wave8GuestInv.«fb_block_rlp_length») :=
  fb_block_rlp_length (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_encode_execution_requests (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_encode_execution_requests») := rfl

theorem certified_fb_encode_execution_requests : (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_encode_execution_requests») :=
  fb_encode_execution_requests (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_calculate_base_fee_per_gas (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_check_gas_limit» →
    type_of% Wave8GuestInv.«fb_u256_add» →
    type_of% Wave8GuestInv.«fb_u256_div» →
    type_of% Wave8GuestInv.«fb_u256_from_word» →
    type_of% Wave8GuestInv.«fb_u256_is_zero» →
    type_of% Wave8GuestInv.«fb_u256_mul» →
    type_of% Wave8GuestInv.«fb_u256_sub» →
    type_of% Wave8GuestInv.«fb_calculate_base_fee_per_gas») := rfl

theorem certified_fb_calculate_base_fee_per_gas : (type_of% Wave8GuestInv.«fb_check_gas_limit» →
    type_of% Wave8GuestInv.«fb_u256_add» →
    type_of% Wave8GuestInv.«fb_u256_div» →
    type_of% Wave8GuestInv.«fb_u256_from_word» →
    type_of% Wave8GuestInv.«fb_u256_is_zero» →
    type_of% Wave8GuestInv.«fb_u256_mul» →
    type_of% Wave8GuestInv.«fb_u256_sub» →
    type_of% Wave8GuestInv.«fb_calculate_base_fee_per_gas») :=
  fb_calculate_base_fee_per_gas (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_calculate_excess_blob_gas (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_calculate_blob_gas_price» →
    type_of% Wave8GuestInv.«fb_u256_from_word» →
    type_of% Wave8GuestInv.«fb_u256_gt» →
    type_of% Wave8GuestInv.«fb_u256_mul» →
    type_of% Wave8GuestInv.«fb_udiv» →
    type_of% Wave8GuestInv.«fb_calculate_excess_blob_gas») := rfl

theorem certified_fb_calculate_excess_blob_gas : (type_of% Wave8GuestInv.«fb_calculate_blob_gas_price» →
    type_of% Wave8GuestInv.«fb_u256_from_word» →
    type_of% Wave8GuestInv.«fb_u256_gt» →
    type_of% Wave8GuestInv.«fb_u256_mul» →
    type_of% Wave8GuestInv.«fb_udiv» →
    type_of% Wave8GuestInv.«fb_calculate_excess_blob_gas») :=
  fb_calculate_excess_blob_gas (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_validate_header (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_calculate_base_fee_per_gas» →
    type_of% Wave8GuestInv.«fb_calculate_excess_blob_gas» →
    type_of% Wave8GuestInv.«fb_header_hash» →
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_memeq» →
    type_of% Wave8GuestInv.«fb_u256_eq» →
    type_of% Wave8GuestInv.«fb_u256_is_zero» →
    type_of% Wave8GuestInv.«fb_validate_header») := rfl

theorem certified_fb_validate_header : (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_calculate_base_fee_per_gas» →
    type_of% Wave8GuestInv.«fb_calculate_excess_blob_gas» →
    type_of% Wave8GuestInv.«fb_header_hash» →
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_memeq» →
    type_of% Wave8GuestInv.«fb_u256_eq» →
    type_of% Wave8GuestInv.«fb_u256_is_zero» →
    type_of% Wave8GuestInv.«fb_validate_header») :=
  fb_validate_header (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_validate_headers (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_decode_header» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_memeq» →
    type_of% Wave8GuestInv.«fb_validate_headers») := rfl

theorem certified_fb_validate_headers : (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_decode_header» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_memeq» →
    type_of% Wave8GuestInv.«fb_validate_headers») :=
  fb_validate_headers (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_ceil_log2 (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_ceil_log2») := rfl

theorem certified_fb_ceil_log2 : (type_of% Wave8GuestInv.«fb_ceil_log2») :=
  fb_ceil_log2 (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_ssz_split_var_list (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_split_var_list») := rfl

theorem certified_fb_ssz_split_var_list : (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_split_var_list») :=
  fb_ssz_split_var_list (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_decode_bytes_list (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_split_var_list» →
    type_of% Wave8GuestInv.«fb_decode_bytes_list») := rfl

theorem certified_fb_decode_bytes_list : (type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_split_var_list» →
    type_of% Wave8GuestInv.«fb_decode_bytes_list») :=
  fb_decode_bytes_list (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_ssz_check_offsets (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_check_offsets») := rfl

theorem certified_fb_ssz_check_offsets : (type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_check_offsets») :=
  fb_ssz_check_offsets (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_ssz_fixed_list_count (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_udivmod» →
    type_of% Wave8GuestInv.«fb_ssz_fixed_list_count») := rfl

theorem certified_fb_ssz_fixed_list_count : (type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_udivmod» →
    type_of% Wave8GuestInv.«fb_ssz_fixed_list_count») :=
  fb_ssz_fixed_list_count (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_decode_payload (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_ssz_check_offsets» →
    type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_fixed_list_count» →
    type_of% Wave8GuestInv.«fb_ssz_split_var_list» →
    type_of% Wave8GuestInv.«fb_decode_payload») := rfl

theorem certified_fb_decode_payload : (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_ssz_check_offsets» →
    type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_fixed_list_count» →
    type_of% Wave8GuestInv.«fb_ssz_split_var_list» →
    type_of% Wave8GuestInv.«fb_decode_payload») :=
  fb_decode_payload (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_decode_requests (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_ssz_check_offsets» →
    type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_fixed_list_count» →
    type_of% Wave8GuestInv.«fb_decode_requests») := rfl

theorem certified_fb_decode_requests : (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_ssz_check_offsets» →
    type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_fixed_list_count» →
    type_of% Wave8GuestInv.«fb_decode_requests») :=
  fb_decode_requests (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_decode_stateless_input (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_decode_bytes_list» →
    type_of% Wave8GuestInv.«fb_decode_payload» →
    type_of% Wave8GuestInv.«fb_decode_requests» →
    type_of% Wave8GuestInv.«fb_ssz_check_offsets» →
    type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_fixed_list_count» →
    type_of% Wave8GuestInv.«fb_decode_stateless_input») := rfl

theorem certified_fb_decode_stateless_input : (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_decode_bytes_list» →
    type_of% Wave8GuestInv.«fb_decode_payload» →
    type_of% Wave8GuestInv.«fb_decode_requests» →
    type_of% Wave8GuestInv.«fb_ssz_check_offsets» →
    type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_ssz_fixed_list_count» →
    type_of% Wave8GuestInv.«fb_decode_stateless_input») :=
  fb_decode_stateless_input (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_input_blob (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_trap_with» →
    type_of% Wave8GuestInv.«fb_input_blob») := rfl

theorem certified_fb_input_blob : (type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_trap_with» →
    type_of% Wave8GuestInv.«fb_input_blob») :=
  fb_input_blob (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_precheck_host_ssz_header (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_host_input_byte» →
    type_of% Wave8GuestInv.«fb_host_input_le32» →
    type_of% Wave8GuestInv.«fb_ssz_check_offsets» →
    type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_precheck_host_ssz_header») := rfl

theorem certified_fb_precheck_host_ssz_header : (type_of% Wave8GuestInv.«fb_host_input_byte» →
    type_of% Wave8GuestInv.«fb_host_input_le32» →
    type_of% Wave8GuestInv.«fb_ssz_check_offsets» →
    type_of% Wave8GuestInv.«fb_ssz_fail» →
    type_of% Wave8GuestInv.«fb_precheck_host_ssz_header») :=
  fb_precheck_host_ssz_header (GuestInv := @Wave8GuestInv.GuestInv)


example : type_of% (fb_decode_host_input (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_decode_stateless_input» →
    type_of% Wave8GuestInv.«fb_input_blob» →
    type_of% Wave8GuestInv.«fb_precheck_host_ssz_header» →
    type_of% Wave8GuestInv.«fb_decode_host_input») := rfl

theorem certified_fb_decode_host_input : (type_of% Wave8GuestInv.«fb_decode_stateless_input» →
    type_of% Wave8GuestInv.«fb_input_blob» →
    type_of% Wave8GuestInv.«fb_precheck_host_ssz_header» →
    type_of% Wave8GuestInv.«fb_decode_host_input») :=
  fb_decode_host_input (GuestInv := @Wave8GuestInv.GuestInv)


end InitECandidate.Solver.Wave8Leaves.S13
