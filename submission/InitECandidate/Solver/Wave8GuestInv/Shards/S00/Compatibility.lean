import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.NodeInvalidateLight
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.node_new_ext
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.node_new_hashed
import InitECandidate.Solver.Wave8GuestInv.Shards.S00._create_branch_from_two_leaves
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.nodedb_lookup
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.is_warm_address
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.access_gas_cost
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.record_pre_state_read
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.trie_lookup
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.node_ref_len
import InitECandidate.Solver.Wave8GuestInv.Shards.S00._resolve_step
import InitECandidate.Solver.Wave8GuestInv.Shards.S00._delete_ext_finish
import InitECandidate.Solver.Wave8GuestInv.Shards.S00._insert_into_leaf
import InitECandidate.Solver.Wave8GuestInv.Shards.S00._split_extension
import InitECandidate.Solver.Wave8GuestInv.Shards.S00._node_rlp_begin
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.node_hash_cached
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.node_write_ref
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.common_prefix_length
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.nibble_list_to_compact
import InitECandidate.Solver.Wave8GuestInv.Shards.S00._collapse_branch
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.access_list_payload_len
import InitECandidate.Solver.Wave8GuestInv.Shards.S00._node_rlp_finish
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.trie_walk

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00Verified

open Flapjack.Basis.Pure.MlString

theorem guestInv_eq : (@S00Spec.GuestInv) = (@Wave8GuestInv.GuestInv) := by
  funext F s
  apply propext
  constructor <;> intro h <;> exact ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr⟩

theorem bound_iff (name : Flapjack.Pancake.PanLang.MlS) (K : Nat) :
    S00Spec.TerminatingFunBoundedOn S00Spec.GuestInv name K ↔
    Wave8GuestInv.TerminatingFunBoundedOn Wave8GuestInv.GuestInv name K := by
  unfold S00Spec.TerminatingFunBoundedOn Wave8GuestInv.TerminatingFunBoundedOn
  rw [guestInv_eq]

theorem fb_node_invalidate : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_invalidate)) := by
  exact S00Light.fb_node_invalidate Wave8GuestInv.GuestInv

example : (type_of% @fb_node_invalidate) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_invalidate)) := rfl

theorem fb_node_new_ext : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_ext)) := by
  intro h0
  exact (bound_iff _ _).mp (S00.fb_node_new_ext ((bound_iff _ _).mpr h0))

example : (type_of% @fb_node_new_ext) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_ext)) := rfl

theorem fb_node_new_hashed : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_hashed)) := by
  intro h0
  exact (bound_iff _ _).mp (S00.fb_node_new_hashed ((bound_iff _ _).mpr h0))

example : (type_of% @fb_node_new_hashed) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_hashed)) := rfl

theorem fb__create_branch_from_two_leaves : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_branch) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_leaf) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__create_branch_from_two_leaves)) := by
  intro h0 h1
  exact (bound_iff _ _).mp (S00.fb__create_branch_from_two_leaves ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1))

example : (type_of% @fb__create_branch_from_two_leaves) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_branch) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_leaf) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__create_branch_from_two_leaves)) := rfl

theorem fb_nodedb_lookup : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_get) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nodedb_lookup)) := by
  intro h0
  exact (bound_iff _ _).mp (S00.fb_nodedb_lookup ((bound_iff _ _).mpr h0))

example : (type_of% @fb_nodedb_lookup) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_get) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nodedb_lookup)) := rfl

theorem fb_is_warm_address : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_has) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_is_warm_address)) := by
  intro h0
  exact (bound_iff _ _).mp (S00.fb_is_warm_address ((bound_iff _ _).mpr h0))

example : (type_of% @fb_is_warm_address) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_has) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_is_warm_address)) := rfl

theorem fb_access_gas_cost : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_is_warm_address) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_access_gas_cost)) := by
  intro h0
  exact (bound_iff _ _).mp (S00.fb_access_gas_cost ((bound_iff _ _).mpr h0))

example : (type_of% @fb_access_gas_cost) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_is_warm_address) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_access_gas_cost)) := rfl

theorem fb_record_pre_state_read : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_set) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_record_pre_state_read)) := by
  intro h0
  exact (bound_iff _ _).mp (S00.fb_record_pre_state_read ((bound_iff _ _).mpr h0))

example : (type_of% @fb_record_pre_state_read) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_set) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_record_pre_state_read)) := rfl

theorem fb_trie_lookup : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_key_to_nibbles) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_trie_walk) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_trie_lookup)) := by
  intro h0 h1
  exact (bound_iff _ _).mp (S00.fb_trie_lookup ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1))

example : (type_of% @fb_trie_lookup) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_key_to_nibbles) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_trie_walk) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_trie_lookup)) := rfl

theorem fb_node_ref_len : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_ref_len)) := by
  intro h0
  exact (bound_iff _ _).mp (S00.fb_node_ref_len ((bound_iff _ _).mpr h0))

example : (type_of% @fb_node_ref_len) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_ref_len)) := rfl

theorem fb__resolve_step : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_hashed) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nodedb_lookup) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_item) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__resolve_step)) := by
  intro h0 h1 h2 h3
  exact (bound_iff _ _).mp (S00.fb__resolve_step ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1) ((bound_iff _ _).mpr h2) ((bound_iff _ _).mpr h3))

example : (type_of% @fb__resolve_step) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_hashed) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nodedb_lookup) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_item) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__resolve_step)) := rfl

theorem fb__delete_ext_finish : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nibbles_concat) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_ext) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_leaf) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__delete_ext_finish)) := by
  intro h0 h1 h2 h3
  exact (bound_iff _ _).mp (S00.fb__delete_ext_finish ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1) ((bound_iff _ _).mpr h2) ((bound_iff _ _).mpr h3))

example : (type_of% @fb__delete_ext_finish) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nibbles_concat) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_ext) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_leaf) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__delete_ext_finish)) := rfl

theorem fb__insert_into_leaf : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb__create_branch_from_two_leaves) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_common_prefix_length) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memeq) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_ext) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__insert_into_leaf)) := by
  intro h0 h1 h2 h3
  exact (bound_iff _ _).mp (S00.fb__insert_into_leaf ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1) ((bound_iff _ _).mpr h2) ((bound_iff _ _).mpr h3))

example : (type_of% @fb__insert_into_leaf) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb__create_branch_from_two_leaves) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_common_prefix_length) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memeq) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_ext) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__insert_into_leaf)) := rfl

theorem fb__split_extension : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_branch) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_ext) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_leaf) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__split_extension)) := by
  intro h0 h1 h2 h3
  exact (bound_iff _ _).mp (S00.fb__split_extension ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1) ((bound_iff _ _).mpr h2) ((bound_iff _ _).mpr h3))

example : (type_of% @fb__split_extension) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_branch) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_ext) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_leaf) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__split_extension)) := rfl

theorem fb__node_rlp_begin : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nibble_list_to_compact) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_bytes_encoded_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_value_encoded_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__node_rlp_begin)) := by
  intro h0 h1 h2 h3
  exact (bound_iff _ _).mp (S00.fb__node_rlp_begin ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1) ((bound_iff _ _).mpr h2) ((bound_iff _ _).mpr h3))

example : (type_of% @fb__node_rlp_begin) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nibble_list_to_compact) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_bytes_encoded_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_value_encoded_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__node_rlp_begin)) := rfl

theorem fb_node_hash_cached : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_keccak256) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_hash_cached)) := by
  intro h0 h1 h2
  exact (bound_iff _ _).mp (S00.fb_node_hash_cached ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1) ((bound_iff _ _).mpr h2))

example : (type_of% @fb_node_hash_cached) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_keccak256) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_hash_cached)) := rfl

theorem fb_node_write_ref : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_hash_cached) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_write_ref)) := by
  intro h0 h1 h2
  exact (bound_iff _ _).mp (S00.fb_node_write_ref ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1) ((bound_iff _ _).mpr h2))

example : (type_of% @fb_node_write_ref) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_hash_cached) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_write_ref)) := rfl

theorem fb_common_prefix_length : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_min) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_common_prefix_length)) := by
  intro h0
  exact (bound_iff _ _).mp (S00.fb_common_prefix_length ((bound_iff _ _).mpr h0))

example : (type_of% @fb_common_prefix_length) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_min) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_common_prefix_length)) := rfl

theorem fb_nibble_list_to_compact : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nibble_list_to_compact)) := by
  exact (bound_iff _ _).mp (S00.fb_nibble_list_to_compact )

example : (type_of% @fb_nibble_list_to_compact) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nibble_list_to_compact)) := rfl

theorem fb__collapse_branch : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nibbles_concat) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_ext) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_leaf) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__collapse_branch)) := by
  intro h0 h1 h2 h3 h4
  exact (bound_iff _ _).mp (S00.fb__collapse_branch ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1) ((bound_iff _ _).mpr h2) ((bound_iff _ _).mpr h3) ((bound_iff _ _).mpr h4))

example : (type_of% @fb__collapse_branch) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_nibbles_concat) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_ext) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_new_leaf) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__collapse_branch)) := rfl

theorem fb_access_list_payload_len : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_list_header_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_access_list_payload_len)) := by
  intro h0
  exact (bound_iff _ _).mp (S00.fb_access_list_payload_len ((bound_iff _ _).mpr h0))

example : (type_of% @fb_access_list_payload_len) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_list_header_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_access_list_payload_len)) := rfl

theorem fb__node_rlp_finish : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_ref_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_write_ref) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_bytes) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_list_header) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_list_header_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_value_encoded_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__node_rlp_finish)) := by
  intro h0 h1 h2 h3 h4 h5 h6
  exact (bound_iff _ _).mp (S00.fb__node_rlp_finish ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1) ((bound_iff _ _).mpr h2) ((bound_iff _ _).mpr h3) ((bound_iff _ _).mpr h4) ((bound_iff _ _).mpr h5) ((bound_iff _ _).mpr h6))

example : (type_of% @fb__node_rlp_finish) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_ref_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_node_write_ref) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_bytes) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_list_header) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_list_header_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_rlp_value_encoded_len) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb__node_rlp_finish)) := rfl

theorem fb_trie_walk : ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memeq) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_trie_walk)) := by
  intro h0 h1
  exact (bound_iff _ _).mp (S00.fb_trie_walk ((bound_iff _ _).mpr h0) ((bound_iff _ _).mpr h1))

example : (type_of% @fb_trie_walk) =
    ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memeq) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_mpt_fail) →
     (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_trie_walk)) := rfl

end InitECandidate.Solver.Wave8Leaves.S00Verified
