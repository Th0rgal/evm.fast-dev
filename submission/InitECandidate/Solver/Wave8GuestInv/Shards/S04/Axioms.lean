import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.mark_account_created
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.compute_jumpdests
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.is_valid_delegation
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.get_delegated_code_address
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.get_pre_state_account
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.is_account_alive
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.warm_address
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.prepare_dispatch
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.recover_authority
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.validate_authorization_checks
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.set_delegation
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.depth0_prepare
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.frame_mem_alloc
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.frame_mem_mark
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.frame_new
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.frame_open
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.refill_frame_state_gas
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.frame_exception
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.log_append
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.emit_transfer_log
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.move_ether
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.precompile_index
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.buffer_read
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.pre_alt_bn128_add

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Leaves.S04.Verified
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded

private theorem toLight {name : MlS} {K : Nat}
    (h : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv name K) :
    Light.TerminatingFunBoundedOn Light.GuestInv name K := by
  obtain ⟨ps, body, ret, hc, hb⟩ := h
  refine ⟨ps, body, ret, hc, ?_⟩
  intro F s hs hi
  exact hb s hs ⟨hi.code, hi.memaddrs, hi.shMemaddrs, hi.baseAddr⟩

private theorem fromLight {name : MlS} {K : Nat}
    (h : Light.TerminatingFunBoundedOn Light.GuestInv name K) :
    InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv name K := by
  obtain ⟨ps, body, ret, hc, hb⟩ := h
  refine ⟨ps, body, ret, hc, ?_⟩
  intro F s hs hi
  exact hb s hs ⟨hi.code, hi.memaddrs, hi.shMemaddrs, hi.baseAddr⟩

theorem fb_compute_jumpdests
    (h_memzero : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memzero))
    (h_scratch_alloc : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_scratch_alloc))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_compute_jumpdests) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_compute_jumpdests
    (toLight h_memzero) (toLight h_scratch_alloc))

example : (type_of% @fb_compute_jumpdests) =
    ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_memzero) →
     (type_of% InitECandidate.Solver.Wave8GuestInv.fb_scratch_alloc) →
     (type_of% InitECandidate.Solver.Wave8GuestInv.fb_compute_jumpdests)) := rfl

theorem fb_mark_account_created
    (h_htab_set : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_set))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_mark_account_created) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_mark_account_created (toLight h_htab_set))

example : (type_of% @fb_mark_account_created) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_set) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_mark_account_created)) := rfl

theorem fb_is_valid_delegation
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_valid_delegation) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_is_valid_delegation)

example : (type_of% @fb_is_valid_delegation) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_valid_delegation)) := rfl

theorem fb_get_delegated_code_address
    (h_is_valid_delegation : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_valid_delegation))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_delegated_code_address) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_get_delegated_code_address (toLight h_is_valid_delegation))

example : (type_of% @fb_get_delegated_code_address) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_valid_delegation) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_delegated_code_address)) := rfl

theorem fb_get_pre_state_account
    (h_acct_empty : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_acct_empty))
    (h_get_pre_state_account_optional : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_pre_state_account_optional))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_pre_state_account) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_get_pre_state_account (toLight h_acct_empty) (toLight h_get_pre_state_account_optional))

example : (type_of% @fb_get_pre_state_account) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_acct_empty) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_pre_state_account_optional) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_pre_state_account)) := rfl

theorem fb_is_account_alive
    (h_acct_is_empty : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_acct_is_empty))
    (h_get_account_optional : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_account_optional))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_account_alive) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_is_account_alive (toLight h_acct_is_empty) (toLight h_get_account_optional))

example : (type_of% @fb_is_account_alive) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_acct_is_empty) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_account_optional) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_account_alive)) := rfl

theorem fb_warm_address
    (h_htab_set : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_set))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_warm_address) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_warm_address (toLight h_htab_set))

example : (type_of% @fb_warm_address) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_set) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_warm_address)) := rfl

theorem fb_prepare_dispatch
    (h_acct_is_empty : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_acct_is_empty))
    (h_alloc : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc))
    (h_charge_gas : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas))
    (h_charge_state_gas : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_state_gas))
    (h_compute_jumpdests : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_compute_jumpdests))
    (h_ext_code_of : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_ext_code_of))
    (h_get_delegated_code_address : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_delegated_code_address))
    (h_get_pre_state_account : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_pre_state_account))
    (h_is_account_alive : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_account_alive))
    (h_is_warm_address : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_warm_address))
    (h_memcpy : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memcpy))
    (h_u256_is_zero : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_is_zero))
    (h_warm_address : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_warm_address))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_prepare_dispatch) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_prepare_dispatch (toLight h_acct_is_empty) (toLight h_alloc) (toLight h_charge_gas) (toLight h_charge_state_gas) (toLight h_compute_jumpdests) (toLight h_ext_code_of) (toLight h_get_delegated_code_address) (toLight h_get_pre_state_account) (toLight h_is_account_alive) (toLight h_is_warm_address) (toLight h_memcpy) (toLight h_u256_is_zero) (toLight h_warm_address))

example : (type_of% @fb_prepare_dispatch) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_acct_is_empty) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_state_gas) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_compute_jumpdests) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_ext_code_of) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_delegated_code_address) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_pre_state_account) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_account_alive) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_warm_address) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_is_zero) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_warm_address) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_prepare_dispatch)) := rfl

theorem fb_recover_authority
    (h_alloc : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc))
    (h_heap_mark : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_heap_mark))
    (h_heap_release : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_heap_release))
    (h_keccak256 : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_keccak256))
    (h_memcpy : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memcpy))
    (h_rlp_encode_bytes : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_bytes))
    (h_rlp_encode_list_header : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_list_header))
    (h_rlp_encode_word : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_word))
    (h_rlp_list_header_len : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_rlp_list_header_len))
    (h_rlp_put_u256 : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_rlp_put_u256))
    (h_secp256k1_recover : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_secp256k1_recover))
    (h_u256_gt : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_gt))
    (h_u256_is_zero : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_is_zero))
    (h_u256_lt : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_lt))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_recover_authority) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_recover_authority (toLight h_alloc) (toLight h_heap_mark) (toLight h_heap_release) (toLight h_keccak256) (toLight h_memcpy) (toLight h_rlp_encode_bytes) (toLight h_rlp_encode_list_header) (toLight h_rlp_encode_word) (toLight h_rlp_list_header_len) (toLight h_rlp_put_u256) (toLight h_secp256k1_recover) (toLight h_u256_gt) (toLight h_u256_is_zero) (toLight h_u256_lt))

example : (type_of% @fb_recover_authority) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_heap_mark) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_heap_release) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_keccak256) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_bytes) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_list_header) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_rlp_encode_word) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_rlp_list_header_len) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_rlp_put_u256) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_secp256k1_recover) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_gt) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_is_zero) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_lt) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_recover_authority)) := rfl

theorem fb_validate_authorization_checks
    (h_get_account : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_account))
    (h_get_code : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_code))
    (h_is_valid_delegation : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_valid_delegation))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_validate_authorization_checks) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_validate_authorization_checks (toLight h_get_account) (toLight h_get_code) (toLight h_is_valid_delegation))

example : (type_of% @fb_validate_authorization_checks) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_account) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_code) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_valid_delegation) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_validate_authorization_checks)) := rfl

theorem fb_set_delegation
    (h_account_exists : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_account_exists))
    (h_alloc : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc))
    (h_charge_gas : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas))
    (h_charge_state_gas : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_state_gas))
    (h_get_code : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_code))
    (h_get_pre_state_account : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_pre_state_account))
    (h_htab_has : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_has))
    (h_htab_new : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_new))
    (h_htab_set : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_set))
    (h_increment_nonce : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_increment_nonce))
    (h_is_valid_delegation : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_valid_delegation))
    (h_memcpy : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memcpy))
    (h_memeq : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memeq))
    (h_recover_authority : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_recover_authority))
    (h_set_code : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_set_code))
    (h_u256_fits_word : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_fits_word))
    (h_u256_is_zero : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_is_zero))
    (h_validate_authorization_checks : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_validate_authorization_checks))
    (h_warm_address : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_warm_address))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_set_delegation) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_set_delegation (toLight h_account_exists) (toLight h_alloc) (toLight h_charge_gas) (toLight h_charge_state_gas) (toLight h_get_code) (toLight h_get_pre_state_account) (toLight h_htab_has) (toLight h_htab_new) (toLight h_htab_set) (toLight h_increment_nonce) (toLight h_is_valid_delegation) (toLight h_memcpy) (toLight h_memeq) (toLight h_recover_authority) (toLight h_set_code) (toLight h_u256_fits_word) (toLight h_u256_is_zero) (toLight h_validate_authorization_checks) (toLight h_warm_address))

example : (type_of% @fb_set_delegation) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_account_exists) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_state_gas) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_code) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_pre_state_account) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_has) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_new) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_set) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_increment_nonce) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_valid_delegation) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memeq) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_recover_authority) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_set_code) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_fits_word) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_is_zero) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_validate_authorization_checks) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_warm_address) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_set_delegation)) := rfl

theorem fb_depth0_prepare
    (h_frame_state_gas_used : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_state_gas_used))
    (h_prepare_dispatch : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_prepare_dispatch))
    (h_set_delegation : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_set_delegation))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_depth0_prepare) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_depth0_prepare (toLight h_frame_state_gas_used) (toLight h_prepare_dispatch) (toLight h_set_delegation))

example : (type_of% @fb_depth0_prepare) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_state_gas_used) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_prepare_dispatch) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_set_delegation) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_depth0_prepare)) := rfl

theorem fb_frame_mem_alloc
    (h_trap_with : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_trap_with))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_mem_alloc) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_frame_mem_alloc (toLight h_trap_with))

example : (type_of% @fb_frame_mem_alloc) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_trap_with) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_mem_alloc)) := rfl

theorem fb_frame_mem_mark
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_mem_mark) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_frame_mem_mark)

example : (type_of% @fb_frame_mem_mark) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_mem_mark)) := rfl

theorem fb_frame_new
    (h_compute_jumpdests : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_compute_jumpdests))
    (h_frame_mem_alloc : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_mem_alloc))
    (h_frame_mem_mark : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_mem_mark))
    (h_htab_count : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_count))
    (h_htab_new_scratch : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_new_scratch))
    (h_lst_new_scratch : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_lst_new_scratch))
    (h_memzero : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memzero))
    (h_scratch_alloc : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_scratch_alloc))
    (h_scratch_mark : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_scratch_mark))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_new) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_frame_new (toLight h_compute_jumpdests) (toLight h_frame_mem_alloc) (toLight h_frame_mem_mark) (toLight h_htab_count) (toLight h_htab_new_scratch) (toLight h_lst_new_scratch) (toLight h_memzero) (toLight h_scratch_alloc) (toLight h_scratch_mark))

example : (type_of% @fb_frame_new) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_compute_jumpdests) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_mem_alloc) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_mem_mark) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_count) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_htab_new_scratch) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_lst_new_scratch) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memzero) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_scratch_alloc) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_scratch_mark) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_new)) := rfl

theorem fb_frame_open
    (h_frame_new : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_new))
    (h_memzero : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memzero))
    (h_scratch_alloc : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_scratch_alloc))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_open) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_frame_open (toLight h_frame_new) (toLight h_memzero) (toLight h_scratch_alloc))

example : (type_of% @fb_frame_open) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_new) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memzero) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_scratch_alloc) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_open)) := rfl

theorem fb_refill_frame_state_gas
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_refill_frame_state_gas) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_refill_frame_state_gas)

example : (type_of% @fb_refill_frame_state_gas) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_refill_frame_state_gas)) := rfl

theorem fb_frame_exception
    (h_frame_halt : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_halt))
    (h_refill_frame_state_gas : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_refill_frame_state_gas))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_exception) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_frame_exception (toLight h_frame_halt) (toLight h_refill_frame_state_gas))

example : (type_of% @fb_frame_exception) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_halt) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_refill_frame_state_gas) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_frame_exception)) := rfl

theorem fb_log_append
    (h_lst_push : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_lst_push))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_log_append) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_log_append (toLight h_lst_push))

example : (type_of% @fb_log_append) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_lst_push) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_log_append)) := rfl

theorem fb_emit_transfer_log
    (h_alloc : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc))
    (h_log_append : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_log_append))
    (h_memcpy : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memcpy))
    (h_memzero : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memzero))
    (h_u256_is_zero : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_is_zero))
    (h_u256_to_be32 : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_to_be32))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_emit_transfer_log) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_emit_transfer_log (toLight h_alloc) (toLight h_log_append) (toLight h_memcpy) (toLight h_memzero) (toLight h_u256_is_zero) (toLight h_u256_to_be32))

example : (type_of% @fb_emit_transfer_log) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_log_append) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memzero) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_is_zero) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_to_be32) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_emit_transfer_log)) := rfl

theorem fb_move_ether
    (h_acct_copy : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_acct_copy))
    (h_get_account : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_account))
    (h_modify_state_commit : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_modify_state_commit))
    (h_u256_add : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_add))
    (h_u256_lt : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_lt))
    (h_u256_sub : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_sub))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_move_ether) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_move_ether (toLight h_acct_copy) (toLight h_get_account) (toLight h_modify_state_commit) (toLight h_u256_add) (toLight h_u256_lt) (toLight h_u256_sub))

example : (type_of% @fb_move_ether) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_acct_copy) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_get_account) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_modify_state_commit) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_add) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_lt) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_sub) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_move_ether)) := rfl

theorem fb_precompile_index
    (h_is_zero_bytes : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_zero_bytes))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_precompile_index) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_precompile_index (toLight h_is_zero_bytes))

example : (type_of% @fb_precompile_index) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_is_zero_bytes) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_precompile_index)) := rfl

theorem fb_buffer_read
    (h_memcpy : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memcpy))
    (h_memzero : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memzero))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_buffer_read) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_buffer_read (toLight h_memcpy) (toLight h_memzero))

example : (type_of% @fb_buffer_read) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_memzero) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_buffer_read)) := rfl

theorem fb_pre_alt_bn128_add
    (h_alloc : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc))
    (h_bn254_g1_add : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_bn254_g1_add))
    (h_buffer_read : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_buffer_read))
    (h_charge_gas : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas))
    (h_heap_mark : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_heap_mark))
    (h_heap_release : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_heap_release))
    : (type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_alt_bn128_add) := by
  exact fromLight (InitECandidate.Solver.Wave8Leaves.S04.fb_pre_alt_bn128_add (toLight h_alloc) (toLight h_bn254_g1_add) (toLight h_buffer_read) (toLight h_charge_gas) (toLight h_heap_mark) (toLight h_heap_release))

example : (type_of% @fb_pre_alt_bn128_add) = ((type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_bn254_g1_add) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_buffer_read) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_heap_mark) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_heap_release) → (type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_alt_bn128_add)) := rfl

end InitECandidate.Solver.Wave8Leaves.S04.Verified
