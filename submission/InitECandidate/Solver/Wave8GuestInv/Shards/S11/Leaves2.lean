import InitECandidate.Solver.Wave8GuestInv.Shards.S11.Core

/-! Loop-free leaves batch 2 (9 leaves) for Wave 8 shard s11 (`wave8/leaves-s11`).
Imports only the light cone via `campaign.leaves.s11.Core`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S11

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem fb_requests_append_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_alloc K_memcpy : Nat}
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_memcpy : TerminatingFunBoundedOn P (ofString "memcpy") K_memcpy) :
    TerminatingFunBoundedOn P (ofString "requests_append")
      ((K_alloc + 1) + (K_memcpy + 1)) := by
  fb_prove hP 876 Guest.Software.guestFn_requests_append

theorem fb_calculate_total_blob_gas_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (_hP : MetadataInv P) :
    TerminatingFunBoundedOn P (ofString "calculate_total_blob_gas") 0 := by
  fb_prove _hP 317 Guest.Software.guestFn_calculate_total_blob_gas

theorem fb_fee_mul_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_u256_mul_full : Nat}
    (h_u256_mul_full : TerminatingFunBoundedOn P (ofString "u256_mul_full") K_u256_mul_full) :
    TerminatingFunBoundedOn P (ofString "fee_mul")
      ((K_u256_mul_full + 1)) := by
  fb_prove hP 867 Guest.Software.guestFn_fee_mul

theorem fb_clear_account_preserving_balance_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_destroy_storage K_get_account K_acct_copy K_modify_state_commit : Nat}
    (h_destroy_storage : TerminatingFunBoundedOn P (ofString "destroy_storage") K_destroy_storage)
    (h_get_account : TerminatingFunBoundedOn P (ofString "get_account") K_get_account)
    (h_acct_copy : TerminatingFunBoundedOn P (ofString "acct_copy") K_acct_copy)
    (h_modify_state_commit : TerminatingFunBoundedOn P (ofString "modify_state_commit") K_modify_state_commit) :
    TerminatingFunBoundedOn P (ofString "clear_account_preserving_balance")
      ((K_destroy_storage + 1) + (K_get_account + 1) + (K_acct_copy + 1) + (K_modify_state_commit + 1)) := by
  fb_prove hP 392 Guest.Software.guestFn_clear_account_preserving_balance

theorem fb_create_ether_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_get_account K_acct_copy K_u256_add K_modify_state_commit : Nat}
    (h_get_account : TerminatingFunBoundedOn P (ofString "get_account") K_get_account)
    (h_acct_copy : TerminatingFunBoundedOn P (ofString "acct_copy") K_acct_copy)
    (h_u256_add : TerminatingFunBoundedOn P (ofString "u256_add") K_u256_add)
    (h_modify_state_commit : TerminatingFunBoundedOn P (ofString "modify_state_commit") K_modify_state_commit) :
    TerminatingFunBoundedOn P (ofString "create_ether")
      ((K_get_account + 1) + (K_acct_copy + 1) + (K_u256_add + 1) + (K_modify_state_commit + 1)) := by
  fb_prove hP 396 Guest.Software.guestFn_create_ether

theorem fb_encode_receipt_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_logs_encoded_bound K_alloc K_rlp_encode_word K_logs_bloom K_rlp_encode_bytes K_encode_logs K_rlp_finish_list : Nat}
    (h_logs_encoded_bound : TerminatingFunBoundedOn P (ofString "logs_encoded_bound") K_logs_encoded_bound)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_rlp_encode_word : TerminatingFunBoundedOn P (ofString "rlp_encode_word") K_rlp_encode_word)
    (h_logs_bloom : TerminatingFunBoundedOn P (ofString "logs_bloom") K_logs_bloom)
    (h_rlp_encode_bytes : TerminatingFunBoundedOn P (ofString "rlp_encode_bytes") K_rlp_encode_bytes)
    (h_encode_logs : TerminatingFunBoundedOn P (ofString "encode_logs") K_encode_logs)
    (h_rlp_finish_list : TerminatingFunBoundedOn P (ofString "rlp_finish_list") K_rlp_finish_list) :
    TerminatingFunBoundedOn P (ofString "encode_receipt")
      ((K_logs_encoded_bound + 1) + (K_alloc + 1) + (K_rlp_encode_word + 1) + (K_alloc + 1) + (K_logs_bloom + 1) + (K_rlp_encode_bytes + 1) + (K_encode_logs + 1) + (K_rlp_finish_list + 1)) := by
  fb_prove hP 836 Guest.Software.guestFn_encode_receipt

theorem fb_tx_u256_encoded_len_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_u256_byte_length : Nat}
    (h_u256_byte_length : TerminatingFunBoundedOn P (ofString "u256_byte_length") K_u256_byte_length) :
    TerminatingFunBoundedOn P (ofString "tx_u256_encoded_len")
      ((K_u256_byte_length + 1)) := by
  fb_prove hP 319 Guest.Software.guestFn_tx_u256_encoded_len

theorem fb_auth_payload_len_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_tx_u256_encoded_len K_rlp_word_encoded_len : Nat}
    (h_tx_u256_encoded_len : TerminatingFunBoundedOn P (ofString "tx_u256_encoded_len") K_tx_u256_encoded_len)
    (h_rlp_word_encoded_len : TerminatingFunBoundedOn P (ofString "rlp_word_encoded_len") K_rlp_word_encoded_len) :
    TerminatingFunBoundedOn P (ofString "auth_payload_len")
      ((K_tx_u256_encoded_len + 1) + (K_rlp_word_encoded_len + 1) + (K_rlp_word_encoded_len + 1) + (K_tx_u256_encoded_len + 1) + (K_tx_u256_encoded_len + 1)) := by
  fb_prove hP 324 Guest.Software.guestFn_auth_payload_len

theorem fb_tx_encode_bound_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_access_list_payload_len K_auth_list_payload_len : Nat}
    (h_access_list_payload_len : TerminatingFunBoundedOn P (ofString "access_list_payload_len") K_access_list_payload_len)
    (h_auth_list_payload_len : TerminatingFunBoundedOn P (ofString "auth_list_payload_len") K_auth_list_payload_len) :
    TerminatingFunBoundedOn P (ofString "tx_encode_bound")
      ((K_access_list_payload_len + 1) + (K_auth_list_payload_len + 1)) := by
  fb_prove hP 327 Guest.Software.guestFn_tx_encode_bound

end InitECandidate.Solver.Wave8Leaves.S11
