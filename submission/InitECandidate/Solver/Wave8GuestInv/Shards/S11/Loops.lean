import InitECandidate.Solver.Wave8GuestInv.Shards.S11.Core

/-! Counted-loop leaves (5 leaves) for Wave 8 shard s11 (`wave8/leaves-s11`).
Imports only the light cone via `campaign.leaves.s11.Core`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S11

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem fb_logs_encoded_bound_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P) :
    TerminatingFunBoundedOn P (ofString "logs_encoded_bound")
      ((2 ^ 64 + 1) * (0 + 1)) := by
  fb_prove hP 834 Guest.Software.guestFn_logs_encoded_bound

theorem fb_auth_list_payload_len_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_auth_payload_len K_rlp_list_header_len : Nat}
    (h_auth_payload_len : TerminatingFunBoundedOn P (ofString "auth_payload_len") K_auth_payload_len)
    (h_rlp_list_header_len : TerminatingFunBoundedOn P (ofString "rlp_list_header_len") K_rlp_list_header_len) :
    TerminatingFunBoundedOn P (ofString "auth_list_payload_len")
      ((2 ^ 64 + 1) * ((K_auth_payload_len + 1) + (K_rlp_list_header_len + 1) + 1)) := by
  fb_prove hP 325 Guest.Software.guestFn_auth_list_payload_len

theorem fb_encode_logs_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_rlp_encode_bytes K_rlp_finish_list : Nat}
    (h_rlp_encode_bytes : TerminatingFunBoundedOn P (ofString "rlp_encode_bytes") K_rlp_encode_bytes)
    (h_rlp_finish_list : TerminatingFunBoundedOn P (ofString "rlp_finish_list") K_rlp_finish_list) :
    TerminatingFunBoundedOn P (ofString "encode_logs")
      ((2 ^ 64 + 1) * ((K_rlp_encode_bytes + 1) + (2 ^ 64 + 1) * ((K_rlp_encode_bytes + 1) + 1) + (K_rlp_finish_list + 1) + (K_rlp_encode_bytes + 1) + (K_rlp_finish_list + 1) + 1) + (K_rlp_finish_list + 1)) := by
  fb_prove hP 835 Guest.Software.guestFn_encode_logs

theorem fb_tx_put_access_list_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_access_list_payload_len K_rlp_encode_list_header K_rlp_list_header_len K_rlp_encode_bytes : Nat}
    (h_access_list_payload_len : TerminatingFunBoundedOn P (ofString "access_list_payload_len") K_access_list_payload_len)
    (h_rlp_encode_list_header : TerminatingFunBoundedOn P (ofString "rlp_encode_list_header") K_rlp_encode_list_header)
    (h_rlp_list_header_len : TerminatingFunBoundedOn P (ofString "rlp_list_header_len") K_rlp_list_header_len)
    (h_rlp_encode_bytes : TerminatingFunBoundedOn P (ofString "rlp_encode_bytes") K_rlp_encode_bytes) :
    TerminatingFunBoundedOn P (ofString "tx_put_access_list")
      ((K_access_list_payload_len + 1) + (K_rlp_encode_list_header + 1) + (2 ^ 64 + 1) * ((K_rlp_list_header_len + 1) + (K_rlp_encode_list_header + 1) + (K_rlp_encode_bytes + 1) + (K_rlp_encode_list_header + 1) + (2 ^ 64 + 1) * ((K_rlp_encode_bytes + 1) + 1) + 1)) := by
  fb_prove hP 322 Guest.Software.guestFn_tx_put_access_list

theorem fb_check_transaction_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_min K_calculate_total_blob_gas K_get_account K_u256_lt K_u256_sub K_u256_add K_fee_mul
     K_calculate_blob_gas_price K_u256_add_carry K_u256_fits_word K_get_code K_memeq K_is_valid_delegation : Nat}
    (h_min : TerminatingFunBoundedOn P (ofString "min") K_min)
    (h_calculate_total_blob_gas : TerminatingFunBoundedOn P (ofString "calculate_total_blob_gas") K_calculate_total_blob_gas)
    (h_get_account : TerminatingFunBoundedOn P (ofString "get_account") K_get_account)
    (h_u256_lt : TerminatingFunBoundedOn P (ofString "u256_lt") K_u256_lt)
    (h_u256_sub : TerminatingFunBoundedOn P (ofString "u256_sub") K_u256_sub)
    (h_u256_add : TerminatingFunBoundedOn P (ofString "u256_add") K_u256_add)
    (h_fee_mul : TerminatingFunBoundedOn P (ofString "fee_mul") K_fee_mul)
    (h_calculate_blob_gas_price : TerminatingFunBoundedOn P (ofString "calculate_blob_gas_price") K_calculate_blob_gas_price)
    (h_u256_add_carry : TerminatingFunBoundedOn P (ofString "u256_add_carry") K_u256_add_carry)
    (h_u256_fits_word : TerminatingFunBoundedOn P (ofString "u256_fits_word") K_u256_fits_word)
    (h_get_code : TerminatingFunBoundedOn P (ofString "get_code") K_get_code)
    (h_memeq : TerminatingFunBoundedOn P (ofString "memeq") K_memeq)
    (h_is_valid_delegation : TerminatingFunBoundedOn P (ofString "is_valid_delegation") K_is_valid_delegation) :
    TerminatingFunBoundedOn P (ofString "check_transaction")
      ((K_min + 1) + (K_calculate_total_blob_gas + 1) + (K_get_account + 1) + Nat.max ((K_u256_lt + 1)) ((K_u256_lt + 1) + (K_u256_lt + 1) + (K_u256_sub + 1) + (K_u256_lt + 1) + (K_u256_add + 1)) + (K_fee_mul + 1) + Nat.max ((2 ^ 64 + 1) * (0 + 1) + (K_calculate_blob_gas_price + 1) + (K_u256_lt + 1) + (K_fee_mul + 1) + (K_u256_add_carry + 1)) (0) + (K_u256_fits_word + 1) + (K_u256_add_carry + 1) + (K_u256_lt + 1) + (K_get_code + 1) + (K_memeq + 1) + Nat.max ((K_is_valid_delegation + 1)) (0)) := by
  fb_prove hP 872 Guest.Software.guestFn_check_transaction

end InitECandidate.Solver.Wave8Leaves.S11
