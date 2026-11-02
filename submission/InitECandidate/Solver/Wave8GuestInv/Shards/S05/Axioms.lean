import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S05.S05

namespace InitECandidate.Solver.Wave8GuestInv

example : type_of% (Campaign.Leaves.S05.fb_sat_word GuestInv) = type_of% fb_sat_word := rfl
example : type_of% (Campaign.Leaves.S05.fb_credit_state_gas_refund GuestInv) =
  type_of% fb_credit_state_gas_refund := rfl
example : type_of% (Campaign.Leaves.S05.fb_pre_identity GuestInv) =
  type_of% fb_pre_identity := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_alt_bn128_mul =
  ((type_of% fb_alloc) → (type_of% fb_bn254_g1_mul) → (type_of% fb_buffer_read) →
   (type_of% fb_charge_gas) → (type_of% fb_heap_mark) → (type_of% fb_heap_release) →
   (type_of% fb_pre_alt_bn128_mul)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_alt_bn128_pairing_check =
  ((type_of% fb_udivmod) → (type_of% fb_charge_gas) → (type_of% fb_bn254_pairing_check) →
   (type_of% fb_alloc) → (type_of% fb_memzero) → (type_of% fb_pre_alt_bn128_pairing_check)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_sha256 =
  ((type_of% fb_words_of) → (type_of% fb_charge_gas) → (type_of% fb_alloc) →
   (type_of% fb_sha256) → (type_of% fb_pre_sha256)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_ripemd160 =
  ((type_of% fb_words_of) → (type_of% fb_charge_gas) → (type_of% fb_alloc) →
   (type_of% fb_memzero) → (type_of% fb_ripemd160) → (type_of% fb_pre_ripemd160)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_ecrecover =
  ((type_of% fb_charge_gas) → (type_of% fb_alloc) → (type_of% fb_heap_mark) →
   (type_of% fb_buffer_read) → (type_of% fb_u256_from_be) → (type_of% fb_u256_fits_word) →
   (type_of% fb_heap_release) → (type_of% fb_secp256k1_ecrecover) →
   (type_of% fb_memzero) → (type_of% fb_pre_ecrecover)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_kzg_point_evaluation =
  ((type_of% fb_charge_gas) → (type_of% fb_alloc) → (type_of% fb_kzg_point_evaluation_exec) →
   (type_of% fb_pre_kzg_point_evaluation)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_p256verify =
  ((type_of% fb_charge_gas) → (type_of% fb_alloc) → (type_of% fb_u256_from_be) →
   (type_of% fb_p256_verify) → (type_of% fb_memzero) → (type_of% fb_pre_p256verify)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_frame_start =
  ((type_of% fb_frame_prologue) → (type_of% fb_frame_exception) → (type_of% fb_frame_start)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_frame_prologue =
  ((type_of% fb_u256_is_zero) → (type_of% fb_move_ether) → (type_of% fb_memeq) →
   (type_of% fb_emit_transfer_log) → (type_of% fb_precompile_index) →
   (type_of% fb_run_precompile) → (type_of% fb_frame_prologue)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_run_precompile =
  ((type_of% fb_pre_ecrecover) → (type_of% fb_pre_sha256) → (type_of% fb_pre_ripemd160) →
   (type_of% fb_pre_identity) → (type_of% fb_pre_alt_bn128_add) →
   (type_of% fb_pre_alt_bn128_mul) → (type_of% fb_pre_alt_bn128_pairing_check) →
   (type_of% fb_pre_modexp) → (type_of% fb_pre_blake2f) →
   (type_of% fb_pre_kzg_point_evaluation) → (type_of% fb_pre_bls_g1_add) →
   (type_of% fb_pre_bls_g1_msm) → (type_of% fb_pre_bls_g2_add) →
   (type_of% fb_pre_bls_g2_msm) → (type_of% fb_pre_bls_pairing) →
   (type_of% fb_pre_bls_map_fp_to_g1) → (type_of% fb_pre_bls_map_fp2_to_g2) →
   (type_of% fb_pre_p256verify) → (type_of% fb_run_precompile)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_modexp =
  ((type_of% fb_buffer_read) → (type_of% fb_u256_from_be) → (type_of% fb_sat_word) →
   (type_of% fb_min) → (type_of% fb_modexp_gas) → (type_of% fb_charge_gas) →
   (type_of% fb_alloc) → (type_of% fb_heap_mark) → (type_of% fb_modexp) →
   (type_of% fb_heap_release) → (type_of% fb_pre_modexp)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_bls_g1_add =
  ((type_of% fb_charge_gas) → (type_of% fb_alloc) → (type_of% fb_bls_g1_add_exec) →
   (type_of% fb_pre_bls_g1_add)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_bls_g2_add =
  ((type_of% fb_charge_gas) → (type_of% fb_alloc) → (type_of% fb_bls_g2_add_exec) →
   (type_of% fb_pre_bls_g2_add)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_bls_map_fp_to_g1 =
  ((type_of% fb_charge_gas) → (type_of% fb_alloc) → (type_of% fb_bls_map_fp_to_g1_exec) →
   (type_of% fb_pre_bls_map_fp_to_g1)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_bls_map_fp2_to_g2 =
  ((type_of% fb_charge_gas) → (type_of% fb_alloc) → (type_of% fb_bls_map_fp2_to_g2_exec) →
   (type_of% fb_pre_bls_map_fp2_to_g2)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_bls_g1_msm =
  ((type_of% fb_udivmod) → (type_of% fb_bls_g1_msm_discount) → (type_of% fb_charge_gas) →
   (type_of% fb_alloc) → (type_of% fb_bls_g1_msm_exec) → (type_of% fb_pre_bls_g1_msm)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_bls_g2_msm =
  ((type_of% fb_udivmod) → (type_of% fb_bls_g2_msm_discount) → (type_of% fb_charge_gas) →
   (type_of% fb_alloc) → (type_of% fb_bls_g2_msm_exec) → (type_of% fb_pre_bls_g2_msm)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_bls_pairing =
  ((type_of% fb_udivmod) → (type_of% fb_charge_gas) → (type_of% fb_alloc) →
   (type_of% fb_bls_pairing_exec) → (type_of% fb_pre_bls_pairing)) := rfl
example : type_of% @Campaign.Leaves.S05.fb_pre_blake2f =
  ((type_of% fb_charge_gas) → (type_of% fb_alloc) → (type_of% fb_heap_mark) →
   (type_of% fb_blake2b_f) → (type_of% fb_st_le64) → (type_of% fb_heap_release) →
   (type_of% fb_pre_blake2f)) := rfl


end InitECandidate.Solver.Wave8GuestInv
