import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.PrecompileWrappers

/-! Standalone bounded termination proofs on `GuestInv` for transaction RLP encoding,
EIP-155 / EIP-2930 / EIP-1559 / EIP-4844 / EIP-7702 signing hashes, ECDSA sender recovery,
EIP-7702 authority recovery, and transaction intrinsic-cost / validation helpers:
- `fb_tx_has_access_list`, `fb_tx_is_blob`, `fb_tx_is_setcode`, `fb_calculate_total_blob_gas`,
  `fb_fee_mul`, `fb_udiv_small5`
- `fb_tx_u256_encoded_len`, `fb_tx_put_u256`, `fb_tx_put_to`, `fb_access_list_payload_len`,
  `fb_tx_put_access_list`, `fb_tx_put_blob_hashes`, `fb_auth_payload_len`, `fb_auth_list_payload_len`,
  `fb_tx_put_authorizations`, `fb_tx_encode_bound`, `fb_tx_encode_generic`, `fb_encode_transaction`
- `fb_tx_signing_hash_mode`, `fb_signing_hash_pre155`, `fb_signing_hash_155`,
  `fb_signing_hash_2930`, `fb_signing_hash_1559`, `fb_signing_hash_4844`, `fb_signing_hash_7702`,
  `fb_tx_chain_id`
- `fb_signature_recovery_parameters`, `fb_recover_transaction_public_key`,
  `fb_sender_address_from_public_key`, `fb_recover_sender_with_chain_id`, `fb_recover_authority`
- `fb_count_tokens_in_data`, `fb_calculate_intrinsic_cost`, `fb_validate_transaction`.
Zero `LeafStatements.lean` dependency. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16ArithPort

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod
open InitECandidate.Solver.Wave8GuestInv.FastU256Core
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB1
open InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles

/-! ### 1. Simple transaction predicates, `fee_mul`, and `udiv_small5` -/

theorem fb_tx_has_access_list :
    TerminatingFunBoundedOn GuestInv (ofString "tx_has_access_list") K.«tx_has_access_list» := by
  bls_prove 315 Guest.Software.guestFn_tx_has_access_list K.«tx_has_access_list»

theorem fb_tx_is_blob :
    TerminatingFunBoundedOn GuestInv (ofString "tx_is_blob") K.«tx_is_blob» := by
  bls_prove 865 Guest.Software.guestFn_tx_is_blob K.«tx_is_blob»

theorem fb_tx_is_setcode :
    TerminatingFunBoundedOn GuestInv (ofString "tx_is_setcode") K.«tx_is_setcode» := by
  bls_prove 866 Guest.Software.guestFn_tx_is_setcode K.«tx_is_setcode»

theorem fb_calculate_total_blob_gas :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_total_blob_gas")
      K.«calculate_total_blob_gas» := by
  bls_prove 317 Guest.Software.guestFn_calculate_total_blob_gas K.«calculate_total_blob_gas»

theorem fb_fee_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fee_mul") K.«fee_mul» := by
  have _ := Arith.fb_u256_mul_full
  bls_prove 867 Guest.Software.guestFn_fee_mul K.«fee_mul»

theorem fb_udiv_small5 :
    TerminatingFunBoundedOn GuestInv (ofString "udiv_small5") K.«udiv_small5» := by
  have _ := FastU256Core.fb_udiv
  bls_prove 874 Guest.Software.guestFn_udiv_small5 K.«udiv_small5»

/-! ### 2. Transaction RLP payload lengths and field encoders -/

theorem fb_tx_u256_encoded_len :
    TerminatingFunBoundedOn GuestInv (ofString "tx_u256_encoded_len")
      K.«tx_u256_encoded_len» := by
  have _ := fb_u256_byte_length
  bls_prove 319 Guest.Software.guestFn_tx_u256_encoded_len K.«tx_u256_encoded_len»

theorem fb_tx_put_u256 :
    TerminatingFunBoundedOn GuestInv (ofString "tx_put_u256") K.«tx_put_u256» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_u256_to_be_min
  have _ := fb_rlp_encode_bytes
  have _ := fb_heap_release
  bls_prove 318 Guest.Software.guestFn_tx_put_u256 K.«tx_put_u256»

theorem fb_tx_put_to :
    TerminatingFunBoundedOn GuestInv (ofString "tx_put_to") K.«tx_put_to» := by
  have _ := fb_rlp_encode_bytes
  bls_prove 320 Guest.Software.guestFn_tx_put_to K.«tx_put_to»

theorem fb_access_list_payload_len :
    TerminatingFunBoundedOn GuestInv (ofString "access_list_payload_len")
      K.«access_list_payload_len» := by
  have _ := fb_rlp_list_header_len
  bls_unfold 321 Guest.Software.guestFn_access_list_payload_len
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "i") (.var .local (ofString "n"))
      · bls_auto
      · counter_step
      · decide
  · bls_arith K.«access_list_payload_len»

theorem fb_tx_put_access_list :
    TerminatingFunBoundedOn GuestInv (ofString "tx_put_access_list") K.«tx_put_access_list» := by
  have _ := fb_access_list_payload_len
  have _ := fb_rlp_encode_list_header
  have _ := fb_rlp_list_header_len
  have _ := fb_rlp_encode_bytes
  bls_unfold 322 Guest.Software.guestFn_tx_put_access_list
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "i") (.var .local (ofString "n"))
      · bls_auto_loops
        · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "j")
            (.var .local (ofString "ns"))
          · bls_auto
          · counter_step
          · decide
      · counter_step
      · decide
  · bls_arith K.«tx_put_access_list»

theorem fb_tx_put_blob_hashes :
    TerminatingFunBoundedOn GuestInv (ofString "tx_put_blob_hashes") K.«tx_put_blob_hashes» := by
  have _ := fb_rlp_encode_list_header
  have _ := fb_rlp_encode_bytes
  bls_unfold 323 Guest.Software.guestFn_tx_put_blob_hashes
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "i") (.var .local (ofString "n"))
      · bls_auto
      · counter_step
      · decide
  · bls_arith K.«tx_put_blob_hashes»

theorem fb_auth_payload_len :
    TerminatingFunBoundedOn GuestInv (ofString "auth_payload_len") K.«auth_payload_len» := by
  have _ := fb_tx_u256_encoded_len
  have _ := fb_rlp_word_encoded_len
  bls_prove 324 Guest.Software.guestFn_auth_payload_len K.«auth_payload_len»

theorem fb_auth_list_payload_len :
    TerminatingFunBoundedOn GuestInv (ofString "auth_list_payload_len")
      K.«auth_list_payload_len» := by
  have _ := fb_auth_payload_len
  have _ := fb_rlp_list_header_len
  bls_unfold 325 Guest.Software.guestFn_auth_list_payload_len
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "i") (.var .local (ofString "n"))
      · bls_auto
      · counter_step
      · decide
  · bls_arith K.«auth_list_payload_len»

theorem fb_tx_put_authorizations :
    TerminatingFunBoundedOn GuestInv (ofString "tx_put_authorizations")
      K.«tx_put_authorizations» := by
  have _ := fb_auth_list_payload_len
  have _ := fb_rlp_encode_list_header
  have _ := fb_auth_payload_len
  have _ := fb_tx_put_u256
  have _ := fb_rlp_encode_bytes
  have _ := fb_rlp_encode_word
  bls_unfold 326 Guest.Software.guestFn_tx_put_authorizations
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "i") (.var .local (ofString "n"))
      · bls_auto
      · counter_step
      · decide
  · bls_arith K.«tx_put_authorizations»

theorem fb_tx_encode_bound :
    TerminatingFunBoundedOn GuestInv (ofString "tx_encode_bound") K.«tx_encode_bound» := by
  have _ := fb_access_list_payload_len
  have _ := fb_auth_list_payload_len
  bls_prove 327 Guest.Software.guestFn_tx_encode_bound K.«tx_encode_bound»

theorem fb_tx_encode_generic :
    TerminatingFunBoundedOn GuestInv (ofString "tx_encode_generic") K.«tx_encode_generic» := by
  have _ := fb_tx_encode_bound
  have _ := fb_alloc
  have _ := fb_rlp_encode_word
  have _ := fb_tx_put_u256
  have _ := fb_tx_put_to
  have _ := fb_rlp_encode_bytes
  have _ := fb_tx_put_access_list
  have _ := fb_tx_put_blob_hashes
  have _ := fb_tx_put_authorizations
  have _ := fb_rlp_list_header_len
  have _ := fb_rlp_encode_list_header
  bls_prove 328 Guest.Software.guestFn_tx_encode_generic K.«tx_encode_generic»

theorem fb_encode_transaction :
    TerminatingFunBoundedOn GuestInv (ofString "encode_transaction") K.«encode_transaction» := by
  have _ := fb_tx_encode_generic
  bls_prove 329 Guest.Software.guestFn_encode_transaction K.«encode_transaction»

/-! ### 3. Signing hashes & chain id -/

theorem fb_tx_signing_hash_mode :
    TerminatingFunBoundedOn GuestInv (ofString "tx_signing_hash_mode")
      K.«tx_signing_hash_mode» := by
  have _ := fb_heap_mark
  have _ := fb_tx_encode_generic
  have _ := fb_keccak256
  have _ := fb_heap_release
  bls_prove 331 Guest.Software.guestFn_tx_signing_hash_mode K.«tx_signing_hash_mode»

theorem fb_signing_hash_pre155 :
    TerminatingFunBoundedOn GuestInv (ofString "signing_hash_pre155")
      K.«signing_hash_pre155» := by
  have _ := fb_tx_signing_hash_mode
  bls_prove 332 Guest.Software.guestFn_signing_hash_pre155 K.«signing_hash_pre155»

theorem fb_signing_hash_155 :
    TerminatingFunBoundedOn GuestInv (ofString "signing_hash_155") K.«signing_hash_155» := by
  have _ := fb_tx_signing_hash_mode
  bls_prove 333 Guest.Software.guestFn_signing_hash_155 K.«signing_hash_155»

theorem fb_signing_hash_2930 :
    TerminatingFunBoundedOn GuestInv (ofString "signing_hash_2930") K.«signing_hash_2930» := by
  have _ := fb_tx_signing_hash_mode
  bls_prove 334 Guest.Software.guestFn_signing_hash_2930 K.«signing_hash_2930»

theorem fb_signing_hash_1559 :
    TerminatingFunBoundedOn GuestInv (ofString "signing_hash_1559") K.«signing_hash_1559» := by
  have _ := fb_tx_signing_hash_mode
  bls_prove 335 Guest.Software.guestFn_signing_hash_1559 K.«signing_hash_1559»

theorem fb_signing_hash_4844 :
    TerminatingFunBoundedOn GuestInv (ofString "signing_hash_4844") K.«signing_hash_4844» := by
  have _ := fb_tx_signing_hash_mode
  bls_prove 336 Guest.Software.guestFn_signing_hash_4844 K.«signing_hash_4844»

theorem fb_signing_hash_7702 :
    TerminatingFunBoundedOn GuestInv (ofString "signing_hash_7702") K.«signing_hash_7702» := by
  have _ := fb_tx_signing_hash_mode
  bls_prove 337 Guest.Software.guestFn_signing_hash_7702 K.«signing_hash_7702»

theorem fb_tx_chain_id :
    TerminatingFunBoundedOn GuestInv (ofString "tx_chain_id") K.«tx_chain_id» := by
  have _ := fb_u256_fits_word
  have _ := fb_u256_sub
  have _ := fb_u256_shr
  bls_prove 338 Guest.Software.guestFn_tx_chain_id K.«tx_chain_id»

/-! ### 4. Signature recovery, sender recovery, and EIP-7702 authority recovery -/

theorem fb_signature_recovery_parameters :
    TerminatingFunBoundedOn GuestInv (ofString "signature_recovery_parameters")
      K.«signature_recovery_parameters» := by
  have _ := P13.Callees.fb_u256_is_zero
  have _ := P13.Callees.fb_u256_lt
  have _ := FastU256Core.fb_u256_gt
  have _ := FastU256Core.fb_u256_fits_word
  have _ := FastU256Core.fb_u256_eq
  have _ := Arith.fb_u256_add
  have _ := fb_signing_hash_pre155
  have _ := fb_signing_hash_155
  have _ := fb_signing_hash_2930
  have _ := fb_signing_hash_1559
  have _ := fb_signing_hash_4844
  have _ := fb_signing_hash_7702
  bls_prove 339 Guest.Software.guestFn_signature_recovery_parameters
    K.«signature_recovery_parameters»

theorem fb_recover_transaction_public_key :
    TerminatingFunBoundedOn GuestInv (ofString "recover_transaction_public_key")
      K.«recover_transaction_public_key» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_signature_recovery_parameters
  have _ := fb_secp256k1_recover
  have _ := fb_heap_release
  bls_prove 340 Guest.Software.guestFn_recover_transaction_public_key
    K.«recover_transaction_public_key»

theorem fb_sender_address_from_public_key :
    TerminatingFunBoundedOn GuestInv (ofString "sender_address_from_public_key")
      K.«sender_address_from_public_key» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_keccak256
  have _ := fb_memcpy
  have _ := fb_heap_release
  bls_prove 341 Guest.Software.guestFn_sender_address_from_public_key
    K.«sender_address_from_public_key»

theorem fb_recover_sender_with_chain_id :
    TerminatingFunBoundedOn GuestInv (ofString "recover_sender_with_chain_id")
      K.«recover_sender_with_chain_id» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_recover_transaction_public_key
  have _ := fb_sender_address_from_public_key
  have _ := fb_heap_release
  bls_prove 343 Guest.Software.guestFn_recover_sender_with_chain_id
    K.«recover_sender_with_chain_id»

theorem fb_recover_authority :
    TerminatingFunBoundedOn GuestInv (ofString "recover_authority") K.«recover_authority» := by
  have _ := P13.Callees.fb_u256_is_zero
  have _ := P13.Callees.fb_u256_lt
  have _ := FastU256Core.fb_u256_gt
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_rlp_put_u256
  have _ := fb_rlp_encode_bytes
  have _ := fb_rlp_encode_word
  have _ := fb_rlp_list_header_len
  have _ := fb_rlp_encode_list_header
  have _ := fb_keccak256
  have _ := fb_secp256k1_recover
  have _ := fb_heap_release
  have _ := fb_memcpy
  bls_prove 572 Guest.Software.guestFn_recover_authority K.«recover_authority»

/-! ### 5. Transaction intrinsic cost & validation (`count_tokens_in_data`, `calculate_intrinsic_cost`, `validate_transaction`) -/

theorem fb_count_tokens_in_data :
    TerminatingFunBoundedOn GuestInv (ofString "count_tokens_in_data")
      K.«count_tokens_in_data» := by
  bls_unfold 344 Guest.Software.guestFn_count_tokens_in_data
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "i") (.var .local (ofString "n"))
      · bls_auto
      · counter_step
      · decide
  · bls_arith K.«count_tokens_in_data»

theorem fb_calculate_intrinsic_cost :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_intrinsic_cost")
      K.«calculate_intrinsic_cost» := by
  have _ := fb_count_tokens_in_data
  have _ := P13.Callees.fb_u256_is_zero
  have _ := fb_memeq
  bls_unfold 345 Guest.Software.guestFn_calculate_intrinsic_cost
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "i") (.var .local (ofString "n"))
      · bls_auto
      · counter_step
      · decide
  · bls_arith K.«calculate_intrinsic_cost»

theorem fb_validate_transaction :
    TerminatingFunBoundedOn GuestInv (ofString "validate_transaction")
      K.«validate_transaction» := by
  have _ := fb_calculate_intrinsic_cost
  have _ := FastU256Core.fb_u256_fits_word
  bls_prove 346 Guest.Software.guestFn_validate_transaction K.«validate_transaction»

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort
