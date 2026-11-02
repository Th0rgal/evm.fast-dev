import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12Simple
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12More
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12Transactions
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12Recovery
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12RecoveryMore
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12RecoveryFinal
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12Chain
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12Loops
import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12LoopsMore

namespace InitECandidate.Solver.Wave8Leaves.S12

open InitECandidate.Solver.Wave8GuestInv

example : type_of% «fb_tx_has_access_list» =
    type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_has_access_list» := rfl
example : type_of% «fb_tx_is_blob» =
    type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_is_blob» := rfl
example : type_of% «fb_tx_is_setcode» =
    type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_is_setcode» := rfl
example : type_of% @«fb_udiv_small5» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_udiv» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_udiv_small5») := rfl
example : type_of% @«fb_signing_hash_pre155» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_signing_hash_mode» → type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_pre155») := rfl
example : type_of% @«fb_signing_hash_155» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_signing_hash_mode» → type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_155») := rfl
example : type_of% @«fb_signing_hash_2930» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_signing_hash_mode» → type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_2930») := rfl
example : type_of% @«fb_signing_hash_1559» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_signing_hash_mode» → type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_1559») := rfl
example : type_of% @«fb_signing_hash_4844» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_signing_hash_mode» → type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_4844») := rfl
example : type_of% @«fb_signing_hash_7702» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_signing_hash_mode» → type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signing_hash_7702») := rfl
example : type_of% @«fb_encode_transaction» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_encode_generic» → type_of% InitECandidate.Solver.Wave8GuestInv.«fb_encode_transaction») := rfl
example : type_of% @«fb_tx_put_to» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_encode_bytes» → type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_put_to») := rfl
example : type_of% @«fb_tx_signing_hash_mode» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_encode_generic» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_signing_hash_mode») := rfl
example : type_of% @«fb_tx_put_u256» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_alloc» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_u256_to_be_min» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_encode_bytes» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_put_u256») := rfl
example : type_of% @«fb_set_account_balance» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_get_account» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_acct_copy» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_modify_state_commit» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_set_account_balance») := rfl
example : type_of% @«fb_recover_sender_with_chain_id» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_alloc» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_recover_transaction_public_key» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_sender_address_from_public_key» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_recover_sender_with_chain_id») := rfl
example : type_of% @«fb_sender_address_from_public_key» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_alloc» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_keccak256» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_memcpy» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_sender_address_from_public_key») := rfl
example : type_of% @«fb_recover_transaction_public_key» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_heap_mark» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_alloc» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_signature_recovery_parameters» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_secp256k1_recover» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_heap_release» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_recover_transaction_public_key») := rfl
example : type_of% @«fb_tx_chain_id» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_u256_fits_word» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_u256_sub» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_u256_shr» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_chain_id») := rfl
example : type_of% @«fb_tx_put_blob_hashes» =
    (type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_encode_list_header» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_encode_bytes» →
     type_of% InitECandidate.Solver.Wave8GuestInv.«fb_tx_put_blob_hashes») := rfl
example : type_of% «fb_count_tokens_in_data» =
    type_of% InitECandidate.Solver.Wave8GuestInv.«fb_count_tokens_in_data» := rfl


end InitECandidate.Solver.Wave8Leaves.S12
