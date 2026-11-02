import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S01.Leaves

/-! Axioms and `type_of%` evidence for shard s01 (`wave8/leaves-s01`).

Each `example` checks that the proved theorem has the exact spec statement
(`type_of% Wave8GuestInv.«fb_f»`), taking as explicit hypotheses the spec statements of any
callee leaves it requires.
Every `#print axioms` line must show only `[propext, Classical.choice, Quot.sound]`.
-/

namespace InitECandidate.Solver.Wave8GuestInv.S01

open InitECandidate.Solver.Wave8GuestInv

instance : IsGuestInv (@Wave8GuestInv.GuestInv) where
  eval s prog h := Wave8GuestInv.guestInv_evaluate s prog h
  congr hcode hmem hsh hbase h := Wave8GuestInv.guestInv_congr hcode hmem hsh hbase h

-- 1. fb_ws_account_leaf
example : type_of% (fb_ws_account_leaf_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_keccak256» →
     type_of% Wave8GuestInv.«fb_trie_lookup» →
     type_of% Wave8GuestInv.«fb_ws_account_leaf») := rfl

-- 2. fb_ws_get_account_optional
example : type_of% (fb_ws_get_account_optional_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_ws_account_leaf» →
     type_of% Wave8GuestInv.«fb_decode_account_from_leaf» →
     type_of% Wave8GuestInv.«fb_ws_get_account_optional») := rfl

-- 3. fb_ws_storage_root_of
example : type_of% (fb_ws_storage_root_of_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_ws_get_account_optional» →
     type_of% Wave8GuestInv.«fb_ws_storage_root_of») := rfl

-- 4. fb_ws_account_has_storage
example : type_of% (fb_ws_account_has_storage_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_ws_storage_root_of» →
     type_of% Wave8GuestInv.«fb_memeq» →
     type_of% Wave8GuestInv.«fb_ws_account_has_storage») := rfl

-- 5. fb_account_has_storage
example : type_of% (fb_account_has_storage_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_htab_get» →
     type_of% Wave8GuestInv.«fb_record_pre_state_read» →
     type_of% Wave8GuestInv.«fb_ws_account_has_storage» →
     type_of% Wave8GuestInv.«fb_account_has_storage») := rfl

-- 6. fb_acct_new
example : type_of% (fb_acct_new (GuestInv := @Wave8GuestInv.GuestInv)) =
    type_of% Wave8GuestInv.«fb_acct_new» := rfl

-- 7. fb_acct_empty
example : type_of% (fb_acct_empty (GuestInv := @Wave8GuestInv.GuestInv)) =
    type_of% Wave8GuestInv.«fb_acct_empty» := rfl

-- 8. fb_get_pre_state_account_optional
example : type_of% (fb_get_pre_state_account_optional_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_htab_set» →
     type_of% Wave8GuestInv.«fb_htab_get» →
     type_of% Wave8GuestInv.«fb_record_pre_state_read» →
     type_of% Wave8GuestInv.«fb_ws_get_account_optional» →
     type_of% Wave8GuestInv.«fb_get_pre_state_account_optional») := rfl

-- 9. fb_get_account_optional
example : type_of% (fb_get_account_optional_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_htab_set» →
     type_of% Wave8GuestInv.«fb_htab_get» →
     type_of% Wave8GuestInv.«fb_get_pre_state_account_optional» →
     type_of% Wave8GuestInv.«fb_get_account_optional») := rfl

-- 10. fb_get_account
example : type_of% (fb_get_account_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_get_account_optional» →
     type_of% Wave8GuestInv.«fb_get_account») := rfl

-- 11. fb_account_deployable
example : type_of% (fb_account_deployable_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_get_account» →
     type_of% Wave8GuestInv.«fb_memeq» →
     type_of% Wave8GuestInv.«fb_account_has_storage» →
     type_of% Wave8GuestInv.«fb_account_deployable») := rfl

-- 12. fb_account_exists
example : type_of% (fb_account_exists_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_get_account_optional» →
     type_of% Wave8GuestInv.«fb_account_exists») := rfl

-- 13. fb_acct_copy
example : type_of% (fb_acct_copy_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_memcpy» →
     type_of% Wave8GuestInv.«fb_acct_copy») := rfl

-- 14. fb_acct_is_empty
example : type_of% (fb_acct_is_empty_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_memeq» →
     type_of% Wave8GuestInv.«fb_acct_is_empty») := rfl

-- 15. fb_bal_ensure_account
example : type_of% (fb_bal_ensure_account_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_htab_get» →
     type_of% Wave8GuestInv.«fb_htab_set» →
     type_of% Wave8GuestInv.«fb_bal_ensure_account») := rfl

-- 16. fb_add_balance_change
example : type_of% (fb_add_balance_change_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_bal_ensure_account» →
     type_of% Wave8GuestInv.«fb_lst_upsert_idx» →
     type_of% Wave8GuestInv.«fb_add_balance_change») := rfl

-- 17. fb_add_code_change
example : type_of% (fb_add_code_change_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_bal_ensure_account» →
     type_of% Wave8GuestInv.«fb_lst_upsert_idx» →
     type_of% Wave8GuestInv.«fb_add_code_change») := rfl

-- 18. fb_add_nonce_change
example : type_of% (fb_add_nonce_change_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_bal_ensure_account» →
     type_of% Wave8GuestInv.«fb_lst_push» →
     type_of% Wave8GuestInv.«fb_add_nonce_change») := rfl

-- 19. fb_add_sat
example : type_of% (fb_add_sat (GuestInv := @Wave8GuestInv.GuestInv)) =
    type_of% Wave8GuestInv.«fb_add_sat» := rfl

-- 20. fb_add_storage_read
example : type_of% (fb_add_storage_read_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_bal_ensure_account» →
     type_of% Wave8GuestInv.«fb_htab_set» →
     type_of% Wave8GuestInv.«fb_add_storage_read») := rfl

-- 21. fb_add_storage_write
example : type_of% (fb_add_storage_write_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_bal_ensure_account» →
     type_of% Wave8GuestInv.«fb_htab_get» →
     type_of% Wave8GuestInv.«fb_htab_set» →
     type_of% Wave8GuestInv.«fb_lst_upsert_idx» →
     type_of% Wave8GuestInv.«fb_add_storage_write») := rfl

-- 22. fb_add_to_bloom
example : type_of% (fb_add_to_bloom_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_keccak256» →
     type_of% Wave8GuestInv.«fb_add_to_bloom») := rfl

-- 23. fb_add_touched_account
example : type_of% (fb_add_touched_account_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (type_of% Wave8GuestInv.«fb_bal_ensure_account» →
     type_of% Wave8GuestInv.«fb_add_touched_account») := rfl

-- 24. fb_addr_from_words
example : type_of% (fb_addr_from_words (GuestInv := @Wave8GuestInv.GuestInv)) =
    type_of% Wave8GuestInv.«fb_addr_from_words» := rfl


end InitECandidate.Solver.Wave8GuestInv.S01
