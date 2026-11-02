import InitECandidate.Solver.Wave8GuestInv.Shards.S01.Base

/-! Shard s01 leaves (`wave8/leaves-s01`): all 24 `fb_*` leaves in `campaign/leaves/shards/s01.txt`.

Each leaf theorem proves the exact spec statement of `fb_f` (`TerminatingFunBoundedOn GuestInv
(ofString "f") K.«f»`). Callee bounds from `GuestUniformClockBound` (`alloc`, `heap_mark`,
`heap_release`, `st_be32`, `st_be64`, `addr_from_words`) and trivial loop-free callees
(`u256_is_zero`, `htab_new`, `lst_new`, `record_pre_state_read`) are proved unconditionally;
remaining cross-shard callee leaves (`keccak256`, `trie_lookup`, `decode_account_from_leaf`,
`memeq`, `memcpy`, `htab_get`, `htab_set`, `lst_push`, `lst_upsert_idx`) are taken as explicit
hypotheses (or provided in both `_of` and self-contained variants where `htab` helpers apply).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8GuestInv.S01

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

attribute [local irreducible] TerminatingProgBoundedOn

variable {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} [IsGuestInv GuestInv]

/-! ## Discharged callee bounds (from `GuestUniformClockBound` and loop-free AST bodies) -/

theorem on_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc» :=
  funOn funBounded_alloc (by decide)

theorem on_heap_mark : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark» :=
  funOn funBounded_heap_mark (by decide)

theorem on_heap_release :
    TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release» :=
  funOn funBounded_heap_release (by decide)

theorem on_st_be32 : TerminatingFunBoundedOn GuestInv (ofString "st_be32") K.«st_be32» :=
  funOn funBounded_st_be32 (by decide)

theorem on_st_be64 : TerminatingFunBoundedOn GuestInv (ofString "st_be64") K.«st_be64» :=
  funOn funBounded_st_be64 (by decide)

theorem on_u256_is_zero :
    TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero» := by
  apply onFun_le 42 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_is_zero _ rfl
  · htab_unfold Guest.Software.guestFn_u256_is_zero
    htab_walk
  · htab_bound K.«u256_is_zero»

theorem on_htab_new : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new» := by
  have ha := on_alloc (GuestInv := GuestInv)
  apply onFun_le 128 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_new _ rfl
  · htab_unfold Guest.Software.guestFn_htab_new
    htab_walk
  · htab_bound K.«htab_new»

theorem on_lst_new : TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new» := by
  have ha := on_alloc (GuestInv := GuestInv)
  apply onFun_le 408 (by rw [guestAst_len]; decide) Guest.Software.guestFn_lst_new _ rfl
  · htab_unfold Guest.Software.guestFn_lst_new
    htab_walk
  · htab_bound K.«lst_new»

theorem on_record_pre_state_read
    (hs : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») :
    TerminatingFunBoundedOn GuestInv (ofString "record_pre_state_read") K.«record_pre_state_read» := by
  apply onFun_le 364 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_record_pre_state_read _ rfl
  · htab_unfold Guest.Software.guestFn_record_pre_state_read
    htab_walk
  · htab_bound K.«record_pre_state_read»

theorem on_lst_push
    (hc : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») :
    TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push» := by
  have ha := on_alloc (GuestInv := GuestInv)
  apply onFun_le 410 (by rw [guestAst_len]; decide) Guest.Software.guestFn_lst_push _ rfl
  · htab_unfold Guest.Software.guestFn_lst_push
    htab_walk
  · htab_bound K.«lst_push»

theorem on_lst_upsert_idx
    (hp : TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push») :
    TerminatingFunBoundedOn GuestInv (ofString "lst_upsert_idx") K.«lst_upsert_idx» := by
  apply onFun_le 413 (by rw [guestAst_len]; decide) Guest.Software.guestFn_lst_upsert_idx _ rfl
  · htab_unfold Guest.Software.guestFn_lst_upsert_idx
    htab_walk
    counted_while
    all_goals htab_walk
  · htab_bound K.«lst_upsert_idx»

/-! ## Shard s01 leaves (1..24) -/

/-- 1. `ws_account_leaf` (AST line 12992): loop-free. -/
theorem fb_ws_account_leaf_of
    (hkeccak : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (htrie : TerminatingFunBoundedOn GuestInv (ofString "trie_lookup") K.«trie_lookup») :
    TerminatingFunBoundedOn GuestInv (ofString "ws_account_leaf") K.«ws_account_leaf» := by
  have hm := on_heap_mark (GuestInv := GuestInv)
  have ha := on_alloc (GuestInv := GuestInv)
  have hr := on_heap_release (GuestInv := GuestInv)
  apply onFun_le 365 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ws_account_leaf _ rfl
  · htab_unfold Guest.Software.guestFn_ws_account_leaf
    htab_walk
  · htab_bound K.«ws_account_leaf»

/-- 2. `ws_get_account_optional` (AST line 13009): loop-free. -/
theorem fb_ws_get_account_optional_of
    (hleaf : TerminatingFunBoundedOn GuestInv (ofString "ws_account_leaf") K.«ws_account_leaf»)
    (hdec : TerminatingFunBoundedOn GuestInv
      (ofString "decode_account_from_leaf") K.«decode_account_from_leaf») :
    TerminatingFunBoundedOn GuestInv
      (ofString "ws_get_account_optional") K.«ws_get_account_optional» := by
  have ha := on_alloc (GuestInv := GuestInv)
  apply onFun_le 366 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ws_get_account_optional _ rfl
  · htab_unfold Guest.Software.guestFn_ws_get_account_optional
    htab_walk
  · htab_bound K.«ws_get_account_optional»

/-- 3. `ws_storage_root_of` (AST line 13027): loop-free. -/
theorem fb_ws_storage_root_of_of
    (hws : TerminatingFunBoundedOn GuestInv
      (ofString "ws_get_account_optional") K.«ws_get_account_optional») :
    TerminatingFunBoundedOn GuestInv (ofString "ws_storage_root_of") K.«ws_storage_root_of» := by
  apply onFun_le 367 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ws_storage_root_of _ rfl
  · htab_unfold Guest.Software.guestFn_ws_storage_root_of
    htab_walk
  · htab_bound K.«ws_storage_root_of»

/-- 4. `ws_account_has_storage` (AST line 13119): loop-free. -/
theorem fb_ws_account_has_storage_of
    (hroot : TerminatingFunBoundedOn GuestInv (ofString "ws_storage_root_of") K.«ws_storage_root_of»)
    (hmemeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») :
    TerminatingFunBoundedOn GuestInv
      (ofString "ws_account_has_storage") K.«ws_account_has_storage» := by
  apply onFun_le 371 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ws_account_has_storage _ rfl
  · htab_unfold Guest.Software.guestFn_ws_account_has_storage
    htab_walk
  · htab_bound K.«ws_account_has_storage»

/-- 5. `account_has_storage` (AST line 13330): loop-free. -/
theorem fb_account_has_storage_of
    (hget : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (hrec : TerminatingFunBoundedOn GuestInv
      (ofString "record_pre_state_read") K.«record_pre_state_read»)
    (hws : TerminatingFunBoundedOn GuestInv
      (ofString "ws_account_has_storage") K.«ws_account_has_storage») :
    TerminatingFunBoundedOn GuestInv (ofString "account_has_storage") K.«account_has_storage» := by
  apply onFun_le 382 (by rw [guestAst_len]; decide) Guest.Software.guestFn_account_has_storage _ rfl
  · htab_unfold Guest.Software.guestFn_account_has_storage
    htab_walk
  · htab_bound K.«account_has_storage»

/-- 6. `acct_new` (AST line 12937): loop-free. -/
theorem fb_acct_new :
    TerminatingFunBoundedOn GuestInv (ofString "acct_new") K.«acct_new» := by
  have ha := on_alloc (GuestInv := GuestInv)
  apply onFun_le 361 (by rw [guestAst_len]; decide) Guest.Software.guestFn_acct_new _ rfl
  · htab_unfold Guest.Software.guestFn_acct_new
    htab_walk
  · htab_bound K.«acct_new»

/-- 7. `acct_empty` (AST line 12956): loop-free. -/
theorem fb_acct_empty :
    TerminatingFunBoundedOn GuestInv (ofString "acct_empty") K.«acct_empty» := by
  have hn := fb_acct_new (GuestInv := GuestInv)
  apply onFun_le 362 (by rw [guestAst_len]; decide) Guest.Software.guestFn_acct_empty _ rfl
  · htab_unfold Guest.Software.guestFn_acct_empty
    htab_walk
  · htab_bound K.«acct_empty»

/-- 8. `get_pre_state_account_optional` (AST line 13135): loop-free. -/
theorem fb_get_pre_state_account_optional_of
    (hset : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (hget : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (hrec : TerminatingFunBoundedOn GuestInv
      (ofString "record_pre_state_read") K.«record_pre_state_read»)
    (hws : TerminatingFunBoundedOn GuestInv
      (ofString "ws_get_account_optional") K.«ws_get_account_optional») :
    TerminatingFunBoundedOn GuestInv
      (ofString "get_pre_state_account_optional") K.«get_pre_state_account_optional» := by
  apply onFun_le 372 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_get_pre_state_account_optional _ rfl
  · htab_unfold Guest.Software.guestFn_get_pre_state_account_optional
    htab_walk
  · htab_bound K.«get_pre_state_account_optional»

/-- 9. `get_account_optional` (AST line 13170): loop-free. -/
theorem fb_get_account_optional_of
    (hset : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (hget : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (hpre : TerminatingFunBoundedOn GuestInv
      (ofString "get_pre_state_account_optional") K.«get_pre_state_account_optional») :
    TerminatingFunBoundedOn GuestInv
      (ofString "get_account_optional") K.«get_account_optional» := by
  apply onFun_le 374 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_get_account_optional _ rfl
  · htab_unfold Guest.Software.guestFn_get_account_optional
    htab_walk
  · htab_bound K.«get_account_optional»

/-- 10. `get_account` (AST line 13188): loop-free. -/
theorem fb_get_account_of
    (hopt : TerminatingFunBoundedOn GuestInv
      (ofString "get_account_optional") K.«get_account_optional») :
    TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account» := by
  have he := fb_acct_empty (GuestInv := GuestInv)
  apply onFun_le 375 (by rw [guestAst_len]; decide) Guest.Software.guestFn_get_account _ rfl
  · htab_unfold Guest.Software.guestFn_get_account
    htab_walk
  · htab_bound K.«get_account»

/-- 11. `account_deployable` (AST line 13358): loop-free. -/
theorem fb_account_deployable_of
    (hget : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (hmemeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hstor : TerminatingFunBoundedOn GuestInv
      (ofString "account_has_storage") K.«account_has_storage») :
    TerminatingFunBoundedOn GuestInv (ofString "account_deployable") K.«account_deployable» := by
  apply onFun_le 383 (by rw [guestAst_len]; decide) Guest.Software.guestFn_account_deployable _ rfl
  · htab_unfold Guest.Software.guestFn_account_deployable
    htab_walk
  · htab_bound K.«account_deployable»

/-- 12. `account_exists` (AST line 13315): loop-free. -/
theorem fb_account_exists_of
    (hopt : TerminatingFunBoundedOn GuestInv
      (ofString "get_account_optional") K.«get_account_optional») :
    TerminatingFunBoundedOn GuestInv (ofString "account_exists") K.«account_exists» := by
  apply onFun_le 381 (by rw [guestAst_len]; decide) Guest.Software.guestFn_account_exists _ rfl
  · htab_unfold Guest.Software.guestFn_account_exists
    htab_walk
  · htab_bound K.«account_exists»

/-- 13. `acct_copy` (AST line 12967): loop-free. -/
theorem fb_acct_copy_of
    (hmemcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») :
    TerminatingFunBoundedOn GuestInv (ofString "acct_copy") K.«acct_copy» := by
  have ha := on_alloc (GuestInv := GuestInv)
  apply onFun_le 363 (by rw [guestAst_len]; decide) Guest.Software.guestFn_acct_copy _ rfl
  · htab_unfold Guest.Software.guestFn_acct_copy
    htab_walk
  · htab_bound K.«acct_copy»

/-- 14. `acct_is_empty` (AST line 13383): loop-free. -/
theorem fb_acct_is_empty_of
    (hmemeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») :
    TerminatingFunBoundedOn GuestInv (ofString "acct_is_empty") K.«acct_is_empty» := by
  have hz := on_u256_is_zero (GuestInv := GuestInv)
  apply onFun_le 384 (by rw [guestAst_len]; decide) Guest.Software.guestFn_acct_is_empty _ rfl
  · htab_unfold Guest.Software.guestFn_acct_is_empty
    htab_walk
  · htab_bound K.«acct_is_empty»

/-- 15. `bal_ensure_account` (AST line 13883): loop-free. -/
theorem fb_bal_ensure_account_of
    (hget : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (hset : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») :
    TerminatingFunBoundedOn GuestInv (ofString "bal_ensure_account") K.«bal_ensure_account» := by
  have ha := on_alloc (GuestInv := GuestInv)
  have hnew := on_htab_new (GuestInv := GuestInv)
  have hlnew := on_lst_new (GuestInv := GuestInv)
  apply onFun_le 412 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bal_ensure_account _ rfl
  · htab_unfold Guest.Software.guestFn_bal_ensure_account
    htab_walk
  · htab_bound K.«bal_ensure_account»

/-- 16. `add_balance_change` (AST line 13978): loop-free. -/
theorem fb_add_balance_change_of
    (hbal : TerminatingFunBoundedOn GuestInv
      (ofString "bal_ensure_account") K.«bal_ensure_account»)
    (hups : TerminatingFunBoundedOn GuestInv (ofString "lst_upsert_idx") K.«lst_upsert_idx») :
    TerminatingFunBoundedOn GuestInv (ofString "add_balance_change") K.«add_balance_change» := by
  apply onFun_le 416 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_balance_change _ rfl
  · htab_unfold Guest.Software.guestFn_add_balance_change
    htab_walk
  · htab_bound K.«add_balance_change»

/-- 17. `add_code_change` (AST line 14023): loop-free. -/
theorem fb_add_code_change_of
    (hbal : TerminatingFunBoundedOn GuestInv
      (ofString "bal_ensure_account") K.«bal_ensure_account»)
    (hups : TerminatingFunBoundedOn GuestInv (ofString "lst_upsert_idx") K.«lst_upsert_idx») :
    TerminatingFunBoundedOn GuestInv (ofString "add_code_change") K.«add_code_change» := by
  apply onFun_le 418 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_code_change _ rfl
  · htab_unfold Guest.Software.guestFn_add_code_change
    htab_walk
  · htab_bound K.«add_code_change»

/-- 18. `add_nonce_change` (AST line 13992): #0 CTR (`while i < n` with step 1). -/
theorem fb_add_nonce_change_of
    (hbal : TerminatingFunBoundedOn GuestInv
      (ofString "bal_ensure_account") K.«bal_ensure_account»)
    (hpush : TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push») :
    TerminatingFunBoundedOn GuestInv (ofString "add_nonce_change") K.«add_nonce_change» := by
  apply onFun_le 417 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_nonce_change _ rfl
  · htab_unfold Guest.Software.guestFn_add_nonce_change
    htab_walk
    counted_while
    all_goals htab_walk
  · rw [show K.«add_nonce_change» =
      (K.«bal_ensure_account» + 1) + (2 ^ 64 + 1) * (0 + 1) + (K.«lst_push» + 1) from rfl]
    generalize (2 ^ 64 + 1) * (0 + 1) = W, K.«bal_ensure_account» = B1, K.«lst_push» = B2
    omega

/-- 19. `add_sat` (AST line 14847): loop-free. -/
theorem fb_add_sat :
    TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat» := by
  apply onFun_le 441 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_sat _ rfl
  · htab_unfold Guest.Software.guestFn_add_sat
    htab_walk
  · htab_bound K.«add_sat»

/-- 20. `add_storage_read` (AST line 13965): loop-free. -/
theorem fb_add_storage_read_of
    (hbal : TerminatingFunBoundedOn GuestInv
      (ofString "bal_ensure_account") K.«bal_ensure_account»)
    (hset : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») :
    TerminatingFunBoundedOn GuestInv (ofString "add_storage_read") K.«add_storage_read» := by
  apply onFun_le 415 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_storage_read _ rfl
  · htab_unfold Guest.Software.guestFn_add_storage_read
    htab_walk
  · htab_bound K.«add_storage_read»

/-- 21. `add_storage_write` (AST line 13942): loop-free. -/
theorem fb_add_storage_write_of
    (hbal : TerminatingFunBoundedOn GuestInv
      (ofString "bal_ensure_account") K.«bal_ensure_account»)
    (hget : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (hset : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (hups : TerminatingFunBoundedOn GuestInv (ofString "lst_upsert_idx") K.«lst_upsert_idx») :
    TerminatingFunBoundedOn GuestInv (ofString "add_storage_write") K.«add_storage_write» := by
  have hlnew := on_lst_new (GuestInv := GuestInv)
  apply onFun_le 414 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_storage_write _ rfl
  · htab_unfold Guest.Software.guestFn_add_storage_write
    htab_walk
  · htab_bound K.«add_storage_write»

/-- 22. `add_to_bloom` (AST line 31915): #0 CTR (`while idx < 6` with step 2). -/
theorem fb_add_to_bloom_of
    (hkeccak : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») :
    TerminatingFunBoundedOn GuestInv (ofString "add_to_bloom") K.«add_to_bloom» := by
  have hm := on_heap_mark (GuestInv := GuestInv)
  have ha := on_alloc (GuestInv := GuestInv)
  have hr := on_heap_release (GuestInv := GuestInv)
  apply onFun_le 831 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_to_bloom _ rfl
  · htab_unfold Guest.Software.guestFn_add_to_bloom
    htab_walk
    refine while_up_signed_guestInv (ofString "idx") 2 (.const (BitVec.ofNat 64 6))
      (straightOn _ rfl) ?_ (by decide) ?_
    · counter_add
    · intro F s v h
      change some (ValueHOL.val (HolWordLab.word (6 : BitVec 64))) =
        some (ValueHOL.val (HolWordLab.word v)) at h
      cases h
      decide
    all_goals htab_walk
  · rw [show K.«add_to_bloom» =
      (K.«heap_mark» + 1) + (K.«alloc» + 1) + (K.«keccak256» + 1) +
        (2 ^ 64 + 1) * (0 + 1) + (K.«heap_release» + 1) from rfl]
    generalize (2 ^ 64 + 1) * (0 + 1) = W, K.«keccak256» = B1, K.«alloc» = B2,
      K.«heap_mark» = B3, K.«heap_release» = B4
    omega

/-- 23. `add_touched_account` (AST line 14039): loop-free. -/
theorem fb_add_touched_account_of
    (hbal : TerminatingFunBoundedOn GuestInv
      (ofString "bal_ensure_account") K.«bal_ensure_account») :
    TerminatingFunBoundedOn GuestInv (ofString "add_touched_account") K.«add_touched_account» := by
  apply onFun_le 419 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_touched_account _ rfl
  · htab_unfold Guest.Software.guestFn_add_touched_account
    htab_walk
  · htab_bound K.«add_touched_account»

/-- 24. `addr_from_words` (AST line 32506): loop-free (`GuestUniformClockBound.funBounded_addr_from_words`). -/
theorem fb_addr_from_words :
    TerminatingFunBoundedOn GuestInv (ofString "addr_from_words") K.«addr_from_words» :=
  funOn funBounded_addr_from_words (by decide)

end InitECandidate.Solver.Wave8GuestInv.S01
