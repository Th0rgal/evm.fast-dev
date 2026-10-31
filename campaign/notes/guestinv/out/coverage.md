functions: 813, reachable from main: 774, loops in reachable: 249, recursive: []

| function | AST line | leaf (guard) | loops: #index depth class N: justification | log2 K |
|---|---|---|---|---|
| `trap_with` | 26 | `fb_trap_with` (GuestInv) | - | 0 |
| `alloc` | 66 | `fb_alloc` (GuestInv) | - | 2 |
| `mpt_fail` | 9769 | `fb_mpt_fail` (GuestInv) | - | 0 |
| `memcpy` | 198 | `fb_memcpy` (GuestInv) | #0 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain; #1 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain; #2 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain; #3 d0 CTR N=2^64: i < L:n, step +1, unconditional | 65 |
| `nibbles_concat` | 9922 | `fb_nibbles_concat` (GuestInv) | - | 66 |
| `node_new_ext` | 10021 | `fb_node_new_ext` (GuestInv) | - | 2 |
| `node_new_leaf` | 9994 | `fb_node_new_leaf` (GuestInv) | - | 2 |
| `_collapse_branch` | 10674 | `fb__collapse_branch` (GuestInv) | #0 d0 CTR N=2^64: i < 16, step +1, unconditional | 66 |
| `memzero` | 251 | `fb_memzero` (GuestInv) | #0 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain; #1 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain; #2 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain; #3 d0 CTR N=2^64: i < L:n, step +1, unconditional | 65 |
| `node_new_branch` | 10046 | `fb_node_new_branch` (GuestInv) | - | 65 |
| `_create_branch_from_two_leaves` | 10507 | `fb__create_branch_from_two_leaves` (GuestInv) | - | 65 |
| `key_to_nibbles` | 9807 | `fb_key_to_nibbles` (GuestInv) | #0 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain; #1 d0 CTR N=2^64: i < L:n, step +1, unconditional | 65 |
| `compact_to_nibbles` | 9849 | `fb_compact_to_nibbles` (GuestInv) | - | 65 |
| `rlp_fail` | 4305 | `fb_rlp_fail` (GuestInv) | - | 0 |
| `rlp_read_length` | 4317 | `fb_rlp_read_length` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 65 |
| `rlp_item_header` | 4432 | `fb_rlp_item_header` (GuestInv) | - | 66 |
| `scratch_alloc` | 154 | `fb_scratch_alloc` (GuestInv) | - | 2 |
| `_rlp_validate_items_body` | 4507 | `fb__rlp_validate_items_body` (GuestInv) | #0 d0 STACK N=2^253: each push calls scratch_alloc(24), which strictly lowers scratch_ptr and cannot wrap (<= 2^61 pushes, arbitrary globals); between pushes the body is read-only, no-repeat key (pos, end, top) | 319 |
| `scratch_mark` | 176 | `fb_scratch_mark` (GuestInv) | - | 0 |
| `scratch_release` | 186 | `fb_scratch_release` (GuestInv) | - | 0 |
| `rlp_validate_items` | 4548 | `fb_rlp_validate_items` (GuestInv) | - | 319 |
| `rlp_item_total` | 4567 | `fb_rlp_item_total` (GuestInv) | - | 319 |
| `rlp_list_count` | 4582 | `fb_rlp_list_count` (GuestInv) | #0 d0 MONO N=2^128: off < len (unsigned); total = hl + pl from rlp_item_header, which returns 1 <= hl + pl <= len - off or raises (rlp_fail); the body writes scratch (_rlp_validate_items_body), so the measure is len - off < 2^64 on the locals, not no-repeat (round 2) | 447 |
| `rlp_item` | 4338 | `fb_rlp_item` (GuestInv) | - | 448 |
| `rlp_decode_fully` | 4417 | `fb_rlp_decode_fully` (GuestInv) | - | 448 |
| `rlp_item_total_unchecked` | 4600 | `fb_rlp_item_total_unchecked` (GuestInv) | - | 66 |
| `rlp_list_to_slices` | 4631 | `fb_rlp_list_to_slices` (GuestInv) | #0 d0 CTR N=2^64: i < L:count, step +1, unconditional | 447 |
| `_decode_step` | 10110 | `fb__decode_step` (GuestInv) | - | 449 |
| `node_new_hashed` | 9975 | `fb_node_new_hashed` (GuestInv) | - | 2 |
| `htab_find_leaf` | 4976 | `fb_htab_find_leaf` (GuestInv) | #0 d0 RO(1) N=2^64: no-repeat, key = carried locals ['n'] (1 word) | 65 |
| `memeq` | 304 | `fb_memeq` (GuestInv) | #0 d0 RO(1) N=2^64: no-repeat, key = carried locals ['i'] (1 word); #1 d0 RO(1) N=2^64: no-repeat, key = carried locals ['i'] (1 word); #2 d0 RO(1) N=2^64: no-repeat, key = carried locals ['i'] (1 word); #3 d0 CTR N=2^64: i < L:n, step +1, unconditional | 67 |
| `htab_get` | 4999 | `fb_htab_get` (GuestInv) | - | 67 |
| `nodedb_lookup` | 9960 | `fb_nodedb_lookup` (GuestInv) | - | 67 |
| `_resolve_step` | 10077 | `fb__resolve_step` (GuestInv) | - | 448 |
| `_decode_witness_node_body` | 10196 | `gb__decode_witness_node_body` (ArenaReady) | #0 d0 GUARD N=2^68: GUARDED (ArenaReady): pushes are scratch_alloc records (<= arena/88), every written object (records, branch nodes, node_new_* results) is a fresh allocation, so the slot counter top+32 < 16 is only written by this loop: <= (pushes + 1) * 64 iterations | 517 |
| `_decode_witness_node_mpt` | 10311 | `gb__decode_witness_node_mpt` (ArenaReady) | - | 517 |
| `_decode_witness_node` | 10328 | `gb__decode_witness_node` (ArenaReady) | - | 517 |
| `_delete_ext_finish` | 10727 | `fb__delete_ext_finish` (GuestInv) | - | 66 |
| `min` | 667 | `fb_min` (GuestInv) | - | 0 |
| `common_prefix_length` | 9903 | `fb_common_prefix_length` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 65 |
| `_insert_into_leaf` | 10532 | `fb__insert_into_leaf` (GuestInv) | - | 67 |
| `node_invalidate` | 10061 | `fb_node_invalidate` (GuestInv) | - | 0 |
| `_mpt_delete_node_body` | 10758 | `gb__mpt_delete_node_body` (MptReady) | #0 d0 GUARD N=2^130: GUARDED (MptReady): descent as in _mpt_insert_node, pushing fresh scratch frames; #1 d0 GUARD N=2^64: GUARDED (MptReady): unwinds the scratch frames pushed by loop #0; frame links are fresh scratch objects disjoint from typed nodes, so each pop strictly shortens the chain | 197 |
| `_mpt_delete_node` | 10852 | `gb__mpt_delete_node` (MptReady) | - | 197 |
| `_split_extension` | 10561 | `fb__split_extension` (GuestInv) | - | 65 |
| `_mpt_insert_node` | 10598 | `gb__mpt_insert_node` (MptReady) | #0 d0 GUARD N=2^130: GUARDED (MptReady): level strictly increases except on empty extension segments (pl = sl = 0); on such a segment node := +48 child; on the self-loop (child = node) node_invalidate and store(slot, node) are idempotent from the second iteration on, which repeats exactly (SameHead, while_rank_stationary with mu = 2 * rank + [not yet stationary]); <= (klen + 1) * 2^65 | 197 |
| `_node_needs_rlp` | 10989 | `fb__node_needs_rlp` (GuestInv) | - | 0 |
| `nibble_list_to_compact` | 9877 | `fb_nibble_list_to_compact` (GuestInv) | #0 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain | 35 |
| `rlp_be_len` | 4698 | `fb_rlp_be_len` (GuestInv) | #0 d0 RO(2) N=2^128: no-repeat, key = carried locals ['n', 'v'] (2 words) | 129 |
| `rlp_header_len` | 4753 | `fb_rlp_header_len` (GuestInv) | - | 129 |
| `rlp_bytes_encoded_len` | 4827 | `fb_rlp_bytes_encoded_len` (GuestInv) | - | 129 |
| `rlp_value_encoded_len` | 11095 | `fb_rlp_value_encoded_len` (GuestInv) | - | 129 |
| `_node_rlp_begin` | 10890 | `fb__node_rlp_begin` (GuestInv) | - | 130 |
| `node_ref_len` | 11110 | `fb_node_ref_len` (GuestInv) | - | 1 |
| `keccak_f1600` | 4038 | `fb_keccak_f1600` (GuestInv) | #0 d0 CTR N=2^64: r < 24, step +1, unconditional | 65 |
| `keccak_absorb_block` | 4239 | `fb_keccak_absorb_block` (GuestInv) | #0 d0 CTR N=2^64: i < 136, step +8, unconditional; #1 d0 CTR N=2^64: i < 136, step +8, unconditional | 66 |
| `keccak256` | 4262 | `fb_keccak256` (GuestInv) | #0 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain | 100 |
| `node_hash_cached` | 11137 | `fb_node_hash_cached` (GuestInv) | - | 100 |
| `node_write_ref` | 11161 | `fb_node_write_ref` (GuestInv) | - | 100 |
| `rlp_put_be` | 4714 | `fb_rlp_put_be` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 65 |
| `rlp_write_header` | 4732 | `fb_rlp_write_header` (GuestInv) | - | 129 |
| `rlp_encode_bytes` | 4768 | `fb_rlp_encode_bytes` (GuestInv) | - | 129 |
| `rlp_encode_list_header` | 4817 | `fb_rlp_encode_list_header` (GuestInv) | - | 129 |
| `rlp_list_header_len` | 4842 | `fb_rlp_list_header_len` (GuestInv) | - | 129 |
| `_node_rlp_finish` | 10930 | `fb__node_rlp_finish` (GuestInv) | #0 d0 CTR N=2^64: i < 16, step +1, unconditional; #1 d0 CTR N=2^64: j < 16, step +1, unconditional | 164 |
| `_node_rlp_fill` | 11011 | `fb__node_rlp_fill` (GuestInv) | #0 d0 ALLOC N=2^62: every iteration either pushes (scratch_alloc(48): scratch_ptr strictly lower) or runs _node_rlp_finish, which allocates its encoding (alloc(n >= 1): heap_ptr strictly higher); callees release only to marks they took themselves; <= 2^64/48 + 2^64/8; #1 d1 RO(3) N=2^192: no-repeat, key = carried locals ['child', 'found', 'i'] (3 words) | 256 |
| `htab_has` | 5022 | `fb_htab_has` (GuestInv) | - | 67 |
| `is_warm_address` | 15473 | `fb_is_warm_address` (GuestInv) | - | 67 |
| `access_gas_cost` | 15496 | `fb_access_gas_cost` (GuestInv) | - | 67 |
| `access_list_payload_len` | 11977 | `fb_access_list_payload_len` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 194 |
| `htab_first_diff` | 4951 | `fb_htab_first_diff` (GuestInv) | #0 d0 CTR N=2^64: i < L:key_len, step +1, unconditional; #1 d1 CTR N=2^64: j < 8, step +1, unconditional | 129 |
| `htab_grow` | 5117 | `fb_htab_grow` (GuestInv) | - | 66 |
| `htab_new_node` | 5041 | `fb_htab_new_node` (GuestInv) | - | 66 |
| `htab_new_internal` | 5097 | `fb_htab_new_internal` (GuestInv) | - | 66 |
| `htab_new_leaf` | 5068 | `fb_htab_new_leaf` (GuestInv) | - | 67 |
| `htab_set` | 5149 | `fb_htab_set` (GuestInv) | #0 d0 RO(2) N=2^128: no-repeat, key = carried locals ['n', 'p'] (2 words) | 130 |
| `record_pre_state_read` | 12980 | `fb_record_pre_state_read` (GuestInv) | - | 130 |
| `decode_account_from_leaf` | 11266 | `fb_decode_account_from_leaf` (GuestInv) | #0 d0 CTR N=2^64: i < rField 2 L:f0, step +1, unconditional; #1 d0 CTR N=2^64: i < rField 2 L:f1, step +1, unconditional | 450 |
| `heap_mark` | 88 | `fb_heap_mark` (GuestInv) | - | 0 |
| `heap_release` | 98 | `fb_heap_release` (GuestInv) | - | 0 |
| `trie_walk` | 10376 | `fb_trie_walk` (GuestInv) | #0 d0 RO(2) N=2^128: no-repeat, key = carried locals ['node', 'pos'] (2 words) | 196 |
| `trie_lookup` | 10432 | `fb_trie_lookup` (GuestInv) | - | 196 |
| `ws_account_leaf` | 12992 | `fb_ws_account_leaf` (GuestInv) | - | 196 |
| `ws_get_account_optional` | 13009 | `fb_ws_get_account_optional` (GuestInv) | - | 450 |
| `ws_storage_root_of` | 13027 | `fb_ws_storage_root_of` (GuestInv) | - | 450 |
| `ws_account_has_storage` | 13119 | `fb_ws_account_has_storage` (GuestInv) | - | 450 |
| `account_has_storage` | 13330 | `fb_account_has_storage` (GuestInv) | - | 450 |
| `acct_new` | 12937 | `fb_acct_new` (GuestInv) | - | 2 |
| `acct_empty` | 12956 | `fb_acct_empty` (GuestInv) | - | 3 |
| `get_pre_state_account_optional` | 13135 | `fb_get_pre_state_account_optional` (GuestInv) | - | 450 |
| `get_account_optional` | 13170 | `fb_get_account_optional` (GuestInv) | - | 450 |
| `get_account` | 13188 | `fb_get_account` (GuestInv) | - | 450 |
| `account_deployable` | 13358 | `fb_account_deployable` (GuestInv) | - | 451 |
| `account_exists` | 13315 | `fb_account_exists` (GuestInv) | - | 450 |
| `acct_copy` | 12967 | `fb_acct_copy` (GuestInv) | - | 65 |
| `u256_is_zero` | 814 | `fb_u256_is_zero` (GuestInv) | - | 0 |
| `acct_is_empty` | 13383 | `fb_acct_is_empty` (GuestInv) | - | 67 |
| `htab_new` | 4867 | `fb_htab_new` (GuestInv) | - | 4 |
| `lst_new` | 13804 | `fb_lst_new` (GuestInv) | - | 3 |
| `bal_ensure_account` | 13883 | `fb_bal_ensure_account` (GuestInv) | - | 130 |
| `lst_push` | 13840 | `fb_lst_push` (GuestInv) | - | 65 |
| `lst_upsert_idx` | 13919 | `fb_lst_upsert_idx` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 66 |
| `add_balance_change` | 13978 | `fb_add_balance_change` (GuestInv) | - | 130 |
| `add_code_change` | 14023 | `fb_add_code_change` (GuestInv) | - | 130 |
| `add_nonce_change` | 13992 | `fb_add_nonce_change` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 130 |
| `add_sat` | 14847 | `fb_add_sat` (GuestInv) | - | 0 |
| `add_storage_read` | 13965 | `fb_add_storage_read` (GuestInv) | - | 131 |
| `add_storage_write` | 13942 | `fb_add_storage_write` (GuestInv) | - | 131 |
| `add_to_bloom` | 31915 | `fb_add_to_bloom` (GuestInv) | #0 d0 CTR N=2^64: idx < 6, step +2, unconditional | 100 |
| `add_touched_account` | 14039 | `fb_add_touched_account` (GuestInv) | - | 130 |
| `st_be32` | 585 | `fb_st_be32` (GuestInv) | - | 0 |
| `bswap64` | 525 | `fb_bswap64` (GuestInv) | - | 0 |
| `st_be64` | 603 | `fb_st_be64` (GuestInv) | - | 2 |
| `addr_from_words` | 32506 | `fb_addr_from_words` (GuestInv) | - | 4 |
| `u256_from_be` | 2213 | `fb_u256_from_be` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 65 |
| `address_to_u256` | 14906 | `fb_address_to_u256` (GuestInv) | - | 65 |
| `udivmod` | 695 | `fb_udivmod` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 65 |
| `udiv` | 727 | `fb_udiv` (GuestInv) | - | 65 |
| `check_gas_limit` | 9590 | `fb_check_gas_limit` (GuestInv) | - | 65 |
| `bal_init` | 13863 | `fb_bal_init` (GuestInv) | - | 6 |
| `htab_keys` | 5332 | `fb_htab_keys` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 129 |
| `rlp_encode_word` | 4790 | `fb_rlp_encode_word` (GuestInv) | - | 129 |
| `bit_length64` | 1919 | `fb_bit_length64` (GuestInv) | - | 0 |
| `u256_bit_length` | 1966 | `fb_u256_bit_length` (GuestInv) | - | 3 |
| `u256_byte_length` | 1991 | `fb_u256_byte_length` (GuestInv) | - | 3 |
| `u256_limb` | 828 | `fb_u256_limb` (GuestInv) | - | 0 |
| `u256_to_be_min` | 2302 | `fb_u256_to_be_min` (GuestInv) | #0 d0 CTR N=2^64: i < L:len, step +1, unconditional | 66 |
| `rlp_put_u256` | 9334 | `fb_rlp_put_u256` (GuestInv) | - | 129 |
| `bal_sort_gt` | 14327 | `fb_bal_sort_gt` (GuestInv) | #0 d0 CTR N=2^64: k < L:len, step +1, unconditional | 65 |
| `sort_elems` | 14364 | `fb_sort_elems` (GuestInv) | #0 d0 MONO N=65: width doubles 1,2,..,2^63,0; width = 2^63 exits after one inner pass, width = 0 makes the inner loop time out (WhileTimesOut, while_rank_stationary); at most 65 iterations; #1 d1 MONO N=2^64: for 1 <= width < n (signed) mid/right are capped at n with unsigned compares and do not wrap, so left strictly increases to n (mu = n - left); width = 0 gives mid = right = left, the merge loops do not run, left := right: the loop head repeats exactly (SameHead, while_rank_stationary); #2 d2 MONO N=2^65: each iteration increments exactly one of i < mid, j < right (signed, no overflow): measure (mid - i) + (right - j); #3 d2 CTR N=2^64: i < L:mid, step +1, unconditional; #4 d2 CTR N=2^64: j < L:right, step +1, unconditional | 201 |
| `sorted_keys32` | 14442 | `fb_sorted_keys32` (GuestInv) | - | 201 |
| `bal_encode_account` | 14455 | `fb_bal_encode_account` (GuestInv) | #0 d0 CTR N=2^64: i < rField 1 L:slots, step +1, unconditional; #1 d1 CTR N=2^64: j < L:n, step +1, unconditional; #2 d0 CTR N=2^64: i < rField 1 L:rk, step +1, unconditional; #3 d0 CTR N=2^64: i < L:kept, step +1, unconditional; #4 d0 CTR N=2^64: i < L:n2, step +1, unconditional; #5 d0 CTR N=2^64: i < L:n3, step +1, unconditional; #6 d0 CTR N=2^64: i < L:n4, step +1, unconditional | 265 |
| `htab_item` | 5314 | `fb_htab_item` (GuestInv) | - | 0 |
| `build_block_access_list_rlp` | 14685 | `fb_build_block_access_list_rlp` (GuestInv) | #0 d0 CTR N=2^64: i < L:cap, step +1, unconditional; #1 d0 CTR N=2^64: i < L:cap, step +1, unconditional; #2 d0 CTR N=2^64: i < rField 1 L:addrs, step +1, unconditional; #3 d1 CTR N=2^64: j < L:scap, step +1, unconditional; #4 d1 CTR N=2^64: j < L:cn, step +1, unconditional; #5 d0 CTR N=2^64: i < rField 1 L:addrs, step +1, unconditional | 329 |
| `mpt_new` | 10444 | `fb_mpt_new` (GuestInv) | - | 2 |
| `node_rlp` | 11074 | `fb_node_rlp` (GuestInv) | - | 256 |
| `node_hash` | 11202 | `fb_node_hash` (GuestInv) | - | 256 |
| `mpt_root` | 11223 | `fb_mpt_root` (GuestInv) | - | 256 |
| `mpt_nibble_key` | 10470 | `fb_mpt_nibble_key` (GuestInv) | - | 100 |
| `mpt_set` | 10872 | `gb_mpt_set` (MptObjReady) | - | 197 |
| `build_mpt_indexed` | 11243 | `gb_build_mpt_indexed` (WorldOK) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 261 |
| `sha256_block` | 2367 | `fb_sha256_block` (GuestInv) | - | 0 |
| `sha256_finish` | 2898 | `fb_sha256_finish` (GuestInv) | #0 d0 CTR N=2^64: i < 8, step +1, unconditional | 66 |
| `sha256_state_init` | 2341 | `fb_sha256_state_init` (GuestInv) | - | 0 |
| `sha256` | 2914 | `fb_sha256` (GuestInv) | #0 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain | 67 |
| `compute_requests_hash` | 32190 | `fb_compute_requests_hash` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 131 |
| `cache_get_root` | 32325 | `fb_cache_get_root` (GuestInv) | - | 450 |
| `encode_account` | 11343 | `fb_encode_account` (GuestInv) | #0 d0 CTR N=32: z < 32, step +1, unconditional | 131 |
| `htab_copy` | 5354 | `fb_htab_copy` (GuestInv) | - | 67 |
| `decode_witness_to_mpt` | 10348 | `gb_decode_witness_to_mpt` (ArenaReady) | - | 517 |
| `mpt_from_witness` | 10459 | `gb_mpt_from_witness` (ArenaReady) | - | 517 |
| `compute_state_root` | 32341 | `gb_compute_state_root` (WorldOK) | #0 d0 CTR N=2^64: i < L:cap, step +1, unconditional; #1 d1 CTR N=2^64: pass < 2, step +1, unconditional; #2 d2 CTR N=2^64: j < L:icount, step +1, unconditional; #3 d0 CTR N=2^64: i < L:cap, step +1, unconditional; #4 d0 CTR N=2^64: i < L:acap, step +1, unconditional | 581 |
| `tx_fixed_bytes` | 11468 | `fb_tx_fixed_bytes` (GuestInv) | - | 448 |
| `tx_list_item` | 11510 | `fb_tx_list_item` (GuestInv) | - | 448 |
| `decode_access_list` | 11525 | `fb_decode_access_list` (GuestInv) | #0 d0 CTR N=2^64: i < rField 1 L:lst, step +1, unconditional; #1 d1 CTR N=2^64: j < rField 1 L:slots, step +1, unconditional | 576 |
| `tx_scalar_item` | 11389 | `fb_tx_scalar_item` (GuestInv) | - | 448 |
| `tx_scalar_u256` | 11416 | `fb_tx_scalar_u256` (GuestInv) | - | 448 |
| `tx_scalar_word` | 11431 | `fb_tx_scalar_word` (GuestInv) | #0 d0 CTR N=2^64: j < rField 1 L:f, step +1, unconditional | 448 |
| `decode_authorizations` | 11588 | `fb_decode_authorizations` (GuestInv) | #0 d0 CTR N=2^64: i < rField 1 L:lst, step +1, unconditional | 514 |
| `decode_blob_hashes` | 11569 | `fb_decode_blob_hashes` (GuestInv) | #0 d0 CTR N=2^64: i < rField 1 L:lst, step +1, unconditional | 512 |
| `tx_bytes_item` | 11453 | `fb_tx_bytes_item` (GuestInv) | - | 448 |
| `tx_to_item` | 11487 | `fb_tx_to_item` (GuestInv) | - | 448 |
| `decode_transaction_rlp` | 11634 | `fb_decode_transaction_rlp` (GuestInv) | - | 576 |
| `decode_transaction` | 11805 | `fb_decode_transaction` (GuestInv) | - | 576 |
| `logs_bloom` | 31941 | `fb_logs_bloom` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional; #1 d1 CTR N=2^64: j < L:nt, step +1, unconditional | 228 |
| `max` | 681 | `fb_max` (GuestInv) | - | 0 |
| `is_zero_bytes` | 477 | `fb_is_zero_bytes` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 65 |
| `ld_be64` | 539 | `fb_ld_be64` (GuestInv) | - | 1 |
| `extract_deposit_data` | 32212 | `fb_extract_deposit_data` (GuestInv) | - | 69 |
| `sk_make` | 12923 | `fb_sk_make` (GuestInv) | - | 66 |
| `ws_get_code` | 13099 | `fb_ws_get_code` (GuestInv) | - | 68 |
| `get_code` | 13203 | `fb_get_code` (GuestInv) | - | 130 |
| `ext_code_of` | 16953 | `fb_ext_code_of` (GuestInv) | - | 450 |
| `frame_mem_release` | 142 | `fb_frame_mem_release` (GuestInv) | - | 0 |
| `htab_union_into` | 13711 | `fb_htab_union_into` (GuestInv) | #0 d0 CTR N=2^64: i < L:cap, step +1, unconditional | 194 |
| `merge_tx_into_block` | 13731 | `fb_merge_tx_into_block` (GuestInv) | #0 d0 CTR N=2^64: i < L:cap, step +1, unconditional | 258 |
| `bal_list_remove_idx` | 14163 | `fb_bal_list_remove_idx` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 129 |
| `bal_remove_change` | 14189 | `fb_bal_remove_change` (GuestInv) | - | 129 |
| `get_pre_tx_account` | 14051 | `fb_get_pre_tx_account` (GuestInv) | - | 450 |
| `st_le32` | 553 | `fb_st_le32` (GuestInv) | - | 0 |
| `st_le64` | 571 | `fb_st_le64` (GuestInv) | - | 2 |
| `idx_start_account` | 14087 | `fb_idx_start_account` (GuestInv) | - | 450 |
| `stor_lookup` | 13233 | `fb_stor_lookup` (GuestInv) | - | 68 |
| `ws_storage_trie` | 13042 | `gb_ws_storage_trie` (WorldOK) | - | 517 |
| `ws_get_storage` | 13061 | `gb_ws_get_storage` (WorldOK) | - | 517 |
| `get_pre_tx_storage` | 14069 | `gb_get_pre_tx_storage` (WorldOK) | - | 517 |
| `idx_start_storage` | 14129 | `gb_idx_start_storage` (WorldOK) | - | 517 |
| `htab_del` | 5217 | `fb_htab_del` (GuestInv) | - | 67 |
| `remove_storage_write` | 14206 | `fb_remove_storage_write` (GuestInv) | - | 129 |
| `u256_eq` | 869 | `fb_u256_eq` (GuestInv) | - | 0 |
| `update_builder_from_tx` | 14233 | `gb_update_builder_from_tx` (WorldOK) | #0 d0 CTR N=2^64: i < L:cap, step +1, unconditional; #1 d0 CTR N=2^64: i < L:cap, step +1, unconditional; #2 d1 CTR N=2^64: j < L:icap, step +1, unconditional | 645 |
| `incorporate_tx_into_block` | 14313 | `gb_incorporate_tx_into_block` (WorldOK) | - | 645 |
| `msg_new` | 15344 | `fb_msg_new` (GuestInv) | - | 65 |
| `frame_state_gas_used` | 15018 | `fb_frame_state_gas_used` (GuestInv) | - | 0 |
| `charge_gas` | 14949 | `fb_charge_gas` (GuestInv) | - | 0 |
| `charge_state_gas` | 14968 | `fb_charge_state_gas` (GuestInv) | - | 1 |
| `jset` | 12825 | `fb_jset` (GuestInv) | - | 130 |
| `jdel` | 12857 | `fb_jdel` (GuestInv) | - | 68 |
| `destroy_storage` | 13480 | `fb_destroy_storage` (GuestInv) | #0 d0 CTR N=2^64: i < L:cap, step +1, unconditional | 194 |
| `set_account` | 13439 | `fb_set_account` (GuestInv) | - | 130 |
| `destroy_account` | 13510 | `fb_destroy_account` (GuestInv) | - | 194 |
| `modify_state_commit` | 13524 | `fb_modify_state_commit` (GuestInv) | - | 194 |
| `set_code` | 13681 | `fb_set_code` (GuestInv) | - | 450 |
| `ceil32` | 14862 | `fb_ceil32` (GuestInv) | - | 1 |
| `words_of` | 14878 | `fb_words_of` (GuestInv) | - | 2 |
| `create_finish` | 18867 | `fb_create_finish` (GuestInv) | - | 450 |
| `frame_halt` | 18756 | `fb_frame_halt` (GuestInv) | - | 0 |
| `increment_nonce` | 13664 | `fb_increment_nonce` (GuestInv) | - | 450 |
| `mark_account_created` | 13562 | `fb_mark_account_created` (GuestInv) | - | 130 |
| `compute_jumpdests` | 15279 | `fb_compute_jumpdests` (GuestInv) | #0 d0 WALK N=2^34: pc strictly increases by adv in [1, 33] and every iteration loads code + pc: fresh address in the contiguous ordinaryDomain | 65 |
| `is_valid_delegation` | 14917 | `fb_is_valid_delegation` (GuestInv) | - | 0 |
| `get_delegated_code_address` | 17610 | `fb_get_delegated_code_address` (GuestInv) | - | 1 |
| `get_pre_state_account` | 13155 | `fb_get_pre_state_account` (GuestInv) | - | 450 |
| `is_account_alive` | 13419 | `fb_is_account_alive` (GuestInv) | - | 450 |
| `warm_address` | 15484 | `fb_warm_address` (GuestInv) | - | 130 |
| `prepare_dispatch` | 17836 | `fb_prepare_dispatch` (GuestInv) | - | 452 |
| `ec_set_infinity` | 6984 | `fb_ec_set_infinity` (GuestInv) | - | 0 |
| `u256_add_carry` | 1039 | `fb_u256_add_carry` (GuestInv) | - | 0 |
| `u256_lt` | 883 | `fb_u256_lt` (GuestInv) | - | 0 |
| `u256_sub` | 1083 | `fb_u256_sub` (GuestInv) | - | 0 |
| `fp_add` | 5427 | `fb_fp_add` (GuestInv) | - | 3 |
| `fp_reduce` | 5479 | `fb_fp_reduce` (GuestInv) | - | 2 |
| `u256_add` | 1061 | `fb_u256_add` (GuestInv) | - | 0 |
| `fp_mul` | 5494 | `fb_fp_mul` (GuestInv) | - | 3 |
| `fp_sqr` | 6163 | `fb_fp_sqr` (GuestInv) | - | 3 |
| `fp_sub` | 5448 | `fb_fp_sub` (GuestInv) | - | 2 |
| `ec_double` | 7027 | `fb_ec_double` (GuestInv) | - | 7 |
| `ec_set_affine` | 7000 | `fb_ec_set_affine` (GuestInv) | - | 0 |
| `ec_add_affine` | 7086 | `fb_ec_add_affine` (GuestInv) | - | 8 |
| `ec_is_infinity` | 7016 | `fb_ec_is_infinity` (GuestInv) | - | 1 |
| `mod_half` | 6866 | `fb_mod_half` (GuestInv) | - | 1 |
| `mod_sub` | 6881 | `fb_mod_sub` (GuestInv) | - | 2 |
| `modinv_bin` | 6815 | `fb_modinv_bin` (GuestInv) | #0 d0 MONO N=2^256: binary gcd: mu = bitlen(odd part of u) + bitlen(odd part of v) <= 512 drops by >= 1 per iteration (u, v odd after the halving loops, so u - v (resp. v - u) is even and its odd part is < u (resp. v)); u - v = 0 makes the next halving loop time out (WhileTimesOut, while_rank_stationary); #1 d1 MONO N=2^128: u != 0: mu = trailing zeros of u <= 255 drops by one; u = 0: u stays 0 and the body (shifts, mod_half = straight-line u256 arithmetic, always returns) cannot leave the loop, so the loop times out (WhileTimesOut, while_rank_stationary); #2 d1 MONO N=2^128: as #1 with v, x2 | 387 |
| `fp_inv` | 6897 | `fb_fp_inv` (GuestInv) | - | 387 |
| `ec_to_affine` | 7308 | `fb_ec_to_affine` (GuestInv) | - | 387 |
| `u256_bit` | 854 | `fb_u256_bit` (GuestInv) | - | 1 |
| `ec_mul2` | 7257 | `fb_ec_mul2` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 387 |
| `fn_inv` | 6974 | `fb_fn_inv` (GuestInv) | - | 387 |
| `digits_len` | 1566 | `fb_digits_len` (GuestInv) | #0 d0 CTR N=2^64: n > 0 (or != 0), step -1, unconditional | 65 |
| `digits_to_u256` | 1556 | `fb_digits_to_u256` (GuestInv) | - | 0 |
| `div64by32` | 1506 | `fb_div64by32` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 65 |
| `nlz32` | 1467 | `fb_nlz32` (GuestInv) | - | 0 |
| `divmnu` | 1583 | `fb_divmnu` (GuestInv) | #0 d0 CTR N=2^64: j > 0 (or != 0), step -1, unconditional; #1 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional; #2 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional; #3 d0 CTR N=2^64: j > 0 (or != 0), step -1, unconditional; #4 d1 RO(3) N=2^192: no-repeat, key = carried locals ['again', 'qhat', 'rhat'] (3 words); #5 d1 CTR N=2^64: i < L:n, step +1, unconditional; #6 d1 CTR N=2^64: i < L:n, step +1, unconditional; #7 d0 CTR N=2^64: j < L:m, step +1, unconditional; #8 d0 CTR N=2^64: i < L:n, step +1, unconditional | 257 |
| `u256_to_digits` | 1530 | `fb_u256_to_digits` (GuestInv) | - | 0 |
| `digits_divmod` | 1718 | `fb_digits_divmod` (GuestInv) | #0 d0 CTR N=16: i < 16, step +1, unconditional; #1 d0 CTR N=8: i < 8, step +1, unconditional | 257 |
| `mul64x64` | 1127 | `fb_mul64x64` (GuestInv) | - | 0 |
| `u256_divmod` | 1754 | `fb_u256_divmod` (GuestInv) | - | 257 |
| `u256_mod` | 1794 | `fb_u256_mod` (GuestInv) | - | 257 |
| `u256_mul_full` | 1230 | `fb_u256_mul_full` (GuestInv) | - | 5 |
| `u256_mulmod` | 1888 | `fb_u256_mulmod` (GuestInv) | - | 258 |
| `fn_mul` | 6917 | `fb_fn_mul` (GuestInv) | - | 258 |
| `fp_neg` | 5464 | `fb_fp_neg` (GuestInv) | - | 2 |
| `fp_pow` | 6778 | `fb_fp_pow` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 68 |
| `fp_sqrt` | 6907 | `fb_fp_sqrt` (GuestInv) | - | 68 |
| `secp256k1_decompress_r` | 7351 | `fb_secp256k1_decompress_r` (GuestInv) | - | 68 |
| `u256_to_be32` | 2265 | `fb_u256_to_be32` (GuestInv) | - | 5 |
| `secp256k1_recover` | 7395 | `fb_secp256k1_recover` (GuestInv) | - | 389 |
| `u256_gt` | 921 | `fb_u256_gt` (GuestInv) | - | 1 |
| `recover_authority` | 17625 | `fb_recover_authority` (GuestInv) | - | 389 |
| `u256_fits_word` | 800 | `fb_u256_fits_word` (GuestInv) | - | 0 |
| `validate_authorization_checks` | 17717 | `fb_validate_authorization_checks` (GuestInv) | - | 450 |
| `set_delegation` | 17740 | `fb_set_delegation` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 516 |
| `depth0_prepare` | 18772 | `fb_depth0_prepare` (GuestInv) | - | 516 |
| `frame_mem_alloc` | 110 | `fb_frame_mem_alloc` (GuestInv) | - | 2 |
| `frame_mem_mark` | 132 | `fb_frame_mem_mark` (GuestInv) | - | 0 |
| `htab_count` | 5294 | `fb_htab_count` (GuestInv) | - | 0 |
| `htab_new_scratch` | 4909 | `fb_htab_new_scratch` (GuestInv) | - | 4 |
| `lst_new_scratch` | 13822 | `fb_lst_new_scratch` (GuestInv) | - | 3 |
| `frame_new` | 15370 | `fb_frame_new` (GuestInv) | - | 66 |
| `frame_open` | 18450 | `fb_frame_open` (GuestInv) | - | 66 |
| `refill_frame_state_gas` | 15029 | `fb_refill_frame_state_gas` (GuestInv) | - | 0 |
| `frame_exception` | 18477 | `fb_frame_exception` (GuestInv) | - | 2 |
| `log_append` | 16486 | `fb_log_append` (GuestInv) | - | 65 |
| `emit_transfer_log` | 17459 | `fb_emit_transfer_log` (GuestInv) | - | 67 |
| `move_ether` | 13597 | `fb_move_ether` (GuestInv) | - | 451 |
| `precompile_index` | 31482 | `fb_precompile_index` (GuestInv) | - | 65 |
| `fq_mul` | 22338 | `fb_fq_mul` (GuestInv) | - | 2 |
| `fq_from_mont` | 23320 | `fb_fq_from_mont` (GuestInv) | - | 2 |
| `fq_inv` | 23330 | `fb_fq_inv` (GuestInv) | - | 387 |
| `bn254_g1_to_bytes` | 24508 | `fb_bn254_g1_to_bytes` (GuestInv) | - | 387 |
| `fe_set_one` | 23653 | `fb_fe_set_one` (GuestInv) | - | 65 |
| `fe_set_zero` | 23641 | `fb_fe_set_zero` (GuestInv) | - | 65 |
| `ecp_set_inf` | 23667 | `fb_ecp_set_inf` (GuestInv) | - | 66 |
| `fq_add` | 22291 | `fb_fq_add` (GuestInv) | - | 2 |
| `fq_to_mont` | 23310 | `fb_fq_to_mont` (GuestInv) | - | 2 |
| `bn254_parse_g1` | 24385 | `fb_bn254_parse_g1` (GuestInv) | - | 67 |
| `fq_mul_small` | 23341 | `fb_fq_mul_small` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 68 |
| `fq_sub` | 22307 | `fb_fq_sub` (GuestInv) | - | 2 |
| `fq12_reduce` | 23386 | `fb_fq12_reduce` (GuestInv) | #0 d0 CTR N=2^64: e > 0 (or != 0), step -1, unconditional | 133 |
| `fq12_mul` | 23413 | `fb_fq12_mul` (GuestInv) | #0 d0 CTR N=23: k < 23, step +1, unconditional; #1 d1 CTR N=2^128: iend >= i (unsigned notLower), i := i + 1 unconditional, iend <= 11 loop-invariant (capped before the loop): mu = iend + 1 - i <= 12 | 136 |
| `fq2_mul` | 23362 | `fb_fq2_mul` (GuestInv) | - | 5 |
| `fe_mul` | 23502 | `fb_fe_mul` (GuestInv) | - | 136 |
| `fe_mul_small` | 23603 | `fb_fe_mul_small` (GuestInv) | #0 d0 CTR N=2^64: i < L:fld, step +1, unconditional | 132 |
| `fq12_sqr` | 23456 | `fb_fq12_sqr` (GuestInv) | #0 d0 CTR N=23: k < 23, step +1, unconditional; #1 d1 CTR N=2^128: i < k - i (unsigned), i := i + 1 unconditional, k <= 22 loop-invariant: mu = k - 2 i <= 22 | 136 |
| `fe_sqr` | 23529 | `fb_fe_sqr` (GuestInv) | - | 137 |
| `fe_sub` | 23566 | `fb_fe_sub` (GuestInv) | #0 d0 CTR N=2^64: i < L:fld, step +1, unconditional | 67 |
| `ecp_double` | 23694 | `fb_ecp_double` (GuestInv) | - | 140 |
| `fe_eq` | 23631 | `fb_fe_eq` (GuestInv) | - | 67 |
| `fe_is_zero` | 23621 | `fb_fe_is_zero` (GuestInv) | - | 65 |
| `ecp_add` | 23764 | `fb_ecp_add` (GuestInv) | - | 141 |
| `bn254_g1_add` | 24541 | `fb_bn254_g1_add` (GuestInv) | - | 387 |
| `buffer_read` | 15256 | `fb_buffer_read` (GuestInv) | - | 66 |
| `pre_alt_bn128_add` | 24699 | `fb_pre_alt_bn128_add` (GuestInv) | - | 387 |
| `ecp_mul` | 23874 | `fb_ecp_mul` (GuestInv) | #0 d0 CTR N=2^64: i < L:len, step +1, unconditional | 206 |
| `bn254_g1_mul` | 24574 | `fb_bn254_g1_mul` (GuestInv) | - | 387 |
| `pre_alt_bn128_mul` | 24728 | `fb_pre_alt_bn128_mul` (GuestInv) | - | 387 |
| `bn254_init` | 22161 | `fb_bn254_init` (GuestInv) | - | 3 |
| `ecp_linefunc` | 23910 | `fb_ecp_linefunc` (GuestInv) | - | 140 |
| `fq_neg` | 22323 | `fb_fq_neg` (GuestInv) | - | 2 |
| `fe_neg` | 23585 | `fb_fe_neg` (GuestInv) | #0 d0 CTR N=2^64: i < L:fld, step +1, unconditional | 67 |
| `fq12_frob` | 24051 | `fb_fq12_frob` (GuestInv) | #0 d0 CTR N=6: k < 6, step +1, unconditional | 71 |
| `bn254_miller_raw` | 24253 | `fb_bn254_miller_raw` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 207 |
| `fe_add` | 23547 | `fb_fe_add` (GuestInv) | #0 d0 CTR N=2^64: i < L:fld, step +1, unconditional | 67 |
| `bn254_parse_g2` | 24436 | `fb_bn254_parse_g2` (GuestInv) | - | 69 |
| `ecp_is_inf` | 23684 | `fb_ecp_is_inf` (GuestInv) | - | 65 |
| `fq12_cast` | 24033 | `fb_fq12_cast` (GuestInv) | - | 65 |
| `fq_poly_deg` | 24084 | `fb_fq_poly_deg` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 129 |
| `fq_poly_submul` | 24103 | `fb_fq_poly_submul` (GuestInv) | #0 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain | 38 |
| `fq12_inv` | 24124 | `fb_fq12_inv` (GuestInv) | #0 d0 MONO N=14: Euclid on degree <= 12 polynomials: deg r1 strictly decreases, or the inner loop #1 times out (zero leading inverse), so this iteration times out (WhileTimesOut, while_rank_stationary); #1 d1 MONO N=14: while_rank_stationary with mu = (if linv = 0 then 0 else d0 - d1) + phase at the active inner head (d0 = deg r0, d1 = deg r1 >= 1 inside the outer loop, so d0 - d1 <= 11); phase = 2 if r0[d0] < p or r0[d0] mod p != 0, 1 if r0[d0] >= p, r0[d0] mod p = 0 and q[d0 - d1] != 0, 0 otherwise. fq_mul always returns < p and fq_mul(k p, linv) = 0 for 1 <= k <= 5, so every continuing iteration strictly lowers mu or is an exact repeat (SameHead: noncanonical lead r + p, period-1 state, ISSUES.md on wave8/leaves-arith-astra), and an inner SameHead makes the outer iteration WhileTimesOut; mu <= 11 + 2 = 13 <= 14; #2 d1 CTR N=13: j < 13, step +1, unconditional; #3 d0 CTR N=12: i < 12, step +1, unconditional | 391 |
| `fq12_pow_words` | 24225 | `fb_fq12_pow_words` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 201 |
| `fq12_twist` | 23999 | `fb_fq12_twist` (GuestInv) | #0 d0 CTR N=3: j < 3, step +1, unconditional | 70 |
| `bn254_pairing_check` | 24600 | `fb_bn254_pairing_check` (GuestInv) | #0 d0 CTR N=2^64: i < L:n_pairs, step +1, unconditional | 391 |
| `pre_alt_bn128_pairing_check` | 24757 | `fb_pre_alt_bn128_pairing_check` (GuestInv) | - | 391 |
| `blake2_g` | 20073 | `fb_blake2_g` (GuestInv) | - | 0 |
| `blake2b_f` | 20115 | `fb_blake2b_f` (GuestInv) | #0 d0 CTR N=2^64: r < L:rounds, step +1, unconditional; #1 d0 CTR N=2^64: i < 8, step +1, unconditional | 68 |
| `pre_blake2f` | 31632 | `fb_pre_blake2f` (GuestInv) | #0 d0 CTR N=2^64: i < 8, step +1, unconditional; #1 d0 CTR N=2^64: i < 16, step +1, unconditional; #2 d0 CTR N=2^64: i < 8, step +1, unconditional | 69 |
| `bls_fp_add_raw` | 26675 | `fb_bls_fp_add_raw` (GuestInv) | - | 0 |
| `bls_fp_sub_raw` | 26703 | `fb_bls_fp_sub_raw` (GuestInv) | - | 0 |
| `bls_fp_add` | 26731 | `fb_bls_fp_add` (GuestInv) | - | 2 |
| `bls_fp_eq` | 26607 | `fb_bls_fp_eq` (GuestInv) | - | 0 |
| `bls_fp_is_zero` | 26593 | `fb_bls_fp_is_zero` (GuestInv) | - | 0 |
| `bls_fp_mul` | 26791 | `fb_bls_fp_mul` (GuestInv) | - | 7 |
| `bls_fp_sqr` | 27550 | `fb_bls_fp_sqr` (GuestInv) | - | 7 |
| `bls_fp_sub` | 26748 | `fb_bls_fp_sub` (GuestInv) | - | 2 |
| `g1_copy` | 28655 | `fb_g1_copy` (GuestInv) | - | 65 |
| `g1_double` | 28689 | `fb_g1_double` (GuestInv) | - | 10 |
| `g1_set_inf` | 28628 | `fb_g1_set_inf` (GuestInv) | - | 0 |
| `g1_add` | 28747 | `fb_g1_add` (GuestInv) | - | 66 |
| `bls_fp_from_be48` | 27719 | `fb_bls_fp_from_be48` (GuestInv) | - | 0 |
| `bls_fp_lt_raw` | 26621 | `fb_bls_fp_lt_raw` (GuestInv) | - | 0 |
| `bls_fp_to_mont` | 27560 | `fb_bls_fp_to_mont` (GuestInv) | - | 7 |
| `bls_fp_decode64` | 27751 | `fb_bls_fp_decode64` (GuestInv) | - | 65 |
| `g1_on_curve` | 28884 | `fb_g1_on_curve` (GuestInv) | - | 8 |
| `g1_decode` | 28901 | `fb_g1_decode` (GuestInv) | - | 66 |
| `bls_fp_from_mont` | 27570 | `fb_bls_fp_from_mont` (GuestInv) | - | 7 |
| `bls_fp_to_be48` | 27729 | `fb_bls_fp_to_be48` (GuestInv) | - | 5 |
| `bls_fp_encode64` | 27775 | `fb_bls_fp_encode64` (GuestInv) | - | 65 |
| `bls_fp_shr1` | 27580 | `fb_bls_fp_shr1` (GuestInv) | - | 0 |
| `bls_fp_half_can` | 27590 | `fb_bls_fp_half_can` (GuestInv) | - | 2 |
| `bls_fp_inv_raw` | 27605 | `fb_bls_fp_inv_raw` (GuestInv) | #0 d0 MONO N=2^256: as modinv_bin #0 on 384-bit values: mu <= 768; #1 d1 MONO N=2^128: as modinv_bin #1 on 384-bit values: trailing zeros <= 383, or u = 0 and the loop times out (bls_fp_shr1, bls_fp_half_can are straight-line arithmetic); #2 d1 MONO N=2^128: as #1 with v, x2 | 388 |
| `bls_fp_inv` | 27658 | `fb_bls_fp_inv` (GuestInv) | - | 388 |
| `g1_normalize` | 28861 | `fb_g1_normalize` (GuestInv) | - | 388 |
| `g1_encode` | 28933 | `fb_g1_encode` (GuestInv) | - | 388 |
| `bls_g1_add_exec` | 30340 | `fb_bls_g1_add_exec` (GuestInv) | - | 388 |
| `pre_bls_g1_add` | 31236 | `fb_pre_bls_g1_add` (GuestInv) | - | 388 |
| `bls_g1_msm_discount` | 31208 | `fb_bls_g1_msm_discount` (GuestInv) | - | 0 |
| `g1_mul` | 28824 | `fb_g1_mul` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 130 |
| `g1_is_inf` | 28644 | `fb_g1_is_inf` (GuestInv) | - | 1 |
| `g1_subgroup_check` | 28953 | `fb_g1_subgroup_check` (GuestInv) | - | 130 |
| `bls_g1_msm_exec` | 30370 | `fb_bls_g1_msm_exec` (GuestInv) | #0 d0 CTR N=2^64: i < L:k, step +1, unconditional | 388 |
| `pre_bls_g1_msm` | 31264 | `fb_pre_bls_g1_msm` (GuestInv) | - | 388 |
| `fp2_add` | 27864 | `fb_fp2_add` (GuestInv) | - | 3 |
| `fp2_copy` | 27791 | `fb_fp2_copy` (GuestInv) | - | 65 |
| `fp2_eq` | 27845 | `fb_fp2_eq` (GuestInv) | - | 2 |
| `fp2_mul` | 27949 | `fb_fp2_mul` (GuestInv) | - | 8 |
| `fp2_sqr` | 27977 | `fb_fp2_sqr` (GuestInv) | - | 8 |
| `fp2_sub` | 27884 | `fb_fp2_sub` (GuestInv) | - | 3 |
| `g2_copy` | 28996 | `fb_g2_copy` (GuestInv) | - | 65 |
| `g2_double` | 29026 | `fb_g2_double` (GuestInv) | - | 66 |
| `fp2_is_zero` | 27829 | `fb_fp2_is_zero` (GuestInv) | - | 0 |
| `g2_is_inf` | 28986 | `fb_g2_is_inf` (GuestInv) | - | 1 |
| `fp2_set_one` | 27815 | `fb_fp2_set_one` (GuestInv) | - | 0 |
| `fp2_set_zero` | 27803 | `fb_fp2_set_zero` (GuestInv) | - | 65 |
| `g2_set_inf` | 28970 | `fb_g2_set_inf` (GuestInv) | - | 65 |
| `g2_add` | 29109 | `fb_g2_add` (GuestInv) | - | 68 |
| `g2_on_curve` | 29276 | `fb_g2_on_curve` (GuestInv) | - | 10 |
| `g2_decode` | 29300 | `fb_g2_decode` (GuestInv) | - | 67 |
| `bls_fp_neg` | 26765 | `fb_bls_fp_neg` (GuestInv) | - | 2 |
| `fp2_inv` | 28035 | `fb_fp2_inv` (GuestInv) | - | 388 |
| `g2_normalize` | 29247 | `fb_g2_normalize` (GuestInv) | - | 388 |
| `g2_encode` | 29343 | `fb_g2_encode` (GuestInv) | - | 388 |
| `bls_g2_add_exec` | 30416 | `fb_bls_g2_add_exec` (GuestInv) | - | 388 |
| `pre_bls_g2_add` | 31300 | `fb_pre_bls_g2_add` (GuestInv) | - | 388 |
| `bls_g2_msm_discount` | 31222 | `fb_bls_g2_msm_discount` (GuestInv) | - | 0 |
| `g2_mul` | 29213 | `fb_g2_mul` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 132 |
| `g2_subgroup_check` | 29367 | `fb_g2_subgroup_check` (GuestInv) | - | 132 |
| `bls_g2_msm_exec` | 30446 | `fb_bls_g2_msm_exec` (GuestInv) | #0 d0 CTR N=2^64: i < L:k, step +1, unconditional | 388 |
| `pre_bls_g2_msm` | 31328 | `fb_pre_bls_g2_msm` (GuestInv) | - | 388 |
| `iso_horner_fp2` | 30055 | `fb_iso_horner_fp2` (GuestInv) | #0 d0 CTR N=2^64: j < sub[L:n, 1], step +1, unconditional | 73 |
| `iso_map_g2` | 30084 | `fb_iso_map_g2` (GuestInv) | - | 75 |
| `fp2_neg` | 27904 | `fb_fp2_neg` (GuestInv) | - | 3 |
| `bls_fp_sgn0` | 27696 | `fb_bls_fp_sgn0` (GuestInv) | - | 7 |
| `fp2_sgn0` | 28096 | `fb_fp2_sgn0` (GuestInv) | - | 8 |
| `fp2_pow` | 28059 | `fb_fp2_pow` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 73 |
| `swu_sqrt_division_fp2` | 29879 | `fb_swu_sqrt_division_fp2` (GuestInv) | #0 d0 CTR N=6: i < 6, step +1, unconditional; #1 d0 CTR N=4: i < 4, step +1, unconditional | 73 |
| `swu_g2` | 29940 | `fb_swu_g2` (GuestInv) | #0 d0 CTR N=4: i < 4, step +1, unconditional | 73 |
| `map_fp2_to_g2` | 30128 | `fb_map_fp2_to_g2` (GuestInv) | - | 132 |
| `bls_map_fp2_to_g2_exec` | 30581 | `fb_bls_map_fp2_to_g2_exec` (GuestInv) | - | 388 |
| `pre_bls_map_fp2_to_g2` | 31426 | `fb_pre_bls_map_fp2_to_g2` (GuestInv) | - | 388 |
| `iso_horner_fp` | 29789 | `fb_iso_horner_fp` (GuestInv) | #0 d0 CTR N=2^64: j < sub[L:n, 1], step +1, unconditional | 72 |
| `iso_map_g1` | 29812 | `fb_iso_map_g1` (GuestInv) | #0 d0 CTR N=15: j < 15, step +1, unconditional | 74 |
| `bls_fp_pow` | 27669 | `fb_bls_fp_pow` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 72 |
| `swu_sqrt_division_fp` | 29697 | `fb_swu_sqrt_division_fp` (GuestInv) | - | 72 |
| `swu_g1` | 29719 | `fb_swu_g1` (GuestInv) | - | 72 |
| `map_fp_to_g1` | 29859 | `fb_map_fp_to_g1` (GuestInv) | - | 130 |
| `bls_map_fp_to_g1_exec` | 30554 | `fb_bls_map_fp_to_g1_exec` (GuestInv) | - | 388 |
| `pre_bls_map_fp_to_g1` | 31398 | `fb_pre_bls_map_fp_to_g1` (GuestInv) | - | 388 |
| `fp6_copy` | 28118 | `fb_fp6_copy` (GuestInv) | - | 65 |
| `fp6_neg` | 28190 | `fb_fp6_neg` (GuestInv) | - | 5 |
| `fp12_conj` | 28429 | `fb_fp12_conj` (GuestInv) | - | 65 |
| `fp12_copy` | 28339 | `fb_fp12_copy` (GuestInv) | - | 65 |
| `fp6_add` | 28158 | `fb_fp6_add` (GuestInv) | - | 5 |
| `fp2_mul_xi` | 27999 | `fb_fp2_mul_xi` (GuestInv) | - | 3 |
| `fp6_mul` | 28206 | `fb_fp6_mul` (GuestInv) | - | 12 |
| `fp6_mul_v` | 28255 | `fb_fp6_mul_v` (GuestInv) | - | 66 |
| `fp6_sub` | 28174 | `fb_fp6_sub` (GuestInv) | - | 5 |
| `fp12_mul` | 28382 | `fb_fp12_mul` (GuestInv) | - | 66 |
| `fp6_set_one` | 28142 | `fb_fp6_set_one` (GuestInv) | - | 66 |
| `fp6_set_zero` | 28130 | `fb_fp6_set_zero` (GuestInv) | - | 65 |
| `fp12_set_one` | 28351 | `fb_fp12_set_one` (GuestInv) | - | 66 |
| `fp12_pow_absx` | 28508 | `fb_fp12_pow_absx` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 131 |
| `fp12_exp_x` | 28545 | `fb_fp12_exp_x` (GuestInv) | - | 131 |
| `fp2_conj` | 27932 | `fb_fp2_conj` (GuestInv) | - | 2 |
| `fp12_frob` | 28476 | `fb_fp12_frob` (GuestInv) | - | 11 |
| `fp6_inv` | 28277 | `fb_fp6_inv` (GuestInv) | - | 388 |
| `fp12_inv` | 28443 | `fb_fp12_inv` (GuestInv) | - | 388 |
| `fp12_final_exp` | 28559 | `fb_fp12_final_exp` (GuestInv) | - | 388 |
| `fp12_is_one` | 28365 | `fb_fp12_is_one` (GuestInv) | - | 67 |
| `pair_addition_step` | 29484 | `fb_pair_addition_step` (GuestInv) | - | 65 |
| `pair_doubling_step` | 29384 | `fb_pair_doubling_step` (GuestInv) | - | 65 |
| `fp2_scale` | 28017 | `fb_fp2_scale` (GuestInv) | - | 8 |
| `pair_ell` | 29595 | `fb_pair_ell` (GuestInv) | - | 67 |
| `pair_miller_loop` | 29619 | `fb_pair_miller_loop` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 132 |
| `pair_accumulate` | 29661 | `fb_pair_accumulate` (GuestInv) | - | 389 |
| `bls_pairing_exec` | 30492 | `fb_bls_pairing_exec` (GuestInv) | #0 d0 CTR N=2^64: i < L:k, step +1, unconditional | 453 |
| `pre_bls_pairing` | 31364 | `fb_pre_bls_pairing` (GuestInv) | - | 453 |
| `secp256k1_address_of_point` | 7465 | `fb_secp256k1_address_of_point` (GuestInv) | - | 100 |
| `secp256k1_ecrecover` | 7483 | `fb_secp256k1_ecrecover` (GuestInv) | - | 389 |
| `pre_ecrecover` | 31556 | `fb_pre_ecrecover` (GuestInv) | - | 389 |
| `pre_identity` | 31515 | `fb_pre_identity` (GuestInv) | - | 3 |
| `bls_fp_is_high` | 27707 | `fb_bls_fp_is_high` (GuestInv) | - | 7 |
| `kzg_decompress_g1` | 30148 | `fb_kzg_decompress_g1` (GuestInv) | - | 72 |
| `kzg_load_g1` | 30216 | `fb_kzg_load_g1` (GuestInv) | - | 130 |
| `g2_neg` | 29008 | `fb_g2_neg` (GuestInv) | - | 66 |
| `kzg_neg_scalar` | 30245 | `fb_kzg_neg_scalar` (GuestInv) | - | 65 |
| `kzg_verify` | 30267 | `fb_kzg_verify` (GuestInv) | - | 390 |
| `kzg_point_evaluation_exec` | 30611 | `fb_kzg_point_evaluation_exec` (GuestInv) | - | 390 |
| `pre_kzg_point_evaluation` | 31454 | `fb_pre_kzg_point_evaluation` (GuestInv) | - | 390 |
| `be_top_bit` | 20407 | `fb_be_top_bit` (GuestInv) | #0 d0 CTR N=2^64: i < L:nbytes, step +1, unconditional | 66 |
| `bn_from_be` | 20170 | `fb_bn_from_be` (GuestInv) | #0 d0 CTR N=2^64: i < L:nd, step +1, unconditional; #1 d0 CTR N=2^64: i < L:nbytes, step +1, unconditional | 66 |
| `bn_divmnu` | 20253 | `fb_bn_divmnu` (GuestInv) | #0 d0 CTR N=2^64: j > 0 (or != 0), step -1, unconditional; #1 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional; #2 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional; #3 d0 CTR N=2^64: j > 0 (or != 0), step -1, unconditional; #4 d1 RO(3) N=2^192: no-repeat, key = carried locals ['again', 'qhat', 'rhat'] (3 words); #5 d1 CTR N=2^64: i < L:n, step +1, unconditional; #6 d1 CTR N=2^64: i < L:n, step +1, unconditional; #7 d0 CTR N=2^64: j < L:m, step +1, unconditional; #8 d0 CTR N=2^64: i < L:n, step +1, unconditional | 257 |
| `bn_mod` | 20386 | `fb_bn_mod` (GuestInv) | - | 257 |
| `bn_mul` | 20218 | `fb_bn_mul` (GuestInv) | #0 d0 CTR N=2^64: i < add[L:na, L:nb], step +1, unconditional; #1 d0 CTR N=2^64: i < L:na, step +1, unconditional; #2 d1 CTR N=2^64: j < L:nb, step +1, unconditional | 129 |
| `bn_to_be` | 20196 | `fb_bn_to_be` (GuestInv) | #0 d0 CTR N=2^64: i < L:nbytes, step +1, unconditional | 65 |
| `modexp` | 20427 | `fb_modexp` (GuestInv) | #0 d0 CTR N=2^64: t > 0 (or != 0), step -1, unconditional | 322 |
| `modexp_gas` | 31689 | `fb_modexp_gas` (GuestInv) | - | 3 |
| `sat_word` | 14833 | `fb_sat_word` (GuestInv) | - | 0 |
| `pre_modexp` | 31725 | `fb_pre_modexp` (GuestInv) | - | 322 |
| `p256_fp_add` | 20490 | `fb_p256_fp_add` (GuestInv) | - | 3 |
| `p256_fp_reduce` | 20527 | `fb_p256_fp_reduce` (GuestInv) | - | 2 |
| `p256_fp_mul` | 20542 | `fb_p256_fp_mul` (GuestInv) | #0 d0 MONO N=2^128: c < 0 (signed), r := r + P, c := c + carry: P > 2^255, so of two consecutive iterations at least one carries; mu = 2 (-c) + [r < 2^256 - P] <= 2^65; #1 d0 MONO N=2^128: 0 < c (signed), c := c - [r < P], r := r - P: r >= P is followed by r - P < P; mu = 2 c + [r >= P] <= 2^64 | 131 |
| `p256_fp_sqr` | 21184 | `fb_p256_fp_sqr` (GuestInv) | #0 d0 MONO N=2^128: as p256_fp_mul #0; #1 d0 MONO N=2^128: as p256_fp_mul #1 | 131 |
| `p256_fp_sub` | 20511 | `fb_p256_fp_sub` (GuestInv) | - | 2 |
| `p256_set_infinity` | 21782 | `fb_p256_set_infinity` (GuestInv) | - | 0 |
| `p256_ec_double` | 21814 | `fb_p256_ec_double` (GuestInv) | - | 134 |
| `p256_set_affine` | 21798 | `fb_p256_set_affine` (GuestInv) | - | 0 |
| `p256_ec_add_affine` | 21880 | `fb_p256_ec_add_affine` (GuestInv) | - | 135 |
| `p256_ec_mul2` | 21944 | `fb_p256_ec_mul2` (GuestInv) | #0 d0 CTR N=2^64: i > 0 (or != 0), step -1, unconditional | 200 |
| `p256_on_curve` | 22001 | `fb_p256_on_curve` (GuestInv) | - | 132 |
| `p256_verify` | 22022 | `fb_p256_verify` (GuestInv) | - | 387 |
| `pre_p256verify` | 22115 | `fb_pre_p256verify` (GuestInv) | - | 387 |
| `rmd_f` | 19800 | `fb_rmd_f` (GuestInv) | - | 0 |
| `rmd_k` | 19826 | `fb_rmd_k` (GuestInv) | - | 0 |
| `rmd_kp` | 19852 | `fb_rmd_kp` (GuestInv) | - | 0 |
| `ripemd160_block` | 19878 | `fb_ripemd160_block` (GuestInv) | #0 d0 CTR N=2^64: i < 16, step +1, unconditional; #1 d0 CTR N=2^64: j < 80, step +1, unconditional | 67 |
| `ripemd160` | 19955 | `fb_ripemd160` (GuestInv) | #0 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain; #1 d0 CTR N=2^64: i < 5, step +1, unconditional | 102 |
| `pre_ripemd160` | 31608 | `fb_pre_ripemd160` (GuestInv) | - | 102 |
| `pre_sha256` | 31534 | `fb_pre_sha256` (GuestInv) | - | 67 |
| `run_precompile` | 31795 | `fb_run_precompile` (GuestInv) | - | 453 |
| `frame_prologue` | 18499 | `fb_frame_prologue` (GuestInv) | - | 453 |
| `frame_start` | 18539 | `fb_frame_start` (GuestInv) | - | 453 |
| `credit_state_gas_refund` | 15000 | `fb_credit_state_gas_refund` (GuestInv) | - | 1 |
| `incorporate_child_on_error` | 18941 | `fb_incorporate_child_on_error` (GuestInv) | - | 0 |
| `incorporate_child_on_success` | 18957 | `fb_incorporate_child_on_success` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 194 |
| `pc_add` | 15437 | `fb_pc_add` (GuestInv) | - | 0 |
| `htab_truncate` | 5278 | `gb_htab_truncate` (HtabArgWF) | #0 d0 WF N=2^64: GUARDED (HtabArgWF), while_rank_stationary with mu = count t+24 < 2^64: each iteration calls htab_del on the key of the last leaf; it either deletes a leaf (count drops by one: htab_del_progress_spec; HtabArgWF kept: htab_del_spec) or returns 0 having written nothing (find_leaf may reach another leaf and memeq reject it: HtabWF does not constrain key bytes), and then the loop head repeats exactly (SameHead) | 131 |
| `rollback_child_access` | 18995 | `gb_rollback_child_access` (RollbackReady) | - | 132 |
| `set_retdata` | 19064 | `fb_set_retdata` (GuestInv) | - | 65 |
| `stack_push` | 15065 | `fb_stack_push` (GuestInv) | - | 65 |
| `state_restore` | 12903 | `fb_state_restore` (GuestInv) | #0 d0 GCTR N=2^64: journal_n > L:snap (or != 0), step -1, unconditional | 194 |
| `finish_child` | 18572 | `gb_finish_child` (FinishReady) | - | 450 |
| `frame_epilogue` | 18558 | `fb_frame_epilogue` (GuestInv) | - | 194 |
| `stack_pop` | 15046 | `fb_stack_pop` (GuestInv) | - | 0 |
| `op_add` | 15525 | `fb_op_add` (GuestInv) | - | 65 |
| `u256_addmod` | 1861 | `fb_u256_addmod` (GuestInv) | - | 258 |
| `op_addmod` | 15658 | `fb_op_addmod` (GuestInv) | - | 258 |
| `op_address` | 16734 | `fb_op_address` (GuestInv) | - | 66 |
| `op_and` | 15851 | `fb_op_and` (GuestInv) | - | 65 |
| `to_address_masked` | 14889 | `fb_to_address_masked` (GuestInv) | - | 4 |
| `warm_after_charge` | 15511 | `fb_warm_after_charge` (GuestInv) | - | 130 |
| `op_balance` | 16751 | `fb_op_balance` (GuestInv) | - | 450 |
| `block_env` | 17115 | `fb_block_env` (GuestInv) | - | 0 |
| `op_basefee` | 17125 | `fb_op_basefee` (GuestInv) | - | 65 |
| `u256_div` | 1783 | `fb_u256_div` (GuestInv) | - | 257 |
| `u256_from_word` | 780 | `fb_u256_from_word` (GuestInv) | - | 0 |
| `u256_mul` | 1150 | `fb_u256_mul` (GuestInv) | - | 3 |
| `taylor_exponential` | 9511 | `fb_taylor_exponential` (GuestInv) | #0 d0 MONO N=2^64: i := i + 1 each iteration from 1; i < 2^64 for the first 2^64 - 1 iterations; when i wraps to 0, di = 0 and u256_div(p, 0) = 0 makes acc = 0, so the loop exits | 321 |
| `calculate_blob_gas_price` | 9550 | `fb_calculate_blob_gas_price` (GuestInv) | - | 321 |
| `op_blobbasefee` | 17165 | `fb_op_blobbasefee` (GuestInv) | - | 321 |
| `op_blobhash` | 17142 | `fb_op_blobhash` (GuestInv) | - | 66 |
| `track_ancestor_access` | 13771 | `fb_track_ancestor_access` (GuestInv) | - | 0 |
| `op_blockhash` | 17183 | `fb_op_blockhash` (GuestInv) | - | 66 |
| `stack_push_word` | 15103 | `fb_stack_push_word` (GuestInv) | - | 65 |
| `u256_byte` | 2197 | `fb_u256_byte` (GuestInv) | - | 1 |
| `op_byte` | 15922 | `fb_op_byte` (GuestInv) | - | 65 |
| `calculate_delegation_cost` | 17693 | `fb_calculate_delegation_cost` (GuestInv) | - | 450 |
| `calculate_message_call_gas` | 19328 | `fb_calculate_message_call_gas` (GuestInv) | - | 3 |
| `extend_memory` | 15206 | `fb_extend_memory` (GuestInv) | - | 66 |
| `memory_gas_cost` | 15129 | `fb_memory_gas_cost` (GuestInv) | - | 3 |
| `extend_memory_cost1` | 15146 | `fb_extend_memory_cost1` (GuestInv) | - | 5 |
| `extend_memory_cost2` | 15181 | `fb_extend_memory_cost2` (GuestInv) | - | 6 |
| `msg_new_scratch` | 15357 | `fb_msg_new_scratch` (GuestInv) | - | 65 |
| `child_message` | 19009 | `fb_child_message` (GuestInv) | - | 65 |
| `state_snapshot` | 12893 | `fb_state_snapshot` (GuestInv) | - | 0 |
| `start_child` | 18703 | `fb_start_child` (GuestInv) | - | 453 |
| `generic_call` | 19294 | `fb_generic_call` (GuestInv) | - | 453 |
| `op_call` | 19358 | `fb_op_call` (GuestInv) | - | 454 |
| `op_callcode` | 19457 | `fb_op_callcode` (GuestInv) | - | 454 |
| `copy_from_buffer` | 16866 | `fb_copy_from_buffer` (GuestInv) | - | 67 |
| `op_calldatacopy` | 16895 | `fb_op_calldatacopy` (GuestInv) | - | 67 |
| `op_calldataload` | 16824 | `fb_op_calldataload` (GuestInv) | - | 67 |
| `op_calldatasize` | 16850 | `fb_op_calldatasize` (GuestInv) | - | 65 |
| `op_caller` | 16791 | `fb_op_caller` (GuestInv) | - | 66 |
| `op_callvalue` | 16808 | `fb_op_callvalue` (GuestInv) | - | 65 |
| `op_chainid` | 17289 | `fb_op_chainid` (GuestInv) | - | 65 |
| `op_clz` | 16002 | `fb_op_clz` (GuestInv) | - | 65 |
| `op_codecopy` | 16924 | `fb_op_codecopy` (GuestInv) | - | 67 |
| `op_codesize` | 16908 | `fb_op_codesize` (GuestInv) | - | 65 |
| `op_coinbase` | 17220 | `fb_op_coinbase` (GuestInv) | - | 66 |
| `compute_contract_address` | 19098 | `fb_compute_contract_address` (GuestInv) | - | 131 |
| `generic_create` | 19156 | `fb_generic_create` (GuestInv) | - | 454 |
| `require_not_static` | 15459 | `fb_require_not_static` (GuestInv) | - | 0 |
| `op_create` | 19223 | `fb_op_create` (GuestInv) | - | 454 |
| `compute_create2_contract_address` | 19129 | `fb_compute_create2_contract_address` (GuestInv) | - | 101 |
| `op_create2` | 19257 | `fb_op_create2` (GuestInv) | - | 454 |
| `op_delegatecall` | 19539 | `fb_op_delegatecall` (GuestInv) | - | 454 |
| `op_div` | 15582 | `fb_op_div` (GuestInv) | - | 257 |
| `op_dup` | 16308 | `fb_op_dup` (GuestInv) | - | 65 |
| `code_imm` | 16370 | `fb_code_imm` (GuestInv) | - | 0 |
| `decode_single` | 16385 | `fb_decode_single` (GuestInv) | - | 0 |
| `op_dupn` | 16401 | `fb_op_dupn` (GuestInv) | - | 65 |
| `stack_push_bool` | 15115 | `fb_stack_push_bool` (GuestInv) | - | 65 |
| `op_eq` | 15814 | `fb_op_eq` (GuestInv) | - | 65 |
| `stack_swap_positions` | 16330 | `fb_stack_swap_positions` (GuestInv) | - | 0 |
| `op_exchange` | 16447 | `fb_op_exchange` (GuestInv) | - | 3 |
| `u256_exp` | 2002 | `fb_u256_exp` (GuestInv) | #0 d0 CTR N=2^64: t < L:len, step +1, unconditional | 69 |
| `op_exp` | 15698 | `fb_op_exp` (GuestInv) | - | 69 |
| `op_extcodecopy` | 16987 | `fb_op_extcodecopy` (GuestInv) | - | 450 |
| `op_extcodehash` | 17072 | `fb_op_extcodehash` (GuestInv) | - | 450 |
| `op_extcodesize` | 16965 | `fb_op_extcodesize` (GuestInv) | - | 450 |
| `op_gas` | 16130 | `fb_op_gas` (GuestInv) | - | 65 |
| `op_gaslimit` | 17272 | `fb_op_gaslimit` (GuestInv) | - | 65 |
| `op_gasprice` | 16936 | `fb_op_gasprice` (GuestInv) | - | 65 |
| `op_gt` | 15757 | `fb_op_gt` (GuestInv) | - | 65 |
| `op_iszero` | 15833 | `fb_op_iszero` (GuestInv) | - | 65 |
| `is_valid_jumpdest` | 15324 | `fb_is_valid_jumpdest` (GuestInv) | - | 0 |
| `op_jump` | 16066 | `fb_op_jump` (GuestInv) | - | 2 |
| `op_jumpdest` | 16146 | `fb_op_jumpdest` (GuestInv) | - | 2 |
| `op_jumpi` | 16086 | `fb_op_jumpi` (GuestInv) | - | 3 |
| `op_keccak` | 16020 | `fb_op_keccak` (GuestInv) | - | 100 |
| `op_log` | 16499 | `fb_op_log` (GuestInv) | #0 d0 CTR N=2^64: i < L:ntopics, step +1, unconditional | 69 |
| `op_lt` | 15738 | `fb_op_lt` (GuestInv) | - | 65 |
| `op_mcopy` | 16233 | `fb_op_mcopy` (GuestInv) | - | 67 |
| `charge_with_memory` | 15240 | `fb_charge_with_memory` (GuestInv) | - | 66 |
| `op_mload` | 16198 | `fb_op_mload` (GuestInv) | - | 67 |
| `op_mod` | 15620 | `fb_op_mod` (GuestInv) | - | 257 |
| `op_msize` | 16217 | `fb_op_msize` (GuestInv) | - | 65 |
| `op_mstore` | 16160 | `fb_op_mstore` (GuestInv) | - | 66 |
| `op_mstore8` | 16179 | `fb_op_mstore8` (GuestInv) | - | 66 |
| `op_mul` | 15544 | `fb_op_mul` (GuestInv) | - | 65 |
| `op_mulmod` | 15678 | `fb_op_mulmod` (GuestInv) | - | 258 |
| `op_not` | 15905 | `fb_op_not` (GuestInv) | - | 65 |
| `op_number` | 17255 | `fb_op_number` (GuestInv) | - | 65 |
| `op_or` | 15869 | `fb_op_or` (GuestInv) | - | 65 |
| `op_origin` | 16773 | `fb_op_origin` (GuestInv) | - | 66 |
| `op_pc` | 16114 | `fb_op_pc` (GuestInv) | - | 65 |
| `op_pop` | 16268 | `fb_op_pop` (GuestInv) | - | 2 |
| `op_prevrandao` | 17306 | `fb_op_prevrandao` (GuestInv) | - | 66 |
| `op_push` | 16283 | `fb_op_push` (GuestInv) | - | 67 |
| `op_return` | 17501 | `fb_op_return` (GuestInv) | - | 66 |
| `op_returndatacopy` | 17038 | `fb_op_returndatacopy` (GuestInv) | - | 66 |
| `op_returndatasize` | 17022 | `fb_op_returndatasize` (GuestInv) | - | 65 |
| `op_revert` | 17526 | `fb_op_revert` (GuestInv) | - | 66 |
| `u256_or` | 1019 | `fb_u256_or` (GuestInv) | - | 0 |
| `u256_shl` | 2028 | `fb_u256_shl` (GuestInv) | - | 0 |
| `u256_shr` | 2088 | `fb_u256_shr` (GuestInv) | - | 0 |
| `u256_sar` | 2148 | `fb_u256_sar` (GuestInv) | - | 2 |
| `op_sar` | 15982 | `fb_op_sar` (GuestInv) | - | 65 |
| `u256_neg` | 1105 | `fb_u256_neg` (GuestInv) | - | 0 |
| `u256_abs` | 1805 | `fb_u256_abs` (GuestInv) | - | 1 |
| `u256_sdiv` | 1819 | `fb_u256_sdiv` (GuestInv) | - | 257 |
| `op_sdiv` | 15601 | `fb_op_sdiv` (GuestInv) | - | 257 |
| `op_selfbalance` | 17098 | `fb_op_selfbalance` (GuestInv) | - | 450 |
| `op_selfdestruct` | 17551 | `fb_op_selfdestruct` (GuestInv) | - | 452 |
| `u256_slt` | 931 | `fb_u256_slt` (GuestInv) | - | 0 |
| `u256_sgt` | 969 | `fb_u256_sgt` (GuestInv) | - | 1 |
| `op_sgt` | 15795 | `fb_op_sgt` (GuestInv) | - | 65 |
| `op_shl` | 15942 | `fb_op_shl` (GuestInv) | - | 65 |
| `op_shr` | 15962 | `fb_op_shr` (GuestInv) | - | 65 |
| `u256_and` | 1009 | `fb_u256_and` (GuestInv) | - | 0 |
| `u256_not` | 999 | `fb_u256_not` (GuestInv) | - | 0 |
| `u256_signextend` | 2175 | `fb_u256_signextend` (GuestInv) | - | 3 |
| `op_signextend` | 15718 | `fb_op_signextend` (GuestInv) | - | 65 |
| `get_storage` | 13249 | `gb_get_storage` (WorldOK) | - | 517 |
| `is_warm_storage_key` | 16559 | `fb_is_warm_storage_key` (GuestInv) | - | 67 |
| `warm_storage_key` | 16571 | `fb_warm_storage_key` (GuestInv) | - | 130 |
| `op_sload` | 16584 | `gb_op_sload` (EvmRun) | - | 517 |
| `op_slotnum` | 17324 | `fb_op_slotnum` (GuestInv) | - | 65 |
| `op_slt` | 15776 | `fb_op_slt` (GuestInv) | - | 65 |
| `u256_smod` | 1840 | `fb_u256_smod` (GuestInv) | - | 257 |
| `op_smod` | 15639 | `fb_op_smod` (GuestInv) | - | 257 |
| `check_gas` | 14935 | `fb_check_gas` (GuestInv) | - | 0 |
| `get_storage_original` | 13276 | `gb_get_storage_original` (WorldOK) | - | 517 |
| `set_storage` | 13451 | `fb_set_storage` (GuestInv) | - | 450 |
| `op_sstore` | 16611 | `gb_op_sstore` (EvmRun) | - | 518 |
| `op_staticcall` | 19600 | `fb_op_staticcall` (GuestInv) | - | 454 |
| `op_stop` | 16052 | `fb_op_stop` (GuestInv) | - | 1 |
| `op_sub` | 15563 | `fb_op_sub` (GuestInv) | - | 65 |
| `op_swap` | 16350 | `fb_op_swap` (GuestInv) | - | 2 |
| `op_swapn` | 16425 | `fb_op_swapn` (GuestInv) | - | 3 |
| `op_timestamp` | 17238 | `fb_op_timestamp` (GuestInv) | - | 65 |
| `get_transient_storage` | 13299 | `fb_get_transient_storage` (GuestInv) | - | 67 |
| `op_tload` | 16688 | `fb_op_tload` (GuestInv) | - | 68 |
| `set_transient_storage` | 13574 | `fb_set_transient_storage` (GuestInv) | - | 130 |
| `op_tstore` | 16710 | `fb_op_tstore` (GuestInv) | - | 130 |
| `op_xor` | 15887 | `fb_op_xor` (GuestInv) | - | 65 |
| `op_dispatch` | 17902 | `gb_op_dispatch` (EvmRun) | - | 519 |
| `run_frames` | 18663 | `gb_run_frames` (EvmInv) | #0 d0 POT N=2^172: EVM frame potential evmPot < N_POT under EvmInv (section 6) | 691 |
| `process_message` | 18803 | `gb_process_message` (MsgReady) | - | 691 |
| `process_create_message` | 18899 | `gb_process_create_message` (MsgReady) | - | 691 |
| `process_message_call` | 19661 | `gb_process_message_call` (MsgReady) | - | 691 |
| `state_fresh_tx` | 12778 | `fb_state_fresh_tx` (GuestInv) | - | 7 |
| `te_new` | 32838 | `fb_te_new` (GuestInv) | - | 65 |
| `process_unchecked_system_transaction` | 32851 | `gb_process_unchecked_system_transaction` (WorldOK) | - | 691 |
| `process_checked_system_transaction` | 32928 | `gb_process_checked_system_transaction` (WorldOK) | - | 691 |
| `requests_append` | 33485 | `fb_requests_append` (GuestInv) | - | 65 |
| `process_general_purpose_requests` | 33507 | `gb_process_general_purpose_requests` (ReqsFresh) | #0 d0 CTR N=2^64: i < L:nr, step +1, unconditional; #1 d1 CTR N=2^64: j < L:nl, step +1, unconditional | 693 |
| `calculate_total_blob_gas` | 11914 | `fb_calculate_total_blob_gas` (GuestInv) | - | 0 |
| `fee_mul` | 32778 | `fb_fee_mul` (GuestInv) | - | 5 |
| `check_transaction` | 32951 | `fb_check_transaction` (GuestInv) | #0 d0 CTR N=2^64: j < L:nb, step +1, unconditional | 450 |
| `clear_account_preserving_balance` | 13541 | `fb_clear_account_preserving_balance` (GuestInv) | - | 450 |
| `create_ether` | 13629 | `fb_create_ether` (GuestInv) | - | 450 |
| `rlp_finish_list` | 31969 | `fb_rlp_finish_list` (GuestInv) | - | 130 |
| `encode_logs` | 32005 | `fb_encode_logs` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional; #1 d1 CTR N=2^64: j < L:nt, step +1, unconditional | 257 |
| `logs_encoded_bound` | 31985 | `fb_logs_encoded_bound` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 65 |
| `encode_receipt` | 32051 | `fb_encode_receipt` (GuestInv) | - | 257 |
| `rlp_word_encoded_len` | 4852 | `fb_rlp_word_encoded_len` (GuestInv) | - | 129 |
| `tx_u256_encoded_len` | 11940 | `fb_tx_u256_encoded_len` (GuestInv) | - | 3 |
| `auth_payload_len` | 12060 | `fb_auth_payload_len` (GuestInv) | - | 130 |
| `auth_list_payload_len` | 12075 | `fb_auth_list_payload_len` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 194 |
| `tx_encode_bound` | 12141 | `fb_tx_encode_bound` (GuestInv) | - | 195 |
| `tx_put_access_list` | 11998 | `fb_tx_put_access_list` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional; #1 d1 CTR N=2^64: j < L:ns, step +1, unconditional | 257 |
| `tx_put_u256` | 11924 | `fb_tx_put_u256` (GuestInv) | - | 129 |
| `tx_put_authorizations` | 12094 | `fb_tx_put_authorizations` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 196 |
| `tx_put_blob_hashes` | 12040 | `fb_tx_put_blob_hashes` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 193 |
| `tx_put_to` | 11961 | `fb_tx_put_to` (GuestInv) | - | 129 |
| `tx_encode_generic` | 12154 | `fb_tx_encode_generic` (GuestInv) | - | 257 |
| `encode_transaction` | 12267 | `fb_encode_transaction` (GuestInv) | - | 257 |
| `tx_signing_hash_mode` | 12289 | `fb_tx_signing_hash_mode` (GuestInv) | - | 257 |
| `signing_hash_155` | 12315 | `fb_signing_hash_155` (GuestInv) | - | 257 |
| `signing_hash_1559` | 12335 | `fb_signing_hash_1559` (GuestInv) | - | 257 |
| `signing_hash_2930` | 12325 | `fb_signing_hash_2930` (GuestInv) | - | 257 |
| `signing_hash_4844` | 12345 | `fb_signing_hash_4844` (GuestInv) | - | 257 |
| `signing_hash_7702` | 12355 | `fb_signing_hash_7702` (GuestInv) | - | 257 |
| `signing_hash_pre155` | 12305 | `fb_signing_hash_pre155` (GuestInv) | - | 257 |
| `signature_recovery_parameters` | 12399 | `fb_signature_recovery_parameters` (GuestInv) | - | 259 |
| `recover_transaction_public_key` | 12483 | `fb_recover_transaction_public_key` (GuestInv) | - | 389 |
| `sender_address_from_public_key` | 12503 | `fb_sender_address_from_public_key` (GuestInv) | - | 100 |
| `recover_sender_with_chain_id` | 12542 | `fb_recover_sender_with_chain_id` (GuestInv) | - | 389 |
| `set_account_balance` | 13647 | `fb_set_account_balance` (GuestInv) | - | 450 |
| `tx_chain_id` | 12365 | `fb_tx_chain_id` (GuestInv) | - | 3 |
| `tx_has_access_list` | 11890 | `fb_tx_has_access_list` (GuestInv) | - | 0 |
| `tx_is_blob` | 32750 | `fb_tx_is_blob` (GuestInv) | - | 0 |
| `tx_is_setcode` | 32764 | `fb_tx_is_setcode` (GuestInv) | - | 0 |
| `udiv_small5` | 33447 | `fb_udiv_small5` (GuestInv) | - | 65 |
| `count_tokens_in_data` | 12562 | `fb_count_tokens_in_data` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 65 |
| `calculate_intrinsic_cost` | 12581 | `fb_calculate_intrinsic_cost` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 67 |
| `validate_transaction` | 12639 | `fb_validate_transaction` (GuestInv) | - | 67 |
| `process_transaction` | 33103 | `gb_process_transaction` (TxReady) | #0 d0 CTR N=2^64: i < L:nal, step +1, unconditional; #1 d0 CTR N=2^64: i < L:nal, step +1, unconditional; #2 d1 CTR N=2^64: j < L:ns, step +1, unconditional; #3 d0 CTR N=2^64: i < 18, step +1, unconditional; #4 d0 CTR N=2^64: i < add[L:nal, 1], step +1, unconditional; #5 d0 CTR N=2^64: i < L:nkeys, step +1, unconditional; #6 d0 CTR N=2^64: i < L:nl, step +1, unconditional; #7 d0 CTR N=2^64: i < L:nl, step +1, unconditional; #8 d0 CTR N=2^64: i < L:dcap, step +1, unconditional | 691 |
| `process_withdrawals` | 33458 | `gb_process_withdrawals` (WorldOK) | #0 d0 CTR N=2^64: i < L:nwd, step +1, unconditional | 645 |
| `validate_block_access_list_gas_limit` | 14776 | `fb_validate_block_access_list_gas_limit` (GuestInv) | #0 d0 CTR N=2^64: i < L:cap, step +1, unconditional; #1 d1 CTR N=2^64: j < L:rcap, step +1, unconditional | 195 |
| `execute_block` | 33580 | `gb_execute_block` (BlockReady) | #0 d0 CTR N=2^64: i < L:ntx, step +1, unconditional | 755 |
| `encode_header` | 9350 | `fb_encode_header` (GuestInv) | - | 133 |
| `header_hash` | 9460 | `fb_header_hash` (GuestInv) | - | 133 |
| `is_valid_versioned_hashes` | 32794 | `fb_is_valid_versioned_hashes` (GuestInv) | #0 d0 CTR N=2^64: i < L:ntx, step +1, unconditional; #1 d1 CTR N=2^64: j < L:nb, step +1, unconditional | 640 |
| `nodedb_build` | 9937 | `fb_nodedb_build` (GuestInv) | #0 d0 RO(1) N=2^64: no-repeat, key = carried locals ['cap'] (1 word); #1 d0 CTR N=2^64: i < L:n, step +1, unconditional | 194 |
| `withdrawal_rlp_len` | 32099 | `fb_withdrawal_rlp_len` (GuestInv) | - | 131 |
| `block_rlp_length` | 32586 | `fb_block_rlp_length` (GuestInv) | #0 d0 CTR N=2^64: i < L:ntx, step +1, unconditional; #1 d0 CTR N=2^64: i < L:nwd, step +1, unconditional | 195 |
| `encode_execution_requests` | 32142 | `fb_encode_execution_requests` (GuestInv) | #0 d0 CTR N=2^64: i < 5, step +1, unconditional | 129 |
| `encode_withdrawal_rlp` | 32114 | `fb_encode_withdrawal_rlp` (GuestInv) | - | 131 |
| `payload_header` | 32645 | `gb_payload_header` (WorldOK) | #0 d0 CTR N=2^64: i < L:nwd, step +1, unconditional | 262 |
| `state_init` | 12708 | `gb_state_init` (WorldOK) | - | 517 |
| `calculate_base_fee_per_gas` | 9613 | `fb_calculate_base_fee_per_gas` (GuestInv) | - | 259 |
| `calculate_excess_blob_gas` | 9561 | `fb_calculate_excess_blob_gas` (GuestInv) | - | 321 |
| `validate_header` | 9675 | `fb_validate_header` (GuestInv) | - | 321 |
| `hdr_bytes_field` | 9168 | `fb_hdr_bytes_field` (GuestInv) | - | 448 |
| `hdr_raw_field` | 9187 | `fb_hdr_raw_field` (GuestInv) | - | 448 |
| `hdr_uint_field` | 9103 | `fb_hdr_uint_field` (GuestInv) | - | 448 |
| `hdr_u256_field` | 9152 | `fb_hdr_u256_field` (GuestInv) | - | 448 |
| `hdr_word_field` | 9130 | `fb_hdr_word_field` (GuestInv) | #0 d0 CTR N=2^64: j < rField 1 L:f, step +1, unconditional | 448 |
| `decode_header` | 9202 | `fb_decode_header` (GuestInv) | - | 452 |
| `validate_headers` | 9476 | `fb_validate_headers` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional; #1 d0 CTR N=2^64: i < L:n, step +1, unconditional | 516 |
| `run_attempt` | 33734 | `gb_run_attempt` (InputReady) | #0 d0 CTR N=2^64: i < L:ntx, step +1, unconditional | 755 |
| `attempt_l1` | 33847 | `gb_attempt_l1` (InputReady) | - | 755 |
| `attempt_l2` | 33863 | `gb_attempt_l2` (InputReady) | - | 755 |
| `attempt_l3` | 33879 | `gb_attempt_l3` (InputReady) | - | 755 |
| `attempt_l4` | 33895 | `gb_attempt_l4` (InputReady) | - | 755 |
| `attempt_l5` | 33911 | `gb_attempt_l5` (InputReady) | - | 755 |
| `attempt_l6` | 33927 | `gb_attempt_l6` (InputReady) | - | 755 |
| `attempt_l7` | 33943 | `gb_attempt_l7` (InputReady) | - | 755 |
| `blake2_init` | 20017 | `fb_blake2_init` (GuestInv) | - | 4 |
| `bls_consts_init` | 24793 | `fb_bls_consts_init` (GuestInv) | - | 2 |
| `bls_lib_init` | 30328 | `fb_bls_lib_init` (GuestInv) | - | 3 |
| `bls_precompiles_init` | 30678 | `fb_bls_precompiles_init` (GuestInv) | - | 4 |
| `ceil_log2` | 749 | `fb_ceil_log2` (GuestInv) | #0 d0 RO(1) N=2^64: no-repeat, key = carried locals ['d'] (1 word) | 65 |
| `ssz_fail` | 8285 | `fb_ssz_fail` (GuestInv) | - | 0 |
| `ssz_split_var_list` | 8447 | `fb_ssz_split_var_list` (GuestInv) | #0 d0 CTR N=2^64: i < L:count, step +1, unconditional | 66 |
| `decode_bytes_list` | 8637 | `fb_decode_bytes_list` (GuestInv) | #0 d0 CTR N=2^64: i < rField 1 L:r, step +1, unconditional | 67 |
| `ssz_check_offsets` | 8414 | `fb_ssz_check_offsets` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 66 |
| `ssz_fixed_list_count` | 8496 | `fb_ssz_fixed_list_count` (GuestInv) | - | 65 |
| `decode_payload` | 8515 | `fb_decode_payload` (GuestInv) | - | 67 |
| `decode_requests` | 8584 | `fb_decode_requests` (GuestInv) | #0 d0 CTR N=2^64: i < 5, step +1, unconditional | 68 |
| `decode_stateless_input` | 8656 | `fb_decode_stateless_input` (GuestInv) | #0 d0 CTR N=2^64: i < 3, step +1, unconditional | 70 |
| `input_blob` | 624 | `fb_input_blob` (GuestInv) | #0 d0 WALK N=2^34: fresh-address walk: the counter strictly increases by a positive constant and every iteration accesses base + counter (or base + 32*counter) in the contiguous domain | 35 |
| `host_input_byte` | 8297 | `fb_host_input_byte` (GuestInv) | - | 0 |
| `host_input_le32` | 8310 | `fb_host_input_le32` (GuestInv) | - | 3 |
| `precheck_host_ssz_header` | 8324 | `fb_precheck_host_ssz_header` (GuestInv) | - | 68 |
| `decode_host_input` | 8401 | `fb_decode_host_input` (GuestInv) | - | 70 |
| `evm_init` | 17353 | `fb_evm_init` (GuestInv) | #0 d0 CTR N=2^64: i < 20, step +1, unconditional | 100 |
| `fork_init` | 32522 | `fb_fork_init` (GuestInv) | #0 d0 CTR N=2^64: i < 17, step +1, unconditional | 66 |
| `header_init` | 9657 | `fb_header_init` (GuestInv) | - | 65 |
| `sha256_pair` | 2954 | `fb_sha256_pair` (GuestInv) | - | 0 |
| `merkleize` | 8052 | `fb_merkleize` (GuestInv) | #0 d0 MONO N=64: cur := cur >> 1 while 1 < cur (signed): cur halves, at most 64 iterations; #1 d1 CTR N=2^64: j < L:half, step +1, unconditional; #2 d0 CTR N=2^64: d < L:target, step +1, unconditional | 72 |
| `pack_bytes` | 8213 | `fb_pack_bytes` (GuestInv) | - | 66 |
| `htr_bytes_vector` | 8229 | `fb_htr_bytes_vector` (GuestInv) | - | 72 |
| `htr_u64_at` | 8271 | `fb_htr_u64_at` (GuestInv) | - | 66 |
| `htr_bdep` | 8943 | `fb_htr_bdep` (GuestInv) | - | 73 |
| `htr_bexit` | 8967 | `fb_htr_bexit` (GuestInv) | - | 73 |
| `mix_in_length` | 8099 | `fb_mix_in_length` (GuestInv) | - | 65 |
| `htr_bytes_list` | 8253 | `fb_htr_bytes_list` (GuestInv) | - | 72 |
| `htr_cons` | 8921 | `fb_htr_cons` (GuestInv) | - | 74 |
| `htr_deposit` | 8873 | `fb_htr_deposit` (GuestInv) | - | 73 |
| `merkleize_progressive` | 8115 | `fb_merkleize_progressive` (GuestInv) | #0 d0 WALK N=2^34: size := size << 2 is 0 after <= 32 iterations; while size != 0 off strictly grows; afterwards each iteration writes roots + 32k (k += 1): fresh address, <= W; #1 d0 CTR N=2^64: k > 0 (or != 0), step -1, unconditional | 106 |
| `htr_plist_chunks` | 8156 | `fb_htr_plist_chunks` (GuestInv) | - | 106 |
| `htr_pbytes` | 8170 | `fb_htr_pbytes` (GuestInv) | - | 106 |
| `htr_pcontainer` | 8186 | `fb_htr_pcontainer` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 106 |
| `htr_withdrawal` | 8755 | `fb_htr_withdrawal` (GuestInv) | - | 73 |
| `htr_payload` | 8793 | `fb_htr_payload` (GuestInv) | #0 d0 CTR N=2^64: i < L:ntx, step +1, unconditional; #1 d0 CTR N=2^64: i < L:nwd, step +1, unconditional | 170 |
| `htr_wdreq` | 8899 | `fb_htr_wdreq` (GuestInv) | - | 73 |
| `htr_request_list` | 8987 | `fb_htr_request_list` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 140 |
| `htr_requests` | 9027 | `fb_htr_requests` (GuestInv) | - | 142 |
| `htr_new_payload_request` | 9053 | `fb_htr_new_payload_request` (GuestInv) | - | 170 |
| `keccak_init` | 3974 | `fb_keccak_init` (GuestInv) | - | 4 |
| `mem_init` | 50 | `fb_mem_init` (GuestInv) | - | 0 |
| `mpt_init` | 9781 | `fb_mpt_init` (GuestInv) | - | 101 |
| `output_write` | 651 | `fb_output_write` (GuestInv) | #0 d0 CTR N=2^64: i < L:n, step +1, unconditional | 65 |
| `ripemd160_init` | 19738 | `fb_ripemd160_init` (GuestInv) | - | 4 |
| `secp256k1_init` | 5417 | `fb_secp256k1_init` (GuestInv) | - | 0 |
| `serialize_result` | 9077 | `fb_serialize_result` (GuestInv) | - | 65 |
| `sha256_init` | 2327 | `fb_sha256_init` (GuestInv) | - | 3 |
| `ssz_init` | 7520 | `fb_ssz_init` (GuestInv) | - | 4 |
| `u256_ws_init` | 766 | `fb_u256_ws_init` (GuestInv) | - | 2 |
| `verify_stateless_new_payload` | 33959 | `gb_verify_stateless_new_payload` (InputReady) | - | 755 |
| `main` | 33979 | `gb_main` (MainEntry) | - | 755 |

unreachable from main (39): account_exists_and_is_empty, bls_fp_dbl, bn254_pairing, cur_msg, ec_add, ec_mul, ec_on_curve, fn_add, fn_inv_fermat, fn_pow, fp12_sqr, fp2_dbl, fp_inv_fermat, g1_neg, get_transaction_hash, htab_cap, htab_copy_scratch, htr_list_roots, ld_be32, ld_le32, ld_le64, mpt_get, p256_ec_to_affine, p256_fp_inv, recover_sender, rlp_bytes_to_word, rlp_check_uint_bytes, tx_blob_count, tx_data, tx_gas, tx_nonce, tx_r, tx_s, tx_to, tx_value, u256_cmp, u256_low, u256_xor, umod
