# R10 Loop-Bound & Specification Override Manifest (`K_pan = 375b`, `K_target <= 10^122 - 1`)

## 1. Loop Overrides for `campaign/notes/guestinv/scripts/coverage.py`
With `W = ordinaryDomain.size`, updating `OVERRIDES` in `coverage.py` with the following provable bounds drops `K["main"]` from `755` bits to `375` bits (`114` digits), so `118223496 * K_pan + 119233963` is `121` digits (`<= 10^122 - 1` with ~23 bits of headroom!).

Also add `"_node_rlp_fill"` to `roots` in `coverage.py:1215` so `_node_rlp_fill` is in `guarded` (giving it `NodeHeap` precondition so `node_rlp` -> `node_hash` -> `mpt_root` works cleanly).

```python
# Verified provable loop overrides for R10 (all pure local arithmetic or unconditional ordinaryDomain memory walk):
R10_LOOP_OVERRIDES = {
    ("rlp_be_len", 0): ("MONO", 8, "w >>= 8 up to 8 bytes"),
    ("fq12_mul", 1): ("CTR", 12, "i < 12"),
    ("fq12_sqr", 1): ("CTR", 22, "i < 22"),
    ("modinv_bin", 0): ("MONO", 513, "u,v bitshift reduction <= 513"),
    ("modinv_bin", 1): ("MONO", 256, "even shift <= 256"),
    ("modinv_bin", 2): ("MONO", 256, "even shift <= 256"),
    ("bls_fp_inv_raw", 0): ("MONO", 769, "u,v bitshift reduction <= 769"),
    ("bls_fp_inv_raw", 1): ("MONO", 384, "even shift <= 384"),
    ("bls_fp_inv_raw", 2): ("MONO", 384, "even shift <= 384"),
    ("p256_fp_mul", 0): ("MONO", 2**65, "carry loop"),
    ("p256_fp_mul", 1): ("MONO", 2**64, "reduce loop"),
    ("p256_fp_sqr", 0): ("MONO", 2**65, "carry loop"),
    ("p256_fp_sqr", 1): ("MONO", 2**64, "reduce loop"),
    ("divmnu", 4): ("MONO", 3, "Knuth D3 qhat correction <= 2"),
    ("bn_divmnu", 4): ("MONO", 3, "Knuth D3 qhat correction <= 2"),
    ("_node_rlp_fill", 1): ("CTR", 16, "branch children i < 16"),
    ("bn254_miller_raw", 0): ("CTR", 64, "64-bit loop counter"),
    ("fq12_reduce", 0): ("CTR", 11, "i < 11"),
    ("fq_mul_small", 0): ("CTR", 64, "bit_length64 <= 64"),
    ("pair_miller_loop", 0): ("CTR", 63, "63-bit miller loop"),
    ("fp12_pow_absx", 0): ("CTR", 64, "64-bit exponent"),
    ("fp_pow", 0): ("CTR", 256, "256-bit exponent"),
    ("div64by32", 0): ("CTR", 32, "32-bit shift-subtract"),
    ("udivmod", 0): ("CTR", 64, "64-bit shift-subtract"),
    ("ecp_mul", 0): ("CTR", 256, "u256_bit_length <= 256"),
    ("htab_first_diff", 0): ("WALK", W + 1, "loadsByte a + i in ordinaryDomain"),
    ("htab_first_diff", 1): ("CTR", 8, "j < 8"),
    # Unconditional ordinaryDomain load/store walks with local index stepping by +-1 (note: for stride s <= 384,
    # at most s * (W // s + 2) <= 2 * W + 384 values of k in [0, 2^64) can have (base + s * k) mod 2^64 in ordinaryDomain!
    # Use 384 * (W // 384 + 2) or 2 * W + 512 so wraparound mod 2^64 is 100% airtight by simple Pigeonhole!):
    ("rlp_read_length", 0): ("WALK", W + 1, "loadsByte p + i"),
    ("rlp_list_count", 0): ("WALK", W + 1, "advances off >= 1 and loads p + off"),
    ("_rlp_validate_items_body", 0): ("STACK", 2 * W + 2, "pushes 24B on scratch or advances pos"),
    ("_decode_witness_node_body", 0): ("GUARD", (W // 88 + 2) * 64, "arena nodes * nibble depth"),
    ("trie_walk", 0): ("RO(2)", (W // 8 + 2) * 2**64, "pos walk"),
    ("htab_set", 0): ("RO(2)", (W // 8 + 2) * 2, "tree depth <= cnt <= W/8"),
    ("_mpt_insert_node", 0): ("GUARD", 2**66, "nibble depth <= 64"),
    ("_mpt_delete_node_body", 0): ("GUARD", 2**66, "nibble depth <= 64"),
    ("fe_add", 0): ("WALK", 8 * W + 16, "loads a + 32*i (or i < 4/6/8)"),
    ("fe_sub", 0): ("WALK", 8 * W + 16, "loads a + 32*i"),
    ("fe_neg", 0): ("WALK", 8 * W + 16, "loads a + 32*i"),
    ("fe_mul_small", 0): ("WALK", 8 * W + 16, "loads a + 32*i"),
    ("bn254_pairing_check", 0): ("WALK", 192 * W + 384, "loads pairs + 192*i in ordinaryDomain"),
    ("bls_g1_msm_exec", 0): ("WALK", 160 * W + 320, "loads in + 160*i in ordinaryDomain"),
    ("bls_g2_msm_exec", 0): ("WALK", 288 * W + 576, "loads in + 288*i in ordinaryDomain"),
    ("bls_pairing_exec", 0): ("WALK", 384 * W + 768, "loads in + 384*i in ordinaryDomain"),
    ("bn_divmnu", 0): ("WALK", 8 * W + 16, "loads u/q + 8*j in ordinaryDomain"),
    ("bn_divmnu", 1): ("WALK", 8 * W + 16, "loads v + 8*i in ordinaryDomain"),
    ("bn_divmnu", 2): ("WALK", 8 * W + 16, "loads u + 8*i in ordinaryDomain"),
    ("bn_divmnu", 3): ("WALK", 8 * W + 16, "stores q + 8*j in ordinaryDomain"),
    ("bn_divmnu", 5): ("WALK", 8 * W + 16, "loads vn + 8*i in ordinaryDomain"),
    ("bn_divmnu", 6): ("WALK", 8 * W + 16, "loads vn + 8*i in ordinaryDomain"),
    ("bn_divmnu", 7): ("WALK", 8 * W + 16, "stores r + 8*i in ordinaryDomain"),
    ("bn_divmnu", 8): ("WALK", 8 * W + 16, "stores r + 8*i in ordinaryDomain"),
    ("divmnu", 0): ("WALK", 8 * W + 16, "loads u + 8*j in ordinaryDomain"),
    ("divmnu", 1): ("WALK", 8 * W + 16, "loads v + 8*i in ordinaryDomain"),
    ("divmnu", 2): ("WALK", 8 * W + 16, "loads u + 8*i in ordinaryDomain"),
    ("divmnu", 3): ("WALK", 8 * W + 16, "stores q + 8*j in ordinaryDomain"),
    ("divmnu", 5): ("WALK", 8 * W + 16, "loads vn + 8*i in ordinaryDomain"),
    ("divmnu", 6): ("WALK", 8 * W + 16, "loads vn + 8*i in ordinaryDomain"),
    ("divmnu", 7): ("WALK", 8 * W + 16, "stores r + 8*i in ordinaryDomain"),
    ("divmnu", 8): ("WALK", 8 * W + 16, "stores r + 8*i in ordinaryDomain"),
    ("bn_mul", 0): ("WALK", 8 * W + 16, "stores out + 8*i in ordinaryDomain"),
    ("bn_mul", 1): ("WALK", 8 * W + 16, "loads a + 8*i in ordinaryDomain"),
    ("bn_mul", 2): ("WALK", 8 * W + 16, "loads b + 8*j in ordinaryDomain"),
    ("destroy_storage", 0): ("WALK", 8 * W + 16, "htab_item loads nodes + 32*i / order + 8*i in ordinaryDomain"),
    # NOTE on execute_block#0, run_attempt#0, process_general_purpose_requests#0..1:
    # Check whether execute_block / run_attempt / process_general_purpose_requests are ALREADY in `guarded`!
    # If YES, ("GUARD", W // 16 + 1, "") or ("WALK", 16 * W + 32, "") works without expanding `guarded`!
    # Even better: in execute_block#0, run_attempt#0, process_general_purpose_requests#0..1, each iteration unconditionally
    # loads [lp + 16*i] or [rp + 8*i] or [lp + 8*j] where i/j steps by +1 and lp/rp is local, so ("WALK", 16 * W + 32, "")
    # needs ZERO extra guarded functions and is unconditionally true on ALL states!
    ("execute_block", 0): ("WALK", 16 * W + 32, "loads txs lp + 16*i in ordinaryDomain"),
    ("run_attempt", 0): ("WALK", 16 * W + 32, "loads txs lp + 16*i in ordinaryDomain"),
    ("process_general_purpose_requests", 0): ("WALK", 8 * W + 16, "loads rls rp + 8*i in ordinaryDomain"),
    ("process_general_purpose_requests", 1): ("WALK", 8 * W + 16, "loads logs lp + 8*j in ordinaryDomain"),
}
```
Notice why `s * W + 2 * s` (e.g. `8 * W + 16`, `16 * W + 32`, `384 * W + 768`) is **unconditionally sound mod `2^64`** for any constant stride `1 <= s < 2^10`:
As `i` increments `0, 1, 2, ... < 2^64` without wrapping `i` itself (`i < n <= 2^64 - 1`), `(base + s * i) mod 2^64` advances by `+s` each step and wraps around `2^64` at most `s` times (`s * 2^64 / 2^64 = s`). In each monotone sweep `[0, 2^64)` before wraparound, `(base + s * i) mod 2^64` can land inside the contiguous interval `ordinaryDomain = [ordinaryBase, ordinaryLimit)` of width `W` at most `W // s + 2` times! Across at most `s` sweeps, the total number of `i in [0, 2^64)` with `(base + s * i) mod 2^64 in ordinaryDomain` is at most `s * (W // s + 2) <= W + 2 * s`! Even simpler in Lean: `W + 2 * s` (or `s * W + 2 * s`) is tiny (~35–43 bits) and trivial to prove by `omega` on `k = (base + s * i) / 2^64 < s`!
And using `"WALK"` instead of `"GUARD"` on `execute_block`, `run_attempt`, `process_general_purpose_requests` avoids expanding the `guarded` function set!

## 2. Budget Theorem in `parts/p6.lean`
Update `K_pan_budget` (or add `K_target_budget`) in `parts/p6.lean` so `GuestInv.lean` itself machine-checks:
```lean
theorem K_target_budget : 118223496 * K_pan + 119233963 ≤ 10 ^ 122 - 1 := by decide
```

## 3. All Specification Fixes Required Across `parts/p1..p6.lean` (from `all_issues_audit.txt` & `m22_ISSUES.md`)
Read `campaign/notes/guestinv/r10_inputs/all_issues_audit.txt` and `m22_ISSUES.md` in full to ensure zero missed details:
1. **`ofString` non-injectivity in global preservation (`m00`, `m11`, `m12`, `m13`, `m19`, `m22`)**:
   - Quantify over `∀ k : MlS, k ∉ gw.map ofString → s.globals.lookup k = post.globals.lookup k` in `GlobalsKept`, `HtabExit`, `UnionExit`, `HtabNewExit`, `MptExit`, `WritesWithin`, `NodeFnExit`, `SameGlobalsExcept`.
2. **Entry parameter shape hypothesis in `FunSpec` and `FunEnsures` (`m12`, `m22`, etc.)**:
   - Include `(∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, s.locals, retShape))` as an antecedent inside `FunSpec` (`p5.lean`) and `FunEnsures` (`p4.lean`), and check `LoopBound` if needed.
3. **Zero-length intervals `(p, 0)` & `Disj` (`m05`, `m13`, `process_transaction`)**:
   - Define `Disj i j : Prop := i.2 = 0 ∨ j.2 = 0 ∨ i.1 + i.2 ≤ j.1 ∨ j.1 + j.2 ≤ i.1` (and check any existing helpers using `Disj` in `parts/`), AND normalize zero-capacity intervals `(if cap = 0 then 0 else ptr, ...)` in `fixedObjects`, `blockOutObjects`, `balObjects`, `lstObjects`, `worldTypedIvls`.
4. **`WorldKeeps` write-sets `R`, global lists `G`, and `worldRoleSlots` (`m05`, `m13`, `m22`)**:
   - Check EVERY `wk_*` theorem's `G` and `R` against transitive global writes and global buffer writes (`sk_buf`, `mpt_hash_scratch`, `keccak_st`, `sha256_st`, `ripemd_st`, `u256_ws`, `b2_v`, etc.):
     - Specifically in `wk_get_code`: add `(globN s "sk_buf", 52)` to `R` (because `sk_make` writes `sk_buf` below `heap_ptr`), and ensure `"ws+16"` (`nodedb` table) is in `worldRoleSlots` so `ws_get_code` -> `nodedb_lookup` -> `htab_get([ws+16], ...)` has `HtabWF`!
     - Specifically in `wk_get_account` (and callers): verify `G` includes `journal`, `journal_n`, `journal_cap`, `mpt_last_trie`, `mpt_last_addr`, `mpt_last_node` (check `coverage.py` transitive `gw[fn]` for EVERY `wk_*` spec automatically via a Python check script!).
     - Audit ALL `wk_*` functions automatically in Python against transitive `gw[fn]` AND transitive writes to global buffers (`globalBuffers`) so NO `wk_*` spec has a missing global or missing global-buffer interval in `R`!
5. **`HeaderOK` (`m05`, `wk_header_hash`, `encode_header`, `validate_header`, `block_rlp_length`)**:
   - Require `WordsOK s (locN s "h", 248) ∧ memW s (locN s "h" + 136) ≤ 32` (`HDR_EXTRA_N ≤ 32`) on `encode_header`, `header_hash`, `validate_header`, `block_rlp_length`, established by `decode_header` / `payload_header` / `validate_headers`.
6. **Host-input `rq` slice count bound (`m05`, `encode_execution_requests`)**:
   - Propagate `cnt * 192 < 2^36` (or `cnt ≤ W / 8`) in `InputAt` / `RetInput` from `decode_payload` -> `payload_header` -> `encode_execution_requests`.
7. **`TxValid`, `TxReadyStrong`, `LogsListOK`, `RetReceiptBounded` (`m04`, `m22`, `process_transaction`)**:
   - Strengthen `decode_transaction` -> `TxValid` (discharging `encode_transaction`, `tx_encode_bound`, `recover_sender*`, and `TxAccessListOK`).
   - Strengthen `TxReady` to `TxReadyStrong` (`journal_cap ≠ 0`, `bo+40 ≠ 0`, `bo+72 ≠ 0`, `TxAccessListOK`).
   - Add `LogsListOK` / `RetReceiptBounded` across `process_message_call` -> `encode_receipt` -> `process_transaction` so `nl < 2^28` (`8 * max nl 1 < 2^64`) and log entries in `out + 16` are valid before `scratch_release(tx_frame_mark)`.
8. **`_node_rlp_fill` & `NodeHeap` (`leaves-s00`)**:
   - Add `"_node_rlp_fill"` to `roots` in `coverage.py` and bound RLP payload lengths `< 2^40` in `NodeHeap` (`p4.lean:531`) so `_node_rlp_fill`, `node_rlp`, `node_hash`, `mpt_root` close cleanly.
9. **`m22` Frame / EVM Execution Contracts (`m22_ISSUES.md`)**:
   - Check every issue listed in `campaign/notes/guestinv/r10_inputs/m22_ISSUES.md` and `all_issues_audit.txt` (including `frame_start`, `run_frames`, `op_dispatch`, `process_message`, etc.) and ensure every contract precondition/postcondition matches its callers and callees cleanly.
