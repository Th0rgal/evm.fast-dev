# GuestInv spec, quorum round 4 (commit 0f8dea8c7)

Coordinator: mission 9409f9a9. The coordinator's own Lean check is in `guestinv-r4-coordinator-lean-check.md`: 0 errors, 918 leaf sorries, and `assembly` with clean axioms. Reviews are appended as they arrive.

## Fable 5.1 (mission 5a2cdc83): REQUEST_CHANGES (narrow)

Fable compiled the spec independently. The census and axiom claims hold:
- 0 errors;
- 918 sorries (727 `fb_*`, 14 hand-written, 142 callee contracts, 35 `gbody_*`);
- `assembly`, `assembly_main` and the 12 proved compositions use only the standard axioms;
- `gb_*` uses `sorryAx` only through the `Primitives` fields.

**Round-3 items are closed**, and the assembly is genuinely closed. Fable also ran its own interprocedural write scan:
- all 30 `ReadOnlyFn` leaves are read-only;
- all 50 `WritesWithin` regions match what the code writes;
- the 7 `NodeFn` leaves write only to parameter nodes and fresh memory.

**The only false primitives are `KeepsOn` leaves whose guard does not own the written memory.** No other primitive Fable checked is false, and the rest of the interface can stay frozen.

**Blocking:**

1. **`wk_stack_pop`, `wk_charge_gas` and `wk_warm_storage_key` are false** (Spec:7691, 7592, 7700). The precondition `WorldOK` says nothing about the global `ev`, yet all three write through it (AST 15046, 14949, 16571). Counterexample: with `ev := t − 16` for a rooted table `t`, `stack_pop` stores 0 at `t`, so `key_len := 0`. Fix: guard the opcode bounds (`gb_op_dispatch` at 8552, `gb_op_sload` at 8404, `gb_op_sstore` at 8456) by `EvmInv ∧ ¬EvmDone`, which `run_frames` provides, and state these contracts as `KeepsOn EvmInv EvmInv`.

2. **`ek_depth0_prepare` is false** (Spec:7433). `EvmInv` does not own the message record at `e+112` (`frameObjects`, Spec:1866). `depth0_prepare` (AST 18772) stores `msg+48`, and `prepare_dispatch` (AST 17836) stores `msg+112` and `msg+120`. Counterexample: `e+112 = t − 112` for a rooted table `t` overwrites `key_len`. Fix: keep `MsgReady`'s message ownership past `frame_open`, by adding `(e+112, 176)` to `frameObjects` or by using `KeepsOn (EvmInv ∧ message owned) EvmInv`.

3. **`wk_mpt_root` and `wk_mpt_set` are false** (Spec:7649, 7652). `MptObjReady` (Spec:5889) does not relate the node set `Nd` to the typed tables or fixed objects. An MPT leaf placed at `nodes + 8` of a rooted table makes `mpt_root` store a hash pointer into the table root's parent field. Fix: require every node of `Nd` to be disjoint from all table footprints and fixed objects, as `TriesTyped` already does for the world tries.

**Non-blocking:**
- `GBody.execute_block` (Spec:8816) cannot be discharged when `ntx ≥ 2^60`, because the allocation size wraps while `blockOutObjects` uses the unwrapped length. Fix: bound `ntx` in the guard, or use the wrapped length.
- DESIGN gives 46 `ww_*` and 51 `wk_*`; the actual counts are 50 and 47. The total of 142 is right.
- Keep the scratch-copy procedure for `#print axioms` in the notes.

## Astra 6 (mission 16ab2069, reviewing 0f8dea8c7): REQUEST_CHANGES

Counterexamples were replayed on an AST interpreter with executable precondition checks. Lean was not run.

**Checked and fine:**
- the zero-capacity witnesses are excluded;
- `RetWindowsOK` excludes the copy-back witness;
- the gas-total bound excludes the saturated-cost witness;
- BAL and `bo` objects are owned;
- none of the 72 `heap_release` callers reaches `set_retdata`.

**Blocking:**

1. **Shared deletion tables** (Spec:1946, 5963). The `MarksOK` exemption for the child's deletion table does not require it to be exclusive. Witness: `parent+136 = bal_idx_accts = child+136 = t = 0xb0bed2f8`, release mark `0xb0bed8a8`. On the child-error path, `t` is freed while both references survive. Fix: an exclusivity/unreachability condition covering surviving frames, global roots and nested roots.

2. **Return data can overwrite trie nodes** (Spec:1805, 1968, 5963). Frame objects are not disjoint from the `TriesTyped` nodes. Witness: the parent's retdata pointer is `ws+24 = n` (a hashed node); `set_retdata` writes kind 4, violating `NodeHeap`. Fix: make frame objects disjoint from trie nodes.

3. **`wk_charge_gas` and `wk_stack_pop` under `WorldOK`** (Spec:7592, 7691). Same as Fable's item 1, already fixed in revision 5. Verify.

4. **Byte-granularity framing** (Spec:1615, 7799, 7803). `memzero(a+1, 1)` changes the aligned word at `a`, which lies outside the declared region `[a+1, a+2)`; `memcpy` behaves the same. Fix: frame the aligned cells that intersect each byte region, or state bytewise preservation. Audit every byte-writing contract.

5. **MPT insert/delete: nibble indices unconstrained** (Spec:1792, 5884, 5914–5916). A key byte of 18 indexes `n+32+8·18 = n+176`, past the 176-byte branch. Insertion writes a pointer there, and deletion clears an out-of-node cell. Fix: constrain key bytes and nibbles to < 16 (or < 17 as appropriate) and preserve that under aliasing.

6. **`NodeFn` needs function-specific node kinds** (Spec:6210, 7454, 7457):
   - `_insert_into_leaf` given an extension node with `seglen = 0` writes 4 to `n+48`;
   - `_delete_ext_finish` given a hashed node writes `node+48`, outside its 32-byte footprint.

   Fix: give each `NodeFn` contract the node kinds its function requires.

7. **`FrameOpenReady` does not establish aligned frame memory** (Spec:1524, 6176, 7448). With `frame_mem_ptr = 0xb0000001`, `frame_mem_alloc` returns an unaligned pointer, so `WordsOK` for frame memory fails after `frame_open`. Fix: add allocator alignment invariants and establish them through the allocation contracts.

8. **Assembly boundary.** The conditional assembly takes 426 assumptions, including 35 admitted composition propositions (`gbody_main`, `gbody_run_frames`, `gbody_process_transaction`, …). Astra holds that this does not meet the stricter round-3 boundary: guard transport, loop invariants and rank application remain inside those admissions. Astra also notes the assembly uses only 239 of the 727 `fb_*` leaves and 10 of the 14 hand-written contracts. Unused assumptions do not invalidate the implication.

**Non-blocking:** DESIGN contract subtotals: 30 `ReadOnlyFn`, 50 `WritesWithin`, 55 `KeepsOn`, 7 `NodeFn`.

## Coordinator note on item 8 (for the quorum to rule on in round 5)

Fable found the assembly genuinely closed: every `gb_*` is a proved application of its `gbody_*` to listed hypotheses. Astra does not accept the `gbody_*` as primitives. Each `gbody_f` states that the body of the single function `f` satisfies its bound and guard-preservation obligations, given its callees' contracts as hypotheses. That is the same shape as each `fb_*` leaf. Round 5 will ask each reviewer to rule explicitly on whether that shape meets the round-3 boundary.

For the round-5 vote, the writer must make each `gbody_*` statement visibly single-function: its hypotheses are exactly its callees' contracts, and nothing else is assumed.
