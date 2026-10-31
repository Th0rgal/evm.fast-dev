# GuestInv spec quorum, round 5 (revision 7, f13145329)

Coordinator Lean check (9409f9a9, Lean 4.33.1, f13145329): 0 errors, 928 `declaration uses sorry`
warnings; `assembly`, `assembly_main`: [propext, Classical.choice, Quot.sound]; `K_pan_budget`: [propext].

| Reviewer | Verdict | Boundary |
|---|---|---|
| Astra 6 (codex) | REQUEST_CHANGES | NOT MET (14 gbody) |
| Fable 5.1 (claudecode) | REQUEST_CHANGES | NOT MET (execute_block, process_transaction) |
| Gemini 4 Carbon (opencode) | REQUEST_CHANGES | NOT MET (Astra's 14 + idx_start_storage, later retracted) |

## Astra 6

VERDICT: REQUEST_CHANGES

BOUNDARY: NOT MET (gbody__decode_witness_node_body, gbody__mpt_delete_node_body, gbody__mpt_insert_node, gbody_build_mpt_indexed, gbody_compute_state_root, gbody_get_storage, gbody_process_message_call, gbody_process_unchecked_system_transaction, gbody_process_general_purpose_requests, gbody_process_transaction, gbody_execute_block, gbody_payload_header, gbody_run_attempt, gbody_main)

Spec = campaign/specs-proposed/GuestInv.lean; AST = Guest/SoftwareAst.lean. AST replays are executable checks, not Lean proofs.

**Blocking: false primitives**

1. **World typing permits incompatible table roles to alias.** Spec:1810, 8827 (`wk_mark_account_created`); AST:13570.
   Two disjoint, allocated, well-formed tables `t,u`; `t` contains one entry whose value is `u`; set `ts+32 = t`, `ts+56 = t`. This satisfies `WorldOK` (`t` a valid table of tables, value in `S = [t,u]`). `mark_account_created` with that key overwrites the value with `1` and returns normally; `HtabValuesIn … S'` would need `1 ∈ S'`. Same for `wk_record_pre_state_read` (Spec:8917) when `bs+72 = bs+32 = t`.
   **`ek_state_restore` is false independently** (Spec:8336; AST:12918): `JournalTyped` constrains the journal's table pointer, not the saved value. A journal entry `(t, key, present=1, value=1)` restoring a table-of-tables entry breaks `WorldOK`, hence `EvmInv`. Fix the role/alias invariant and type journal restoration values; membership in one undifferentiated `S` is insufficient.
2. **`wk_bal_remove_change` has unconstrained selector/element-size arguments.** Spec:8587; AST:14202, 14183. Account record `ad` typed; put `ws` in unowned word `ad+40`, `ws+0 = p`, `ws+8 = 1`, `memory[p] = 7`. `bal_remove_change(addr, 40, 8, 7)` treats `ws` as a list and changes `ws+8` from 1 to 0, returning normally, contradicting `RecordsKept`. Restrict `(which, esz)` to `(16,40)`, `(24,16)`, `(32,24)`.
3. **`rt_htab_copy` omits source allocation/separation.** Spec:8501; AST:5363–5378. `t=0xa1000100, keys=0xa1000200, nodes=heap_ptr=0xa1000300, order=0xa1000400`, valid singleton table (key length 1, stride 8, node cap 2, root 1, next 2, leaf (0,0,0,8)). `htab_copy` allocates its destination header over the source nodes; returns normally but the copied root's parent is `0xa1000358` and its leaf criterion is 1, violating `HtabWF`. Require allocation of the source footprint, as `HtabArgWF` does.

**Blocking: interfaces do not support the claimed single-function walks**

4. **Fresh constructor results need not be outside the exit world.** Spec:6681 (`WorldStep`), 6797 (`FreshBlock`), 8575/8857/8863/9001; DESIGN:2265. `OwnedGrows` permits world objects to expand into fresh heap; `FreshBlock` puts the returned object there too; nothing makes them disjoint. Interface counterexample: persistent branch node `n`; a constructor allocates zeroed `p`, returns `p`, sets `n+32 := p` (a new hashed trie node). All listed clauses hold; for `te_new` the caller's `te+0 := sender` destroys that node. Blocks build_mpt_indexed, compute_state_root, process_message_call, process_unchecked_system_transaction, process_general_purpose_requests, process_transaction, execute_block, payload_header, run_attempt. `main`: Spec:6835 makes `RetInput` fresh but not disjoint from the exit world (a fresh `pl+40` may occupy a newly attached trie node's cache word); Spec:6114 gives only `WorldOK` after `mem_init`, not zero-root facts. Supply constructor-specific separation contracts and exit-world avoidance for `RetInput`; W4 proves disjointness from entry allocations only.
5. **`execute_block` cannot apply its `memzero` frame contract during initialization.** Spec:10621; AST:33590–33592. After `bo := alloc(88)` fresh memory may hold e.g. `bo+40 = 1`, so `WorldOK` need not hold at `memzero`; `ZeroFills` (under `ArenaReady`) only guarantees zeros in the destination. Add an `ArenaReady` write-frame or initialization contract.
6. **`process_transaction` lacks `lst_push` return-pointer typing.** Spec:10428, 8821; AST:33398–33400, 33418–33420. `wk_lst_push` constrains the transition, not the returned pointer; an identity transition returning an existing table header satisfies it, and the caller stores a log value through it. Require the result to identify the element slot, separated from typed records/tables/trie nodes.
7. **Guarded-loop contracts omit the facts their ranks use.** Spec:9082, 9187, 9247; AST:10213, 10796, 10625.
   - `_decode_witness_node_body`: `ak__decode_step` is only `ArenaReady → ArenaReady`; it may return the same frame repeatedly, overwrite saved links/counters; no fresh scratch frames or bounded pushes.
   - `_mpt_delete_node_body`: `ww_scratch_alloc` has no return-location or progress guarantee; returning a heap-node address satisfies it, and the caller writes scratch fields into that node.
   - `_mpt_insert_node`: `nf_node_invalidate` permits changes across node records and the free scratch gap; no idempotence for the zero-length-extension stationary-cycle argument (an opaque callee may advance a counter there while preserving `NodeHeap`).
   Need allocation/progress and field-preservation contracts.
8. **`run_attempt`'s count argument fails for signed-negative words.** Spec:6420, 10804; AST:33776, 33841. `InputReady` allows `ntx = 2^63`; signed `Cmp.less` makes `0 < ntx` false, zero iterations, but `BlockReady` needs `16*ntx + 16 < 2^64`. Also `gbody_get_storage` (Spec:9880; AST:13258): sharing `ts+24` with a table-of-tables role makes its own `htab_set(…,1)` destroy world typing; `ReadOnlyFn stor_lookup` gives no result contract repairing this before `ws_get_storage`.

**Round-4 regression check:** original witnesses remain excluded (DelExclusive; frame objects avoid trie nodes/paths; charge_gas/stack_pop need EvmInv; FrameOutside intersecting cells; KeyIn/NodeHeap nibbles; NodeFn kinds; ArenaOK alignment). gbody statements syntactically list direct callees.

**Spot checks:** process_create_message — sufficient (conditional on primitives). finish_child — boundary repaired (its `ek_state_restore` primitive remains false). No independent interface gap in `_mpt_delete_node`, `mpt_set`, `idx_start_storage`, `update_builder_from_tx`, `htab_truncate`, `rollback_child_access`, `op_sload`, `op_sstore`, `op_dispatch`, `run_frames`, `process_message`, `process_withdrawals`, `state_init`.

## Fable 5.1

VERDICT: REQUEST_CHANGES

Text census matches: 928 sorries = 727 fb, 84 wk, 12 ek, 2 mk, 30 ro, 5 ww, 1 ak, 1 fk, 7 nf, 1 nk, 6 rt, 5 rv, 1 zv, 1 nz, 2 dm, 29 gbody, 14 hand-written. Round-4 items still fixed (EvmKeeps EvmInv for ev-writing opcodes under EvmRun guards; EvmStep keeps ev/cur_cont/chain; message ownership survives frame_open; MptObjInWith disjointness).

**Blocking**

1. **`wk_process_message_call` is false** (Spec:8893–8897). `WorldStep` (Spec:6681) quantifies over every typing `(S, Nd)` of the entry state, demanding `FrameOutside` for everything outside `worldOwned s S Nd`, `(msg,176)`, the free gap and free heap. `MsgReady` (Spec:6448) only says some `S` contains `msg+152`, `msg+160`. Take `S₀ := S` minus those tables (still a typing). `frame_new` copies them to `e+168/e+176` (AST 15418, 15420); `warm_address` (AST 15486) and `warm_storage_key` (AST 16573) `htab_set` into them. Code `PUSH1 0; SLOAD; STOP` on a cold slot changes `ak+24` and a node of `ak`, outside `worldOwned s S₀ Nd`. Used at Spec:10428ff and in process_unchecked_system_transaction. Fix: restrict `∀ S` to typings containing `memW s (msg+152)`, `memW s (msg+160)` (a `WorldKeepsWith` variant taking the guard's owned tables), for every `WorldKeeps` with a MsgReady-style guard.
2. **`wk_process_transaction` is false; `gbody_process_transaction` unprovable** (Spec:8899–8903, 10583). `TxReady` (Spec:6414) is `WorldOK ∧ index < bo+80`; `blockOutObjects` (Spec:1756) makes a null array an empty object, so `bo+24 = 0`, `bo+32 = 0`, `bo+80 = 2^40` is allowed. The first stores write `load(bo+24) + 16·index` (AST 33116, 33118) = `16·index`; with `index := t/16` for the root table `t = memW (ws+32)` this overwrites `t+0`, then `tx_chain_id` mismatches and the body raises BlockErr 100 (which `Resumes` counts). Fix: `TxReady := WorldOK ∧ index < bo+80 ∧ bo+24 ≠ 0 ∧ bo+32 ≠ 0`; execute_block establishes these and RecordsKept carries them.
3. **`gbody_execute_block` is not provable from its hypotheses** (Spec:10621–10718). After `bo := alloc(88)` (AST 33590) the record holds arbitrary words, so `WorldOK` fails; `memzero(bo,88)` (AST 33592) has only `wk_memzero` (needs WorldOK, Spec:10685) and `ZeroFills` (Spec:10686, nothing outside the block). Revision 6's `ww_memzero : WritesWithin [(dst,n)]` from `ArenaReady` closed this and was removed. Fix: add an ArenaReady-tier frame for memzero to `GBody.execute_block` (or fold it into ZeroFills). DESIGN's execute_block row citing wk_memzero is wrong.

**Non-blocking**
- `MptObjInWith` does not require object nodes `Nm` disjoint from persistent nodes `Nd` (RetMptObj does). Add `IvlsDisj (nodeExtents Nm) (nodeExtents Nd)`.
- `RecordsKept` comes from `rec_written`, which follows local aliases but not memory aliases of the four records; sound today, add an automated check in coverage.py.
- Verified true against AST: rt_alloc, rt_msg_new, rt_te_new, rt_mpt_new, rt_lst_new, rt_htab_copy (nonzero), zv_memzero, dm_memcpy, dm_encode_withdrawal_rlp, rv_min, rv_u256_to_be_min, rv_rlp_encode_bytes, rv_validate_transaction, nz_htab_set, ek_* write sets.

BOUNDARY: NOT MET (execute_block, process_transaction). Walks completed from own hypotheses: process_message_call, process_create_message, process_message, finish_child, op_dispatch, state_init, process_general_purpose_requests, run_attempt.

## Coordinator note (also to fold into revision 8)

- `fq12_inv` (campaign/leaves/arith/ISSUES.md on wave8/leaves-arith-astra): noncanonical input `r+p` makes the inner polynomial-division loop reach an exact period-1 state repeat. `fb_fq12_inv` is unguarded and `K.fq12_inv` caps the inner loop at 14. The writer must state explicitly (DESIGN) that this is covered by `while_rank_stationary` (`SameHead` ⇒ timeout) with a rank ≤ 14 on non-stationary iterations, OR guard `fq12_inv` with canonical Fq12 inputs supplied by `bn254_pairing_check` / adjust `K.fq12_inv`. Either way, decide in revision 8, not after the freeze.
- Astra 8 and Fable's walk of run_attempt disagree; the signed-comparison witness is concrete, so treat it as blocking.

## Gemini 4 Carbon (resumed, 13:57Z)

VERDICT: REQUEST_CHANGES. Agrees with all Astra 1–8 and Fable 1–3 items (confirmed independently). Additions:

1. **Table-role aliasing is broader than Astra 1** (Spec:1810–1825, 2108, 6130–6156, 8551–8573, 8617, 8773, 8779, 8929). Under cross-role aliasing, essentially every table-writing `wk_*`/`ek_*`/§7 contract is false, not only the `1`-writers:
   - `bal_accounts` = `ts+16` (both key_len 20): `set_account_balance`/`create_ether` insert an `acct_new` record into it, so `TablesTyped` needs `memW a = 0 ∈ S'`. Same for aliasing with ts+8, ts+56, bs+8, bs+16, bs+72, ev+136, ev+168.
   - `ad+0 = ad+8` on a live BAL record: `add_storage_read` does `htab_set(ad+8, slot, 1)`, so `1` becomes a storage-list value (violates LstOK). Same for ad+0 aliasing ts+48, bs+48, ws+32, inner tables.
   - `ws+32 = ts+48`: `set_code` puts a code-slice pointer into the trie cache (`sl-1 ∈ Nd'` false); conversely `ws_storage_trie` puts `node+1` into an LstOK table.
   - Frame tables e+136/e+168/e+176 are only required `∈ S`; `DelExclusive` only covers tables below a child's scratch mark. `ev+176 = bal_accounts` breaks `ek_warm_storage_key`/`op_dispatch_spec`; `child+168 = bal_accounts` breaks `finish_child_spec` via rollback/union.
   Fix: partition/tag `S` by value schema, require pairwise distinctness (Nodup) of all writable table pointers across distinct logical slots (e+168/e+176 legitimately shared parent/child), and type journal entries by their table's role and key_len.
2. **Pin key_len per table role** (blocking for `wk_build_block_access_list_rlp`, Spec:8617; AST:14717–14725, 5339): `HtabWF` only gives 1 ≤ klen ≤ 60. `bal_accounts` with klen=8, stride=8, n=3: `htab_keys` allocates 3*8+8 = 32 bytes, then `sort_elems(…, esz=24, …)` writes 72 bytes on pass 2. Pin `hdr s t 0` (20/28/32/52/60) per role in `TablesTyped`.
3. Retracted: `gbody_idx_start_storage` with `bal_key_buf = 0` is walkable (IvlsDisj holds in both cases).
4. Checked and fine: `StateErr`/`MptErr`/`RlpErr` escaping `run_frames` (counted by `Resumes`) does not break `WorldStep`: scratch deletion tables never enter world roots, so `OwnedGrows` is not violated.
5. Specific fix suggestions: Astra 4 — for pure constructors `OwnedGrows` should not grow worldOwned (or state the return block disjoint from `worldOwned post S' Nd'`); `RetInput` should state `IvlsDisj (inputCells post w) (worldOwned post S' Nd')` (then main needs no zero-root facts). Astra 7 — `_decode_step` pushed record fresh scratch + `WritesWithin [] ["heap_ptr","scratch_ptr"]`; `rt_scratch_alloc` (p ≠ 0, aligned, WordsOK, Inside fresh scratch, strict decrease for n > 0); `nf_node_invalidate` = heap/scratch unchanged, only (nd+8, 24) zeroed (SameHead after one warm-up). Astra 8 — record `ntx < 2^63` in RetInput/InputAt (decode_payload's ssz_split_var_list already enforces it).

**fq12_inv: covered, no statement change.** `fb_fq12_inv` with the inner cap N = 14 is TRUE via `while_rank_stationary`. fq_mul always returns < p; fq_mul(k·p, linv) = 0 for 1 ≤ k ≤ 5. Rank at the active inner head: `μ = (if linv = 0 then 0 else d0 − d1) + phase`, where phase = 2 if r0[d0] < p or r0[d0] mod p ≠ 0; 1 if r0[d0] ≥ p, r0[d0] mod p = 0, q[d0−d1] ≠ 0; 0 otherwise (the next step is SameHead). μ ≤ 11 + 2 = 13 ≤ 14 (d1 ≥ 1 inside the outer loop). Every step strictly decreases μ or is SameHead; an inner SameHead makes the outer iteration WhileTimesOut. Record this rank in DESIGN/coverage.py.

Non-blocking: agrees with Fable's MptObjInWith IvlsDisj and RecordsKept alias-check items.
