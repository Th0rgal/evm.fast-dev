# GuestInv revision 6: a guarded route to `CoveredSourceTicksConsumedBounded`

Track `guestinv-opus55`, mission 9409f9a9 (Wave 8), branch `wave8/guestinv-opus55`. Revision 2
answered the round-1 quorum (`campaign/reviews/guestinv-r1.md`), revision 3 the round-2 quorum
(`guestinv-r2.md`), revision 4 the round-3 quorum (`guestinv-r3.md`, §0.3 and §0.4), and revision
5 (Fable's items) and revision 6 (Astra's items, commit d16ff8bc0; Gemini's item 2 and
non-blocking items on top) answer the round-4 quorum (`guestinv-r4.md`), §0.1 and §0.2. These are
narrow fix rounds: only the statements listed in §0.2 (and, for Gemini, in §0.1) changed. Gemini's
item 1 is the revision-7 redesign (§0.1). All statements are in
`campaign/specs-proposed/GuestInv.lean`. The generated parts of that file, the per-loop table (§4),
the coverage table (§5) and the composition lists (§6) come from
`campaign/notes/guestinv/scripts/coverage.py` run on `Guest/SoftwareAst.lean` (§9). No frozen file
is touched.

## 0. Summary

| Deliverable | Where | Status |
|---|---|---|
| `GuestInv` = code ∧ memaddrs ∧ shMemaddrs ∧ baseAddr | §2 of the Lean file | definition; `guestInv_evaluate`: **every** evaluation preserves it (**proved**) |
| guarded `call`/`decCall`/`seq`/`ite`/`dec` rules, no preservation side conditions | §3 | **proved** |
| tail call, handler calls (`callHandle_guestInv`, **new** guarded `callHandle_on`), stationary `while`, `while_rank`, **new** active-head `while_rank_active` / `while_rank_stationary_active`, `dec` for local-reading guards, guarded `decCall`, condition-aware `ite` | §3 | **proved** (no combinator has a `sorry`) |
| bridge `TerminatingFunBoundedOn MainEntry "main" K → CoveredSourceTicksConsumedBounded (K+1)` | §4 | **proved** (unchanged) |
| one bound `K.«f»` per function on `main`'s call graph (774 functions, 249 loops) | §6 (generated) | definitions (unchanged) |
| unguarded leaves `fb_f : TerminatingFunBoundedOn GuestInv f K.«f»` | §6 (generated) | `sorry` (727 statements, textually unchanged) |
| memory contracts: `HtabWF`, `ArenaOK`, `WorldOK`, `NodeHeap`, `EvmInv`, `evmPot` | §5 | definitions (revision 4: `FrameWF`, `frameObjects`, `MarksOK`, `EvmInv`, `fixedObjects`) |
| contract leaves (tables, MPT, frames, `mem_init`) | §7 | `sorry` (14 statements, unchanged); the frame glue **proved** |
| callee contracts: `ReadOnlyFn` (30), `WritesWithin` (50), `KeepsOn` (55: `wk_*` 43, `ek_*` 10, `ak_*` 1, `fk_frame_open`), `NodeFn` (7), value contracts (2: `nk_mpt_nibble_key`, `rv_common_prefix_length`) | §7 (generated) | `sorry` (144 statements; revisions 5-6, §0.2) |
| **new** composition obligations `gbody_f : GBody.«f»` (callee bounds and contracts → `f`'s bound; revision 6: each checked single-function, `«callees_f»`) | §7 (generated) | 16 **proved** by concrete-body composition (revision 6: +4), 31 `sorry` |
| guarded bounds `gb_f : TerminatingFunBoundedOn Guard_f f K.«f»` | §7 (generated) | **proved** (revision 4): `gbody_f` applied to the callees' facts |
| **new** `assembly : Primitives → CoveredSourceTicksConsumedBounded K_pan` | §7–§8 | **proved, no `sorryAx`** |
| `LocalsOnly`/`LocalsFree` instances for every guard (incl. `MainEntry`, `TxReady`, `ReqsFresh`, `MsgReady`, `FrameOpenReady`; revision 5: `EvmRun`, `EvmMsgReady`, `BlockReady`, the restated `MptObjReady`) | §7 | **proved** |
| `K_pan = K.«main» + 1`, `32·K_pan + 23077 ≤ (10^299 − 1)/10^4` | §8 | **proved** (`decide`) |
| end-to-end `CoveredSourceTicksConsumedBounded K_pan` | §8 | `assembly primitives`; its `sorry` dependencies are exactly the primitive leaves |

## 0.1 Round-4 items and how each is addressed (revisions 5 and 6)

Round 4 (`campaign/reviews/guestinv-r4.md`) found 6 false `KeepsOn` leaves, plus two
non-blocking items. Each fix is confined to the listed statements. The rest of the interface,
judged freezable, is textually unchanged (§0.2).

### Fable 5.1, blocking

**1. `wk_stack_pop`, `wk_charge_gas`, `wk_warm_storage_key` false.** All three write through
the global `ev` (AST 15046, 14949, 16571): stack, gas, and the frame's access table. `WorldOK`
does not own those blocks. Fix, as proposed:
- new guard `EvmRun := EvmInv ∧ ¬EvmDone`, the precondition of `op_dispatch_spec`;
- `op_dispatch`, `op_sload`, `op_sstore` are bounded under `EvmRun`, so `gb_op_dispatch` (8552),
  `gb_op_sload` (8404) and `gb_op_sstore` (8456) change;
- `run_frames` provides `EvmRun` at its `op_dispatch` call: `EvmInv` at the active head, `¬EvmDone`
  on the dispatch branch, exactly what `run_frames_step_of_specs` already uses;
- `op_dispatch` makes no guard-carrying call before it dispatches, so it passes `EvmRun` on to
  `op_sload`/`op_sstore` unchanged.

The callee contracts of `op_sload`/`op_sstore` are now generated against `EvmInv`:
- `ek_charge_gas`, `ek_stack_pop`, `ek_warm_storage_key : KeepsOn EvmInv EvmInv`;
- `ek_get_storage_original : KeepsOn EvmInv EvmInv` replaces `wk_get_storage_original`. `op_sstore`
  was its only user. Its guard `WorldOK` follows from `worldOK_of_evmInv`, and it writes only
  world tables and fresh memory, which `EvmInv` keeps disjoint from the frame blocks.

The four `wk_*` leaves are removed; `op_sload`/`op_sstore` were their only callers. Re-checked:
`assembly` and `assembly_main` are still proved, with clean axioms (§9).

**2. `ek_depth0_prepare` false.** The fix guards the contract and leaves `frameObjects` alone.
Adding `(e+112, 176)` to `frameObjects` would also cover child messages, which `child_message`
builds with `msg_new_scratch` under the parent's scratch marks. That would change what `MarksOK`
and every `EvmInv` leaf must preserve. Only depth 0 writes through the message:
- `depth0_prepare` stores `msg+48` (18772);
- `prepare_dispatch` stores `msg+112` and `msg+120` (17836); its only call site is
  `depth0_prepare` (18797).

New definitions:
- `EvmInvAt s S`: the body of `EvmInv` after `∃ S`, verbatim. `evmInv_iff_at : EvmInv s ↔
  ArenaReady s ∧ ∃ S, EvmInvAt s S` is proved by `Iff.rfl`, which certifies the copy.
- `MsgOwned s S m`: `(m, 176)` is allocated words, disjoint from every table of `S`, every fixed
  object and every frame block of the chain.
- `EvmMsgReady := ArenaReady ∧ ∃ S, EvmInvAt s S ∧ MsgOwned s S (ev+112)`. The message must be
  owned for the same `S` that witnesses `EvmInv`; a separate `∃ S` would not protect `EvmInv`'s
  tables.

Statements:
- `fk_frame_open : KeepsOn FrameOpenReady EvmMsgReady`. It is true for the same reason as
  `MsgReady`: `frame_new` stores `msg` into `e+112`, and the new frame's blocks are fresh scratch
  and frame memory, disjoint from the allocated message.
- `ek_depth0_prepare : KeepsOn EvmMsgReady EvmInv`.
- Between the two, `state_snapshot` is read-only, so `ro_state_snapshot` keeps `EvmMsgReady`
  (`localsFree_evmMsgReady`, proved).

**3. `wk_mpt_root`, `wk_mpt_set` false.** `MptObjReady` is restated through the new
`MptObjIn s S`:
- every node of `Nd` is disjoint from every table footprint of `S` and every fixed object, as
  `TriesTyped` requires;
- so is the trie object `(m, 16)` itself. `mpt_set` stores `m+0` (10886), so it is the same defect.

`MptObjReady := MptObjAvoids (fun _ => [])`, where
`MptObjAvoids R := ArenaReady ∧ ∃ S, WorldTyped s S ∧ MptObjIn s S ∧ R avoids S and the fixed
objects`. Again the table set must be the one the post-state `WorldOK` is shown for. The contracts
are:
- `wk_mpt_set : KeepsOn MptObjReady WorldOK` (was `WorldOK ∧ MptObjReady`);
- `wk_mpt_root : KeepsOn (MptObjAvoids [(out, 32)]) WorldOK` (was
  `WorldAvoids [(out, 32)] ∧ MptObjReady`).

Every trie object comes from `mpt_new` (`build_mpt_indexed` 11251, `mpt_from_witness` 10467): a
fresh 16-byte heap block, with nodes freshly decoded or built. So the callers
(`build_mpt_indexed`, `compute_state_root`) meet the stronger entry. `gb_mpt_set`'s guard is the
restated `MptObjReady`. Its body needs only the node typing, which is unchanged.

### Non-blocking

- **`execute_block` with `ntx ≥ 2^60`.** The guard is bounded, as proposed: new
  `BlockReady := WorldOK ∧ 16·ntx + 16 < 2^64`, with `ntx = (si+0)+40` read at entry (33588).
  With it, `alloc(16·ntx + 16)` (33593, 33596) returns exactly the unwrapped `blockOutObjects`
  length. `fixedObjects` and `TxReady` are unchanged. The wrapped-length alternative would have made
  `wk_process_transaction` false: `TxReady`'s `index < bo+80` allows slots past a wrapped array.
  The obligation moves to the caller `gbody_run_attempt` (Q11).
- **DESIGN counts.** Revision 4's `ww_*`/`wk_*` were 50/47, not 46/51; corrected in §0.4. In
  revision 5 they are `ww_*` 50, `wk_*` 43, `ek_*` 10 (§6, §7).
- **Scratch-copy `#print axioms` procedure.** Kept, with the exact commands, in §9.

### Astra 6, blocking (revision 6, commit d16ff8bc0)

Astra's round-4 review was appended after revision 5 (`52f2459bf`). Revision 6 answers it. Each
fix is again confined to the statements listed in §0.2.

**1. Shared deletion tables.** The release exemption of `MarksOK` is now exclusive. A table of
`S` may lie below the child's mark only if it is the deletion table `e_j+136` of a frame `j ≤ i`
and `DelExclusive s S ch i t` holds:
- no world reference names it. `worldTableRefs` lists the `ws`/`bs`/`ts` record slots, the
  global roots, the live values of `bs+32`/`ts+32`, the two tables of every BAL account record,
  and the table of every journal record;
- every chain slot `+136/+168/+176` holding it is a deletion slot `+136` at a position `j ≤ i`.

Astra's witness `parent+136 = bal_idx_accts = child+136` is excluded. Only `frame_new`
(`htab_new_scratch`) creates a deletion table. Each `jset`/`jdel` call writes into a `ts` slot
table or into a table nested in one, never a deletion table. The one copy of `e+136`
(`process_message_call` 19711) happens after the outermost frame has ended.

**2. Return data (and other writes) over trie nodes.** `TriesTyped` is restated as
`∃ Nd, TriesTypedWith s S Nd`, and `nodeExtents s Nd` lists the node records and their paths.
`AvoidsTries s S os` says some typed node set of the tries, for the same `S`, avoids the regions
`os`. It is required of:
- every frame block (new `EvmInv` conjunct, mirrored in `EvmInvAt`);
- the message record (`MsgReady`, `MsgOwned`);
- the `WorldAvoids` output regions;
- the trie object `m` and the `MptObjAvoids` regions.

**3. Verified fixed by revision 5.** This is Fable's item 1, fixed in revision 5 and re-checked
on revision 6:
- `wk_charge_gas`, `wk_stack_pop`, `wk_warm_storage_key` and `wk_get_storage_original` no longer
  occur in the Lean file;
- their only callers `op_sload`/`op_sstore` use `ek_charge_gas`, `ek_stack_pop`,
  `ek_warm_storage_key` and `ek_get_storage_original : KeepsOn EvmInv EvmInv`;
- `op_dispatch`, `op_sload` and `op_sstore` are bounded under `EvmRun = EvmInv ∧ ¬EvmDone`.
  `GBody.«run_frames»` takes `gb_op_dispatch` under `EvmRun`, the guard `run_frames_step_of_specs`
  already has on its dispatch branch;
- `EvmInv` owns the frame blocks those three write through `ev` (stack, gas word, access table:
  `frameObjects`, `FrameWF`).

Lean accepts the revision-6 file with these statements (0 errors, §9).

**4. Byte-granularity framing.** `FrameOutside` is cell-granular: a cell may change iff it meets a
kept or fresh region (`CellHits`). Memory maps cells to words, and a byte store rewrites its whole
aligned cell. The one definition covers every frame: `WritesWithin`, `HtabExit`, `UnionExit`,
`HtabNewExit`, `MptExit`, `NodeFnExit`. This includes every byte-writing contract (`ww_memcpy`,
`ww_memzero`, `ww_rlp_encode_*`, …). Supporting results:
- the regression `example` for `memzero(a+1, 1)`;
- `cellHits_aligned` (proved): for word-aligned objects the cell frame is the old address frame,
  so owned objects are protected exactly as before.

**5. Nibble keys and paths.** New definitions:
- `memB`: the byte `loadByte` reads, with the state's `be`;
- `NibblesOK`;
- `KeyIn s Nd p len`: empty, or nibbles in allocated heap, disjoint from every node record;
- `nodePath`.

`NodeHeap` requires every leaf/extension path to satisfy `KeyIn`. `MptReady` requires
`level ≤ klen` and the unread key suffix to satisfy `KeyIn`. Two value contracts let the callers
establish this:
- `nk_mpt_nibble_key : RetNibbles "mpt_nibble_key"` (fresh heap nibble array);
- `rv_common_prefix_length : RetLe (min al bl)`.

**6. Function-specific node kinds.** `NodeFn names req g` carries `g`'s own requirement, read off
its body (`NODE_REQ` in `coverage.py`). `NodeKind` is the kind of the node it reads/writes at
fixed offsets:
- `_insert_into_leaf`: 1;
- `_split_extension`: 2, plus `pl < node+40` and `pl ≤ rl`;
- `_delete_ext_finish`: 2;
- `_collapse_branch`: 3.

It also carries `KeyIn` for every array the function copies into a path. `NodeFnExit` adds that
old nodes keep their kinds and new nodes are fresh heap records. The callers' loop invariants need
both.

**7. Aligned allocator.** `ArenaOK` requires `heap_ptr`, `frame_mem_ptr` and `scratch_ptr ≡ 0
(mod 8)`. `mem_init` sets aligned constants; the allocators set `(p + n + 7) & -8` /
`(p - n) & -8`; the releases restore earlier pointer values. `MarksOK` requires its marks
aligned.

**8. Assembly boundary (for the round-5 ruling).** Each `GBody.«f»` is now visibly
single-function (§6, "The `gbody_*` boundary", has the full per-function list):
- its docstring lists the direct callees of `f`, then the contract hypotheses;
- a proved `«callees_f»` checks by `decide` on the literal AST (`progCallees`, `fnBody`,
  `sameNames`) that the direct callees of `f` are exactly the functions whose bounds are
  hypotheses (47 theorems);
- `coverage.py` asserts that every hypothesis names a direct callee of `f`;
- §6 has the per-function table (`out/gbody.md`).

So `gbody_f` assumes only facts about `f`'s callees and concludes only about `f`'s body. That is
the shape of an `fb_*` leaf, plus callee hypotheses. Whether it meets the round-3 boundary is the
quorum's ruling.

Fewer admitted compositions (commit fcb670d84). Four more `gbody_*` are **proved** from the proved
Hoare layer, so 16 of 47 are proved and 31 remain primitives:
- `get_pre_tx_storage`;
- `get_storage_original`;
- `ws_storage_trie`;
- `decode_witness_to_mpt`.

The new proved rules are general:
- `TerminatingProgBoundedOn.seq_hoare`: a guarded `seq` that needs the guard after the first part
  only on fall-through, given as a `Hoare` triple. `seq_on` needs preservation on every outcome,
  which a call cannot give, because a trapped callee leaves an arbitrary state;
- `Hoare.ite_return_skip`: a guard clause `if c then return e` falls through only from the
  unchanged state (`return_ne_none`);
- `Hoare.call_keeps`: a call whose callee has `KeepsOn W W` falls through only into `W`, for a
  locals-free `W` (from `Hoare.call0`);
- `Hoare.ite_call_keeps`, the conditional form;
- `clock_skip`, `clock_store`.

Each proof is a combinator term that follows the body exactly, followed by `omega` on `K.«f»`. Every
hypothesis it uses is one of the listed callee facts. The `Primitives` structure shrinks from 428
to 424 fields.

**Why most `fb_*` leaves and four §7 leaves are not in `Primitives`.** `Primitives` (generated)
has exactly the facts `assembly_main` uses, 424 fields:
- the `fb_*` bounds of the 239 unguarded direct callees of guarded functions;
- the 10 §7 contract leaves the compositions name;
- the 144 callee contracts;
- the 31 unproved `gbody_*`.

The other 488 `fb_*` leaves bound functions that only unguarded functions call. A guarded
composition needs only its direct callees' bounds. Each of the 239 used `fb_g` is itself a leaf, to
be proved from the bounds of `g`'s callees, and the 488 are those bounds. So they are decomposition
targets for proving the 239, not assumptions of the assembly. They stay in the file as stated
obligations (the coverage table, §5, lists all 774 functions), and the assembly does not depend on
them.

The four §7 leaves outside `Primitives` are:
- `htab_union_into_spec`, a lemma for `finish_child_spec` (`incorporate_child_on_success`);
- `htab_new_scratch_spec`, for `fk_frame_open` (`frame_new`);
- `mpt_insert_node_spec` and `mpt_delete_node_body_spec`, for `wk_mpt_set`.

No guarded body calls these functions at a guard-carrying site with a §7 contract. Removing all 492
leaves would not change `assembly` or its axioms.

**Found while auditing the hypotheses: `RollbackReady`.** `rollback_child_access` truncates
`child+168`, then reloads `child+176` and `child+272`. Its guard therefore also requires:
- the child record `(child, 280)` allocated words, outside both table footprints;
- the two tables equal, or with disjoint footprints.

`finish_child` gets these from `EvmInv`.

### Gemini 4 Carbon (review of 0f8dea8c7; answered on top of revision 6)

**Item 2 (fixed): per-slot storage lists of the block access list.** The storage table `+0` of
every BAL account record has live values `l` that are lists of 40-byte elements:
- created in `add_storage_write` (13944) by `lst_new(40, 2)`;
- updated by `lst_upsert_idx(l, 40, idx)`;
- written through by `remove_storage_write` and by the in-place `sort_elems` of
  `build_block_access_list_rlp`.

Changes:
- `balObjects` now owns `lstObjects s l 40` for every `l ∈ htabValues s (memW s ad)`, so the
  lists are fixed objects: allocated words, pairwise disjoint (`FixedTyped`) and disjoint from
  every table, frame block and trie node (the existing conjuncts over `fixedObjects`);
- `TablesTyped` requires `LstOK s l` for each of them;
- `htabValues` moves up next to `HtabValuesIn` (same definition).

This makes `wk_add_storage_write`, `wk_remove_storage_write`, `wk_build_block_access_list_rlp`
and `gb_update_builder_from_tx` (via its composition) true against Gemini's witness. Their
statements are textually unchanged, and only the two definitions change (`sigdiff.py`:
`TablesTyped`, `balObjects`).

**Non-blocking (fixed):**
- the Lean header now says revision 6;
- `mpt_insert_node_spec` has a docstring: a cycle of empty extension segments never returns and
  reaches `WhileTimesOut` within the `2^130` bound, so the spec is vacuous on such runs.

**Item 1 (open; the revision-7 redesign of the coordinator's round-5 note).** The callee
contracts are forgetful. `KeepsOn W W` allows any `W → W` transition, so a caller loses local
facts across the call: a fresh allocation, `index < ntx`, `bo+64 < 8`, `ev`/`cur_cont` for
`finish_child`, … . So several `gbody_f` cannot be proved from their own hypotheses. Gemini's
Option A:
- relational `wk_*` contracts (`S ⊆ S'`, heap only grows, unowned memory below the heap and the
  globals outside `gw` unchanged, `bo+64` up by one for `requests_append`);
- `ek_*` contracts that keep `ev`, `cur_cont` and `evmChain`;
- return typing for `alloc`, `msg_new`, `lst_new`, `htab_copy`, `mpt_new`, `mpt_from_witness`;
- typed post-states for `bal_init`, `state_fresh_tx` and `main`'s `*_init` calls.

This changes the shape of all 55 `KeepsOn` contracts, part of the `WritesWithin` ones, and every
`GBody` that uses them. It is not part of this fix round. The coordinator has scheduled it as
revision 7, which round 5 votes on. The 31 unproved `gbody_*` should be read as possibly not
provable from their own hypotheses until then.

## 0.2 Changes since 141ff1f6b (revision 6)

`sigdiff.py` (§9) on revision 5 (`141ff1f6b`) vs revision 6 (`fcb670d84`): 29 changed signatures, 0
of them `fb_*`, no removals, 79 new names. Every change answers an Astra round-4 item (numbered as
in §0.1), or the `RollbackReady` audit.

**Changed leaf statements (7, all callee contracts):** `nf__insert_into_leaf`,
`nf__split_extension`, `nf__collapse_branch`, `nf__delete_ext_finish`, `nf_node_invalidate`,
`nf_node_new_ext`, `nf_node_new_leaf`: `NodeFn names g` → `NodeFn names req g` (items 5, 6).

**New leaf statements (2):** `nk_mpt_nibble_key : RetNibbles "mpt_nibble_key"`,
`rv_common_prefix_length : RetLe (min al bl) "common_prefix_length"` (item 5).

All 727 `fb_*`, all 14 §7 leaves and the other 135 callee contracts are textually unchanged. Their
meaning changes through the definitions below.

**Changed definitions (19):**
- `ArenaOK`: aligned pointers (7);
- `FrameOutside`: `CellHits` (4);
- `NodeHeap`: `KeyIn` paths (5);
- `TriesTyped`: `∃ Nd, TriesTypedWith` (2);
- `MarksOK`: `DelExclusive`, aligned marks (1, 7);
- `EvmInv`, `EvmInvAt`: `AvoidsTries` of the frame blocks (2);
- `MsgReady`, `MsgOwned`, `WorldAvoids`: `AvoidsTries` (2);
- `MptObjIn`: `nodeExtents` (2, 5);
- `MptObjAvoids`: `AvoidsTries` (2);
- `MptReady`: `level ≤ klen` and `KeyIn` of the key suffix (5);
- `NodeArgs`, `NodeFnExit`, `NodeFn`: `req`; old kinds kept, new nodes fresh (6);
- `RollbackReady`: the audit fix;
- `Primitives`: the field types above, two new contracts, four fewer `gbody_*`.

**Changed proved theorem statement (1):** `localsOnly_mptReady` (`LocalsOnly ["node", "key",
"klen", "level"]`).

**Changed composition obligations (3, still `sorry`):** `GBody.«mpt_set»` (+`nk_mpt_nibble_key`),
`GBody.«_mpt_insert_node»` and `GBody.«_mpt_delete_node_body»` (+`rv_common_prefix_length`, new
`nf_*` types). Every `GBody` docstring is regenerated (item 8). Four `gbody_*` are now proved (their
statements are unchanged).

**New definitions (21):** `CellHits`, `memB`, `NibblesOK`, `KeyIn`, `nodePath`, `nodeExtents`,
`TriesTypedWith`, `AvoidsTries`, `htabValues`, `recordSlots`, `worldTableRefs`, `DelExclusive`,
`NodeKind`, `RetLe`, `RetNibbles`, `progCallees`, `fnBody`, `sameNames` (and the generated
`lookup_*` of the four new proofs).

**New proved theorems:**
- `cellHits_aligned`, `return_ne_none`, `clock_skip`, `clock_store`;
- `TerminatingProgBoundedOn.seq_hoare`, `Hoare.ite_return_skip`, `Hoare.call_keeps`,
  `Hoare.ite_call_keeps`;
- the 47 `«callees_f»`;
- `gbody_get_pre_tx_storage`, `gbody_get_storage_original`, `gbody_ws_storage_trie`,
  `gbody_decode_witness_to_mpt`.

**Unchanged:** every `K.«f»`, `K_pan`, `K_pan_budget`, the bridge, the glue
`run_frames_step_of_specs`, every revision-5 combinator, the 12 previously proved `gbody_*`,
`frameObjects`, `fixedObjects`, `WorldOK`, `TxReady`, `BlockReady`.

**Census:** 916 leaf sorries:
- 727 `fb_*`;
- 14 §7 contracts;
- 144 callee contracts: `ReadOnlyFn` 30, `WritesWithin` 50, `KeepsOn` 55 (`wk_*` 43, `ek_*` 10,
  `ak_*` 1, `fk_frame_open`), `NodeFn` 7, value contracts 2;
- 31 `gbody_*`.

## 0.2b Changes since 0f8dea8c7 (revisions 5 and 6, cumulative)

`sigdiff.py` (§9) on revision 4 (0f8dea8c7) vs revision 6 (d16ff8bc0; fcb670d84 adds only the
four proofs and their helpers, §0.2):

**Changed leaf statements:**
- revision 5: `ek_depth0_prepare`, `fk_frame_open`, `wk_mpt_set`, `wk_mpt_root` restated;
  `wk_charge_gas`, `wk_stack_pop`, `wk_warm_storage_key`, `wk_get_storage_original` replaced by
  `ek_*` (`KeepsOn EvmInv EvmInv`);
- revision 6: the seven `nf_*` (`NodeFn` with requirements, item 6); new value contracts
  `nk_mpt_nibble_key`, `rv_common_prefix_length` (item 5).

All 727 `fb_*` and all 14 §7 contract leaves are textually unchanged. Some leaves keep their text
but change meaning through a definition below: the frames through `FrameOutside`, the `EvmInv`
contracts through `EvmInv`/`MarksOK`, the MPT specs through `NodeHeap`/`MptReady`.

**Changed definitions:** `ArenaOK` (7), `FrameOutside` (4), `NodeHeap` (5), `TriesTyped` (2),
`MarksOK` (1, 7), `EvmInv` (2), `MptReady` (5), `MptObjReady` (Fable 3), `MsgReady` (2),
`WorldAvoids` (2), `NodeArgs`, `NodeFn`, `NodeFnExit` (6), `RollbackReady` (audit).
`localsOnly_mptReady` now lists `key`, `klen`, `level`.

**Changed composition obligations (13 `GBody.«f»`, all still `sorry`):** `op_dispatch`, `op_sload`,
`op_sstore`, `run_frames`, `process_message`, `build_mpt_indexed`, `compute_state_root`,
`execute_block`, `run_attempt` (revision 5); `mpt_set`, `_mpt_insert_node`,
`_mpt_delete_node_body` (revision 6, new hypotheses). Every `GBody` docstring is regenerated
(item 8).

**Changed guarded bounds (4, proved):** `gb_op_dispatch`, `gb_op_sload`, `gb_op_sstore` (`EvmRun`),
`gb_execute_block` (`BlockReady`). `Primitives` changes accordingly.

**New definitions:**
- revision 5: `EvmRun`, `EvmInvAt`, `MsgOwned`, `EvmMsgReady`, `MptObjIn`, `MptObjAvoids`,
  `BlockReady`;
- revision 6: `CellHits`, `memB`, `NibblesOK`, `KeyIn`, `nodePath`, `nodeExtents`,
  `TriesTypedWith`, `AvoidsTries`, `htabValues`, `recordSlots`, `worldTableRefs`, `DelExclusive`,
  `NodeKind`, `RetLe`, `RetNibbles`, `progCallees`, `fnBody`, `sameNames`.

**New proved theorems:**
- revision 5: `localsFree_evmRun`, `evmInv_iff_at` (`Iff.rfl`), `evmInv_of_evmMsgReady`,
  `localsFree_evmMsgReady`, `localsOnly_blockReady`;
- revision 6: `cellHits_aligned`, the 47 `«callees_f»`.

**Unchanged:** `frameObjects`, `fixedObjects`, `blockOutObjects`, `WorldOK`, `TxReady`, every
`K.«f»`, `K_pan`, `K_pan_budget`, the bridge, the glue `run_frames_step_of_specs`, every
combinator, the 12 proved `gbody_*`.

**Census:** 916 leaf sorries (§0.2).

## 0.3 Round-3 items and how each was addressed (revision 4)

### Fable 5.1, blocking

**1. `while_rank` could not assemble `gb_run_frames`.** New corollaries with the same proof:
`TerminatingProgBoundedOn.while_rank_active` and `while_rank_stationary_active`, whose body bound is
`TerminatingProgBoundedOn (fun s => P s ∧ LoopActive condition s) body B`. The induction core
`while_rank_stationary_aux` now takes the body bound only at active `P` heads (it is a proved
helper; `while_rank` and `while_rank_stationary` are restated through it with unchanged
statements). `LoopActive` survives the clock step by the proved `loopActive_decClock`
(`evalHOLFinite_upd_clock_eq`). For `run_frames`, `P = GuestInv ∧ (EvmInv ∨ go = 0)`, and the active
head (`go ≠ 0`) gives `EvmInv`, so the guarded callees' guards hold.

**2. No handler-call rule for guarded callees.** `TerminatingProgBoundedOn.callHandle_on` (proved):
callee bound under `Pc`, call site discharged by `CallEntryOn P Pc`, handler bounded under
`GuestInv` (from `hPG : P s → GuestInv s` and `guestInv_evaluate`). `callHandle_guestInv` is now its
instance `P = Pc = GuestInv` (statement unchanged).

**3. `op_dispatch_spec` false at capacity 0.** `FrameWF` requires `1 ≤ e+232` (stack capacity) and
`1 ≤` the logs capacity `(e+88)+16`. `frame_new` gives 32 (15388) and 4 (15407, `lst_new_scratch(8,
4)`). `stack_push` regrows to `min(2·cap, 1024)` (15080-15083) and `lst_push` to `2·cap` (13856), so
both growth paths keep `≥ 1`. Astra's item 1 is the same defect and is closed by this change.

**4. `finish_child_spec` false.**
- *Output window* (AST 18650-18652): new `RetWindowsOK s ch` in `EvmInv`. For every chain position
  `i` with a parent: `c_i+80 = 0 ∨ c_i+72 + c_i+80 ≤ e_{i+1}+40` (parent memory capacity). The
  disjunct `c_i+80 = 0` is necessary, and the reviewer's unconditional form would be false: `op_call`
  passes `os = sat_word(out_start)` (19447), which is arbitrary when the size is 0, and
  `finish_child` only copies `min(out_size, …) ≠ 0` bytes. `extend_memory` on the output window
  establishes it before `generic_call` → `start_child` stores the window (18746-18748). The
  suspended parent's capacity does not change until `finish_child`.
- *Return-data buffer* (`set_retdata` 19064): new `frameRet s ec`, index 6 of `frameObjects`. It is
  `(e+144, round8(e+216 + 8))` (the block `alloc(n + 8)` returns), or `(0, 0)` when the capacity
  `e+216` is 0. `FrameWF` requires `e+216 = 0 ∧ e+144 = evm_empty`, or the block allocated on the
  heap with words. So it is pairwise disjoint from every frame block, table and fixed object.
  Astra's witness (`parent+144 = parent+64`, capacity 8) violates that disjointness.
- *Field audit (DESIGN Q1)*: §8 Q1 has the field-by-field table for the frame record (AST 15370) and
  the continuation (AST 18450/18705). It is generated by a write-root scan over the `op_dispatch`,
  `finish_child`, `frame_exception` and `frame_epilogue` cones: every store and every argument
  passed to a written parameter, with locals resolved to their definitions. Every pointer field
  written through is owned:
  - `+8`: stack;
  - `+24`: memory; the `+32`/`+40` hits are offsets into it;
  - `+88`: logs header and array;
  - `+136/+168/+176`: tables;
  - `+144`: return data;
  - `c+72`: output window.

### Fable 5.1, assembly ruling, recommendation adopted (item 5); Astra 6, assembly ruling

The coordinator required a proved assembly theorem `(∀ primitive obligation) → target`. Revision 4
has it:
- `structure Primitives : Prop` (generated, 426 fields) lists every obligation the guarded tier uses:
  - the `fb_*` bounds of the 239 unguarded callees of guarded functions;
  - the 10 §7 contract leaves those compositions use;
  - the 142 new callee contracts;
  - the 35 composition obligations `gbody_f` that are not yet proved. The other 12 are proved, so
    they are no longer primitives; this follows the coordinator's "prove the assembly with an
    explicit list, then shrink that list".
- `assembly_main : Primitives → TerminatingFunBoundedOn MainEntry "main" K.«main»` is **proved**
  (generated `have` chain in callee-first order). So is `assembly : Primitives →
  CoveredSourceTicksConsumedBounded K_pan`. `#print axioms assembly` gives `[propext,
  Classical.choice, Quot.sound]`, with no `sorryAx`.
- `primitives : Primitives` fills each field with its leaf. The end-to-end theorem is `assembly
  primitives`.
- Every `gb_f` is now a **proved** theorem: `gbody_f` applied to its callees' `fb_*`/`gb_*` and
  contracts. Statements are unchanged except five guards (§0.4).

Each primitive is a statement about one function body:
- **`gbody_f`**: `GBody.«f»` is `(bound of every direct callee) → (contract of every guard-carrying
  callee) → TerminatingFunBoundedOn Guard_f f K.«f»`. Its proof is a walk over `f`'s body with the
  §3 combinators, using **only** the listed hypotheses. Guard establishment and transport at the
  guarded calls, the loop invariants and the rank/stationary obligations (§3 table) are part of that
  walk. A `gbody_f` that needs a fact absent from its hypotheses is unprovable, so the interface is
  explicit and checked by Lean (see §8 Q9 for where the walk is expected to be hardest).
- **Guard-carrying call sites** are computed by `coverage.py` (`needed_calls`): a call site counts
  when a guarded call or a guarded loop head is reachable after it inside the body. `return` and
  `raise` end a path, and a tail call flows only into its callee. 150 callees (133 of the 239
  BETWEEN functions plus 17 guarded callees) need a contract. Nine of them are covered by the
  existing §7 leaves (`htab_set/del/truncate/new`, `mem_init`, `op_dispatch`, `frame_exception`,
  `frame_epilogue`, `finish_child`). The other 141 get 142 new contract leaves:
  `node_new_ext` is used under two frames and gets one leaf per frame. The other 106 BETWEEN
  functions are only ever followed by unguarded code and need none. That includes all 85 `op_*`
  called from `op_dispatch`, because each dispatch branch returns.
- **Callee contracts**, four uniform shapes (§7 of the Lean file), chosen mechanically:
  - `ReadOnlyFn g` (30): `g` (transitively) has no store, no global assignment and no FFI call. On a
    resuming outcome (return, or an exception other than `TrapErr`) the post-state is the entry state
    up to locals and clock. The proved `ReadOnlyFn.keepsOn` turns it into `KeepsOn W W` for any
    `LocalsFree` guard.
  - `WritesWithin R gw g` (50): on a resuming outcome, memory changes only inside `R` and inside the
    memory free at entry (above `heap_ptr`, between `frame_mem_ptr` and `scratch_ptr`); only the
    globals `gw` (computed) change; the arenas stay separated and the heap does not shrink. It holds
    for arbitrary states, and the caller shows `R` is unowned:
    - `R` is the parameter extents for the 16 pointer-parameter writers (hand-checked table
      `REGION` in `coverage.py`: `memcpy (dst, n)`, `memzero (dst, n)`, `rlp_encode_bytes (dst, n +
      9)`, `lst_push` header and array, …), plus the global buffers the closure writes (computed,
      e.g. `keccak_pad`, `keccak_st` for `keccak256`);
    - `R` is just the global buffers for the 30 callees whose every store lands in a block their
      own closure allocated or in a global buffer (computed, `fresh_only`).
  - `KeepsOn P W g` (55; revision 4 printed 59, corrected in revision 6 as Astra's round-4
    non-blocking item asks): the reviewers' `PreservesOn WorldOK WorldOK` restricted to resuming
    outcomes. `W` is the caller's world guard: `WorldOK`; `EvmInv` inside `finish_child` and after
    `frame_open` in `process_message`; `ArenaReady` in the decoder and MPT tier. `P = W` except:
    - guarded callees, where `P` is their own guard (`TxReady`, `ReqsFresh`, `MsgReady`, …);
    - `requests_append` (`ReqRoom`);
    - `mpt_set`, `mpt_root`, `compute_state_root`, `build_mpt_indexed` (output region outside the
      world, typed trie object);
    - `frame_open` in `process_message`: `KeepsOn FrameOpenReady EvmInv`, because it builds the
      outermost frame.
  - `NodeFn names g` (7): the node-returning callees of the MPT tier (`node_new_leaf`,
    `node_new_ext`, `_insert_into_leaf`, `_split_extension`, `_collapse_branch`,
    `_delete_ext_finish`, `node_invalidate`). It has the `MptExit` shape: every typed node set
    rooting the node parameters `names` extends to a typed set of the post-state; writes stay
    inside those node records and the free heap; the returned word is a typed node or `0`. That is
    what `_mpt_insert_node`/`_mpt_delete_node_body` need to re-establish `MptReady` at their loop
    heads. None of these functions writes a global buffer (checked on their closures).
- **The bound** of each contract callee is its `fb_*`/`gb_*` leaf, also a hypothesis of
  `GBody.«f»`.

### Astra 6, blocking

**1. Zero-capacity logs.** Fable item 3 above (`1 ≤` capacity for stack and logs).

**2. Unowned return-data buffers.** Fable item 4 above (`frameRet` owned, disjoint; output windows
`RetWindowsOK`).

**3. Release marks did not protect surviving tables.** `MarksOK` now takes the table set `S`. For
each child position `i` (mark `m_i = c_i+48`), every table of `S` that is not the deletion table
`e_j+136` of a frame `j ≤ i` has its whole footprint in the heap or in `[m_i, scratchEnd)`. Likewise
every non-empty fixed object. The only table ever built in scratch is a frame's deletion table:
`htab_new_scratch` has the single caller `frame_new`, and `htab_copy_scratch` is unreachable.
Astra's witness (a shared `htab_new_scratch` table below the child's mark) violates the new
conjunct.

### Non-blocking (both reviewers)

- *`cap` bound*: `HtabNewReady` requires `cap ≤ htabCapMax = 2^32` instead of membership in a
  literal list. `nodedb_build` (9948) passes a computed power of two; `htabCaps` is removed.
- *`MainEntry`*: `localsFree_mainEntry` and `localsOnly_mainEntry` (proved).

### Gemini 4 Carbon, blocking (review of revision 3)

**1. `op_dispatch_spec` false via the saturated memory-cost sentinel (`op_extcodecopy`,
`op_mstore`, …).** With a frame's gas at `2^64 − 1`, `charge_gas` accepts the `2^64 − 1` that
`extend_memory_cost1/2` return on overflow, `extend_memory(0)` does nothing, and the opcode writes
outside EVM memory. `EvmInv` now requires `R + 1 < 2^64`, where `R = Σ (gas + spilled)` over the
chain, so every frame's gas is below the sentinel. `R` never grows along `run_frames` (the
potential argument), and `MsgReady` bounds its start (item 2). The copy-back window is
`RetWindowsOK` (Fable item 4).

**2. Establishing the gas bound.** `MsgReady` requires `msg+40 < 2^63`. `frame_new` copies it to
`e+64`, and `e+192` starts at 0 (`memzero`). `process_transaction` gets `mgas ≤ 16777216` after
`validate_transaction`; system calls use `30000000`.

**3. Unconstrained pointer parameters.**
- `process_message`, `process_message_call`, `process_create_message` are guarded by `MsgReady`.
  The 176-byte message record is now owned too: allocated, words, and disjoint from every typed
  table and fixed object. So `depth0_prepare`'s stores through `msg` cannot reach the world, and
  the access tables are typed.
- `state_init`, `mpt_from_witness`, `compute_state_root`, `build_mpt_indexed`: the bound leaves
  `gb_*` hold for any parameters, because a wild pointer only makes a load fail. The
  write-parameter scan (`written_params`) shows none of them writes through `nodedb`/`db`/
  `root_hash`. The `out` buffers of `compute_state_root`/`build_mpt_indexed` are constrained where
  it matters, in their `KeepsOn (WorldAvoids …)` contracts.

**4. Nested objects.**
- The `bo` objects are `blockOutObjects` (§0.3 below), and `index < ntx` is `TxReady`.
- The BAL account records are new: `balRecords` (the live values of `bal_accounts`) and
  `balObjects` (each 40-byte record, plus the headers and backing arrays of its 40-, 16- and
  24-byte lists). Both are in `fixedObjects`, so they are allocated, pairwise disjoint and disjoint
  from every table.
- `TablesTyped` requires the records' two tables in `S` and every list (BAL and `bo+40/+72`)
  `LstOK` (`1 ≤ cap`, `len ≤ cap`).

**5. MPT contracts false.**
- `NodeHeap` hard-coded 176-byte nodes. It now sizes nodes by kind (`nodeSize`: hashed 32, leaf
  64, extension 56, branch 176; `node_new_*` 9975-10060) and requires `kind ≤ 3`. `TriesTyped`,
  `MptObjReady`, `MptExit` and `NodeFnExit` use `nodeIvl`.
- `MptExit` did not frame `_mpt_delete_node_body`'s unreleased 40-byte scratch frames. It now
  keeps the free scratch gap `[frame_mem_ptr, scratch_ptr)` at entry, and has the missing globals
  frame. `HtabNewExit` gains the globals frame too.
- Cycles (5b): Gemini's own trace shows they only lead to timeouts or the `level` bound, which
  `FunSpec` (non-timeout runs) and `K` already cover. No acyclicity conjunct is added.

**Non-blocking.**
- `bls_discount`, `bn_gamma`, `bn_expw`, `precompile_addrs` and `zero_hashes` (allocated with
  constant products) are now in `globalBuffers`: the generator folds `*`/`+` of literals.
- The `htabCaps` comment is gone with `htabCaps`.
- Lean and `#print axioms` were re-run (§9).

### What the composition analysis found (new, round-3 item 5)

The write-root scan over the guarded bodies and the guard-carrying callees found writes through
pointer fields of the global record `bo` that `WorldOK` did not own:
- the transaction and receipt arrays `bo+24`, `bo+32` (`process_transaction` 33368-33374);
- the request array `bo+56` (`requests_append`);
- the logs and requests lists `bo+40`, `bo+72` (`lst_push` from `process_transaction`).

With those unowned, `KeepsOn WorldOK WorldOK process_transaction` would be false: `bo+24` could
alias a table. The new `blockOutObjects` (in `fixedObjects`) owns them. Their index bounds become
guards:
- `TxReady` for `process_transaction` (`index < bo+80`);
- `ReqsFresh` for `process_general_purpose_requests` (`bo+64 = 0`: no request recorded yet);
- `ReqRoom` for `requests_append`.

Every other world write goes through a typed table slot (`ws+32`, `bs+8…+72`, `ts+8…+64`) or a
global buffer. The message path needs the message's access tables typed when `frame_open` copies
them into the outermost frame, hence `MsgReady` for `process_message`, `process_message_call` and
`process_create_message`.

## 0.4 Changes in revision 4 (since 1c54006ca, revision 3)

Mechanical statement diff of the two Lean files (`theorem`/`def`/`structure` signatures, comments
dropped; script in §9).

**Changed leaf statements: none.** All 727 `fb_*` and all 14 §7 contract leaves are textually
unchanged. So the speculative provers' `fb_*` targets (arith, rlp, htab) are stable.

**Changed guarded bounds (5), now proved theorems rather than leaves:**
- `gb_process_transaction`: guard `WorldOK` → `TxReady`;
- `gb_process_general_purpose_requests`: guard `WorldOK` → `ReqsFresh`;
- `gb_process_message`, `gb_process_message_call`, `gb_process_create_message`: guard `WorldOK` →
  `MsgReady`.

The other 42 `gb_*` statements are unchanged and now proved.

**Changed definitions (14 by the diff: `EvmInv`, `FrameWF`, `HtabNewExit`, `HtabNewReady`,
`MarksOK`, `MptExit`, `MptObjReady`, `NodeHeap`, `TablesTyped`, `TriesTyped`, `fixedObjects`,
`frameObjects`, `globalBuffers`, and the proved helper `while_rank_stationary_aux`), and the leaves
whose meaning they change:**
- `FrameWF`: `1 ≤` stack and logs capacity; return-data buffer owned. This affects `EvmInv`, hence
  `op_dispatch_spec`, `frame_exception_spec`, `frame_epilogue_spec` and `finish_child_spec`.
- `frameObjects`: adds `frameRet`, with the same effect.
- `EvmInv`: adds `RetWindowsOK`, with the same effect.
- `MarksOK`: takes `S`, and keeps surviving tables and fixed objects outside the child's scratch.
  Same effect.
- `fixedObjects`: adds `blockOutObjects`. Through `TablesTyped`, `FixedTyped`, `TriesTyped`,
  `WorldOK`, `EvmInv` it affects:
  - every §7 contract leaf that mentions `WorldOK`/`EvmInv`: `mem_init_world` and the four frame
    contracts;
  - every new `KeepsOn` contract.
- `HtabNewReady`: `cap ≤ htabCapMax` (was `cap ∈ htabCaps`). It affects `htab_new_spec` and
  `htab_new_scratch_spec`, whose pre-condition is now weaker, so the leaves are stronger.
- Gemini items (also changed definitions; they change the meaning of the leaves that mention
  them):
  - `EvmInv`: adds `R + 1 < 2^64`. This affects the four frame contracts.
  - `NodeHeap`: nodes sized by kind (`nodeIvl`), `kind ≤ 3`. Through `TriesTyped`, `MptReady`,
    `MptObjReady`, `MptExit` it affects `mpt_insert_node_spec`, `mpt_delete_node_body_spec` and
    every `WorldOK`/`EvmInv` leaf.
  - `MptExit`: frames the free scratch gap and the globals. This affects the two MPT specs, which
    are now true on `_mpt_delete_node_body`'s scratch frames.
  - `HtabNewExit`: adds a globals frame. This affects `htab_new_spec` and `htab_new_scratch_spec`.
  - `TablesTyped`: BAL account records' tables typed and lists `LstOK`; `bo` lists `LstOK`.
  - `fixedObjects`: adds `balObjects`.
  - `globalBuffers`: +5 buffers.
- `while_rank_stationary_aux` (proved helper): body bound required only at active heads.

**Removed:** `htabCaps`.

**New proved theorems:**
- `callHandle_on`, `while_rank_active`, `while_rank_stationary_active`, `loopActive_decClock`;
- `ReadOnlyFn.keepsOn`, `worldOK_of_evmInv`, `msgReady_worldOK`, `worldOK_guestInv`,
  `evmInv_guestInv`;
- `localsFree_mainEntry`, `localsOnly_mainEntry`, `localsOnly_txReady`, `localsFree_reqsFresh`,
  `localsOnly_msgReady`, `localsOnly_frameOpenReady`;
- the 47 `gb_*`, `assembly_main`, `assembly`, `primitives`, the 12 concrete `gbody_*` and their
  `lookup_*`;
- composition helpers: `TerminatingProgBoundedOn.mono_bound`, `of_clock`, `seq_guestInv_after`,
  `seq_clock`, `clock_return`, `clock_raise`, `clock_shMemStore`, `clock_assign`,
  `callEntryOn_of_localsFree`, `callEntryOn_of_imp`, `decCallResumeOn_guestInv`,
  `ReadOnlyFn.resumeOn`;

**New definitions:**
- `frameRet`, `RetWindowsOK`, `blockOutObjects`, `htabCapMax`;
- `Resumes`, `ReadOnlyFn`, `KeepsOn`, `WritesWithin`, `WorldAvoids`, `NodeArgs`, `NodeFnExit`,
  `NodeFn`;
- `TxReady`, `ReqsFresh`, `ReqRoom`, `MsgReady`, `FrameOpenReady`;
- `NodeArgs`, `NodeFnExit`, `NodeFn`, `nodeSize`, `nodeIvl`, `lstObjects`, `LstOK`, `balRecords`,
  `balObjects`;
- the 47 `GBody.«f»`, `Primitives`.

**New leaves (177):** 142 callee contracts (`ro_*` 30, `ww_*` 50, `wk_*` 47, `ek_*` 6, `ak_*` 1,
`fk_frame_open`, `nf_*` 7) and 35 `gbody_*`. (Revision 4 printed 46 and 51 here; the round-4
review counted 50 and 47. Revision 5 counts are in §0.2.)

**Proved compositions (12):** `gbody_attempt_l1` … `gbody_attempt_l7`,
`gbody_verify_stateless_new_payload`, `gbody_incorporate_tx_into_block`, `gbody_mpt_from_witness`,
`gbody__decode_witness_node_mpt` and `gbody__decode_witness_node`. Each reads its body off the
installed code (generated `lookup_f`) and walks it with the §3 combinators. Guards are carried by
locals-freeness, by `callEntryOn_of_imp`, and across `scratch_mark` by its `ro_` contract
(`ReadOnlyFn.resumeOn`). The bound closes by `omega` against the generated `K.«f»`.

**Unchanged:** every `K.«f»`, `K_pan`, `K_pan_budget`, the bridge, the glue
`run_frames_step_of_specs`, every revision-3 combinator statement.

## 0.5 Round-2 items and how each was addressed (revision 3)

### Fable 5.1

Fable 5.1's review (`campaign/reviews/guestinv-r2.md`). Every combinator below is proved, and
`#print axioms` on each gives `[propext, Classical.choice, Quot.sound]` (§9).

**Blocking 1: `htab_new_spec` / `htab_new_scratch_spec` false for a wild `key_len`.** Both are now
guarded by `HtabNewReady = ArenaReady ∧ locN s "key_len" ∈ htabKeyLens`. The 32 call sites all pass
a literal (15×20, 1×28, 8×32, 7×52, 1×60, re-counted on the AST), so the caller discharges the
guard by evaluating the argument. `localsOnly_htabNewReady` is proved.

**Blocking 2: `finish_child_spec` false for a full suspended parent.** `EvmInv` gains
`∀ ec ∈ (evmChain s).tail, FrameRoom s ec`, where `FrameRoom` is `height + 1 ≤ capacity` (`e+16`,
`e+232`). Only the six frame-opening opcodes make a frame non-current, and each pops before
`generic_call`/`generic_create`: `op_call`/`op_callcode` pop 7 and push at most 1;
`op_delegatecall`/`op_staticcall` pop 6; `op_create` pops 3 and `op_create2` pops 4. So
`op_dispatch_spec`, whose post-state is `EvmInv`, discharges `FrameRoom` for the new parent at
`op_call`/`op_create`. In `finish_child`, `stack_push` on the parent then never allocates, and
`scratch_release(child_mark)` keeps the parent's stack. `finish_child_spec`'s pre-state is the
strengthened `EvmInv`; its post-state needs `FrameRoom` only for the grandparents, which is
unchanged.

**Blocking 3: the decomposition was not closed by the stated combinators.**
- *Tail calls* (`Prog.call none`, 88 sites in 75 functions): `TerminatingProgBoundedOn.tailCall_on`
  (callee guard from `CallEntryOn`) and `tailCall_guestInv` (no call-site obligation), bound
  `B + 1` like `call_on`.
- *Stationary iterations*: `TerminatingProgBoundedOn.while_rank_stationary`. Each continuing
  iteration from an active `P` head either lowers `μ ≤ N` or is `Stationary`: an exact repeat
  (`SameHead s t`: all fields but the clock agree) or a state from which the loop times out
  (`WhileTimesOut`). The proof is the `while_noRepeat` induction (`wave8/step0`), with the
  visited-key count replaced by `μ` and the key collision replaced by `SameHead`. Its three helper
  lemmas are copied verbatim because that file is not on this branch's cone. `while_rank` is now
  the corollary without stationary steps; its statement is unchanged.
  A loop that becomes stationary only after a warm-up iteration uses
  `μ = 2·rank + [the next iteration is not an exact repeat]`. The per-loop arguments (§4 table) are:
  - `htab_truncate`: see the next item.
  - `fq12_inv` #1: `μ = 2(d0+1) + [not yet stationary]`. With `fq_inv(lead) = 0`, `cf = 0` and the
    writes to `q` and `r0` are idempotent from the second iteration on.
  - `fq12_inv` #0: an iteration whose inner loop times out times out.
  - `sort_elems` #1 at width `0`: `mid = right = left` and `left := right`, an exact repeat.
  - `sort_elems` #0: width `0` makes #1 time out.
  - `_mpt_insert_node` self-loop: `node_invalidate` and `store(slot, node)` are idempotent from the
    second iteration on.
- *`htab_truncate` justification.* "Every iteration is a successful `htab_del`" was wrong:
  `HtabWF` does not constrain key bytes, so `htab_find_leaf` on the last leaf's key may reach
  another leaf, and `memeq` may reject it. The corrected argument is
  `while_rank_stationary` with `μ = count (t+24) < 2^64`. Each iteration either deletes a leaf
  (count drops by one) or returns 0 having written nothing, and then the loop head repeats exactly.
  The count decrement is a NEW additive leaf, `htab_del_progress_spec : FunSpec HtabArgWF
  (OnReturn HtabDelProgress) "htab_del"`. `HtabDelProgress` says the count dropped by one, or the
  post-state equals the entry state up to locals and clock. `htab_del_spec` is unchanged, so
  provers building on it are unaffected.
- *`dec` for guards that read locals*: `LocalsOnly names P` (P reads locals only through `names` and
  ignores the clock). `TerminatingProgBoundedOn.dec_onLocals` needs the declared name to be outside
  `names`, which holds for every `dec` in a guarded body. Supporting lemmas:
  - `LocalsOnly.decClock` discharges `hdec` of both `while` rules;
  - `LocalsOnly.setVar` handles setting a local the guard does not read;
  - instances are proved for every guard: `localsOnly_htabArgWF` (`t`), `localsOnly_unionArgWF`
    (`dst`), `localsOnly_mptReady` (`node`), `localsOnly_mptObjReady` (`m`),
    `localsOnly_rollbackReady` (`child`), `localsOnly_htabNewReady` (`key_len`), and
    `localsFree_{arenaReady,worldOK,evmInv,finishReady}`.
- *Also closed, because the guarded leaves need them*:
  - `decCall_on`: the continuation guard `Q` comes from `DecCallResumeOn`, i.e. the callee's
    contract plus `LocalsOnly`;
  - `ite_cond_on`: each branch may use the outcome of the test (`CondTrue`/`CondFalse`), e.g. the
    `kind ≠ 0` test before `finish_child`;
  - `callHandle_guestInv` (proposed in revision 2) is now proved.

**Non-blocking.**
- *Read-only loops with struct-shaped keys.* `classify` now counts the words of every carried
  local (`local_words`: parameter and `dec` shapes), so the default `RO(k)` is `2^(64·words)`. The
  loops this re-sizes are exactly the ones Fable listed: `modinv_bin` #0-2, `bls_fp_inv_raw` #0-2,
  `fq12_mul` #1, `fq12_sqr` #1, `p256_fp_mul` #0-1, `p256_fp_sqr` #0-1. Each is now an `OVERRIDES`
  entry with its real measure (§4 table) and its revision-2 `N`, which is an upper bound. So
  `K.«f»` is unchanged, and the generated `kgen.lean` is byte-identical to revision 2's. The
  measures:
  - binary gcd: bit length of the odd parts;
  - halving loops: trailing zeros, or divergence at `u = 0`;
  - `fq12_mul`/`fq12_sqr` #1: counters (`iend ≤ 11`, `k ≤ 22`);
  - `p256` carry loops: `2|c| + [phase]`.
- *`rlp_list_count`* is reclassified `MONO`: the measure is `len − off`, since `rlp_item_header`
  returns `1 ≤ hl + pl ≤ len − off` or raises. The body is not read-only, as Fable notes.
- *Arithmetic facts behind `taylor_exponential` and `fq12_inv`* are listed as explicit prover
  obligations in §8 (Q6).

### Astra 6 (appended review)

**1. `FrameOutside` forbade every memory change.** It quantified over `a : Nat` and read
`BitVec.ofNat 64 a`, so `x + 2^64` was an outside alias of every changed `x`. It now quantifies over
`a : BitVec 64` and tests the intervals with `a.toNat`. The proved regression `example` shows a
single store inside `fresh` respects the frame.

**2. `HtabNewExit` intersected two frames.** It is now one `FrameOutside` over the union: the fresh
scratch interval is in `keep`, the fresh heap interval is `fresh`.

**3. Constructor parameter limits.** `HtabNewReady` also requires `cap ∈ htabCaps = [4, 8, 16, 64,
256]`, the literals of the same 32 call sites (1×4, 8×8, 6×16, 12×64, 4×256, re-counted on the
AST). `key_len ∈ htabKeyLens` was already required for Fable's item 1. `localsOnly_htabNewReady` now
reads both locals.

**4. `HtabWF` admitted disconnected cycles.** It now also requires
`∃ dep : Nat → Nat, ∀ n ∈ L ++ I, n ≠ root → (nd (nd n 0) 8 = n ∨ nd (nd n 0) 16 = n) ∧
dep (nd n 0) < dep n`. This makes the tree rooted and acyclic: following parents strictly lowers
`dep`, so it reaches the root, and descent through children reaches a leaf.
- Astra's counterexample (node 3 is its own parent) is excluded; `htabWF_no_self_parent` proves it.
- With a genuine tree, `htab_del` of any leaf splices the sibling into the grandparent, which keeps
  `HtabWF`.
- The key-bit (search) invariants are not needed for well-formedness or termination: `find_leaf`
  and the `htab_set` descent are bounded read-only loops, and `htab_truncate` uses
  `htab_del_progress_spec`.

**5. `EvmInv` missed the logs backing arrays.**
- `frameObjects` gains `frameLogs` (data `+0`, capacity `+16` of the logs header `e+88`, 8-byte
  elements), so it is pairwise disjoint from every frame block, table and fixed object. Astra's
  `data = ev+64` case now violates disjointness.
- `FrameWF` allows the array in the allocated heap OR scratch: `lst_push` (13842) regrows it on the
  heap.
- `MarksOK` constrains only the scratch blocks (`frameScratch`) and requires each ancestor's logs
  array to be on the heap or above the child's mark.

**6. Assembly not closed.**
- `callHandle_guestInv` and `while_rank` are proved (above).
- The `htab_del` count decrease is `htab_del_progress_spec` (above).
- **`run_frames_step_of_specs` is now PROVED.** A small proved outcome-triple layer (`Hoare` with
  `skip`, `seq`, condition-aware `ite`, `dec`, `assign`, handler-free `call0` and handler `callH`
  over `FunSpec` callees) evaluates the concrete `run_frames` loop body. It is read off the
  installed code by `lookup_run_frames` and the structural translation. The loop tests (`cur_cont+32`,
  `ev+104`, `pc ≥ ev+56`, `done`, `cur_cont+16`) are decoded by proved evaluation lemmas.
  `evmPot_lt_bound` turns "`R` not larger, `F` smaller" into a strict decrease under `EvmInv`.
- `run_frames_step` therefore depends only on the four frame contract leaves.

**`gb_main` stays a leaf, by design.** *(Superseded in revision 4: the round-3 assembly ruling made every `gb_*` a proved theorem over the `gbody_*` primitives, §0.1.)* Every `fb_*`/`gb_*` leaf, `gb_main` included, is a
*composition leaf*. Its proof is a walk over its own body with the proved §3 combinators, using
only its callees' leaves, its loops' measures and, in the guarded tier, the §7 contracts, the
proved `LocalsOnly`/`Hoare` facts and the proved glue. Proving those walks is the leaf provers'
work; this role does not prove leaves. What is closed now is everything between the leaves and the
target:
- every combinator;
- the glue;
- the guard-transport lemmas;
- the bridge;
- `K_pan_budget`.

The only `sorry`s are leaf statements: 14 contracts, 727 `fb_*` and 47 `gb_*`. Each is a statement
about one function's code. `coveredSourceTicksConsumedBounded_K_pan` applies the bridge to
`gb_main`, so the end-to-end theorem's `sorryAx` dependencies are exactly the leaves.

**Non-blocking.**
- `RO(k)` word sizing and `modinv_bin`: see Fable's non-blocking item above.
- The tautological `example` (`HtabWF s t → HtabWF s t`) is removed. It is replaced by semantic
  regressions:
  - `htabWF_no_self_parent` (item 4);
  - the `FrameOutside` store `example` (item 1);
  - the `dec_onLocals` name check;
  - the proved glue itself, which exercises the frame contracts on the real loop body.

## 0.6 Changes in revision 3 (since 7e73988d)

Mechanical statement diff of the two Lean files (`theorem`/`def`/`example` signatures, comments
dropped).

**Changed leaf statements (2):**
- `htab_new_spec`, `htab_new_scratch_spec`: guard `ArenaReady` → `HtabNewReady` (adds
  `key_len ∈ htabKeyLens ∧ cap ∈ htabCaps`); the exit `HtabNewExit` frames the union of the fresh
  heap and scratch.

**Changed definitions (7), which change the meaning of the leaves that mention them:**
- `FrameOutside` (BitVec addresses). Through `HtabExit`, `UnionExit`, `HtabNewExit` and `MptExit` it
  affects `htab_set_spec`, `htab_del_spec`, `htab_truncate_spec`, `htab_union_into_spec`,
  `htab_new_spec`, `htab_new_scratch_spec`, `mpt_insert_node_spec` and `mpt_delete_node_body_spec`.
  Every one of them is now satisfiable by real stores; in revision 2 none could change memory.
- `HtabNewExit` (one union frame).
- `HtabWF` (rooted, acyclic). Through `HtabArgWF`, `UnionArgWF`, `RollbackReady`, `TablesTyped`
  (so `WorldOK`) and `EvmInv` it affects:
  - the table contracts (stronger pre- and post-condition);
  - `htab_del_progress_spec`;
  - every guarded leaf (`gb_*`), whose guard is stronger;
  - `mem_init_world` and every frame contract.
- `frameObjects` (adds the logs array), `FrameWF` (logs array on heap or scratch), `MarksOK`
  (scratch blocks only), `EvmInv` (adds `FrameRoom` for suspended frames). These affect:
  - `op_dispatch_spec`, which must establish `FrameRoom` at `op_call`/`op_create` and keep the logs
    array owned;
  - `frame_exception_spec`, `frame_epilogue_spec`, `finish_child_spec`;
  - `gb_run_frames`, `gb_finish_child`, `gb_process_message`.

**New leaf (1):** `htab_del_progress_spec`.

**No longer a leaf (1):** `run_frames_step_of_specs` (statement unchanged, now proved).

**Unchanged:**
- all 727 `fb_*` and 47 `gb_*` statements (textually);
- every `K.«f»`, `K_pan`;
- the bridge;
- `while_rank` and `callHandle_guestInv` (statements kept, now proved).

Docstrings of 7 `fb_*` leaves changed (loop-class label only, e.g. `RO(4)` → `MONO`):
`rlp_list_count`, `modinv_bin`, `bls_fp_inv_raw`, `fq12_mul`, `fq12_sqr`, `p256_fp_mul`,
`p256_fp_sqr`. The arithmetic leaf provers (`wave8/leaves-arith-astra`) and the RLP leaf provers
(`wave8/leaves-rlp-opus55`) prove `fb_*` statements, which are textually and semantically
unchanged (no `fb_*` mentions a changed definition).

**New proved theorems:**
- combinators: `tailCall_on`, `tailCall_guestInv`, `while_rank_stationary` (+ `_aux`),
  `dec_onLocals`, `decCall_on`, `ite_cond_on`;
- the `Hoare` layer: `Hoare.{of_false,mono,skip,seq,ite,dec,assign,call0,callH}`,
  `FunSpec.at_lookup`;
- the glue and its lemmas: `lookup_run_frames`, the `evalAt_*`/`cond*` evaluation lemmas, and the
  `evm*`/`evmPot_lt_bound` potential arithmetic;
- the `LocalsOnly`/`LocalsFree` instances and their congruence lemmas;
- `htabWF_no_self_parent`.

**New definitions:**
- `FrameRoom`, `frameLogs`, `frameScratch`, `htabCaps`, `HtabNewReady`, `HtabDelProgress`;
- `SameHead`, `WhileTimesOut`, `Stationary`, `LocalsOnly`, `PostLocalsOnly`, `CondTrue`,
  `CondFalse`, `DecCallResumeOn`, `Hoare`;
- `evmFp`, `evmS`, and the glue's assertion predicates `GPre … GPh4`.

## 1. Round-1 blocking items and how each is addressed

### Item 1. `PreservesOn.call_guestInv` false for global destinations

`GuestInv` no longer mentions globals at all (§2). Its four fields are preserved by **every** Pancake
evaluation: `evaluateHOLFiniteState_metadata` gives code/memaddrs/shMemaddrs, and Flapjack's
`evaluateInvariantsHOLFinite` gives baseAddr. So `PreservesOn.call_guestInv` is now a proved
theorem for every destination, including globals. The regression `example`
`call heap_mark → journal_n` is checked in the file. The round-1 conjuncts it dropped are:
`heap_ptr ≤ 0xb0000000`, `ArenaOK`, `journal_n ≤ journal_cap`, and globals well-shaped. They were
never needed by an unguarded bound once bounds use local counters. They come back only inside the
guarded-tier contracts (`ArenaOK`, `JournalTyped`), with explicit preservation obligations.

### Item 2. False W-based constants

Every constant is now **(iteration bound) × (body cost including callees)**, generated mechanically
(§3, §9) from loop measures that hold for arbitrary memory and globals. The counterexamples no longer
apply. Each has an `example … ≤ K.«f» := by decide` in §8 of the Lean file:

| Round-1 counterexample | Why it is covered now |
|---|---|
| `sort_elems`, `esz = 0`, `n = 2^62` | outer loop ≤ 65 (width doubles), middle ≤ 2^64 (`left` strictly increases, caps are unsigned), merge ≤ 2^65 (measure `(mid−i)+(right−j)`); no memory fact used. `2^62 ≤ K.«sort_elems»` |
| `htr_payload`, `htr_new_payload_request`, `ntx = 2^59` wrap | all loops are strict counters (2^64 each) times the full callee cost (`htr_pbytes` included). `2.9·10^16 ≤ K` |
| `_mpt_insert_node` / `trie_walk`, self-looping extension | `trie_walk` is read-only: no-repeat on its carried locals (2^64 per local). `_mpt_insert_node` is in the guarded tier (`MptReady`), bound `2^130 · body` |
| `tx_scalar_word`, `hdr_word_field`: `rlp_list_count` over `W−10` bytes of `0xc0` | `rlp_list_count` is read-only, with no-repeat key `(off, count)` = 2^128, times its callee costs. `9W ≤ K` |
| `_decode_witness_node_body`, `klen ≈ W/2` lookups | each `memeq` is a strict counter (2^64), multiplied through; the loop is in the guarded tier (`ArenaReady`) with ≤ 2^68 iterations |

### Item 3. `finish_child` / `htab_union_into` aliasing

`htab_union_into` loops on `i < cap` (signed), with `i := i + 1` unconditional and `cap` a local
cached at entry. That gives a strict counter of ≤ 2^64 iterations, **whatever** `src`/`dst` alias
(including `src = dst` and `count` zeroed by the first insertion). Its bound is GuestInv-only:
`K.«htab_union_into» = 1 + (2^64 + 1)·(K.«htab_item» + K.«htab_set» + 3) + …` (generated).
`merge_tx_into_block`, `incorporate_child_on_success` and every other caller get it by plain call
composition. `finish_child` is guarded (`FinishReady`) for one reason only: it calls
`rollback_child_access → htab_truncate`, the one table loop with no arbitrary-memory measure
(item 4). Its constant includes every callee transitively (`state_restore`, `create_finish`,
`incorporate_*`, union, truncate, logs). The round-1 example `2^62 ≤ K.«finish_child»` is checked.

### Item 4. `HtabWF`

- **Counter bounds where possible.** `htab_set`, `htab_del`, `htab_find_leaf`, `htab_keys`,
  `htab_union_into` and `state_restore` are GuestInv-only. `find_leaf` and the descent in `htab_set`
  are read-only no-repeat loops (key `n`, resp. `(p, n)`). `memeq`, `first_diff` and `memcpy` are
  counters or walks. `htab_keys` is a counter. `state_restore` decrements the global `journal_n`,
  which no callee writes (checked by the script's global-write closure).
- **The real structural invariant** for the one loop that needs it (`htab_truncate`: count `t+24` is
  re-read from memory and rewritten by `htab_del`). `HtabWF` (§5) is the crit-bit invariant:
  - the allocated indices `[1, next)` split into live leaves `L` (listed by `order[0..count)`),
    internal nodes `I` with `|I| + 1 = count`, and the free list `Fr` headed at `t+72`;
  - parent, child, order-position and root are all constrained;
  - the leaf value `+8` is **not** constrained (round 1's bug).

  This gives `count ≤ ncap`, and every index the code computes stays in its block.
- `maxKeyLen = 60` and stride `≤ 64` (`bal_init` uses 28 and 60).
- Preservation obligations are explicit contract leaves: `htab_set_spec`, `htab_del_spec`,
  `htab_truncate_spec`, `htab_union_into_spec`, `htab_new_spec` and `htab_new_scratch_spec`. Each
  exit contract keeps `HtabWF` and states the **write frame**: memory outside the table's old
  footprint and the freshly allocated heap is unchanged, the new footprint is old ∪ fresh, and no
  global other than `heap_ptr` changes. The frame is what keeps every *other* table, frame and
  buffer intact.

### Item 5. `EvmFramesWF`

Replaced by `EvmInv` and the gas-value-free potential `evmPot` (§5, §6 here):

- **No gas conjunct.** `evmPot = R·(F_max·S_max) + F·S_max + S` with
  `R = Σ(gas + spilled)`, `F = 2·depth + [running]`, `S = Σ state gas`. Every word is
  `< 2^64` and depth ≤ `maxChain`, so `evmPot < evmPotMax ≈ 2^173` for **arbitrary** gas words.
  Minting through `refill_frame_state_gas` (`gas += spilled; sgas := msg+48; spilled := 0`) keeps
  `R` and only changes `S`, which is lower priority and is bounded by word size. The round-1
  `2^62`-mint counterexample is therefore harmless, and no `msg+48` relation is needed.
- **Stack/frame/continuation aliasing**: all frame blocks (record, continuation, stack, EVM memory,
  logs header) are pairwise disjoint and disjoint from every typed table and fixed object; the stack
  satisfies height ≤ capacity ≤ 1024, and memory length ≤ capacity.
- **Release marks**: `MarksOK` says releasing scratch to `c+48` and frame memory to `c+56` frees
  exactly the child's blocks and keeps every ancestor's blocks allocated.
- **Tables `e+136/+168/+176`**: members of the typed table set (`HtabWF`, allocated, disjoint).
- **The rest of the world**: `WorldTyped` covers the global tables (`ws`/`bs`/`ts` slots, `bal_*`),
  the two tables of tables (`bs+32`, `ts+32`), the journal (every record's table is typed), the
  fixed records and the persistent tries.

### Item 6. Closed decomposition

- **Composition.** `GuestInv` preservation is a theorem, so `call`/`decCall`/handler/`seq`
  composition needs no extra obligation (`decCall_guestInv` no longer takes `FunPreservesOn`).
  Every function on `main`'s call graph has its own leaf, and its constant is literally the
  composition of its callees' constants and its loops' measures. A leaf's proof therefore uses only
  the combinators, its callees' leaves and its loops' measures (§4).
- **Guards.** `finish_child → rollback_child_access → htab_truncate` now carry guards
  (`FinishReady` ⊇ `EvmInv` gives the typed child tables; `RollbackReady`, `HtabArgWF`).
  `incorporate_child_on_success → htab_union_into` needs none (item 3).
- **Coverage map**: §5, generated from the AST, lists all 774 reachable functions and 249 loops with
  their class, `N` and leaf. The 39 unreachable functions are listed too.
- **Top obligation**: made explicit (§2 below). It is `gb_main : TerminatingFunBoundedOn MainEntry
  "main" K.«main»`, a generated guarded leaf decomposed like every other leaf.
- **`K_run_attempt`**: there is no hand-written `K_run_attempt` any more. `K.«run_attempt»` is
  generated from the AST, so it counts every `process_message` call site reachable from
  `execute_block` (round 1 budgeted 4, the reviewers counted 6) with its loop multiplicity.

### Non-blocking items

- **Qualified name and adapter.** `coveredTarget_of_terminatingMainOnEntry` concludes the fully
  qualified `InitECandidate.Solver.UniformSourceClock.CoveredSourceTicksConsumedBounded`.
- **Frozen together.** Guards, contracts and constants are generated together by one script from one
  AST.
- **Regression `example`s** for items 1, 2, 3 and 4 are in the Lean file.
- **Modmul leaves.** `u256_addmod`, `u256_mulmod`, `p256_fp_mul` and `p256_fp_sqr` are ordinary
  generated leaves (their loops are counters).
- **`topAddr`** has been dropped from `GuestInv`.

## 2. The top obligation: `MainEntry` vs `GuestInv`

`main` is entered exactly once, from the covered post-declarations state. `MainEntry` records
everything true there:
- `GuestInv`;
- `CoveredFfi` (the input's declared gas ≤ 2·10^8);
- `InitialMemory` (the bootstrap image; `alloc` never zeroes, so `main` may rely on fresh cells
  being 0);
- `GlobalsZero` (all 67 globals = 0).

All four are proved at the entry (`guestInv_postDecls`, `coveredFfi_postDecls`,
`initialMemory_postDecls`, `postDecls_globals`). The campaign target needs exactly
`TerminatingFunBoundedOn MainEntry "main" K.«main»`. That is **stronger than needed for any other
function, and weaker than the round-1 claim** `TerminatingFunBoundedOn GuestInv "main"`, which would
quantify over arbitrary memory at `main`'s entry. For the covered target this is exactly what is
required. `gb_main`'s proof establishes `WorldOK` after `mem_init` (`mem_init_world`) and then
composes its callees.

`CoveredFfi` is no longer used by any bound: the EVM potential does not depend on gas values, so the
round-1 header↔input gas link (Q1) and the `wordGas` fallback are gone.

## 3. Loop measures (each `N` holds for arbitrary memory unless marked GUARDED)

The ranking rule `TerminatingProgBoundedOn.while_rank_stationary` (§3 of the Lean file, proved)
turns a measure `μ ≤ N` that strictly decreases on every continuing, non-stationary iteration into
the bound `(N+1)·(B+1)`; `while_rank` is the special case without stationary iterations. A
non-timeout run that ends by `error`/`raise`/`return` inside the body is covered as well.

| Class | Rule (checked syntactically by `coverage.py`) | `N` |
|---|---|---|
| `CTR` | local `i`, exactly one assignment `i := i ± c` in the body, executed unconditionally (top level of the body's seq/dec chain); test `i < X` (step +1, or any step ≥ 1 when `X` is a literal ≤ 2^62), `X > i`, or `i ≠ 0` / `i > X` (step −1); `X` loop-invariant (its variables are not assigned in the body; loads only in read-only bodies). Then `X − i` (resp. `i`) is a strictly decreasing natural number that never wraps | `2^64`, or `X` for an unsigned literal `X ≤ 2^16` |
| `GCTR` | same with a global counter that no callee writes (transitive global-write closure); only `state_restore` (`journal_n`) | `2^64` |
| `RO(k)` | read-only body: no store/storeByte/shMemStore/extCall, no global write, all callees pure (`trap_with` counts as pure: it always raises, so it never continues an iteration). No-repeat (`while_noRepeat`, `wave8/step0`) with key = the loop-carried locals, `k` = their total number of WORDS (a 4-word struct local counts 4) | `2^(64k)` |
| `WALK` | counter strictly increasing by a positive constant, and every iteration loads/stores `base + counter` (or `base + 32·counter`) in the contiguous `ordinaryDomain` (or the 1 GiB shared input window). The address leaves the domain within `W` iterations, long before any wrap | `W + 1`, `W = 31 104 957 928` |
| `MONO` | hand-checked strictly monotone measure (halving, doubling width, degree, Taylor index, bit length, carry potential); a non-decreasing iteration, if any, is `Stationary` (an exact repeat, or the rest of the loop times out): `while_rank_stationary` | per loop |
| `STACK` | explicit stack whose pushes call `scratch_alloc` (`scratch_ptr` strictly decreases, never wraps, never released inside the loop: ≤ 2^61 pushes for arbitrary globals); read-only between pushes (no-repeat) | `(2^61+1)·2^(64k)` |
| `ALLOC` | every iteration either pushes (`scratch_alloc`) or makes a net heap allocation `alloc(n ≥ 1)` (`heap_ptr` strictly increases; callees release only to marks they took) | `2^62` |
| `POT` | `run_frames`: `evmPot` under `EvmInv` (GUARDED) | `evmPotMax` |
| `WF` | `htab_truncate`: count `t+24` drops by one (`htab_del_progress_spec`) or the head repeats exactly (GUARDED, `while_rank_stationary`) | `2^64` |
| `GUARD` | `_decode_witness_node_body` (`ArenaReady`), `_mpt_insert_node`, `_mpt_delete_node_body` (`MptReady`) | per loop |

Why `CTR` needs the unconditional single update and a strict test: a loop whose exit test never
becomes false can still end by an error in the body after arbitrarily many iterations, and that is a
non-timeout run. A "deterministic orbit" argument is therefore **not** enough. Only a strictly
decreasing natural measure is. For the same reason `n ≥ i + 32` style tests and steps > 1 against a
non-literal bound are not `CTR`; all such loops in the guest are `WALK`s. The per-loop table in §4
gives the class, `N` and the justification of each of the 249 loops. Hand-checked loops carry their
argument in the `OVERRIDES` table of the script.

## 4. Cost model and nesting product

Pancake spends a tick only at a call and at a `while` iteration. So
`K.«f» = Σ_calls (K.«g» + 1 [+ handler]) + Σ_loops (N + 1)·(body + 1)`. `ite` takes the `max`, and
straight-line code is free; these are the frozen `ite`/`seq`/`dec`/`call` combinators plus the
§3 rules of the Lean file (`tailCall_on`, `callHandle_guestInv`, `decCall_on`, `dec_onLocals`,
`ite_cond_on`, `while_rank`, `while_rank_stationary`), all proved. The definitions in the Lean file are these formulas verbatim, symbolic in the callees'
constants. There is no recursion on `main`'s call graph (the script computes the SCCs: none). So the
definitions are well-founded and every leaf's proof uses only its callees' leaves.

The nesting product along the deepest chain (`out/chain.txt`, §5) dominates `K.«main»`.
`K_pan_budget` checks the whole sum by `decide`. `K_pan.log2 = 754`, so `K_pan < 2^755 ≈ 10^227`,
against the budget `(10^299 − 1)/10^4/32 ≈ 2^973`: a slack of 2^218. The dominant chain (§5) runs
tx loop 2^64 → `run_frames` potential 2^172 → witness decoder 2^68 → `rlp_list_count` 2^128 →
RLP validation stack 2^253, plus the callee bodies.


## 5. Coverage table (GENERATED by `coverage.py`; one row per function on `main`'s call graph)

The dominant nesting chain of `K.«main»` (`out/chain.txt`): at each step, the call with the largest
loop-multiplicity × callee bound, together with the log2 of the loop multiplicity it sits under.

```
main  log2K=755  -> verify_stateless_new_payload  (loop multiplicity log2 0)
verify_stateless_new_payload  log2K=755  -> attempt_l7  (loop multiplicity log2 0)
attempt_l7  log2K=755  -> attempt_l6  (loop multiplicity log2 0)
attempt_l6  log2K=755  -> attempt_l5  (loop multiplicity log2 0)
attempt_l5  log2K=755  -> attempt_l4  (loop multiplicity log2 0)
attempt_l4  log2K=755  -> attempt_l3  (loop multiplicity log2 0)
attempt_l3  log2K=755  -> attempt_l2  (loop multiplicity log2 0)
attempt_l2  log2K=755  -> attempt_l1  (loop multiplicity log2 0)
attempt_l1  log2K=755  -> run_attempt  (loop multiplicity log2 0)
run_attempt  log2K=755  -> execute_block  (loop multiplicity log2 0)
execute_block  log2K=755  -> process_transaction  (loop multiplicity log2 64)
process_transaction  log2K=691  -> process_message_call  (loop multiplicity log2 0)
process_message_call  log2K=691  -> process_create_message  (loop multiplicity log2 0)
process_create_message  log2K=691  -> process_message  (loop multiplicity log2 0)
process_message  log2K=691  -> run_frames  (loop multiplicity log2 0)
run_frames  log2K=691  -> op_dispatch  (loop multiplicity log2 172)
op_dispatch  log2K=519  -> op_sstore  (loop multiplicity log2 0)
op_sstore  log2K=518  -> get_storage  (loop multiplicity log2 0)
get_storage  log2K=517  -> ws_get_storage  (loop multiplicity log2 0)
ws_get_storage  log2K=517  -> ws_storage_trie  (loop multiplicity log2 0)
ws_storage_trie  log2K=517  -> decode_witness_to_mpt  (loop multiplicity log2 0)
decode_witness_to_mpt  log2K=517  -> _decode_witness_node  (loop multiplicity log2 0)
_decode_witness_node  log2K=517  -> _decode_witness_node_mpt  (loop multiplicity log2 0)
_decode_witness_node_mpt  log2K=517  -> _decode_witness_node_body  (loop multiplicity log2 0)
_decode_witness_node_body  log2K=517  -> _decode_step  (loop multiplicity log2 68)
_decode_step  log2K=449  -> rlp_decode_fully  (loop multiplicity log2 0)
rlp_decode_fully  log2K=448  -> rlp_item  (loop multiplicity log2 0)
rlp_item  log2K=448  -> rlp_list_count  (loop multiplicity log2 0)
rlp_list_count  log2K=447  -> rlp_item_total  (loop multiplicity log2 128)
rlp_item_total  log2K=319  -> rlp_validate_items  (loop multiplicity log2 0)
rlp_validate_items  log2K=319  -> _rlp_validate_items_body  (loop multiplicity log2 0)
_rlp_validate_items_body  log2K=319  -> rlp_item_header  (loop multiplicity log2 253)
rlp_item_header  log2K=66  -> rlp_read_length  (loop multiplicity log2 0)
rlp_read_length  log2K=65  -> rlp_fail  (loop multiplicity log2 0)
rlp_fail  log2K=0  -> None  (loop multiplicity log2 0)
```

Guarded tier, the functions called by guarded functions (`BETWEEN`, all unguarded), and the global
buffers (`globalBuffers` in the Lean file):

```
GUARDED 47: _decode_witness_node _decode_witness_node_body _decode_witness_node_mpt 
_mpt_delete_node _mpt_delete_node_body _mpt_insert_node attempt_l1 attempt_l2 attempt_l3 attempt_l4 
attempt_l5 attempt_l6 attempt_l7 build_mpt_indexed compute_state_root decode_witness_to_mpt 
execute_block finish_child get_pre_tx_storage get_storage get_storage_original htab_truncate 
idx_start_storage incorporate_tx_into_block main mpt_from_witness mpt_set op_dispatch op_sload 
op_sstore payload_header process_checked_system_transaction process_create_message 
process_general_purpose_requests process_message process_message_call process_transaction 
process_unchecked_system_transaction process_withdrawals rollback_child_access run_attempt 
run_frames state_init update_builder_from_tx verify_stateless_new_payload ws_get_storage 
ws_storage_trie
BETWEEN 239: _collapse_branch _decode_step _delete_ext_finish _insert_into_leaf _resolve_step 
_split_extension account_deployable add_balance_change add_code_change add_nonce_change 
add_storage_write address_to_u256 alloc bal_init bal_remove_change blake2_init block_rlp_length 
bls_precompiles_init bn254_init build_block_access_list_rlp cache_get_root calculate_blob_gas_price 
calculate_total_blob_gas charge_gas charge_state_gas check_gas check_gas_limit check_transaction 
clear_account_preserving_balance common_prefix_length compute_contract_address 
compute_requests_hash create_ether create_finish credit_state_gas_refund decode_host_input 
decode_transaction depth0_prepare destroy_storage encode_account encode_execution_requests 
encode_receipt encode_transaction encode_withdrawal_rlp evm_init ext_code_of extract_deposit_data 
fee_mul fork_init frame_epilogue frame_exception frame_halt frame_mem_release frame_open 
frame_start frame_state_gas_used get_account get_code header_hash header_init heap_mark 
heap_release htab_copy htab_del htab_get htab_has htab_item htab_new htab_set 
htr_new_payload_request idx_start_account incorporate_child_on_error incorporate_child_on_success 
increment_nonce is_valid_versioned_hashes is_warm_storage_key keccak256 keccak_init logs_bloom 
lst_new lst_push mark_account_created max mem_init memcpy memeq memzero merge_tx_into_block min 
mpt_fail mpt_init mpt_new mpt_nibble_key mpt_root msg_new node_invalidate node_new_ext 
node_new_leaf nodedb_build nodedb_lookup op_add op_addmod op_address op_and op_balance op_basefee 
op_blobbasefee op_blobhash op_blockhash op_byte op_call op_callcode op_calldatacopy op_calldataload 
op_calldatasize op_caller op_callvalue op_chainid op_clz op_codecopy op_codesize op_coinbase 
op_create op_create2 op_delegatecall op_div op_dup op_dupn op_eq op_exchange op_exp op_extcodecopy 
op_extcodehash op_extcodesize op_gas op_gaslimit op_gasprice op_gt op_iszero op_jump op_jumpdest 
op_jumpi op_keccak op_log op_lt op_mcopy op_mload op_mod op_msize op_mstore op_mstore8 op_mul 
op_mulmod op_not op_number op_or op_origin op_pc op_pop op_prevrandao op_push op_return 
op_returndatacopy op_returndatasize op_revert op_sar op_sdiv op_selfbalance op_selfdestruct op_sgt 
op_shl op_shr op_signextend op_slotnum op_slt op_smod op_staticcall op_stop op_sub op_swap op_swapn 
op_timestamp op_tload op_tstore op_xor output_write pc_add record_pre_state_read 
recover_sender_with_chain_id refill_frame_state_gas remove_storage_write requests_append 
require_not_static ripemd160_init rlp_decode_fully rlp_encode_bytes rlp_encode_word rlp_item 
scratch_alloc scratch_mark scratch_release secp256k1_init serialize_result set_account_balance 
set_retdata set_storage sha256_init sk_make ssz_init st_le64 stack_pop stack_push state_fresh_tx 
state_restore state_snapshot stor_lookup te_new track_ancestor_access trie_lookup tx_chain_id 
tx_has_access_list tx_is_blob tx_is_setcode u256_eq u256_from_be u256_is_zero u256_mul u256_sub 
u256_to_be32 u256_to_be_min u256_ws_init udiv_small5 validate_block_access_list_gas_limit 
validate_header validate_headers validate_transaction warm_storage_key ws_get_account_optional 
ws_storage_root_of
BUF b2_iv [('alloc', 64)]
BUF b2_sigma [('alloc', 80)]
BUF b2_v [('alloc', 128)]
BUF bal_key_buf [('alloc', 64)]
BUF be [('alloc', 120)]
BUF beacon_roots_address [('alloc', 24)]
BUF bls_c [('alloc', 7136)]
BUF bls_discount [('alloc', 2048)]
BUF bn_expw [('alloc', 352)]
BUF bn_gamma [('alloc', 384)]
BUF bo [('alloc', 88)]
BUF bs [('alloc', 80)]
BUF builder_deposit_address [('alloc', 24)]
BUF builder_exit_address [('alloc', 24)]
BUF consolidation_request_address [('alloc', 24)]
BUF deposit_contract_address [('alloc', 24)]
BUF deposit_event_signature_hash [('alloc', 32)]
BUF empty_code_hash [('alloc', 32)]
BUF empty_trie_root [('alloc', 32)]
BUF evm_empty [('alloc', 8)]
BUF evm_key_buf [('alloc', 32)]
BUF hdr_zero8 [('alloc', 8)]
BUF history_storage_address [('alloc', 24)]
BUF keccak_pad [('alloc', 136)]
BUF keccak_rc [('alloc', 192)]
BUF keccak_st [('alloc', 200)]
BUF mpt_hash_scratch [('alloc', 40)]
BUF mpt_key_scratch [('alloc', 16)]
BUF mpt_nib_scratch [('alloc', 64)]
BUF null_address [('alloc', 24)]
BUF pre_hdr_buf [('alloc', 96)]
BUF precompile_addrs [('alloc', 360)]
BUF rmd_h [('alloc', 40)]
BUF rmd_pad [('alloc', 128)]
BUF rmd_tab [('alloc', 160)]
BUF rmd_x [('alloc', 128)]
BUF sha_pad [('alloc', 128)]
BUF sha_st [('alloc', 64)]
BUF sk_buf [('alloc', 64)]
BUF ssz_len_chunk [('alloc', 32)]
BUF ssz_offs [('alloc', 64)]
BUF transfer_topic [('alloc', 32)]
BUF ts [('alloc', 72)]
BUF u256_ws [('alloc', 640)]
BUF vm_system_address [('alloc', 24)]
BUF withdrawal_request_address [('alloc', 24)]
BUF ws [('alloc', 40)]
BUF zero32 [('alloc', 32)]
BUF zero_hashes [('alloc', 2048)]
```

Column "loops": `#i` is the `i`-th `while` of the function in pre-order, `d` its nesting depth,
then the class (§3), the iteration bound `N`, and the justification. `log2 K` is the bit length of
`K.«f»`. Every reachable function and every reachable loop appears exactly once.

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
| `_decode_witness_node_mpt` | 10311 | `gb__decode_witness_node_mpt` (WorldOK) | - | 517 |
| `_decode_witness_node` | 10328 | `gb__decode_witness_node` (WorldOK) | - | 517 |
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
| `decode_witness_to_mpt` | 10348 | `gb_decode_witness_to_mpt` (WorldOK) | - | 517 |
| `mpt_from_witness` | 10459 | `gb_mpt_from_witness` (WorldOK) | - | 517 |
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
| `fq12_inv` | 24124 | `fb_fq12_inv` (GuestInv) | #0 d0 MONO N=14: Euclid on degree <= 12 polynomials: deg r1 strictly decreases, or the inner loop #1 times out (zero leading inverse), so this iteration times out (WhileTimesOut, while_rank_stationary); #1 d1 MONO N=14: mu = 2 (d0 + 1) + [not yet stationary]: d0 = deg r0 in [-1, 12] strictly decreases when fq_poly_submul cancels the leading coefficient (needs: fq arithmetic cancels on non-canonical inputs, DESIGN 8); with linv = fq_inv(lead) = 0, cf = 0 and the writes to q and r0 are idempotent from the second iteration on, which repeats exactly (SameHead, while_rank_stationary); #2 d1 CTR N=13: j < 13, step +1, unconditional; #3 d0 CTR N=12: i < 12, step +1, unconditional | 391 |
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
| `run_attempt` | 33734 | `gb_run_attempt` (WorldOK) | #0 d0 CTR N=2^64: i < L:ntx, step +1, unconditional | 755 |
| `attempt_l1` | 33847 | `gb_attempt_l1` (WorldOK) | - | 755 |
| `attempt_l2` | 33863 | `gb_attempt_l2` (WorldOK) | - | 755 |
| `attempt_l3` | 33879 | `gb_attempt_l3` (WorldOK) | - | 755 |
| `attempt_l4` | 33895 | `gb_attempt_l4` (WorldOK) | - | 755 |
| `attempt_l5` | 33911 | `gb_attempt_l5` (WorldOK) | - | 755 |
| `attempt_l6` | 33927 | `gb_attempt_l6` (WorldOK) | - | 755 |
| `attempt_l7` | 33943 | `gb_attempt_l7` (WorldOK) | - | 755 |
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
| `verify_stateless_new_payload` | 33959 | `gb_verify_stateless_new_payload` (WorldOK) | - | 755 |
| `main` | 33979 | `gb_main` (MainEntry) | - | 755 |

unreachable from main (39): account_exists_and_is_empty, bls_fp_dbl, bn254_pairing, cur_msg, ec_add, ec_mul, ec_on_curve, fn_add, fn_inv_fermat, fn_pow, fp12_sqr, fp2_dbl, fp_inv_fermat, g1_neg, get_transaction_hash, htab_cap, htab_copy_scratch, htr_list_roots, ld_be32, ld_le32, ld_le64, mpt_get, p256_ec_to_affine, p256_fp_inv, recover_sender, rlp_bytes_to_word, rlp_check_uint_bytes, tx_blob_count, tx_data, tx_gas, tx_nonce, tx_r, tx_s, tx_to, tx_value, u256_cmp, u256_low, u256_xor, umod

## 6. Guarded tier

### Guards

| Guard | Definition | Leaves |
|---|---|---|
| `HtabArgWF` | `ArenaReady` ∧ `HtabWF` of parameter `t` ∧ footprint allocated | `htab_truncate`, `htab_set/del/truncate_spec`, `htab_del_progress_spec` |
| `HtabNewReady` | `ArenaReady` ∧ `key_len ∈ htabKeyLens` ∧ `cap ≤ 2^32` | `htab_new_spec`, `htab_new_scratch_spec` |
| `RollbackReady` | the child's tables `+168/+176` are `HtabWF` and allocated; revision 6: the child record `(child, 280)` allocated words outside both footprints, the two tables equal or disjoint | `rollback_child_access` |
| `FinishReady` | `EvmInv` ∧ `EvmDone` ∧ kind ≠ 0 | `finish_child` |
| `EvmInv` | §5 of the Lean file (revision 4: capacities `≥ 1`, return data owned, `RetWindowsOK`, release lifetime of surviving tables) | `run_frames` |
| `EvmRun` (revision 5) | `EvmInv` ∧ `¬EvmDone` (the precondition of `op_dispatch_spec`) | `op_dispatch`, `op_sload`, `op_sstore` |
| `ArenaReady` | `GuestInv` ∧ `ArenaOK` (revision 6: the three allocator pointers 8-byte aligned) | `_decode_witness_node_body` |
| `MptReady` | `ArenaReady` ∧ the `node` parameter is rooted in a typed `NodeHeap` (revision 6: paths typed) ∧ `level ≤ klen` ∧ `KeyIn` of the key suffix `(key + level, klen − level)` (revision 6) | `_mpt_insert_node`, `_mpt_delete_node(_body)` |
| `MptObjReady` (restated in revision 5) | `ArenaReady` ∧ ∃ S, `WorldTyped s S` ∧ `MptObjIn s S`: trie object `m` allocated and rooted in a typed `NodeHeap`, `m` and every node disjoint from the tables of `S` and the fixed objects | `mpt_set` |
| `MsgReady` (new) | `ArenaReady` ∧ ∃ S, `WorldTyped s S` ∧ `msg+152`, `msg+160` ∈ S, the record owned (revision 6: also `AvoidsTries`) | `process_message`, `process_message_call`, `process_create_message` |
| `TxReady` (new) | `WorldOK` ∧ `index < bo+80` | `process_transaction` |
| `BlockReady` (revision 5) | `WorldOK` ∧ `16·ntx + 16 < 2^64`, `ntx = (si+0)+40` | `execute_block` |
| `ReqsFresh` (new) | `WorldOK` ∧ `bo+64 = 0` | `process_general_purpose_requests` |
| `WorldOK` | `ArenaReady` ∧ ∃ S, `WorldTyped s S` (tables, journal, fixed records and block-output objects, tries) | the other 28 guarded functions |
| `MainEntry` | §2 | `main` |

Callee-contract pre-conditions (not bound guards): `ReqRoom` (`requests_append`), `FrameOpenReady`
(`frame_open` in `process_message`), `WorldAvoids R` (an output region outside every typed table
and fixed object). Revision 5: `EvmMsgReady` (post of `fk_frame_open`, pre of `ek_depth0_prepare`:
`EvmInv` with the outermost message `ev+112` owned for the same table set, `EvmInvAt`/`MsgOwned`)
and `MptObjAvoids R` (`MptObjReady` plus an output region, pre of `wk_mpt_root`).

Every guard is `LocalsOnly` (proved instances, §7 of the Lean file), so `dec_onLocals`,
`LocalsOnly.decClock` and `LocalsOnly.setVar` apply inside every guarded body.

### NodeFn requirements (revision 6, round-4 Astra items 5 and 6)

`NodeFn names req g`. Each function's `req s Nd` is read off its body (`NODE_REQ` in
`coverage.py`); "rooted" means `RootIn Nd`, i.e. `0` or a node of `Nd`:

| function | node parameters (rooted) | requirement `req` | why (AST) |
|---|---|---|---|
| `node_new_leaf(nib, nlen, vptr, vlen)` | — | `KeyIn nib nlen` | the new leaf's path is `(nib, nlen)` (9994) |
| `node_new_ext(nib, nlen, child)` | `child` | `KeyIn nib nlen` | the new extension's path (10021) |
| `node_invalidate(nd)` | `nd` | none | stores `nd+8..+24`, inside every node kind (≥ 32 B; `nd = 0` errors) (10061) |
| `_insert_into_leaf(node, rk, rl, …)` | `node` | `NodeKind node 1`, `KeyIn rk rl` | stores `node+48/+56` (a 56-byte extension has no `+56`); `_create_branch_from_two_leaves` indexes a branch by `ek[pl]`, `rk[pl]` (10532) |
| `_split_extension(node, rk, rl, …, pl)` | `node` | `NodeKind node 2`, `KeyIn rk rl`, `pl < node+40`, `pl ≤ rl` | reads the child `+48`; indexes the fresh branch by `seg[pl]` and `rk[pl]`; `pl ≥ sl` wrapped `sl − pl` (10561) |
| `_collapse_branch(node)` | `node` | `NodeKind node 3` | reads the 16 children and `+160/+168`; copies a child path (10674) |
| `_delete_ext_finish(node, seg, sl, nc)` | `node`, `nc` | `NodeKind node 2`, `KeyIn seg sl` | stores `node+48` (a 32-byte hashed node has none); concatenates `(seg, sl)` with `nc`'s path (10727) |

`NodeFnExit` also gives two facts. The old nodes keep their kinds: all seven functions store at
offsets ≥ 8 of their node parameters only. Every new node of `Nd'` is a fresh heap record: nodes
are built only by `alloc`. With them, the callers' loop invariants can be carried:
- a saved extension (`_mpt_delete_node_body`'s scratch frame `(node, 2, seg, sl)`) is still an
  extension when `_delete_ext_finish` runs;
- a key or saved path, allocated before the call, stays disjoint from the grown node set.

The callers meet the requirements as follows.
- `_mpt_insert_node`: the kind is the loaded `k`. The key is `MptReady`'s suffix. For
  `_split_extension`, `pl ≠ sl` and `rv_common_prefix_length` (`pl ≤ min(sl, klen − level)`) give
  `pl < sl` and `pl ≤ rl`. `node_new_ext(seg, pl, br)` gets a prefix of the extension's own typed
  path.
- `_mpt_delete_node_body`: the kinds are the loaded `k`, or the frame tag `2` together with
  `NodeFnExit`'s kept kinds. `(seg, sl)` is the saved path, whose bytes are allocated heap outside
  every write region.

With aligned pointers, those regions are node records, fresh heap and the free scratch gap, so no
cell of a `KeyIn` array is written.

### Compositions (revision 4)

`gb_f` is proved as `gbody_f` applied to the callee facts. `GBody.«f»`'s hypotheses are, in order:
- the bound of every direct callee: `fb_g` (under `GuestInv`) or `gb_g` (under its guard);
- at every guard-carrying call site, the callee's contract:
  - a §7 leaf;
  - `ro_g : ReadOnlyFn g`;
  - `ww_g : WritesWithin R gw g`;
  - `wk_g`/`ek_g`/`ak_g : KeepsOn P W g` for `W` = `WorldOK`/`EvmInv`/`ArenaReady`;
  - `fk_frame_open`;
  - `nf_g : NodeFn names g` (MPT tier).

What each composition must show, beyond the combinator walk:
- `gbody_run_frames`: `while_rank_active` with `P = GuestInv ∧ (EvmInv ∨ go = 0)`,
  `μ = if go = 0 then 0 else evmPot + 1`, `N = evmPotMax + 1`. The step is `run_frames_step_of_specs`
  applied to its four hypotheses `op_dispatch_spec`, `frame_exception_spec`, `frame_epilogue_spec`,
  `finish_child_spec`. The body bound under `P ∧ go ≠ 0` uses `callHandle_on`:
  - for `op_dispatch`, its guard `EvmRun = EvmInv ∧ ¬EvmDone` (revision 5; it was `WorldOK`,
    from `worldOK_of_evmInv`);
  - for `finish_child`, `FinishReady`.
- `gbody_finish_child` → `rollback_child_access`: `RollbackReady` from `EvmInv`, carried across
  `create_finish`, `frame_halt`, `refill_frame_state_gas`, `state_restore` by their `ek_*` contracts.
- `gbody_htab_truncate`: `while_rank_stationary` with `μ = count (t+24)`, by `htab_del_spec` and
  `htab_del_progress_spec` (revision-3 argument, unchanged).
- `gbody_process_message`: `MsgReady` at entry. `fk_frame_open` gives `EvmMsgReady` (revision 5).
  `ro_state_snapshot` keeps it (`ReadOnlyFn.keepsOn`, `localsFree_evmMsgReady`).
  `ek_depth0_prepare` takes it to `EvmInv`, `ek_frame_start` carries `EvmInv`, and the inline store
  `cur_cont+24` writes a non-pointer field of the continuation. That gives `EvmInv` at `run_frames`.
- `gbody_op_sload` / `gbody_op_sstore` (revision 5, guard `EvmRun`): `ek_charge_gas`,
  `ek_stack_pop`, `ek_warm_storage_key` and `ek_get_storage_original` carry `EvmInv`, and
  `worldOK_of_evmInv` gives the `WorldOK` guard of `get_storage`/`get_storage_original`.
- `gbody_run_attempt` (revision 5): the call to `execute_block` needs `BlockReady`, i.e. the
  transaction count of the decoded input satisfies `16·ntx + 16 < 2^64` (Q11).
- `gbody_process_transaction` / `gbody_execute_block` / … carry `WorldOK` (or `MsgReady`, `TxReady`,
  `ReqsFresh`) to every guarded call with the contracts listed below:
  - fresh tables from `htab_new_spec` extend `S`;
  - `WritesWithin` regions are fresh blocks or outputs the body allocated;
  - inline stores land in owned objects (`bo` arrays below `bo+80`, frame records) or in fresh
    memory.
- `gbody_main`: `mem_init_world` at the first call. `WorldOK` is then carried through:
  - the `*_init` functions: `WritesWithin` for those whose stores all land in buffers they
    allocate, `KeepsOn WorldOK` for `bls_precompiles_init`, `bn254_init`, `fork_init`, `ssz_init`,
    and `ReadOnlyFn` for `secp256k1_init`. A changed buffer global is a fresh allocation, so
    `FixedTyped` follows from the frame;
  - `decode_host_input` (`KeepsOn WorldOK`);
  - `htr_new_payload_request` (`WritesWithin (out, 32)`).

The guard-carrying callees of every guarded function (generated, `out/contracts.txt`):

```
_decode_witness_node [WorldOK]: scratch_mark
_decode_witness_node_body [ArenaReady]: _decode_step _resolve_step mpt_fail node_new_ext rlp_item
_decode_witness_node_mpt [WorldOK]: 
_mpt_delete_node [MptReady]: scratch_mark
_mpt_delete_node_body [MptReady]: _collapse_branch _delete_ext_finish common_prefix_length memeq mpt_fail node_invalidate scratch_alloc
_mpt_insert_node [MptReady]: _insert_into_leaf _split_extension common_prefix_length mpt_fail node_invalidate node_new_ext node_new_leaf
attempt_l1 [WorldOK]: 
attempt_l2 [WorldOK]: 
attempt_l3 [WorldOK]: 
attempt_l4 [WorldOK]: 
attempt_l5 [WorldOK]: 
attempt_l6 [WorldOK]: 
attempt_l7 [WorldOK]: 
build_mpt_indexed [WorldOK]: heap_mark mpt_new mpt_set rlp_encode_word
compute_state_root [WorldOK]: alloc cache_get_root encode_account htab_copy htab_get htab_has htab_item htab_new htab_set memcpy mpt_from_witness mpt_root mpt_set rlp_encode_bytes u256_is_zero u256_to_be_min ws_get_account_optional ws_storage_root_of
decode_witness_to_mpt [WorldOK]: memeq mpt_fail nodedb_lookup
execute_block [BlockReady]: alloc bal_init build_block_access_list_rlp build_mpt_indexed compute_state_root decode_transaction logs_bloom lst_new memzero process_general_purpose_requests process_transaction process_unchecked_system_transaction process_withdrawals state_fresh_tx track_ancestor_access validate_block_access_list_gas_limit
finish_child [FinishReady]: create_finish frame_halt refill_frame_state_gas state_restore
get_pre_tx_storage [WorldOK]: record_pre_state_read stor_lookup
get_storage [WorldOK]: htab_set record_pre_state_read sk_make stor_lookup
get_storage_original [WorldOK]: htab_has record_pre_state_read stor_lookup
htab_truncate [HtabArgWF]: htab_del
idx_start_storage [WorldOK]: htab_get memcpy st_le64
incorporate_tx_into_block [WorldOK]: 
main [MainEntry]: alloc blake2_init bls_precompiles_init bn254_init decode_host_input evm_init fork_init header_init htr_new_payload_request keccak_init mem_init memzero mpt_init ripemd160_init secp256k1_init sha256_init ssz_init u256_ws_init
mpt_from_witness [WorldOK]: 
mpt_set [MptObjReady]: mpt_nibble_key
op_dispatch [EvmRun]: 
op_sload [EvmRun]: charge_gas is_warm_storage_key stack_pop u256_to_be32 warm_storage_key
op_sstore [EvmRun]: charge_gas check_gas get_storage_original is_warm_storage_key max require_not_static stack_pop u256_to_be32 warm_storage_key
payload_header [WorldOK]: alloc block_rlp_length build_mpt_indexed encode_withdrawal_rlp keccak256 memzero
process_checked_system_transaction [WorldOK]: alloc ext_code_of state_fresh_tx
process_create_message [MsgReady]: destroy_storage increment_nonce mark_account_created state_snapshot
process_general_purpose_requests [ReqsFresh]: alloc extract_deposit_data memcpy memeq process_checked_system_transaction requests_append
process_message [MsgReady]: depth0_prepare frame_open frame_start state_snapshot
process_message_call [MsgReady]: account_deployable alloc memzero
process_transaction [TxReady]: alloc calculate_blob_gas_price calculate_total_blob_gas check_transaction clear_account_preserving_balance compute_contract_address create_ether encode_receipt encode_transaction fee_mul get_account htab_item htab_new htab_set increment_nonce keccak256 lst_new lst_push max memcpy min msg_new process_message_call recover_sender_with_chain_id set_account_balance state_fresh_tx te_new tx_chain_id tx_has_access_list tx_is_blob tx_is_setcode u256_sub udiv_small5 validate_transaction
process_unchecked_system_transaction [WorldOK]: ext_code_of htab_new msg_new process_message_call state_fresh_tx te_new
process_withdrawals [WorldOK]: create_ether state_fresh_tx u256_mul
rollback_child_access [RollbackReady]: htab_truncate
run_attempt [WorldOK]: alloc check_gas_limit header_hash is_valid_versioned_hashes memeq memzero nodedb_build payload_header state_init validate_header validate_headers
run_frames [EvmInv]: finish_child frame_epilogue frame_exception op_dispatch
state_init [WorldOK]: alloc
update_builder_from_tx [WorldOK]: add_balance_change add_code_change add_nonce_change add_storage_write bal_remove_change get_code htab_item idx_start_account idx_start_storage memeq remove_storage_write u256_eq
verify_stateless_new_payload [WorldOK]: 
ws_get_storage [WorldOK]: memeq ws_storage_root_of
ws_storage_trie [WorldOK]: htab_get
```

### The `gbody_*` boundary (revision 6, round-4 Astra item 8; generated, `out/gbody.md`)

One row per guarded function `f`. `GBody.«f»` is an implication. Its hypotheses are:
- the bounds of exactly the direct callees of `f` (column 4): `fb_g` under `GuestInv`, or `gb_g`
  under `g`'s guard. `«callees_f»` checks by `decide` on the literal AST that this set is exactly
  the set of functions `f`'s body calls;
- the contracts of the callees at `f`'s guard-carrying call sites (column 5). Each names one direct
  callee: `coverage.py` asserts it, and the contract's statement mentions only that callee.

The conclusion is `TerminatingFunBoundedOn Guard_f f K.«f»`. `f`'s own guard appears only there.
Nothing else is assumed: no fact about a non-callee, no invariant of a caller, no global lemma. The
proof of `gbody_f` must use the §3 combinators and the proved Hoare rules on `f`'s body. Guard
transport across calls, loop invariants and the rank/stationary obligations are part of that walk
(§0.1, item 8). "proved" rows are closed in the Lean file; "primitive" rows are fields of
`Primitives`.

| `gbody_*` (function) | guard | loops | direct callees = bound hypotheses | contract hypotheses | status |
|---|---|---|---|---|---|
| `_decode_witness_node_body` (AST 10196) | `ArenaReady` | #0 GUARD | 5: _decode_step, _resolve_step, mpt_fail, node_new_ext, rlp_item | 5: `ak__decode_step`, `ww__resolve_step`, `ro_mpt_fail`, `ww_node_new_ext`, `ww_rlp_item` | primitive |
| `_decode_witness_node_mpt` (AST 10311) | `WorldOK` | loop-free | 2: _decode_witness_node_body, scratch_release | 0: — | **proved** |
| `_decode_witness_node` (AST 10328) | `WorldOK` | loop-free | 3: _decode_witness_node_mpt, scratch_mark, scratch_release | 1: `ro_scratch_mark` | **proved** |
| `_mpt_delete_node_body` (AST 10758) | `MptReady` | #0 GUARD; #1 GUARD | 7: _collapse_branch, _delete_ext_finish, common_prefix_length, memeq, mpt_fail, node_invalidate, scratch_alloc | 8: `nf__collapse_branch`, `nf__delete_ext_finish`, `ro_common_prefix_length`, `rv_common_prefix_length`, `ro_memeq`, `ro_mpt_fail`, `nf_node_invalidate`, `ww_scratch_alloc` | primitive |
| `_mpt_delete_node` (AST 10852) | `MptReady` | loop-free | 3: _mpt_delete_node_body, scratch_mark, scratch_release | 1: `ro_scratch_mark` | primitive |
| `_mpt_insert_node` (AST 10598) | `MptReady` | #0 GUARD | 7: _insert_into_leaf, _split_extension, common_prefix_length, mpt_fail, node_invalidate, node_new_ext, node_new_leaf | 8: `nf__insert_into_leaf`, `nf__split_extension`, `ro_common_prefix_length`, `rv_common_prefix_length`, `ro_mpt_fail`, `nf_node_invalidate`, `nf_node_new_ext`, `nf_node_new_leaf` | primitive |
| `mpt_set` (AST 10872) | `MptObjReady` | loop-free | 3: _mpt_delete_node, _mpt_insert_node, mpt_nibble_key | 2: `ww_mpt_nibble_key`, `nk_mpt_nibble_key` | primitive |
| `build_mpt_indexed` (AST 11243) | `WorldOK` | #0 CTR | 6: heap_mark, heap_release, mpt_new, mpt_root, mpt_set, rlp_encode_word | 4: `ro_heap_mark`, `ww_mpt_new`, `wk_mpt_set`, `ww_rlp_encode_word` | primitive |
| `decode_witness_to_mpt` (AST 10348) | `WorldOK` | loop-free | 6: _decode_witness_node, alloc, memcpy, memeq, mpt_fail, nodedb_lookup | 3: `ro_memeq`, `ro_mpt_fail`, `ro_nodedb_lookup` | **proved** |
| `mpt_from_witness` (AST 10459) | `WorldOK` | loop-free | 2: decode_witness_to_mpt, mpt_new | 0: — | **proved** |
| `compute_state_root` (AST 32341) | `WorldOK` | #0 CTR; #1 CTR; #2 CTR; #3 CTR; #4 CTR | 18: alloc, cache_get_root, encode_account, htab_copy, htab_get, htab_has, htab_item, htab_new, htab_set, memcpy, mpt_from_witness, mpt_root, mpt_set, rlp_encode_bytes, u256_is_zero, u256_to_be_min, ws_get_account_optional, ws_storage_root_of | 18: `ww_alloc`, `ww_cache_get_root`, `ww_encode_account`, `ww_htab_copy`, `ro_htab_get`, `ro_htab_has`, `ro_htab_item`, `htab_new_spec`, `htab_set_spec`, `ww_memcpy`, `wk_mpt_from_witness`, `wk_mpt_root`, `wk_mpt_set`, `ww_rlp_encode_bytes`, `ro_u256_is_zero`, `ww_u256_to_be_min`, `ww_ws_get_account_optional`, `ww_ws_storage_root_of` | primitive |
| `ws_storage_trie` (AST 13042) | `WorldOK` | loop-free | 3: decode_witness_to_mpt, htab_get, htab_set | 1: `ro_htab_get` | **proved** |
| `ws_get_storage` (AST 13061) | `WorldOK` | loop-free | 10: alloc, heap_mark, heap_release, keccak256, memeq, rlp_decode_fully, trie_lookup, u256_from_be, ws_storage_root_of, ws_storage_trie | 2: `ro_memeq`, `ww_ws_storage_root_of` | primitive |
| `get_pre_tx_storage` (AST 14069) | `WorldOK` | loop-free | 3: record_pre_state_read, stor_lookup, ws_get_storage | 2: `wk_record_pre_state_read`, `ro_stor_lookup` | **proved** |
| `idx_start_storage` (AST 14129) | `WorldOK` | loop-free | 6: alloc, get_pre_tx_storage, htab_get, htab_set, memcpy, st_le64 | 3: `ro_htab_get`, `ww_memcpy`, `ww_st_le64` | primitive |
| `update_builder_from_tx` (AST 14233) | `WorldOK` | #0 CTR; #1 CTR; #2 CTR | 12: add_balance_change, add_code_change, add_nonce_change, add_storage_write, bal_remove_change, get_code, htab_item, idx_start_account, idx_start_storage, memeq, remove_storage_write, u256_eq | 12: `wk_add_balance_change`, `wk_add_code_change`, `wk_add_nonce_change`, `wk_add_storage_write`, `wk_bal_remove_change`, `wk_get_code`, `ro_htab_item`, `wk_idx_start_account`, `wk_idx_start_storage`, `ro_memeq`, `wk_remove_storage_write`, `ro_u256_eq` | primitive |
| `incorporate_tx_into_block` (AST 14313) | `WorldOK` | loop-free | 2: merge_tx_into_block, update_builder_from_tx | 0: — | **proved** |
| `htab_truncate` (AST 5278) | `HtabArgWF` | #0 WF | 1: htab_del | 2: `htab_del_spec`, `htab_del_progress_spec` | primitive |
| `rollback_child_access` (AST 18995) | `RollbackReady` | loop-free | 1: htab_truncate | 1: `htab_truncate_spec` | primitive |
| `finish_child` (AST 18572) | `FinishReady` | loop-free | 16: address_to_u256, create_finish, credit_state_gas_refund, frame_halt, frame_mem_release, incorporate_child_on_error, incorporate_child_on_success, memcpy, min, pc_add, refill_frame_state_gas, rollback_child_access, scratch_release, set_retdata, stack_push, state_restore | 4: `ek_create_finish`, `ek_frame_halt`, `ek_refill_frame_state_gas`, `ek_state_restore` | primitive |
| `get_storage` (AST 13249) | `WorldOK` | loop-free | 5: htab_set, record_pre_state_read, sk_make, stor_lookup, ws_get_storage | 4: `htab_set_spec`, `wk_record_pre_state_read`, `ww_sk_make`, `ro_stor_lookup` | primitive |
| `op_sload` (AST 16584) | `EvmRun` | loop-free | 8: charge_gas, get_storage, is_warm_storage_key, pc_add, stack_pop, stack_push, u256_to_be32, warm_storage_key | 5: `ek_charge_gas`, `ww_is_warm_storage_key`, `ek_stack_pop`, `ww_u256_to_be32`, `ek_warm_storage_key` | primitive |
| `get_storage_original` (AST 13276) | `WorldOK` | loop-free | 4: htab_has, record_pre_state_read, stor_lookup, ws_get_storage | 3: `ro_htab_has`, `wk_record_pre_state_read`, `ro_stor_lookup` | **proved** |
| `op_sstore` (AST 16611) | `EvmRun` | loop-free | 16: charge_gas, charge_state_gas, check_gas, credit_state_gas_refund, get_storage, get_storage_original, is_warm_storage_key, max, pc_add, require_not_static, set_storage, stack_pop, u256_eq, u256_is_zero, u256_to_be32, warm_storage_key | 9: `ek_charge_gas`, `ro_check_gas`, `ek_get_storage_original`, `ww_is_warm_storage_key`, `ro_max`, `ro_require_not_static`, `ek_stack_pop`, `ww_u256_to_be32`, `ek_warm_storage_key` | primitive |
| `op_dispatch` (AST 17902) | `EvmRun` | loop-free | 87: op_add, op_addmod, op_address, op_and, op_balance, op_basefee, op_blobbasefee, op_blobhash, op_blockhash, op_byte, op_call, op_callcode, op_calldatacopy, op_calldataload, op_calldatasize, op_caller, op_callvalue, op_chainid, op_clz, op_codecopy, op_codesize, op_coinbase, op_create, op_create2, op_delegatecall, op_div, op_dup, op_dupn, op_eq, op_exchange, op_exp, op_extcodecopy, op_extcodehash, op_extcodesize, op_gas, op_gaslimit, op_gasprice, op_gt, op_iszero, op_jump, op_jumpdest, op_jumpi, op_keccak, op_log, op_lt, op_mcopy, op_mload, op_mod, op_msize, op_mstore, op_mstore8, op_mul, op_mulmod, op_not, op_number, op_or, op_origin, op_pc, op_pop, op_prevrandao, op_push, op_return, op_returndatacopy, op_returndatasize, op_revert, op_sar, op_sdiv, op_selfbalance, op_selfdestruct, op_sgt, op_shl, op_shr, op_signextend, op_sload, op_slotnum, op_slt, op_smod, op_sstore, op_staticcall, op_stop, op_sub, op_swap, op_swapn, op_timestamp, op_tload, op_tstore, op_xor | 0: — | primitive |
| `run_frames` (AST 18663) | `EvmInv` | #0 POT | 4: finish_child, frame_epilogue, frame_exception, op_dispatch | 4: `finish_child_spec`, `frame_epilogue_spec`, `frame_exception_spec`, `op_dispatch_spec` | primitive |
| `process_message` (AST 18803) | `MsgReady` | loop-free | 10: depth0_prepare, frame_halt, frame_mem_release, frame_open, frame_start, refill_frame_state_gas, run_frames, scratch_release, state_restore, state_snapshot | 4: `ek_depth0_prepare`, `fk_frame_open`, `ek_frame_start`, `ro_state_snapshot` | primitive |
| `process_create_message` (AST 18899) | `MsgReady` | loop-free | 9: create_finish, destroy_storage, frame_halt, increment_nonce, mark_account_created, process_message, refill_frame_state_gas, state_restore, state_snapshot | 4: `wk_destroy_storage`, `wk_increment_nonce`, `wk_mark_account_created`, `ro_state_snapshot` | primitive |
| `process_message_call` (AST 19661) | `MsgReady` | loop-free | 6: account_deployable, alloc, frame_state_gas_used, memzero, process_create_message, process_message | 3: `wk_account_deployable`, `ww_alloc`, `ww_memzero` | primitive |
| `process_unchecked_system_transaction` (AST 32851) | `WorldOK` | loop-free | 11: alloc, ext_code_of, frame_mem_release, htab_new, incorporate_tx_into_block, memcpy, msg_new, process_message_call, scratch_release, state_fresh_tx, te_new | 6: `wk_ext_code_of`, `htab_new_spec`, `ww_msg_new`, `wk_process_message_call`, `ww_state_fresh_tx`, `ww_te_new` | primitive |
| `process_checked_system_transaction` (AST 32928) | `WorldOK` | loop-free | 4: alloc, ext_code_of, process_unchecked_system_transaction, state_fresh_tx | 3: `ww_alloc`, `wk_ext_code_of`, `ww_state_fresh_tx` | primitive |
| `process_general_purpose_requests` (AST 33507) | `ReqsFresh` | #0 CTR; #1 CTR | 6: alloc, extract_deposit_data, memcpy, memeq, process_checked_system_transaction, requests_append | 6: `ww_alloc`, `ww_extract_deposit_data`, `ww_memcpy`, `ro_memeq`, `wk_process_checked_system_transaction`, `wk_requests_append` | primitive |
| `process_transaction` (AST 33103) | `TxReady` | #0 CTR; #1 CTR; #2 CTR; #3 CTR; #4 CTR; #5 CTR; #6 CTR; #7 CTR; #8 CTR | 37: alloc, calculate_blob_gas_price, calculate_total_blob_gas, check_transaction, clear_account_preserving_balance, compute_contract_address, create_ether, encode_receipt, encode_transaction, fee_mul, frame_mem_release, get_account, htab_item, htab_new, htab_set, incorporate_tx_into_block, increment_nonce, keccak256, lst_new, lst_push, max, memcpy, min, msg_new, process_message_call, recover_sender_with_chain_id, scratch_release, set_account_balance, state_fresh_tx, te_new, tx_chain_id, tx_has_access_list, tx_is_blob, tx_is_setcode, u256_sub, udiv_small5, validate_transaction | 34: `ww_alloc`, `wk_calculate_blob_gas_price`, `ro_calculate_total_blob_gas`, `wk_check_transaction`, `wk_clear_account_preserving_balance`, `ww_compute_contract_address`, `wk_create_ether`, `wk_encode_receipt`, `wk_encode_transaction`, `ro_fee_mul`, `wk_get_account`, `ro_htab_item`, `htab_new_spec`, `htab_set_spec`, `wk_increment_nonce`, `ww_keccak256`, `ww_lst_new`, `ww_lst_push`, `ro_max`, `ww_memcpy`, `ro_min`, `ww_msg_new`, `wk_process_message_call`, `ww_recover_sender_with_chain_id`, `wk_set_account_balance`, `ww_state_fresh_tx`, `ww_te_new`, `ro_tx_chain_id`, `ro_tx_has_access_list`, `ro_tx_is_blob`, `ro_tx_is_setcode`, `ro_u256_sub`, `ro_udiv_small5`, `ro_validate_transaction` | primitive |
| `process_withdrawals` (AST 33458) | `WorldOK` | #0 CTR | 4: create_ether, incorporate_tx_into_block, state_fresh_tx, u256_mul | 3: `wk_create_ether`, `ww_state_fresh_tx`, `ro_u256_mul` | primitive |
| `execute_block` (AST 33580) | `BlockReady` | #0 CTR | 20: alloc, bal_init, build_block_access_list_rlp, build_mpt_indexed, compute_requests_hash, compute_state_root, decode_transaction, keccak256, logs_bloom, lst_new, max, memeq, memzero, process_general_purpose_requests, process_transaction, process_unchecked_system_transaction, process_withdrawals, state_fresh_tx, track_ancestor_access, validate_block_access_list_gas_limit | 16: `ww_alloc`, `ww_bal_init`, `wk_build_block_access_list_rlp`, `wk_build_mpt_indexed`, `wk_compute_state_root`, `ww_decode_transaction`, `ww_logs_bloom`, `ww_lst_new`, `ww_memzero`, `wk_process_general_purpose_requests`, `wk_process_transaction`, `wk_process_unchecked_system_transaction`, `wk_process_withdrawals`, `ww_state_fresh_tx`, `ww_track_ancestor_access`, `ro_validate_block_access_list_gas_limit` | primitive |
| `payload_header` (AST 32645) | `WorldOK` | #0 CTR | 8: alloc, block_rlp_length, build_mpt_indexed, compute_requests_hash, encode_execution_requests, encode_withdrawal_rlp, keccak256, memzero | 6: `ww_alloc`, `wk_block_rlp_length`, `wk_build_mpt_indexed`, `wk_encode_withdrawal_rlp`, `ww_keccak256`, `ww_memzero` | primitive |
| `state_init` (AST 12708) | `WorldOK` | loop-free | 3: alloc, decode_witness_to_mpt, htab_new | 1: `ww_alloc` | primitive |
| `run_attempt` (AST 33734) | `WorldOK` | #0 CTR | 12: alloc, check_gas_limit, execute_block, header_hash, is_valid_versioned_hashes, memeq, memzero, nodedb_build, payload_header, state_init, validate_header, validate_headers | 11: `ww_alloc`, `ro_check_gas_limit`, `ww_header_hash`, `ww_is_valid_versioned_hashes`, `ro_memeq`, `ww_memzero`, `wk_nodedb_build`, `wk_payload_header`, `wk_state_init`, `wk_validate_header`, `ww_validate_headers` | primitive |
| `attempt_l1` (AST 33847) | `WorldOK` | loop-free | 1: run_attempt | 0: — | **proved** |
| `attempt_l2` (AST 33863) | `WorldOK` | loop-free | 1: attempt_l1 | 0: — | **proved** |
| `attempt_l3` (AST 33879) | `WorldOK` | loop-free | 1: attempt_l2 | 0: — | **proved** |
| `attempt_l4` (AST 33895) | `WorldOK` | loop-free | 1: attempt_l3 | 0: — | **proved** |
| `attempt_l5` (AST 33911) | `WorldOK` | loop-free | 1: attempt_l4 | 0: — | **proved** |
| `attempt_l6` (AST 33927) | `WorldOK` | loop-free | 1: attempt_l5 | 0: — | **proved** |
| `attempt_l7` (AST 33943) | `WorldOK` | loop-free | 1: attempt_l6 | 0: — | **proved** |
| `verify_stateless_new_payload` (AST 33959) | `WorldOK` | loop-free | 1: attempt_l7 | 0: — | **proved** |
| `main` (AST 33979) | `MainEntry` | loop-free | 21: alloc, blake2_init, bls_precompiles_init, bn254_init, decode_host_input, evm_init, fork_init, header_init, htr_new_payload_request, keccak_init, mem_init, memzero, mpt_init, output_write, ripemd160_init, secp256k1_init, serialize_result, sha256_init, ssz_init, u256_ws_init, verify_stateless_new_payload | 18: `ww_alloc`, `ww_blake2_init`, `ww_bls_precompiles_init`, `ww_bn254_init`, `wk_decode_host_input`, `ww_evm_init`, `ww_fork_init`, `ww_header_init`, `ww_htr_new_payload_request`, `ww_keccak_init`, `mem_init_world`, `ww_memzero`, `ww_mpt_init`, `ww_ripemd160_init`, `ro_secp256k1_init`, `ww_sha256_init`, `ww_ssz_init`, `ww_u256_ws_init` | primitive |

### Contract leaves (all `sorry`)

- §7 (hand-written, unchanged statements): `htab_set_spec`, `htab_del_spec`,
  `htab_del_progress_spec`, `htab_truncate_spec`, `htab_union_into_spec`, `htab_new_spec`,
  `htab_new_scratch_spec`, `mpt_insert_node_spec`, `mpt_delete_node_body_spec`, `mem_init_world`,
  `op_dispatch_spec`, `frame_exception_spec`, `frame_epilogue_spec`, `finish_child_spec`. The
  assembly uses ten of them directly. `htab_union_into_spec`, `htab_new_scratch_spec` and the two
  MPT specs are the lemmas the frame and table contract proofs are expected to use.
- Generated callee contracts (144): `ro_*` (30), `ww_*` (50), `wk_*` (43), `ek_*` (10), `ak_*` (1),
  `fk_frame_open`, `nf_*` (7), `nk_mpt_nibble_key`, `rv_common_prefix_length`. (Revision 4: 142,
  with `wk_*` 47, `ek_*` 6.)

## 7. Every `sorry`

- Combinators, glue, bridge, assembly: none.
- §7 contract leaves (14).
- Generated callee contracts (144).
- Composition obligations `gbody_*` (31; the other 16 are proved, 4 of them new in revision 6).
- Unguarded bound leaves `fb_*` (727).

916 in total. No definition contains `sorry`, and no `gb_*` does (they are proved). `assembly` and
`assembly_main` are `sorry`-free. `coveredSourceTicksConsumedBounded_K_pan = assembly primitives`
depends on `sorryAx` only through the `Primitives` fields. `run_frames_step` depends on the four
frame contracts.

## 8. Open questions and known risks (for the quorum)

- **Q1 (ownership of everything an opcode writes; round-3 field-by-field audit).** A write-root
  scan over the `op_dispatch`, `finish_child`, `frame_exception` and `frame_epilogue` cones lists
  every pointer field written through. It covers every store and every argument passed to a written
  parameter, with locals resolved through their `dec` definitions.

  | field (AST) | role | written through by | owned by |
  |---|---|---|---|
  | `e+8` (15386) | stack | `stack_push`, `stack_swap_positions` | `frameObjects[2]` = `(e+8, 32·e+232)`, `1 ≤ cap ≤ 1024` |
  | `e+24` (15393) | EVM memory | `op_mstore(8)`, `op_mcopy`, `*copy` via `buffer_read`/`memcpy`, `extend_memory` (`memzero`), `finish_child` output copy | `frameObjects[3]` = `(e+24, e+40)`; `e+32`, `e+40` appear only as offsets |
  | `e+88` (15409) | logs list | `log_append` → `lst_push` (through its parameter, not seen by the scan) | `frameObjects[4]` (header), `[5]` = `frameLogs` (array), `1 ≤ cap` |
  | `e+136/+168/+176` | deletion / access tables | `htab_set`, `htab_union_into` | typed tables in `S` (`FrameWF`) |
  | `e+144` (15431) | return data | `set_retdata` → `memcpy` | `frameObjects[6]` = `frameRet` (new) |
  | `c+72/+80` (18746-18748) | output window in the parent | `finish_child` → `memcpy` | `RetWindowsOK` (new) |

  The other record fields are values, or pointers only read during execution:
  - `e+48` code, `e+80` jump bitmap, `e+112` message;
  - `e+120` output: set by `RETURN`/`REVERT`, read by `finish_child` before the release;
  - `c+0/+8` chain links, `c+40` message, `c+88` contract address.

  The message record is written only by `prepare_dispatch`/`depth0_prepare` (outermost frame,
  before `run_frames`; revision 5: owned there by `EvmMsgReady`, which `fk_frame_open` provides) and
  by `child_message` into its own fresh block. Global buffers are fixed
  objects. Table values are never written through. The remaining risk is a write through a pointer
  loaded from a table value or from the message, which the syntactic scan treats as unresolved.
  None was reported in the frame cones.
- **Q2 (`finish_child` on `EvmErr`).** Unchanged from revision 3.
- **Q3 (`TriesTyped`).** Unchanged: storage tries are typed through the `ws+32` cache only.
- **Q4 (MPT descent).** Unchanged.
- **Q5 (cost of the generated interface).** 727 unguarded leaves plus 144 contracts, mostly
  loop-free.
- **Q6, Q7.** Unchanged (arithmetic facts behind two `MONO` measures; divergence obligations).
- **Q8 (heap-resident frame blocks).** Logs arrays and, new in revision 4, return-data buffers live
  on the heap. `op_dispatch_spec`/`finish_child_spec` are true only if no handler `heap_release`s to
  a mark taken before such an allocation. Astra and Fable both checked that no `heap_release`
  caller reaches `lst_push`/`log_append`; the same check is needed for `set_retdata`.
- **Q9 (composition obligations; new).** `gbody_f` can only use its listed hypotheses. Where the
  walk is expected to be hardest:
  - `gbody_process_transaction` (308 statements, 55 inline stores, 9 loops): inline stores into the
    transaction environment `te` (a fresh `te_new` block) and the `bo` arrays below `bo+80`.
  - `gbody_execute_block`: establishing `TxReady` (`i < ntx = bo+80`) and `ReqsFresh` (`bo` was just
    zeroed, nothing appended yet); with `BlockReady` the arrays `alloc(16·ntx + 16)` are exactly
    the `blockOutObjects` lengths (revision 5).
  - The MPT tier (`_mpt_insert_node`, `_mpt_delete_node_body`): `MptReady` at the loop heads is
    re-established from the `nf_*` contracts (returned node typed, node set extended). The loop
    measures are the revision-3 ones (§3; Q4).
  - `_decode_witness_node_body` (`ArenaReady`) needs only the arena; its node constructors have
    `ww_*` contracts there.
- **Q10 (contract classification is syntactic).**
  - `ReadOnlyFn` uses the transitive purity of `coverage.py`.
  - `WritesWithin` uses `fresh_only`: every store and written argument has a fresh-block,
    global-buffer or inner-parameter root and no loaded component.
  - The `REGION` lengths are hand-read from the AST: `encode_account` 110 bytes,
    `extract_deposit_data` 192, `rlp_encode_bytes` `n + 9`, `rlp_encode_word` 33. A
    too-small length makes a `ww_*` leaf false, so the leaf provers will notice; the quorum should
    spot-check them.
  - `KeepsOn WorldOK` callees that write through table values or message pointers are true only
    if those writes never reach an owned object. The world write-root scan (§0.3) found none outside
    the typed slots and the `bo` objects.
- **Q11 (`BlockReady` at `run_attempt`; revision 5).** `gbody_run_attempt` must show
  `16·ntx + 16 < 2^64` for the decoded input `si` at its `execute_block` call. `ntx` is the length
  of the SSZ transaction list of the payload (`pl+40`, stored by the payload decoder, AST 8557). It
  is bounded by the input size, but no guard records that, and `run_attempt`'s guard is `WorldOK`.
  This is the residual of the round-4 non-blocking item. Without the bound, the guest itself
  writes past `alloc(16·ntx + 16)` when the size wraps and two transactions decode. The fact must
  come either from the input decoder (an `fb_*` postcondition, outside the current interface) or
  from a guard on `run_attempt`/`attempt_l*`. Revision 5 leaves it in `gbody_run_attempt` and flags
  it for the quorum.

## 9. How this was produced and checked

```
python3 -I campaign/notes/guestinv/scripts/coverage.py Guest/SoftwareAst.lean OUT
#   -> OUT/coverage.md, OUT/kgen.lean, OUT/leaves.lean, OUT/gleaves.lean (callee contracts,
#      GBody/gbody/gb, Primitives, assembly_main, primitives), OUT/contracts.txt, OUT/tiers.txt,
#      OUT/chain.txt, OUT/manual.txt (must be empty: every loop classified),
#      OUT/parsed.pickle (parse cache)
sh campaign/notes/guestinv/scripts/assemble.sh OUT campaign/specs-proposed/GuestInv.lean
lake env lean campaign/specs-proposed/GuestInv.lean
```

`#print axioms` runs on a scratch copy: the prints go just before the final `end`, the copy sits
in the same directory so imports resolve, and it is deleted afterwards. The file is never
committed:

```
F=campaign/specs-proposed/GuestInv.lean; S=campaign/specs-proposed/GuestInvAxioms_scratch.lean
{ head -n -1 $F
  for t in assembly assembly_main K_pan_budget run_frames_step_of_specs; do echo "#print axioms $t"; done
  tail -n 1 $F; } > $S
lake env lean $S; rm $S
```

Result on Lean 4.33.1 with the `wave8-cone-cache` release (revision 6, fcb670d84): no errors;
916 `declaration uses 'sorry'` warnings, all leaves: 14 §7 contracts, 144 generated callee
contracts, 31 `gbody_*`, 727 `fb_*`. No combinator, glue, definition, bridge theorem, `gb_*` or assembly theorem has a `sorry`.
There are also style-linter notes about the `__` in generated names such as `fb__decode_step`.
`#print axioms`, checked on a scratch copy:
- `[propext, Classical.choice, Quot.sound]` (no `sorryAx`):
  - `assembly`, `assembly_main`;
  - the 16 proved `gbody_*` (revision 6: `gbody_get_pre_tx_storage`, `gbody_get_storage_original`,
    `gbody_ws_storage_trie`, `gbody_decode_witness_to_mpt`), the revision-6 helpers `seq_hoare`,
    `Hoare.ite_return_skip`, `Hoare.call_keeps`, `Hoare.ite_call_keeps`, and the composition helpers (`seq_guestInv_after`, `of_clock`,
    `clock_*`, `ReadOnlyFn.resumeOn`, `decCallResumeOn_guestInv`, `callEntryOn_of_imp`);
  - every combinator: the revision-3 ones, plus `callHandle_on`, `while_rank_active`,
    `while_rank_stationary_active`, `loopActive_decClock`;
  - `ReadOnlyFn.keepsOn`, `worldOK_of_evmInv`, every `localsOnly_*`/`localsFree_*` instance
    (incl. `localsFree_mainEntry`, `localsOnly_txReady`, `localsFree_reqsFresh`,
    `localsOnly_htabNewReady`; revision 5: `localsFree_evmRun`, `localsFree_evmMsgReady`,
    `localsOnly_blockReady`, `localsOnly_mptObjReady`);
  - revision 5: `evmInv_iff_at`, `evmInv_of_evmMsgReady`;
  - revision 6: `cellHits_aligned` and the 47 `«callees_f»` (`decide` on the AST);
  - the glue `run_frames_step_of_specs`;
  - the bridge (unchanged).
- `[propext]`: `K_pan_budget`.
- also `sorryAx`:
  - `gb_*`, through their `gbody_*`;
  - `run_frames_step`;
  - `coveredSourceTicksConsumedBounded_K_pan`, through `primitives`.

The statement diffs of §0.2 and §0.4 are produced by `sigdiff.py` (in `scripts/`). It compares the
`theorem`/`def`/`structure` signatures of two revisions of the Lean file, with comments removed.

`K_pan.log2 = 754` (`#eval`).

The script uses only the Python standard library. `panast.py` parses the generated AST file
line-record by line-record into a term tree; `coverage.py` computes the call graph, purity and
transitive global writes, the loop classes (`OVERRIDES` holds the hand-checked loops with their
argument), the cost formulas and the outputs. The hand-written parts of the Lean file live next to
the script (`parts/`); `assemble.sh` concatenates them with the generated parts. Revision 4 adds
`compose` to `coverage.py`, which generates the guarded compositions: `needed_calls`,
`written_params`, `fresh_only`, and the hand tables `REGION`, `KEEP_PRE`, `CALL_STMT`, `CALL_W`.
