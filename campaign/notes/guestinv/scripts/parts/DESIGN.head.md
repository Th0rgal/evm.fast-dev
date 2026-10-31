# GuestInv revision 7: a guarded route to `CoveredSourceTicksConsumedBounded`

Track `guestinv-opus55`, mission 9409f9a9 (Wave 8), branch `wave8/guestinv-opus55`. Revision 2
answered the round-1 quorum (`campaign/reviews/guestinv-r1.md`), revision 3 the round-2 quorum
(`guestinv-r2.md`), revision 4 the round-3 quorum (`guestinv-r3.md`, §0.3 and §0.4), and revision
5 (Fable's items), revision 6 (Astra's items, commit d16ff8bc0) and revision 7 (Gemini's items 1
and 2: relational callee contracts, constructor return typing, typed init post-states, the BAL
storage lists, and the walk audit of every `gbody_*`) answer the round-4 quorum
(`guestinv-r4.md`), §0.1 and §0.2a. Only the statements listed there changed. All statements are in
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
| callee contracts (revision 7: RELATIONAL in the world and EVM tiers): `WorldKeeps` (84 `wk_*`: `WorldStep` = typing `S ⊆ S'`, `OwnedGrows`, `FrameOutside`, `GlobalsKept`, `RecordsKept`, extra), `EvmKeeps` (12 `ek_*`: `EvmInv`, `ev`/`cur_cont`/`evmChain` kept), `MptKeeps` (2 `mk_*`), `ReadOnlyFn` (30), `WritesWithin` (5, `ArenaReady` tier only), `KeepsOn` (`ak__decode_step`, `fk_frame_open`), `NodeFn` (7), return typing (6 `rt_*`), value contracts (10: `nk_*`, `rv_*` ×5, `zv_memzero`, `nz_htab_set`, `dm_*` ×2) | §7 (generated) | `sorry` (158 statements; revision 7, §0.2a) |
| composition obligations `gbody_f : GBody.«f»` (callee bounds and contracts → `f`'s bound; each checked single-function, `«callees_f»`; revision 7: every walk checked against its hypotheses, §6) | §7 (generated) | 18 **proved** by concrete-body composition (revision 7: +2, `process_checked_system_transaction`, `ws_get_storage`), 29 `sorry` |
| revision-7 lemmas: `worldTyped_iff_with`, `WorldStep.worldOK(_nil)`, `WorldKeeps.keepsOn`, `EvmKeeps.keepsOn`, `rollbackReadyAt_of_evmInv`, `callee_param_one`, `callEntryOn_inputReady`, `KeepsOn.resumeOn`, `Hoare.ite_raise_skip`, `localsOnly_inputReady` | §7 | **proved** |
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

### Gemini 4 Carbon (review of 0f8dea8c7; revisions 6 and 7)

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
- the Lean header now says revision 7;
- `mpt_insert_node_spec` has a docstring: a cycle of empty extension segments never returns and
  reaches `WhileTimesOut` within the `2^130` bound, so the spec is vacuous on such runs.

**Item 1 (fixed in revision 7): relational callee contracts.** `KeepsOn W W` allowed any
`W → W` transition, so a caller lost its local facts across a call. Revision 7 REPLACES every
non-read-only callee contract at a world-tier or EVM-tier call site by a relational one. It does
not add a second leaf next to the old `KeepsOn` (a parallel revision-7 attempt on this branch,
commits d589ac3e5..f6d059cd0, did that; it is merged in history and superseded by b2ccd7a97, see
§0.2a). The definitions are in §7 of the Lean file ("Relational callee contracts").

- **(a) `wk_g : WorldKeeps P R gw keep Q g`**: from a `P` entry, every resuming outcome is a
  `WorldStep R gw keep Q`:
  - `ArenaReady post`; `heap_ptr` only grows;
  - every global outside `gw` (the closure's global writes, `coverage.py` `gwf`) is unchanged;
  - `RecordsKept`: the words `keep` of the four typed records `ws`, `bs`, `ts`, `bo` that the
    closure never stores to are unchanged (`coverage.py` `rec_written`: a field-precise scan of
    every store target and written-parameter argument over the full closure, contracted callees
    included; a non-constant offset counts as the whole record). Example: `process_transaction`
    writes `bo+0/8/16/48`, so `wk_process_transaction` keeps `bo+24 … bo+80`, in particular
    `bo+64` and `bo+80`; `requests_append` writes only `bo+64`;
  - for EVERY typing `(S, Nd)` of the entry (`WorldTypedWith`, `WorldTyped` with the trie node set
    exposed) whose typed memory (`worldTypedIvls`) the callee's output regions `R s` avoid:
    - some `S' ⊇ S`, `Nd'` type the exit, so a caller's own tables in `S` stay typed tables;
    - `OwnedGrows`: every exit-owned interval (`worldOwned`: table footprints, fixed objects,
      trie nodes and paths) is `(0, 0)`, inside an entry-owned interval, or in the heap allocated
      during the call; a caller object disjoint from the world at entry stays disjoint;
    - `FrameOutside`: memory outside the entry-owned intervals, `R s`, the free scratch gap and
      the free heap is unchanged; a caller object outside the world keeps its contents;
    - the callee-specific extra `Q` for the same `S'`.

  `R` is the callee's caller-memory output: the `REGION` parameter extents (`dst`/`out`/…), plus
  `RREG`: `msg` (176 bytes) of `process_message_call`, `out` (32 bytes) of `compute_state_root`,
  `build_mpt_indexed`, `mpt_root`. Writes into world objects (the `bo` arrays and lists, tables,
  content-free global buffers such as `keccak_pad`, `bal_key_buf`) are covered by the owned
  intervals instead; `lst_push` at a world site has pre `BoListArg` (its list is `bo+40` or
  `bo+72`) and no region. The revision-6 `WorldAvoids [(out, 32)]` preconditions are gone: the
  avoidance is now a hypothesis inside `WorldStep`. Extras `Q`: `ReqCountInc` (`requests_append`:
  `bo+64` up by exactly 1), `RetMptObj` (`mpt_from_witness`), `RetInput` (`decode_host_input`).

  Every callee that revision 6 covered by `WritesWithin` at a world-tier site now gets a
  `WorldKeeps` too (`ww_* → wk_*`, 43 leaves; 2 more at EVM sites become `ek_*`), because `WritesWithin` alone does not give the
  post-state `WorldOK` when the callee writes a typed record or rebinds a world global
  (`track_ancestor_access` writes the `bs` record; `bal_init`, `state_fresh_tx` and `main`'s 12
  `*_init` assign world globals). `WritesWithin` stays only in the `ArenaReady` tier (5 leaves).
- **(a′) `mk_mpt_set`, `mk_mpt_root : MptKeeps R gw keep g`**: `MptObjStep`, the trie-object
  analogue. For every typing `(S, Nd)` and every node set `Nm` of the object `m`
  (`MptObjInWith s S Nm m`, `MptObjIn` with `Nm` and `m` exposed), the object stays typed in the
  exit world `S'`, away from the persistent tries, its intervals grow only into fresh heap, and
  memory outside the world, the object and `R` is unchanged. `compute_state_root` and
  `build_mpt_indexed` call `mpt_set` in a loop on one object, then `mpt_root` on it.
- **(b) `ek_g : EvmKeeps P gw g`**: `EvmStep gw`: `EvmInv post`, the heap only grows, the globals
  outside `gw` are unchanged (`ev`, `cur_cont` are in no `ek` callee's `gw`), and
  `evmChain post = evmChain s`. `RollbackReady` on `child` comes from the PROVED lemma
  `rollbackReadyAt_of_evmInv : EvmInv s → RollbackReadyAt s (globN s "ev")` (`RollbackReady` is
  `RollbackReadyAt` at the local `child`). `finish_child` reads `child := ev`, so after any
  `ek_*` step (`ev` kept, `EvmInv` again) and after `ev := parent` (memory unchanged) its callee
  guard follows. A callee writing a caller buffer at an EVM site (`u256_to_be32` into
  `evm_key_buf`) has pre `EvmAvoids R`.
- **(c) Return typing** (`rt_*`, `Returns P Q g`: a normal return is a word `w` with `Q s post w`),
  at every guard-carrying site of an unproved composition:
  - `rt_alloc`: `FreshBlock s post p n`: aligned, `[p, p + round8 n)` allocated during the
    call, in-domain words;
  - `rt_msg_new`: a fresh 176-byte block, zeroed (22 words); `rt_te_new`: likewise, 200 bytes;
  - `rt_lst_new`: if `esz·cap < 2^64` and `1 ≤ cap`, a fresh 24-byte header, a fresh disjoint
    `esz·cap`-byte array, length `0`, capacity `cap` (hence `LstOK`);
  - `rt_htab_copy`: a normal return copied a NONZERO table (`load(t + 80)` errors at `0`), and
    a copy of a well-formed table is a fresh well-formed table with the same count;
  - `rt_mpt_new`: a fresh 16-byte block holding `root_node`, `secured`;
  - `mpt_from_witness`: `wk_mpt_from_witness` with extra `RetMptObj`, a fresh trie object with a
    fresh node set, `MptObjInWith` in the exit world `S'`, away from its tries.
- **(d) Init contracts.** `bal_init`, `state_fresh_tx` and `main`'s 12 `*_init` calls get
  `wk_*`: from `WorldOK`, a `WorldStep`, so `WorldOK` after the call (`WorldStep.worldOK_nil`,
  proved). The buffer globals they set are fixed objects of the exit typing; `OwnedGrows` puts
  them in fresh heap, so they are disjoint from everything the caller holds.

Facts each caller needed, and where they now come from:
- **`process_create_message`, `process_message_call` (`MsgReady`)**: the record is outside the
  world (`MsgReady`), so `FrameOutside` keeps its words (`msg+152`, `msg+160`, `msg+40`);
  `S ⊆ S'` keeps the two tables; `OwnedGrows` keeps the disjointness. Revision 7 puts the record
  in the heap (`Inside … sourceBase heap_ptr`, was `Allocated`, which allowed scratch), so it stays
  allocated (the heap only grows; `scratch_ptr` is in most callees' `gw`).
- **`process_transaction`**: `m`, `te`, `sender`, `al_addrs`, `al_keys` are fresh blocks
  (`rt_*`), `aa`, `ak` fresh tables (`htab_new_spec`); the message gas `m+40 = mgas ≤ 2^24` from
  the new value contracts `rv_validate_transaction` (`RetIntrinsic`: regular intrinsic `≤ 2^24`,
  `TxErr 63` otherwise) and `rv_min` (`RetLe`). `index < ntx` is its own guard.
- **`execute_block`**: `bo ≠ 0` (`bo` in no callee's `gw`); `bo+80 = ntx` and `bo+64 = 0` by
  `RecordsKept`; the zeroed record by the new `zv_memzero` (`ZeroFills`).
- **`process_general_purpose_requests`**: `bo+64` by `RecordsKept` across the system
  transactions and by `ReqCountInc` across `requests_append` (at most 5 appends, `ReqRoom`).
- **`compute_state_root`**: `cache` (`rt_htab_copy`), `new_roots` (`htab_new_spec`) join `S`;
  the trie objects by `RetMptObj` / `MptObjStep`; the buffers `vbuf`, `enc`, `root` are fresh,
  and the new `rv_u256_to_be_min` (`≤ 32`) and `rv_rlp_encode_bytes` (`≤ n + 9`) keep
  `rlp_encode_bytes`'s region inside `vbuf`.
- **`payload_header`**: `(wr, 32)` is fresh (`rt_alloc`) and outside the world; `OwnedGrows`
  across `build_mpt_indexed` and `encode_withdrawal_rlp` keeps it so.
- **`finish_child`**: `ek_*` keep `ev`, `cur_cont`, `evmChain`; `rollbackReadyAt_of_evmInv`.

**Audit of every `gbody_*` against its hypotheses (revision 7).** Checking the walks
(§6 "Revision-7 walk check") found six more places where the revision-6 hypotheses did not
suffice; each is fixed:
1. **`state_init`** calls `decode_witness_to_mpt` (guard `WorldOK`) after `ws := alloc(40)` and
   before `ws+24`/`ws+32` are stored: fresh heap can hold anything, so `WorldOK` does not hold
   there. The decoders `decode_witness_to_mpt`, `_decode_witness_node`,
   `_decode_witness_node_mpt`, `mpt_from_witness` only need `ArenaReady` (their revision-6 proofs
   used `WorldOK` only to reach it), so their guard is now `ArenaReady` and their proofs carry over.
2. **`run_attempt` → `execute_block`**: `BlockReady` needs `16·ntx + 16 < 2^64`, which follows only
   from `run_attempt`'s own loop (a full cycle of `txs + 16 i + 8 mod 2^64` leaves the memory
   domain, so the loads error), and `execute_block` re-reads `ntx` through `si+0`, `pl+40`. Those
   two cells must be outside the world for the steps in between to keep them, and `WorldOK` says
   nothing about `si`. New guard `InputReady` on `verify_stateless_new_payload`, `attempt_l1..7`,
   `run_attempt`: `WorldOK` and the input cells allocated words outside the world (`InputAt`).
   `main` gets them fresh from `decode_host_input` (`RetInput`). The 8 proved attempt bodies are
   re-proved under `InputReady` with the new PROVED `callEntryOn_inputReady` (a call `f(si)` to
   a function whose only parameter is `si` keeps the guard; from `callee_param_one`, proved).
3. **`get_storage`** calls `htab_set(load(ts + 24), …)` and then the guarded `ws_get_storage`;
   `RootIn` allows the slot to be `0`, where `htab_set_spec` does not apply. New
   `nz_htab_set : ArgNonNull "t"` (`htab_set` loads `t+0` first). The walk splits on `t = 0`.
4. **`build_mpt_indexed`**: `rlp_encode_word(mpt_key_scratch, i)` had the extent 33, past the
   16-byte buffer, so the region could not be shown to avoid the world. It writes `1 + rlp_be_len(w)
   ≤ 9` bytes (AST 4795): `REGION` extent 9.
5. **`compute_state_root`**: `rv_u256_to_be_min`, `rv_rlp_encode_bytes` (above).
6. **`payload_header`, `process_transaction`**: arrays sized by a count read from memory
   (`alloc(16·nwd + 16)`, `alloc(52·nkeys + 8)`) may wrap; the loops filling them exit normally
   only when the count is small, which needs `dm_encode_withdrawal_rlp`,
   `dm_memcpy : ResumesInDomain` (the callee touches its region, so a normal return means it is in
   the domain). The loop invariant is "no wrap → `WorldOK` and the local facts".

**New proved Hoare/glue lemmas:** `worldTyped_iff_with`, `WorldStep.worldOK`,
`WorldStep.worldOK_nil`, `WorldKeeps.keepsOn` (the revision-6 shape, so the proved compositions
keep their proofs), `EvmKeeps.keepsOn`, `rollbackReadyAt_of_evmInv`, `callee_param_one`,
`callEntryOn_inputReady`, `inputReady_worldOK`, `localsOnly_inputReady`, `inputAt_with_locals`,
`KeepsOn.resumeOn` (a `decCall` into a `KeepsOn W W` callee resumes in `W`), `raise_ne_none`,
`Hoare.ite_raise_skip`. With them `gbody_process_checked_system_transaction` is PROVED
(`state_fresh_tx`, `ext_code_of`, `alloc` through their world steps, guard clauses, the guarded
`process_unchecked_system_transaction`), and so is `gbody_ws_get_storage` (`ws_storage_root_of`
through its world step, `memeq` read-only, the guarded `ws_storage_trie`, then a `GuestInv`
tail).

## 0.2a Changes since 311d46674 (revision 7)

`sigdiff.py` on `311d46674` vs the revision-7 file. The parallel commits d589ac3e5..f6d059cd0
(`ws_*`/`es_*` steps next to `KeepsOn` leaves, 991 sorries) are merged in history (b2ccd7a97) and
superseded: their Lean and script changes are not in the revision-7 file, only their DESIGN text
on item 2 and the non-blocking items is kept.

**No `fb_*` changed** (727, textually identical). The 14 §7 contract leaves are unchanged, except
that `mpt_insert_node_spec` gains a docstring.

**Changed definitions (6):**
- `balObjects` and `TablesTyped`: the BAL per-slot storage lists (Gemini item 2);
- `MptObjIn`: now `∃ Nm, MptObjInWith s S Nm (locN s "m")` (the same proposition, node set and
  object exposed);
- `RollbackReady`: now `RollbackReadyAt s (locN s "child")` (the same proposition);
- `MsgReady`: the record lies in the heap (`Inside … sourceBase heap_ptr`, was `Allocated`);
- `Primitives`: the field list of the new hypotheses.

**Changed guards (13 `gb_*` statements):** `ArenaReady` for `decode_witness_to_mpt`,
`_decode_witness_node`, `_decode_witness_node_mpt`, `mpt_from_witness` (audit 1); `InputReady` for
`verify_stateless_new_payload`, `attempt_l1..7`, `run_attempt` (audit 2).

**Changed `GBody.«f»` (37):** new hypothesis lists. The 16 revision-6 proved ones keep their callee bounds; the
contract hypotheses of `get_pre_tx_storage`, `get_storage_original` (`wk_record_pre_state_read`)
and `ws_storage_trie` are now relational.

**Changed callee contracts (51):** 41 revision-6 `wk_*` (`KeepsOn … WorldOK`) are now
`WorldKeeps`; the 10 `ek_*` (`KeepsOn … EvmInv`) are now `EvmKeeps`.

**Replaced (47):**
- `wk_mpt_set`, `wk_mpt_root` → `mk_mpt_set`, `mk_mpt_root` (`MptKeeps`);
- 45 `ww_*` at world- or EVM-tier sites → 43 `wk_*` and 2 `ek_*` with their regions (`ww_alloc` →
  `wk_alloc`, `ww_memcpy` → `wk_memcpy`, `ww_bal_init` → `wk_bal_init`, the 12 `ww_*_init` →
  `wk_*_init`, `ww_state_fresh_tx` → `wk_state_fresh_tx`, `ww_track_ancestor_access` →
  `wk_track_ancestor_access`, `ww_u256_to_be32` → `ek_u256_to_be32`,
  `ww_is_warm_storage_key` → `ek_is_warm_storage_key`, …). `wk_rlp_encode_word`'s extent is 9
  (`ww_rlp_encode_word` had 33).

**New leaves (14):**
- return typing `rt_alloc`, `rt_msg_new`, `rt_te_new`, `rt_lst_new`, `rt_htab_copy`, `rt_mpt_new`;
- value contracts `zv_memzero`, `rv_validate_transaction`, `rv_min`, `rv_u256_to_be_min`,
  `rv_rlp_encode_bytes`, `nz_htab_set`, `dm_memcpy`, `dm_encode_withdrawal_rlp`.

**New definitions:** `WorldTypedWith`, `typedRecords`, `worldTypedIvls`, `worldOwned`,
`IvlsDisj`, `freeGap`, `heapFree`, `GlobalsKept`, `RecordsKept`, `OwnedGrows`, `NoExtra`,
`WorldStep`, `WorldKeeps`, `EvmAvoids`, `EvmStep`, `EvmKeeps`, `mptObjIvls`, `MptObjInWith`,
`MptObjStep`, `MptKeeps`, `FreshBlock`, `RetWord`, `Returns`, `RetMptObj`, `ReqCountInc`,
`inputCells`, `RetInput`, `InputAt`, `InputReady`, `RollbackReadyAt`, `ArgNonNull`,
`ResumesInDomain`, `BoListArg`, `ZeroFills`, `RetIntrinsic`.

**New proved theorems:** the lemmas listed under item 1, `gbody_process_checked_system_transaction`
and `gbody_ws_get_storage` (18 proved `gbody_*`, was 16).

**Census:** 928 leaf sorries:
- 727 `fb_*`;
- 14 §7 contracts;
- 158 callee contracts: `wk_*` 84, `ek_*` 12, `mk_*` 2, `ro_*` 30, `ww_*` 5, `ak_*` 1,
  `fk_frame_open`, `nf_*` 7, `nk_*` 1, `rt_*` 6, `rv_*` 5, `zv_*` 1, `nz_*` 1, `dm_*` 2;
- 29 `gbody_*`.

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
| `ArenaReady` | `GuestInv` ∧ `ArenaOK` (revision 6: the three allocator pointers 8-byte aligned) | `_decode_witness_node_body`; revision 7: `decode_witness_to_mpt`, `_decode_witness_node`, `_decode_witness_node_mpt`, `mpt_from_witness` |
| `MptReady` | `ArenaReady` ∧ the `node` parameter is rooted in a typed `NodeHeap` (revision 6: paths typed) ∧ `level ≤ klen` ∧ `KeyIn` of the key suffix `(key + level, klen − level)` (revision 6) | `_mpt_insert_node`, `_mpt_delete_node(_body)` |
| `MptObjReady` (restated in revision 5) | `ArenaReady` ∧ ∃ S, `WorldTyped s S` ∧ `MptObjIn s S`: trie object `m` allocated and rooted in a typed `NodeHeap`, `m` and every node disjoint from the tables of `S` and the fixed objects | `mpt_set` |
| `MsgReady` (new) | `ArenaReady` ∧ ∃ S, `WorldTyped s S` ∧ `msg+152`, `msg+160` ∈ S, the record owned (revision 6: also `AvoidsTries`) | `process_message`, `process_message_call`, `process_create_message` |
| `TxReady` (new) | `WorldOK` ∧ `index < bo+80` | `process_transaction` |
| `BlockReady` (revision 5) | `WorldOK` ∧ `16·ntx + 16 < 2^64`, `ntx = (si+0)+40` | `execute_block` |
| `InputReady` (revision 7) | `InputAt s si`: `ArenaReady` ∧ a typing `(S, Nd)` ∧ the input cells `(si, 8)`, `(pl + 40, 8)` heap words outside `worldOwned` | `verify_stateless_new_payload`, `attempt_l1..7`, `run_attempt` |
| `ReqsFresh` (new) | `WorldOK` ∧ `bo+64 = 0` | `process_general_purpose_requests` |
| `WorldOK` | `ArenaReady` ∧ ∃ S, `WorldTyped s S` (tables, journal, fixed records and block-output objects, tries) | the other 15 guarded functions |
| `MainEntry` | §2 | `main` |

Callee-contract pre-conditions (not bound guards): `ReqRoom` (`requests_append`), `FrameOpenReady`
(`frame_open` in `process_message`), `WorldAvoids R` (an output region outside every typed table
and fixed object). Revision 5: `EvmMsgReady` (post of `fk_frame_open`, pre of `ek_depth0_prepare`:
`EvmInv` with the outermost message `ev+112` owned for the same table set, `EvmInvAt`/`MsgOwned`)
and `MptObjAvoids R` (`MptObjReady` plus an output region, pre of `wk_mpt_root`).

Every guard is `LocalsOnly` (proved instances, §7 of the Lean file), so `dec_onLocals`,
`LocalsOnly.decClock` and `LocalsOnly.setVar` apply inside every guarded body.

### Revision-7 walk check of every `gbody_*` (round-4 Gemini item 1, coordinator note)

A `gbody_f` is a genuine single-function primitive only if its own hypotheses suffice to prove it
without unfolding a callee. For each of the 30 revision-7 primitives, the walk below names, at every
guard-carrying call site and loop head, the fact needed and the hypothesis it comes from (the
`ws_get_storage` row is now PROVED). The
walks also use only the following facts about the DEFINITIONS (no callee involved). Where proved,
this is said; the others are lemmas the prover of the composition states and proves on the way.

- **W1, typed-cell congruence:** `WorldTypedWith s S Nd` reads memory only in
  `worldTypedIvls s S Nd`, and reads the globals of the roots, buffers, journal and allocator.
  The allocator pointers enter only monotonically (`Allocated` grows with `heap_ptr`). So a store,
  or an output region, outside those cells keeps the typing.
- **W2, table update:** `htab_set/del/truncate_spec` (`HtabExit`) on a table `t ∈ S` keeps the
  typing with the same `S`, provided the value written is allowed. `S`-tables that are values of
  `bs+32`/`ts+32` must stay tables. Every world-tier `htab_set` writes `1`, a fresh pointer, or (on
  a local table) anything.
- **W3, fresh extension:** a fresh well-formed table (`htab_new_spec`, `rt_htab_copy`) extends
  `S`. A fresh block bound to a buffer global or to `bo` keeps `FixedTyped` once the typed words
  it holds are set (`zv_memzero`, then the stores).
- **W4, freshness:** a `FreshBlock` (or an `OwnedGrows` interval in fresh heap) is disjoint from
  every interval allocated at the call's entry.
- **W5, domain cycle:** a loop that has accessed `base + c·i` for every `i < N` (`c > 0`) without
  error has `c·(N − 1) < 2^64` and `base + c·(N−1) ∈ [sourceBase, heapEnd)`. A count read from
  memory that sizes an array is therefore small once the loop exits normally.
- **W6, call parameters:** the callee's parameter holds the argument's value (`callee_param_one`,
  PROVED for one parameter; `callEntryOn_inputReady` PROVED on top of it). The same
  `lookupCodeHOLFinite` unfolding gives the multi-parameter case for `MsgReady` (`msg`),
  `TxReady` (`index ← i`), `MptReady`, `RollbackReady`, `HtabArgWF` and `FrameOpenReady`.

With `WorldStep` the WorldOK-tier walks never re-type the world after a callee: `WorldStep.worldOK`
(PROVED) gives `WorldOK`. The local facts come from the same `S'` (`S ⊆ S'`), `OwnedGrows` and
`FrameOutside`. W1–W3 are needed only for the function's OWN stores and global assignments.

| `gbody_*` | guard-carrying sites and loop heads: fact needed ← hypothesis |
|---|---|
| `_decode_witness_node_body` | loop head (`GUARD`, revision 6): `ArenaReady` ← `ak__decode_step`, `ww__resolve_step`, `ww_node_new_ext`, `ww_rlp_item` (frames), `ro_mpt_fail`; rank: the scratch stack (DESIGN §3) |
| `_mpt_delete_node` | `_mpt_delete_node_body`: `MptReady` ← entry, `ro_scratch_mark` (resume), W6 (four same-named arguments) |
| `_mpt_insert_node`, `_mpt_delete_node_body` | loop heads: `MptReady` ← `nf_*` (`NodeFnExit`: grown node set, kinds kept, paths fresh), `rv_common_prefix_length` (`level ≤ klen`, `pl < sl`), `ro_*`; revision 6 requirement table below |
| `mpt_set` | `_mpt_insert_node`/`_mpt_delete_node`: `MptReady` with `node := m+0`, `key/klen := nk`, `level = 0` ← `MptObjReady` (typed `Nm`), `ww_mpt_nibble_key` (frame: only global buffers, which `Nm` avoids, and fresh heap), `nk_mpt_nibble_key` (fresh nibbles: `KeyIn` by W4) |
| `build_mpt_indexed` | `mpt_set`: `MptObjReady` for `m` ← `wk_mpt_new` + `rt_mpt_new` (fresh, `+0 = 0`, so `Nm = []`, W4); loop head: `MptObjReady` ← `wk_rlp_encode_word` (region `(mpt_key_scratch, 9)` inside a content-free buffer, so it avoids the typed cells, and the object is outside world and region), `mk_mpt_set` (`MptObjStep`); `ro_heap_mark` |
| `compute_state_root` | `htab_set(cache|new_roots)`: `HtabArgWF` ← `rt_htab_copy` (`bs+72 ≠ 0`, so it is in `S`, and the copy is fresh and typed; W3), `htab_new_spec` (W3); `mpt_set(mpt|state_mpt)`: `MptObjReady` ← `wk_mpt_from_witness` (`RetMptObj`); carried across `wk_alloc`/`rt_alloc`, `wk_u256_to_be_min` + `rv_u256_to_be_min` (region `(vbuf+8, 32)` in fresh `vbuf`), `wk_rlp_encode_bytes` + `rv_rlp_encode_bytes` (region `(vbuf+40, n+9)`, `n ≤ 32`, in `vbuf`), `wk_memcpy` (into fresh `enc`), `wk_encode_account` (fresh `enc`), `wk_ws_get_account_optional`, `wk_cache_get_root`, `ro_htab_get/has/item`, `ro_u256_is_zero` by `FrameOutside`/`OwnedGrows`; after `htab_set` by W2 and the `HtabExit` frame; `mk_mpt_set`, `mk_mpt_root` (region `(root, 32)` fresh) keep `cache`, `new_roots` in `S'`; five `CTR` loop heads: the same invariant |
| `ws_get_storage` | `ws_storage_trie`: `WorldOK` ← `wk_ws_storage_root_of`, `ro_memeq` |
| `idx_start_storage` | `get_pre_tx_storage`: `WorldOK` ← `wk_st_le64` (region `(bal_key_buf, 8)`), `wk_memcpy` (`(bal_key_buf+8, 20)`, `(bal_key_buf+28, 32)`: inside a content-free buffer, avoiding the typed cells), `ro_htab_get` |
| `update_builder_from_tx` | `idx_start_account`, `idx_start_storage` (guarded) and three `CTR` loop heads: `WorldOK` ← the `wk_*` steps (`add_*_change`, `bal_remove_change`, `add_storage_write`, `remove_storage_write`, `get_code`, `idx_start_*`), `ro_*`; item 2 makes `wk_add_storage_write`/`wk_remove_storage_write` true |
| `htab_truncate` | loop head: `HtabArgWF` ← `htab_del_spec`; rank: count `t+24` ← `htab_del_progress_spec` (revision 4) |
| `rollback_child_access` | 1st `htab_truncate`: ← `RollbackReady`; 2nd: `child+176` unchanged (record outside the first footprint, `HtabExit` frame), its table equal to the first (`HtabExit`) or with a disjoint footprint (unchanged, so `HtabWF` by congruence), allocated (heap grows, `scratch_ptr` unchanged) ← `htab_truncate_spec` |
| `finish_child` | `rollback_child_access(child)`: `RollbackReadyAt child` ← entry (`FinishReady`, `child = ev`, `rollbackReadyAt_of_evmInv` PROVED), or after the `kind = 2` branch ← `ek_create_finish`, `ek_state_restore`, `ek_refill_frame_state_gas`, `ek_frame_halt` (`ev` kept, `EvmInv`, then the lemma), the handler's two stores into `child+120/128` (outside both footprints, so W1 at the record) and `ev := parent` (memory unchanged); W6 |
| `get_storage` | `ws_get_storage`: `WorldOK` ← `wk_sk_make`, case `ts+24 = 0` (`nz_htab_set`: no resume) / `≠ 0` (`∈ S`, `htab_set_spec` and W2), `ro_stor_lookup`, `wk_record_pre_state_read` |
| `op_sload` | `get_storage`: `WorldOK` ← `EvmInv` (`worldOK_of_evmInv`) ← `ek_stack_pop`, `ek_u256_to_be32` (pre `EvmAvoids [(evm_key_buf, 32)]`: a fixed buffer, disjoint from typed cells and frames by `EvmInv`), `ek_is_warm_storage_key`, `ek_charge_gas`, `ek_warm_storage_key` |
| `op_sstore` | `get_storage_original`, `get_storage`: as `op_sload`, plus `ek_require_not_static`, `ek_check_gas`, `ro_max`, `ek_get_storage_original` |
| `op_dispatch` | `op_sload`/`op_sstore`: `EvmRun` ← entry (the opcode dispatch does not write) |
| `run_frames` | the glue `run_frames_step_of_specs` (PROVED) from the four §7 specs; rank `evmPot` |
| `process_message` | `frame_open`: `FrameOpenReady` ← `MsgReady`, `kind = 0` (W6); `depth0_prepare`: `EvmMsgReady` ← `fk_frame_open`; `frame_start`: `EvmInv` ← `ek_depth0_prepare`, `ro_state_snapshot`, the store `cur_cont+24` (W1 for `EvmInv`: the continuation's `+24` is not read); `run_frames`: ← `ek_frame_start` |
| `process_create_message` | `process_message`: `MsgReady` ← `wk_destroy_storage`, `wk_mark_account_created`, `wk_increment_nonce` (record outside the world, `FrameOutside`/`OwnedGrows`, `S ⊆ S'`, heap record stays allocated), `ro_state_snapshot` |
| `process_message_call` | `process_create_message`/`process_message`: `MsgReady` ← `wk_alloc`, `rt_alloc`, `wk_memzero` (region `(out, 96)` fresh), `wk_account_deployable` |
| `process_unchecked_system_transaction` | `process_message_call`: `MsgReady` for `m` ← `wk_state_fresh_tx`, `wk_ext_code_of`, `wk_te_new`/`rt_te_new` and `wk_msg_new`/`rt_msg_new` (fresh; the own stores into them by W1), `htab_new_spec` ×2 (W3: `aa`, `ak` join `S`), `m+40 = 30000000`; `incorporate_tx_into_block`: `WorldOK` ← `wk_process_message_call` (region `(m, 176)` avoids the typed cells) |
| `process_general_purpose_requests` | `requests_append` (`ReqRoom`, `bo+64 < 8`) and `process_checked_system_transaction` ×4: `WorldOK` and `bo+64 = k` ← `ReqsFresh`, `wk_alloc`/`rt_alloc`, `wk_memcpy`, `wk_extract_deposit_data` (regions in the fresh `dep` block; `dep_n + 192 ≤ dep_cap` by the code), `ro_memeq`, `wk_process_checked_system_transaction` (`RecordsKept bo/64`), `wk_requests_append` (`ReqCountInc`); at most 5 appends; two `CTR` loop heads: the same invariant |
| `process_transaction` | `process_message_call`: `MsgReady` for `m` ← the `wk_*` steps, `rt_msg_new`/`rt_te_new`/`rt_alloc` (fresh; own stores by W1; the receipt stores `bo+24/32 + 16·index` stay in the owned arrays since `index < ntx`, so W1), `htab_new_spec` + `htab_set_spec` on `aa`, `ak` (W3, W2), `m+40 = mgas ≤ 2^24` ← `rv_validate_transaction`, `rv_min`; the `al_*` loops (`CTR`): invariant "no wrap → `WorldOK` and the local facts", exit implies no wrap by W5 (own loads of `acc`) and `dm_memcpy`; `incorporate_tx_into_block` and the deletion loop's `clear_account_preserving_balance`: `WorldOK` ← `wk_process_message_call`, `wk_create_ether`, the own stores into `bo+0/8/16/48` (untyped words, W1), `wk_lst_new`/`rt_lst_new` (`8·nl < 2^64` by W5 on the preceding loop's loads of `lp + 8 i`), `wk_lst_push` (`BoListArg`), `wk_encode_receipt`, `ro_htab_item` |
| `process_withdrawals` | `incorporate_tx_into_block` and the `CTR` loop head: `WorldOK` ← `wk_state_fresh_tx`, `ro_u256_mul`, `wk_create_ether`, `journal_n := 0` (`JournalTyped` trivially) |
| `execute_block` | `bal_init` and later: `WorldOK` after `bo := alloc(88)` ← `wk_alloc`/`rt_alloc`, `wk_memzero` + `zv_memzero` (zero record), `rt_alloc` (`txs`, `rcs`, `reqs`; `16·ntx + 16 < 2^64` by `BlockReady`), `wk_lst_new`/`rt_lst_new` (`logs`, `rls`: `LstOK`), the own stores and W3; `process_transaction`: `TxReady` (`i < ntx = bo+80`) ← `wk_bal_init`, `process_unchecked_system_transaction` ×2 (`wk_*`), `wk_state_fresh_tx`, `wk_track_ancestor_access`, `wk_decode_transaction`, `wk_process_transaction` (each keeps `bo` and `bo+80`: `GlobalsKept`, `RecordsKept`); `process_general_purpose_requests`: `ReqsFresh` (`bo+64 = 0`) ← `RecordsKept` through the same steps and `wk_process_withdrawals`; `compute_state_root`, `build_mpt_indexed` ×3, `logs_bloom`: `WorldOK` with fresh output regions (`rt_alloc`) ← `wk_build_block_access_list_rlp`, `wk_validate_block_access_list_gas_limit`, `wk_compute_state_root`, `wk_build_mpt_indexed`, `wk_logs_bloom` |
| `payload_header` | `build_mpt_indexed` ×2: `WorldOK` and the fresh region `(txr|wr, 32)` outside the world ← `wk_alloc`/`rt_alloc`, `wk_memzero`, `wk_keccak256` (`(oh, 32)` fresh), own stores into fresh `h`, `wk_block_rlp_length`, `wk_build_mpt_indexed`, `wd_rlp_slices := alloc(…)` (not a world global); the `CTR` loop: invariant "no wrap → `WorldOK`", exit implies no wrap by W5 with `dm_encode_withdrawal_rlp`, `wk_encode_withdrawal_rlp` |
| `state_init` | `decode_witness_to_mpt` (now `ArenaReady`): ← `wk_alloc` from the `WorldOK` entry (`ArenaReady` after `ws := alloc(40)` and the stores; audit 1); `htab_new_spec`: `HtabNewReady` (literal key lengths) ← `ArenaReady` |
| `run_attempt` | `state_init`, `payload_header` and the `CTR` loop: `WorldOK` and the input cells outside the world ← `InputReady`, `wk_validate_headers`, `ro_check_gas_limit`, `wk_nodedb_build` ×2 (the assignments to `block_hashes(_n)` are not world globals); `execute_block`: `BlockReady` ← the loop (W5: `16·ntx + 16 < 2^64`) and the cells `si+0`, `pl+40` kept by `wk_state_init`, `wk_payload_header`, `wk_alloc`, `wk_header_hash`, `ro_memeq`, `wk_is_valid_versioned_hashes`, `wk_validate_header`, `wk_memzero` (`(be, 120)`, a content-free buffer); `be := alloc(120)` rebinds a fixed buffer (W3) |
| `main` | `mem_init_world` (`WorldOK`); the 12 `wk_*_init` (item 1(d)); `wk_alloc`/`rt_alloc`, `wk_memzero`; `verify_stateless_new_payload`: `InputReady` ← `wk_decode_host_input` (`RetInput`: fresh input cells), `wk_htr_new_payload_request` (`(root, 32)` fresh), W6 |

The two compositions above whose walk has the most bookkeeping, `process_transaction` and
`execute_block`, need no fact beyond these hypotheses and W1–W6.

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

