# GuestInv revision 6: a guarded route to `CoveredSourceTicksConsumedBounded`

Track `guestinv-opus55`, mission 9409f9a9 (Wave 8), branch `wave8/guestinv-opus55`. Revision 2
answered the round-1 quorum (`campaign/reviews/guestinv-r1.md`), revision 3 the round-2 quorum
(`guestinv-r2.md`), revision 4 the round-3 quorum (`guestinv-r3.md`, §0.3 and §0.4), and revision
5 (Fable's items) and revision 6 (Astra's items, commit d16ff8bc0) answer the round-4 quorum
(`guestinv-r4.md`), §0.1 and §0.2. Both are narrow fix rounds: only the statements listed in §0.2
changed. All statements are in
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
| **new** composition obligations `gbody_f : GBody.«f»` (callee bounds and contracts → `f`'s bound) | §7 (generated) | 12 **proved** by concrete-body composition, 35 `sorry` |
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

**3.** Fable's item 1, already fixed in revision 5 (`EvmRun`, `ek_*`). Astra's `wk_charge_gas`
and `wk_stack_pop` no longer exist.

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
single-function:
- its docstring lists the direct callees of `f`, then the contract hypotheses;
- a proved `«callees_f»` checks by `decide` on the literal AST (`progCallees`, `fnBody`,
  `sameNames`) that the direct callees of `f` are exactly the functions whose bounds are
  hypotheses (47 theorems);
- `coverage.py` asserts that every hypothesis names a direct callee of `f`;
- §6 has the per-function table (`out/gbody.md`).

So `gbody_f` assumes only facts about `f`'s callees and concludes only about `f`'s body. That is
the shape of an `fb_*` leaf, plus callee hypotheses. Whether it meets the round-3 boundary is the
quorum's ruling.

**Found while auditing the hypotheses: `RollbackReady`.** `rollback_child_access` truncates
`child+168`, then reloads `child+176` and `child+272`. Its guard therefore also requires:
- the child record `(child, 280)` allocated words, outside both table footprints;
- the two tables equal, or with disjoint footprints.

`finish_child` gets these from `EvmInv`.

## 0.2 Changes since 0f8dea8c7 (revisions 5 and 6)

`sigdiff.py` (§9) on revision 4 (0f8dea8c7) vs revision 6 (d16ff8bc0 + this DESIGN):

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

**Census:** 920 leaf sorries:
- 727 `fb_*`;
- 14 §7 contracts;
- 144 callee contracts: `ro_*` 30, `ww_*` 50, `wk_*` 43, `ek_*` 10, `ak_*` 1, `fk_frame_open`,
  `nf_*` 7, `nk_*` 1, `rv_*` 1;
- 35 `gbody_*`.

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
  - `KeepsOn P W g` (59): the reviewers' `PreservesOn WorldOK WorldOK` restricted to resuming
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
| `RollbackReady` | the child's tables `+168/+176` are `HtabWF` and allocated | `rollback_child_access` |
| `FinishReady` | `EvmInv` ∧ `EvmDone` ∧ kind ≠ 0 | `finish_child` |
| `EvmInv` | §5 of the Lean file (revision 4: capacities `≥ 1`, return data owned, `RetWindowsOK`, release lifetime of surviving tables) | `run_frames` |
| `EvmRun` (revision 5) | `EvmInv` ∧ `¬EvmDone` (the precondition of `op_dispatch_spec`) | `op_dispatch`, `op_sload`, `op_sstore` |
| `ArenaReady` | `GuestInv` ∧ `ArenaOK` | `_decode_witness_node_body` |
| `MptReady` | `ArenaReady` ∧ the `node` parameter is rooted in a typed `NodeHeap` | `_mpt_insert_node`, `_mpt_delete_node(_body)` |
| `MptObjReady` (restated in revision 5) | `ArenaReady` ∧ ∃ S, `WorldTyped s S` ∧ `MptObjIn s S`: trie object `m` allocated and rooted in a typed `NodeHeap`, `m` and every node disjoint from the tables of `S` and the fixed objects | `mpt_set` |
| `MsgReady` (new) | `ArenaReady` ∧ ∃ S, `WorldTyped s S` ∧ `msg+152`, `msg+160` ∈ S | `process_message`, `process_message_call`, `process_create_message` |
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

