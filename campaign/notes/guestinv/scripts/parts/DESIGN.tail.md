
### Contract leaves (all `sorry`)

- §7 (hand-written, unchanged statements): `htab_set_spec`, `htab_del_spec`,
  `htab_del_progress_spec`, `htab_truncate_spec`, `htab_union_into_spec`, `htab_new_spec`,
  `htab_new_scratch_spec`, `mpt_insert_node_spec`, `mpt_delete_node_body_spec`, `mem_init_world`,
  `op_dispatch_spec`, `frame_exception_spec`, `frame_epilogue_spec`, `finish_child_spec`. The
  assembly uses ten of them directly. `htab_union_into_spec`, `htab_new_scratch_spec` and the two
  MPT specs are the lemmas the frame and table contract proofs are expected to use.
- Generated callee contracts (141): `ro_*` (30), `ww_*` (50), `wk_*` (51), `ek_*` (6), `ak_*` (3),
  `fk_frame_open`.

## 7. Every `sorry`

- Combinators, glue, bridge, assembly: none.
- §7 contract leaves (14).
- Generated callee contracts (141).
- Composition obligations `gbody_*` (47).
- Unguarded bound leaves `fb_*` (727).

929 in total. No definition contains `sorry`, and no `gb_*` does (they are proved). `assembly` and
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
  before `run_frames`) and by `child_message` into its own fresh block. Global buffers are fixed
  objects. Table values are never written through. The remaining risk is a write through a pointer
  loaded from a table value or from the message, which the syntactic scan treats as unresolved.
  None was reported in the frame cones.
- **Q2 (`finish_child` on `EvmErr`).** Unchanged from revision 3.
- **Q3 (`TriesTyped`).** Unchanged: storage tries are typed through the `ws+32` cache only.
- **Q4 (MPT descent).** Unchanged.
- **Q5 (cost of the generated interface).** 727 unguarded leaves plus 141 contracts, mostly
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
    zeroed, nothing appended yet).
  - The MPT tier (`_mpt_insert_node`, `_mpt_delete_node_body`, `mpt_set`) carries only
    `ArenaReady` across its node constructors (`ak_*`, and `ww_*` for the node writers
    `node_invalidate`, `_insert_into_leaf`, `_delete_ext_finish`). Re-establishing `MptReady` at the
    loop heads needs the constructors' RETURNED nodes typed, which `KeepsOn ArenaReady` does not
    state. Richer node contracts (`MptExit`-shaped, with the returned root typed) may be needed
    there; the quorum may prefer them now.
- **Q10 (contract classification is syntactic).**
  - `ReadOnlyFn` uses the transitive purity of `coverage.py`.
  - `WritesWithin` uses `fresh_only`: every store and written argument has a fresh-block,
    global-buffer or inner-parameter root and no loaded component.
  - The `REGION` lengths are hand-read from the AST: `encode_account` 110 bytes,
    `extract_deposit_data` 192, `rlp_encode_bytes` `n + 9`, `rlp_encode_word` 33. A
    too-small length makes a `ww_*` leaf false, so the leaf provers will notice; the quorum should
    spot-check them.
  - `KeepsOn WorldOK` callees that write through table values or message pointers are true only
    if those writes never reach an owned object. The world write-root scan (§0.1) found none outside
    the typed slots and the `bo` objects.
