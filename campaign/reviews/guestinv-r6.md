# GuestInv spec quorum, round 6 (revision 8, 16aa6f4b0)

Coordinator Lean check (16aa6f4b0, Lean 4.33.1): 0 errors; 931 sorry warnings, all in leaf bodies. `assembly` and `assembly_main` use [propext, Classical.choice, Quot.sound]; `K_pan_budget` uses [propext]. The 727 `fb_*` statements, the `K` namespace and the `GuestInv` definition are byte-identical to rev7 (f13145329).

Quorum after the 15:30Z credit rule: no new Claude missions. Round 6 Fable (cb23d111) was interrupted by infra and cannot be resumed. The quorum from round 7 on is Astra 6 + Gemini 4 Carbon + GPT-6.1 Sol.

## Astra 6: REQUEST_CHANGES

All round-5 items (Astra 1–8, Fable 1–3, Gemini 1–2) are excluded at their concrete witnesses. No ordinary resuming path violates RolesOK distinctness: htab_copy allocates distinct blocks, block storage merging creates separate inner tables, and parent/child access-table sharing is allowed by sharedRoles. There are four single-function boundary gaps, all missing contracts at ordinary call sites:

1. **HtabExit does not preserve key lengths pinned by RolesOK** (Spec:1698, 1900, 10284, 10920; AST:13258, 33343). Interface witness: an empty ts+24 table with klen 52 and stride 56 changes klen to 51 and returns normally. HtabExit still holds and RolesOK fails, so get_storage cannot re-establish WorldOK. Likewise an aa table can go from klen 20 to 19 across htab_set, and then process_transaction cannot establish MsgReady. Fix: add explicit key-length (header) preservation. DESIGN:2499 W2 does not follow without it.
2. **The decoder push contract does not type the pointers that are later written through** (Spec:7073, 9422, 9447; AST:10260–10266). Witness: a pushed extension frame at T has tag 1, T+48 = T and T+56 = 1, which satisfies PushesFrame. ww_node_new_ext allows an identity transition that returns ex = T−8. The caller stores T into T+0 and 1 into T+8, and the pop builds a self-linked stack. Fix: ownership/separation for returned nodes, and for the frame's branch-node pointer and other results used by inline stores.
3. **Deletion unwind contracts can release the live scratch stack** (Spec:6688, 9554; AST:10840–10848). Witness: with two live scratch frames, `_delete_ext_finish` raises scratch_ptr above both. NodeFnExit allows this, since it constrains heap growth but not scratch-pointer growth. Fix: callers' allocated scratch is preserved, e.g. scratch monotonicity for these NodeFn callees.
4. **HtabNewExit does not preserve allocator frontiers** (Spec:6119, 9838, 10679; AST:32349, 32899). Witness: return a fresh table in newly allocated scratch while resetting heap_ptr to sourceBase. Fix: state allocator preservation explicitly (heap_ptr is monotone, and scratch only shrinks into fresh space).

BOUNDARY: NOT MET (gbody_get_storage, gbody_process_transaction, gbody__decode_witness_node_body, gbody__mpt_delete_node_body, gbody_compute_state_root, gbody_process_unchecked_system_transaction). Repaired walks: execute_block, run_attempt, main and _mpt_insert_node.

## Gemini 4 Carbon

Interrupted by infra; relaunched against 16aa6f4b0. Its result will be appended here.
