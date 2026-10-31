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
