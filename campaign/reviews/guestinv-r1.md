# GuestInv spec, quorum round 1 (commit 45ca9218f): REQUEST_CHANGES

Reviewers: Astra 6 (mission 71e1d25b), Gemini 4 Carbon (f5a50b89), Fable 5.1 (ba223c5d, pending; appended below when it lands).
Coordinator: mission 9409f9a9. Line numbers are for `campaign/specs-proposed/GuestInv.lean` (Spec) and `Guest/SoftwareAst.lean` (AST) unless stated.

## Passed (both reviewers)

- Bridge: `coveredSourceTicksConsumedBounded_of_terminatingMainOn*` resolve to `UniformSourceClock.CoveredSourceTicksConsumedBounded` (UniformSourceClock.lean:201) and discharge `GuestInv`, `CoveredFfi`, and initial memory at the post-declarations entry with no leftover hypotheses. `K_pan_budget` is correct (`23077 + 32·K_pan`). The existing `ConcreteStage1To5Transfer` convenience lemma assumes `K_pan ≤ 10^30`, so use the new direct arithmetic.
- `GuestInv` entry and preservation hold on the guest code. Gemini scanned all globals, call-result writes, the journal guards, and the heap/scratch/frame mark LIFO discipline.
- No `sorry` or axiom in definitions, and the guards are satisfiable.

## Blocking issues

1. **`PreservesOn.call_guestInv` is false for global destinations** (Spec:496–500; Astra). Counterexample: call `heap_mark` with destination global `journal_n`; this writes `sourceBase` and breaks `journal_n ≤ journal_cap`. Fix: restrict to local/none destinations, or add a post-assignment hypothesis and audit the actual global destinations (Gemini: all such writes come from `alloc`/`htab_new`).

2. **Several W-based constants are false: arbitrary memory and parameters defeat the "fresh address per iteration" argument** (Design §1 is wrong as a general claim).
   - `sort_elems_on` (Spec:1011): `esz = 0`, `n = 2^50..2^62`. `alloc(0)` succeeds and all pointers coincide, so the run takes ≥ n iterations > `K_sort_elems ≈ 1.6e13` and terminates normally.
   - `htr_payload_on` and `htr_new_payload_request_on`: `ntx = 2^59` makes `alloc(ntx*32+32)` wrap to `alloc(32)`. Then about W/32 iterations each call `htr_pbytes` on a 250 MB slice, giving about 2.9e16 ticks > 4.1e15.
   - `_mpt_insert_node_on` (4W+8192) and `trie_walk_on` (4W+4096): a self-looping extension node with `sl = 1` gives 6·W and 5.25·W ticks, then returns normally.
   - `tx_scalar_word_on` and `hdr_word_field_on` (2W+128): `rlp_item` runs `rlp_list_count` before the error. A list of W−10 bytes of `0xc0` costs 9 ticks per byte, about 9W.
   - `_decode_witness_node_body_on` (16W+65536): `db` is an arbitrary pointer, so a header with `klen ≈ W/2` makes every lookup a W/2 `memeq`. 16,000 lookups is about 7.7e12.
   - Fix direction (Gemini, endorsed by the coordinator): use loop-counter bounds that hold for arbitrary memory. A signed counter loop runs at most 2^63 iterations, and a pointer walk that touches a fresh address per iteration at most W. Each constant must equal (iterations bound) × (body cost including callees) and be justified per loop. The budget has about 10^230 slack, so 2^63-factor constants are fine if nesting depth stays bounded: track the nesting product and keep `K_pan ≤ 10^290`.

3. **`finish_child_on` is still false** (Spec:1028–1030; Astra). The success path goes through `incorporate_child_on_success` → `htab_union_into` with a source `count = 2^62`. The parent table aliases the source header, so the first insertion zeroes `src.count`. The cached `cap = 2^62` then loops on `htab_item` returning absent without touching memory: 2^62 iterations, normal return, against `K_finish_child ≈ 1.6e18`. Similarly, `htab_union_into` is only guarded by `HtabLocalWF "src"`, but `merge_tx_into_block` calls it from `process_transaction`, whose guard `BlockGasCapped` says nothing about tables. Gemini gives an aliasing construction via `bal_idx_accts` and `record_pre_state_read` that overwrites `src.count`. Fix: give `htab_union_into` a `GuestInv`-only bound `2^63·(K_htab_set + 64) + 64`, valid because `i < cap` is a signed local counter. Thread that bound through `finish_child`, `merge_tx_into_block` and every other caller, and account for the union/truncate/log costs transitively.

4. **`HtabWF` is wrong and not preserved** (Spec:843–868; both).
   - It requires leaf `+8` (an arbitrary stored value) to be ≤ `ncap`. `htab_set` on an existing key writes the value there, which breaks it.
   - It does not constrain parent (`+0`), `order[0..cnt)`, leaf `+16` order position, root `t+56`, next `t+64`, or freelist `t+72`.
   - `htab_truncate_on_wf` is false: a wild parent pointer lets `htab_del` overwrite `t+24` (count), so the run is non-stationary and terminates past the bound.
   - `maxKeyLen = 52` is wrong. `bal_init` calls `htab_new` with 28 and 60 (AST:13873–13875), so use 60 and stride ≤ 64.
   - Fix: either a real inductive crit-bit invariant (internal vs leaf nodes, parent, order, freelist, allocation) with preservation lemmas, or (preferred where possible) counter-based bounds that need no table invariant. For example, `htab_truncate` decrements count only on a successful delete; if count is unchanged the state is stationary and the run times out, so bound it by noRepeat on (count, …) or by a counter.

5. **`EvmFramesWF` does not protect the gas measure or the release marks** (Spec:873–896, 1140–1142; both).
   - `spilled` (`e+192`) and the msg reservoir (`msg+48`) are unconstrained. `refill_frame_state_gas` mints 2^62 gas, and `incorporate_child_on_error` adds it into the parent, giving about 2^58 loop iterations.
   - Stack, frame and continuation aliasing is allowed: `ev+8 = ev` lets `stack_push` overwrite gas. Stack height and capacity (`e+16 ≤ e+232 ≤ 1024`) are unconstrained.
   - The release marks `cur_cont+48/+56` are unchecked, so `scratch_release(0)` breaks `ArenaOK`.
   - Fix: bound `gas + sgas + spilled`, relate `sgas + spilled` to `msg+48`, require disjointness of all active frames, stacks, continuations and scratch tables, mark validity, and table well-formedness for `e+136/168/176` (or counter bounds per item 4).

6. **The decomposition is not closed** (Astra).
   - The `decCall` and handler composition and sequencing need preservation proofs that the leaf bounds don't provide.
   - `finish_child` → `rollback_child_access` → `htab_truncate` and `incorporate_child_on_success` → `htab_union_into` lack their guards.
   - There is no checked coverage map from the 813 functions and 252 loops to the interface.
   - The final theorem rests directly on the `main_on_entry` sorry.
   - The real top obligation is `TerminatingFunBoundedOn MainEntry "main" (R.K_main_body R.G)`. That is fine for the covered target, but say so.
   - Also, `K_run_attempt` budgets 4 `process_message` calls but `execute_block` makes 6. The total still dominates, but fix the formula.

## Non-blocking

- Fully qualify `CoveredSourceTicksConsumedBounded` and add an explicit adapter to the concrete-transfer predicate (the names collide across files).
- Freeze guards, preservation contracts and budgets together.
- Add small regression counterexamples (zero stride, allocator/table aliasing, global return destinations, stack/frame aliasing) as `example`s that pin the corrected statements.
- Gemini thinks `u256_addmod_on`, `u256_mulmod_on`, `p256_fp_mul_on` and `p256_fp_sqr_on` are true (m ≤ 16, n ≤ 8), but `funBounded_divmnu` can't be reused as is.
- `topAddr` is harmless; drop it or keep it.
