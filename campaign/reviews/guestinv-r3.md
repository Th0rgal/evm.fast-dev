# GuestInv spec, quorum round 3 (commit 1c54006ca)

Coordinator: mission 9409f9a9. Line numbers refer to `campaign/specs-proposed/GuestInv.lean` (Spec), `Guest/SoftwareAst.lean` (AST) and `campaign/notes/guestinv/DESIGN.md` (DESIGN). Reviews are appended as they arrive.

## Fable 5.1 (mission 0647161d): REQUEST_CHANGES

**Checked and fine:**
- The generated parts regenerate byte for byte.
- There are 788 theorem sorries (14 contracts, 727 `fb_*`, 47 `gb_*`), and no definition or combinator contains one.
- Round-2 items:
  - Item 1: `HtabNewReady` guards `key_len` and `cap`.
  - Item 2: `FrameRoom` holds. All six frame-opening opcodes pop 3–7 words, and `frame_start` catches `EvmErr` locally.
  - Item 3: `while_rank_stationary` with `SameHead`/`WhileTimesOut` covers `htab_truncate`, `sort_elems` at width 0, the `_mpt_insert_node` self-loop, both `fq12_inv` loops and the halving loops at u = 0. `tailCall_on`, `dec_onLocals`, `decCall_on` and `ite_cond_on` are stated generally.
- Astra's items 1, 2, 4 and 5 are fixed.
- Q8: no heap-releasing function reachable from `op_dispatch` reaches `lst_push` or `log_append`.

Fable could not run Lean, so the coordinator must confirm elaboration and `#print axioms`.

**Blocking:**

1. **`while_rank` and `while_rank_stationary` cannot assemble `gb_run_frames`** (Spec:835, Spec:862, DESIGN:1373). Both require `hbody` on every `P` state. The final iteration restores `ev`/`cur_cont` and sets `go := 0`, so `P` must admit exit states that are not `EvmInv`, and from those the body's guarded callees have no leaf. Fix: a corollary with the same proof, `hbody : TerminatingProgBoundedOn (fun s => P s ∧ LoopActive cond s) body B`.

2. **No handler-call rule for guarded callees** (Spec:484). `callHandle_guestInv` needs a `GuestInv` leaf for the callee. `run_frames` (AST:18663) calls `op_dispatch` and `finish_child` under `EvmErr` handlers, and both have only guarded leaves. Fix: add a `callHandle_on` taking `CallEntryOn P Pc` for the callee; the handler under `GuestInv` is enough.

3. **`op_dispatch_spec` is false** (Spec:5736). `FrameWF` (Spec:1735, Spec:1738) admits capacity 0:
   - **Stack:** with `e+232 = 0` and `e+16 = 0`, `PUSH0` makes `stack_push` (AST:15065) call `scratch_alloc(0)`. The result is height 1 with capacity 0.
   - **Logs:** with header `(data, len 0, cap 0)`, `LOG0` reaches `lst_push` (AST:13840), which does `alloc(0)` and sets `len := 1`, so `len ≤ cap` fails.

   Fix: require `1 ≤ cap` for both. Real values are `32·2^k ≤ 1024` and `4·2^k`; `frame_new` and the two growth paths keep it.

4. **`finish_child_spec` is false** (Spec:5762). `EvmInv` constrains neither the continuation fields `+72`/`+80` nor the retdata buffer `e+144`/`e+216`, and `finish_child` writes through both:
   - **AST:18652:** `memcpy(parent_mem + rec+72, ev+144, min(rec+80, child+128))`. With `rec+72 = (e_parent + 232) − parent_mem` it overwrites the parent's stack capacity.
   - **AST:18624/18643 via `set_retdata`:** `memcpy(e+144, child+120, 8)` where `e+144` is a typed table header overwrites `key_len`.

   Fix:
   - add `rec+72 + rec+80 ≤ parent memory capacity (e+40)` for every suspended frame, established by `extend_memory_cost2`/`extend_memory` before `start_child`;
   - add the retdata block `(e+144, e+216+8)`, or `cap = 0 ∧ ptr = evm_empty`, to `frameObjects` on the heap.

**Ruling on `gb_main` as a leaf: acceptable in principle**, because the bridge is proved and nothing between the leaves and the target is admitted. But the `gb_*` leaves are not simple compositions:
- `gb_main` must establish `WorldOK` after `mem_init` and keep it across 13 `*_init` functions, `decode_host_input` and `htr_new_payload_request`;
- `gb_process_transaction` and its siblings must keep `WorldOK` across 239 BETWEEN functions that have no contracts.

**Recommendation, adopted by the coordinator for revision 4:** add `PreservesOn WorldOK WorldOK` (or a suitable frame) contract leaves for the BETWEEN functions called from guarded bodies, so that the `gb_*` leaves become genuine compositions.

**Non-blocking:**
- `nodedb_build` (AST:9948) passes a computed power-of-two `cap`, so 31 of the 32 `htab_new` sites pass literals, not 32 (DESIGN:36, 124). Guard `cap` by a bound, e.g. `cap ≤ 2^32`.
- `MainEntry` has no `LocalsFree`/`LocalsOnly` instance.
- Q1 (opcodes write only owned memory): do a field-by-field audit of `frame_new`'s record (AST:15370) and of the continuation (AST:18450).

## Astra 6 (mission ef93d111): REQUEST_CHANGES

All five round-2 counterexamples are confirmed fixed. Q8 (the log-regrowth / heap-release pattern) was not found: across the 534-function dispatch cone, no function that calls `heap_release` reaches `log_append`. There are 788 admissions; the combinators and the glue have proof bodies. Lean was not run, so elaboration and the axiom claim remain unconfirmed by Astra. Counterexamples come from an executable AST interpreter.

**Blocking:**

1. **Zero-capacity logs break `op_dispatch_spec`** (Spec:1738, 5736). With `len = cap = 0`, `LOG0` returns normally with `len = 1`, `cap = 0`. This is the same issue as Fable's item 3; the stack needs the same audit.

2. **Unowned return-data buffers break `finish_child_spec`** (Spec:1716, 1729, 5762; AST:18572, 19064). Take `parent+144 = parent+64` and `parent+216 = 8`, with child output the word 10000. `set_retdata` copies over the parent's gas, so `evmR` goes from 100 to 10000. Fix: ownership, capacity and disjointness for the reusable return-data storage, preserved across reuse, allocation and release, plus constraints on the continuation output-copy ranges. This is the same issue as Fable's item 4.

3. **Release marks don't protect surviving tables** (Spec:1627, 1756, 5762; AST:18657–18660). Witness:
   - both frames reference a table from `htab_new_scratch(20,4)`, with header `0xb0bdffa8`;
   - the child's release mark is `0xb0be8000`.

   On the child-error path, `finish_child` sets `scratch_ptr = 0xb0be8000`, so the parent's table is no longer `Allocated` and `EvmInv` fails. Fix: release-lifetime conditions for every surviving table and fixed object, including globally rooted ones.

**Assembly ruling: NOT acceptable as claimed** (Spec:7010, 7022–7023). The final theorem applies the bridge directly to `gb_main`, which is itself `sorry`, so the other 787 obligations are not connected to the target. To freeze, either:
- prove `gb_main` (and the assembly down to an explicit leaf boundary) by concrete-body composition from lower obligations, including guard establishment and transport at guarded calls, loop invariants, and rank/stationary obligations; or
- prove an equivalent conditional assembly theorem: (all primitive obligations) → target.

## Coordinator decision on the assembly question

Fable judged `gb_main` as a leaf acceptable in principle, with `PreservesOn` contracts for the BETWEEN functions. Astra did not. The stricter requirement is adopted for revision 4, because otherwise proving the leaves proves nothing about `main`. There must be a proved assembly theorem
`(∀ primitive obligation) → CoveredSourceTicksConsumedBounded K_pan`,
or equivalently every `gb_*` must be proved by composition. The primitive obligations are the `fb_*` leaves, the contract leaves, and the new `PreservesOn` contracts for BETWEEN functions. Each primitive must be a small statement about a single function body.
