# GuestInv spec, quorum round 2 (commit 7e73988d)

Coordinator: mission 9409f9a9. Line numbers refer to `campaign/specs-proposed/GuestInv.lean` (Spec) and `Guest/SoftwareAst.lean` (AST). Reviews are appended as they arrive.

## Fable 5.1 (mission 8ee7c754): REQUEST_CHANGES

**Checked and fine:**
- The generated parts regenerate byte for byte.
- The frozen `PanTerminatingBounded` matches its MANIFEST hash.
- No `sorry` or axiom appears in any definition.
- The round-1 items are otherwise addressed:
  - `GuestInv` is metadata only, and its preservation is proved;
  - the counters hold for arbitrary memory;
  - `htab_union_into` is a plain counter loop;
  - the `EvmInv` potential is satisfiable, and every opcode either charges gas or halts;
  - the coverage table lists all 774 reachable functions and 249 loops;
  - the bridge and `K_pan_budget` are stated correctly.

Fable could not run Lean, so the coordinator must confirm elaboration, the `decide` budget proof and `#print axioms` on the frozen candidate.

**Blocking:**

1. **`htab_new_spec` and `htab_new_scratch_spec` are false** (Spec:5080–5081). `key_len` is arbitrary at entry, and `htab_new` (AST:4867) never checks it:
   - `key_len = 0` gives header word 0 = 0, but `HtabWF` needs `1 ≤ klen`;
   - `key_len = 61` breaks `klen ≤ maxKeyLen`;
   - `key_len = 2^64 − 3` wraps the stride.

   Fix: guard on `locN s "key_len" ∈ htabKeyLens`. Every call site passes a literal, so the guard is easy to discharge.

2. **`finish_child_spec` is false** (Spec:5158). `FrameWF` (Spec:1162) admits a suspended parent whose stack height equals its capacity. `finish_child` (AST:18572) runs `stack_push` before `scratch_release(child_mark)`. A full parent therefore gets a new 64-slot stack allocated below the child's mark, and the release then leaves the parent's stack outside `[scratch_ptr, scratchEnd)`, so `FrameWF` and `EvmInv` fail. Real runs never reach this state, because CALL pops at least six words, but the leaf is stated over all guarded states.

   Fix: require `height + 1 ≤ capacity` for every non-current frame in `FrameWF`, and discharge it at `op_call` and `op_create`.

3. **The decomposition is not closed by the stated combinators.** All three fixes below are additive.
   - **Tail calls.** `Prog.call none` occurs at 88 sites in 75 functions, 67 of them on main's call graph (e.g. `rlp_list_header_len`, AST:4842). `call_on` (Spec:280) and `callHandle_guestInv` (Spec:415) cover only `.call (some _)`. Add a tail-call combinator.
   - **Stationary iterations.** `while_rank` (Spec:520) needs a strict decrease on every continuing iteration. Several bounds rely on "stationary means timeout": `htab_truncate`, both `fq12_inv` loops, `sort_elems` loop 1 at width 0, and the `_mpt_insert_node` self-loop. Add a `while` rule that allows stationary iterations: rank decreases or the full state repeats, building on `while_noRepeat`. Also:
     - the `htab_truncate` justification "every iteration is a successful `htab_del`" (coverage.py:127, DESIGN.md:831) is wrong as stated;
     - `htab_del_spec` (Spec:5062) does not promise the count decrement that `gb_htab_truncate` needs.
   - **`dec_on`.** It requires `LocalsFree P` (Spec:473), but `HtabArgWF`, `UnionArgWF`, `MptReady`, `MptObjReady` and `RollbackReady` all mention locals. Add a `dec` rule for guards that mention locals.

**Non-blocking:**
- Read-only loops with struct-shaped keys are mis-sized: `RO(k)` gives `2^(64k)`, but `modinv_bin`, `bls_fp_inv_raw`, `fq12_mul`, `fq12_sqr`, `p256_fp_mul` and `p256_fp_sqr` carry 4- or 6-word locals. The bounds are still true because the real measures are tiny. `fq12_mul` loop 1 is a plain counter if `classify` accepts `notLower`.
- The `rlp_list_count` justification is wrong (the body is not read-only; `_rlp_validate_items_body` writes scratch records), but the bound is true via the measure `len − off`.
- The `taylor_exponential` and `fq12_inv` measures rest on two arithmetic facts the provers must establish: `u256_divmod` returns zero on a zero divisor (AST:1754, confirmed), and field cancellation on non-canonical inputs (not traced).
