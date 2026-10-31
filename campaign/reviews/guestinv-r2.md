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

## Astra 6 (mission 0bb32836): REQUEST_CHANGES

**Checked and fine:**
- The global-destination counterexample is fixed.
- The revised constants dominate the round-1 numerical counterexamples.
- Regeneration is byte-for-byte: 813 functions, 774 reachable, 249 loops, no recursion.
- There are 790 `sorry`s, all in theorems.
- The bridge is proved.
- The budget inequality was checked independently (`K_pan` has 755 bits).

The counterexamples below come from executable AST probes. Lean was not run.

**Blocking:**

1. **`FrameOutside` forbids every memory change** (Spec:989). It quantifies over `a : Nat`, tests the intervals before truncating, then reads memory at `BitVec.ofNat 64 a`. For any changed address x, `a = x + k·2^64` lies outside every interval, so x must stay unchanged. Concrete case: updating a singleton table value 7 → 9 changes `0xa1100098`. Fix: quantify over `BitVec 64` and test intervals with `toNat`, or restrict to canonical word addresses.

2. **The constructor exit contract intersects where it should take a union** (Spec:5077). `HtabNewExit` requires memory to be unchanged outside the fresh heap AND outside the fresh scratch. `htab_new(20, 2)` writes the header 0 → 20 in the heap without moving scratch, so the scratch clause forbids that write. `htab_new_scratch` fails the same way. Fix: one frame over the union.

3. **Constructor guards omit the parameter limits** (Spec:5080). Counterexamples:
   - `htab_new(0, 2)` violates `1 ≤ key_len`;
   - `htab_new(61, 2)` violates `key_len ≤ 60`;
   - `htab_new(20, 2^64−1)` wraps `ncap+1` in the allocation products.

   Fix: add explicit parameter contracts, including a bounded `cap`, and establish them at callers. This extends Fable's item 1.

4. **`HtabWF` admits disconnected cycles, so `htab_del_spec` is false** (Spec:953, Spec:5062). Counterexample:
   - parameters: `key_len=1`, `stride=8`, `count=2`, `ncap=3`, `next=4`, `root=1`;
   - lists: `L=[1,2]`, `I=[3]`, `Fr=[]`, `order=[1,2]`;
   - nodes as (parent, +8, +16, crit): `1=(0,7,0,8)`, `2=(3,9,1,8)`, `3=(3,2,3,0)`.

   Deleting leaf 1 returns 1 and sets `count=1`, `root=0`, which breaks `HtabWF`. Fix: require rooted connectivity and acyclicity, plus the search invariants that delete and truncate rely on.

5. **`EvmInv` misses log backing arrays** (Spec:1155, Spec:1172; `op_dispatch_spec` at Spec:5132). Two concrete failures:
   - **Gas overwrite:** take a logs header `(data=ev+64, len=0, cap=1)`. That array is not in `frameObjects`, so the guard holds. `LOG0` then writes the new log pointer into `ev+64`, raising gas from 1000 to 2702180640, so `evmPot` increases.
   - **Normal growth:** with `len=cap=4`, `lst_push` reallocates the array on the HEAP, which violates the scratch-only clause at Spec:1172.

   Fix: include backing arrays in ownership and disjointness, and allow the allocator transitions the code actually performs.

6. **Assembly is not closed** (Spec:415, 517, 5166, 5315):
   - `callHandle_guestInv` and `while_rank` are still admitted (sorry);
   - `run_frames_step_of_specs` is admitted glue;
   - **`gb_main` itself is `by sorry`**, and the final theorem applies the bridge directly to `gb_main` rather than composing the lower leaves;
   - `htab_del_spec`/`HtabExit` has no count-decrease conclusion.

   Round-1 item 6 is still open. Every combinator and glue lemma, and the composition from leaves up to `main`, must be proved, so that only true leaf statements remain `sorry`.

**Non-blocking:**
- coverage.py:359 counts each carried local as one 64-bit word; `modinv_bin` carries four 256-bit structures, so its `RO(4)` argument is invalid. A real measure is needed.
- Spec:986 is the tautology `HtabWF s t → HtabWF s t`.
- The examples at Spec:5333 onward only compare constants. Add semantic regression tests.
