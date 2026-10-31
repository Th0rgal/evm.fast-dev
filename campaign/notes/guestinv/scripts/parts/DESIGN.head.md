# GuestInv revision 3: a guarded route to `CoveredSourceTicksConsumedBounded`

Track `guestinv-opus55`, mission 9409f9a9 (Wave 8), branch `wave8/guestinv-opus55`. Revision 2
answered the round-1 quorum (`campaign/reviews/guestinv-r1.md`, Astra 6 and Gemini 4 Carbon);
revision 3 answers the round-2 quorum (`campaign/reviews/guestinv-r2.md`), §0.1 and §0.2. All statements are in `campaign/specs-proposed/GuestInv.lean`. The generated parts of
that file, the per-loop table (§4) and the coverage table (§5) come from
`campaign/notes/guestinv/scripts/coverage.py` run on `Guest/SoftwareAst.lean` (§9). No frozen file
is touched.

## 0. Summary

| Deliverable | Where | Status |
|---|---|---|
| `GuestInv` = code ∧ memaddrs ∧ shMemaddrs ∧ baseAddr | §2 of the Lean file | definition; `guestInv_evaluate`: **every** evaluation preserves it (**proved**) |
| guarded `call`/`decCall`/`seq`/`ite`/`dec` rules, no preservation side conditions | §3 | **proved** |
| tail call, handler call, stationary `while`, `while_rank`, `dec` for local-reading guards, guarded `decCall`, condition-aware `ite` | §3 | **proved** (revision 3; no combinator has a `sorry`) |
| bridge `TerminatingFunBoundedOn MainEntry "main" K → CoveredSourceTicksConsumedBounded (K+1)` | §4 | **proved** (unchanged proof, `MainEntry` gains the proved `GlobalsZero`) |
| one bound `K.«f»` per function on `main`'s call graph (774 functions, 249 loops) | §6 (generated) | definitions; formula = Σ calls `K(g)+1` + Σ loops `(N+1)(body+1)` |
| unguarded leaves `fb_f : TerminatingFunBoundedOn GuestInv f K.«f»` | §6 (generated) | `sorry` (727 statements) |
| memory contracts: `HtabWF`, `ArenaOK`, `WorldOK`, `NodeHeap`, `EvmInv`, `evmPot` | §5 | definitions |
| contract leaves (tables, MPT, frames, `mem_init`, frame glue) | §7 | `sorry` (15 statements); `run_frames_step` **proved** from them |
| `LocalsOnly` instances for every guard | §7 | **proved** |
| guarded leaves `gb_f : TerminatingFunBoundedOn Guard_f f K.«f»` | §7 (generated) | `sorry` (47 statements) |
| `K_pan = K.«main» + 1`, `32·K_pan + 23077 ≤ (10^299 − 1)/10^4` | §8 | **proved** (`decide`) |
| end-to-end `CoveredSourceTicksConsumedBounded K_pan` | §8 | proved term; depends only on the leaf `gb_main` |

## 0.1 Round-2 items and how each is addressed

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

## 0.2 Changes since 7e73988d (revision 2)

Mechanical statement diff of the two Lean files (`theorem`/`def`/`example` signatures, comments
dropped):

**Changed leaf statements (2):**
- `htab_new_spec`: guard `ArenaReady` → `HtabNewReady` (adds `key_len ∈ htabKeyLens`; strictly
  weaker obligation for the prover).
- `htab_new_scratch_spec`: same.

**Changed definition (1), which changes the meaning of leaves that mention it:**
- `EvmInv`: new conjunct `∀ ec ∈ ch.tail, FrameRoom s ec`. Leaves affected are those whose
  statement mentions `EvmInv`, directly or through `FinishReady`:
  - `op_dispatch_spec`, which must establish it at `op_call`/`op_create`;
  - `frame_exception_spec`, `frame_epilogue_spec` and `finish_child_spec`, which must preserve it
    (they touch no suspended frame);
  - `run_frames_step_of_specs` (glue);
  - `gb_run_frames` and `gb_finish_child`, whose guards are now stronger, so they are easier;
  - `gb_process_message`, which establishes `EvmInv` at a one-frame chain whose `tail` is empty,
    so `FrameRoom` is vacuous there.

**New leaf (1):** `htab_del_progress_spec`.

**Unchanged:**
- all 727 `fb_*` and 47 `gb_*` statements (textually);
- every `K.«f»`, `K_pan`;
- `htab_set/del/truncate/union_into_spec`, `mpt_*_spec`, `mem_init_world`;
- all bridge theorems;
- `while_rank` and `callHandle_guestInv` (statements kept, now proved).

Docstrings of 7 `fb_*` leaves changed (loop-class label only, e.g. `RO(4)` → `MONO`): `rlp_list_count`, `modinv_bin`, `bls_fp_inv_raw`, `fq12_mul`, `fq12_sqr`, `p256_fp_mul`, `p256_fp_sqr`.

**New proved theorems:**
- combinators: `tailCall_on`, `tailCall_guestInv`, `while_rank_stationary` (+ `_aux`),
  `dec_onLocals`, `decCall_on`, `ite_cond_on`;
- helpers: `evaluate_clock_irrelevant`, `evaluate_ne_of_clock_lt`, `while_unfold_continue`;
- `LocalsOnly.{of_localsFree,decClock,setVar}`;
- the `LocalsOnly`/`LocalsFree` instances and their congruence lemmas (`freeChain_with_locals`,
  `htabWF_with_locals`, `tablesTyped_with_locals`, `worldTyped_with_locals`,
  `arenaReady_with_locals`, `evmChainFrom_with_locals`, `evmChain_with_locals`, `locN_congr`).

**New definitions:** `FrameRoom`, `HtabNewReady`, `HtabDelProgress`, `SameHead`, `WhileTimesOut`,
`Stationary`, `LocalsOnly`, `CondTrue`, `CondFalse`, `DecCallResumeOn`.

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
| `HtabNewReady` | `ArenaReady` ∧ `key_len ∈ htabKeyLens` | `htab_new_spec`, `htab_new_scratch_spec` |
| `RollbackReady` | the child's tables `+168/+176` are `HtabWF` and allocated | `rollback_child_access` |
| `FinishReady` | `EvmInv` ∧ `EvmDone` ∧ kind ≠ 0 | `finish_child` |
| `EvmInv` | §5 of the Lean file (item 5; revision 3 adds `FrameRoom` for suspended frames) | `run_frames` |
| `ArenaReady` | `GuestInv` ∧ `ArenaOK` (heap ⊆ `[sourceBase, 0xb0000000]`, frame memory below scratch inside `[0xb0000000, 0xb0bee000]`) | `_decode_witness_node_body` |
| `MptReady` / `MptObjReady` | `ArenaReady` ∧ the `node` parameter (resp. trie object `m`) is rooted in a typed `NodeHeap` | `_mpt_insert_node`, `_mpt_delete_node(_body)`, `mpt_set` |
| `WorldOK` | `ArenaReady` ∧ ∃ S, `WorldTyped s S` (tables, journal, fixed records, tries) | the other 37 guarded functions |
| `MainEntry` | §2 | `main` |

Every guard is `LocalsOnly` (proved instances, §7 of the Lean file), so `dec_onLocals`,
`LocalsOnly.decClock` and `LocalsOnly.setVar` apply inside every guarded body.

`WorldOK` holds right after `mem_init`: every root is 0, so `S = []` works (`mem_init_world`).
`EvmInv → WorldOK`. Inside `run_frames` every frame-level callee (`op_dispatch`, `op_sload`,
`op_sstore`, …) is called from an `EvmInv` state.

### What each guarded leaf must establish at its guarded call sites

The guarded leaves are "big" leaves. Besides composing callee bounds, each proves that its guarded
callees' guards hold at their call sites, using the contract leaves:

- `gb_run_frames` uses `while_rank` with `P = GuestInv ∧ (EvmInv ∨ go = 0)`,
  `μ = if go = 0 then 0 else evmPot + 1`, `N = evmPotMax + 1`, and `run_frames_step`, which is proved
  from `op_dispatch_spec`, `frame_exception_spec`, `frame_epilogue_spec`, `finish_child_spec` and the
  glue `run_frames_step_of_specs`. The body's time bound comes from the callees' leaves; `finish_child`
  is called under `FinishReady`, which `EvmInv ∧ EvmDone ∧ kind ≠ 0` gives directly.
- `gb_finish_child` → `rollback_child_access`: `RollbackReady` from `EvmInv` (the child's tables are
  in `S`).
- `gb_rollback_child_access` → `htab_truncate`: `HtabArgWF` directly.
- `gb_htab_truncate`: `while_rank_stationary` with `P = HtabArgWF`, `μ = count (t+24) < 2^64`. Each
  iteration calls `htab_del` on the key of the last leaf. It either deletes a leaf (count drops by
  one: `htab_del_progress_spec`; `HtabArgWF` kept: `htab_del_spec` and `localsOnly_htabArgWF`) or
  returns 0 having written nothing. In the latter case the caller's `dec`s restore `pos`/`leaf`, so
  the loop head is `SameHead`. (Round 2: "every iteration is a successful `htab_del`" was wrong,
  because `HtabWF` does not constrain key bytes.)
- `gb_process_message`: establishes `EvmInv` at the `run_frames` call from `WorldOK`, using the fresh
  `frame_open` record and continuation, the marks just taken, tables in `S`, and the `htab_new_scratch`
  contract for `e+136`.
- `gb_process_transaction` / `gb_execute_block` / `gb_run_attempt` / … establish `WorldOK` at every
  guarded call site. They use the contract leaves for table and trie mutations, and the frame
  `FrameOutside` facts for everything else. The functions called in between are the `BETWEEN` list of
  §5.

### Contract leaves (all `sorry`)

`htab_set_spec`, `htab_del_spec`, `htab_del_progress_spec`, `htab_truncate_spec`,
`htab_union_into_spec`, `htab_new_spec`, `htab_new_scratch_spec`, `mpt_insert_node_spec`, `mpt_delete_node_body_spec`, `mem_init_world`,
`op_dispatch_spec`, `frame_exception_spec`, `frame_epilogue_spec`, `finish_child_spec`,
`run_frames_step_of_specs` (glue).

## 7. Every `sorry`

- Combinators: none (all proved in revision 3).
- Contract leaves (15): listed in §6.
- Guarded bound leaves (47): `gb_*`, listed in §5 (column "leaf").
- Unguarded bound leaves (727): `fb_*`, listed in §5.

No definition contains `sorry`. Proved terms that depend on a `sorry` are `run_frames_step` (on the
four frame contracts and the glue) and `coveredSourceTicksConsumedBounded_K_pan` (on `gb_main`).

## 8. Open questions and known risks (for the quorum)

- **Q1 (`EvmInv` completeness).** `op_dispatch_spec` is true only if every write an opcode performs
  lands in its frame's blocks, a typed table (through the table contracts), a fixed global buffer or
  fresh memory. The 44 global buffers (`keccak_st`, `u256_ws`, …; `globalBuffers`, generated from
  the literal-size `alloc` calls that assign a global) are in `fixedObjects`: allocated, pairwise
  disjoint, and disjoint from every table, node and frame block. The remaining risk is a buffer
  allocated with a non-literal size and written during EVM execution. The script lists only
  literal-size allocations, so the quorum should check `out/tiers.txt` against the `*_init`
  functions.
- **Q2 (`finish_child` on `EvmErr`).** `finish_child_spec` assumes that an `EvmErr` escaping
  `finish_child` is raised after the pop (by `stack_push` in the parent). `create_finish` has its own
  handler, so this looks right.
- **Q3 (`TriesTyped`).** Storage tries are typed through the `ws+32` cache only. If
  `compute_state_root` mutates tries reached through account records, those roots must be added.
- **Q4 (MPT descent).** `_mpt_insert_node`'s measure relies on writes during empty-extension runs
  being idempotent; this holds for typed nodes (`NodeHeap`), which is why it is guarded.
- **Q6 (arithmetic facts behind two `MONO` measures; round-2 non-blocking).** The provers of
  `fb_taylor_exponential` and `fb_fq12_inv` must establish:
  - (a) `u256_divmod` returns quotient 0 on a zero divisor (`Guest/SoftwareAst.lean:1754`;
    Fable confirmed it), so `taylor_exponential` exits when `i` wraps to 0;
  - (b) `fq_poly_submul` with `cf = fq_mul(top, fq_inv(lead))` makes `r0[d0]` the literal word 0
    when `lead` is invertible mod p, even on non-canonical inputs (not traced). If (b) fails for
    some non-canonical input, the iteration is not stationary either, and `N = 14` would need a
    no-repeat argument instead.
- **Q7 (divergence obligations).** The `WhileTimesOut` alternative of the `modinv_bin` /
  `bls_fp_inv_raw` halving loops at `u = 0` needs: `mod_half`, `mod_sub`, `bls_fp_half_can`,
  `bls_fp_sub` and the `u256_*`/`bls_fp_*_raw` helpers they call always return normally. They are
  straight-line word arithmetic with no load, store or raise (checked on the AST).
- **Q5 (cost of the generated interface).** 727 unguarded leaves are mostly loop-free (their proof is
  pure call composition). A single tactic that walks the body with the combinators should discharge
  all loop-free ones; the loop leaves need their measure.
