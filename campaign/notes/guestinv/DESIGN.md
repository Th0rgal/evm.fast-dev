# GuestInv: a guarded route to `CoveredSourceTicksConsumedBounded`

Track `guestinv-opus55`, mission 9409f9a9 (Wave 8). Branch `wave8/guestinv-opus55` off
`wave8/base2` (950ac7fda). This is a specification proposal. All proposed statements are in
`campaign/specs-proposed/GuestInv.lean`, which elaborates with `lake env lean` on Lean 4.33.1
with no errors. No frozen file is touched.

## 0. Summary

| Deliverable | Where | Status |
|---|---|---|
| `GuestInv : ∀ {F}, PanSemStateFiniteExact 64 F → Prop` | §2 | definition; locals/clock/memory independence lemmas **proved** |
| `TerminatingFunBoundedOn`, `PreservesOn`, `FunPreservesOn`, `CallEntryOn` | §3 | definitions |
| guarded `call` / `decCall` / `seq` / `ite` / `dec` rules | §3 | **proved** (ported from `PanTerminatingCallOn` and the repaired frozen combinators) |
| handler-call rule, call preservation | §3 | statements, `sorry` |
| `GuestInv` holds at the covered post-declarations entry | §4 `guestInv_postDecls` | **proved** (including all 67 globals = word 0) |
| `TerminatingFunBoundedOn GuestInv "main" K → CoveredSourceTicksConsumedBounded (K+1)` | §4 | **proved**, plus covered-input and `MainEntry` variants |
| restated leaf interface (FALSE and UNCLEAR leaves) | §6 | statements, `sorry` |
| explicit `K_pan` with `32·K_pan + 23077 ≤ (10^299-1)/10^4` | §6 `K_pan_budget` | **proved** by `decide` |

`#print axioms` for the proved bridge theorems, `guestInv_postDecls` and `callEntryOn_guestInv`
gives `[propext, Classical.choice, Quot.sound]`. For `K_pan_budget`, `K_pan_wordGas_budget` and
`astGlobalNames_eq` it gives `[propext]`.

Values (from `#eval`):

- `K_pan = 6327163022056460853946490190703860891670147713` (≈ 6.3·10^45).
- `K_pan_wordGas = 583577776136387101824429899526330462116047797193810768513` (≈ 5.8·10^56).

The budget is ≈ 10^295, so every constant can be off by a factor of 10^230 without breaking
the inequality. This matters because the leaf constants are proposals (§6).

## 1. Why a guard is needed, and why this one

The audit (`wave8/specfix-astra6`, `SPECFIX.md`) refutes `htab_keys`, `htab_set`,
`frame_epilogue` and `finish_child` as all-state statements. Every counterexample uses either
an odd pointer (`memeq(1,1,2^63)`) or a huge walk through arbitrary 64-bit memory. Two
semantic facts kill all of them once `memaddrs = ordinaryDomain`:

1. **Byte loads check the aligned word.** `memLoadByteAuxHOL` (Flapjack `LoopSem.lean:552`)
   reads `memory (byteAlign a)` and requires `domain (byteAlign a)`. Pointer `1` aligns to
   `0`, which is not in `ordinaryDomain = [0xa1000000, heapEnd)`, so `memeq(1,1,·)` returns
   `.error` on its first load.
2. **Memory walks are domain-bounded.** A loop that loads or stores a fresh address on each
   iteration leaves the contiguous domain within `domainBytes = heapEnd − sourceBase =
   31 104 957 928` steps, and the next access errors. Wrap-around needs more than 2^63 steps.
   This bounds `memcpy`/`memzero`/`memeq` and every array scan by `W = domainBytes`, for
   arbitrary memory content, and it never requires a 2^64 counter argument.

`TerminatingProgBoundedOn` already requires `code = originalRuntimeCode`. `GuestInv` adds
only the non-memory facts below, so it is cheap to thread:

- It ignores `locals`, `clock`, `memory` and `ffi`.
- Call entry, `setVar`, caller-locals restoration and every store preserve it. This is proved
  as `guestInv_callEntry`, `guestInv_setVar`, `guestInv_with_locals_clock` and
  `guestInv_with_memory`.
- Hence `CallEntryOn GuestInv GuestInv f args` holds for every call (`callEntryOn_guestInv`,
  proved).

## 2. Conjuncts: rationale, which leaves use them, and the preservation obligation

| Conjunct | Holds at entry because | Used by | Preserved because / obligation |
|---|---|---|---|
| `code = originalRuntimeCode` | `evaluateDecls_meta.code` | every leaf, to resolve callees. It duplicates the `TerminatingProgBoundedOn` hypothesis so that `GuestInv` is self-contained for `PreservesOn` | `evaluateHOLFiniteState_metadata` (code never changes) |
| `memaddrs = ordinaryDomain` | `evaluateDecls_meta.memaddrs` | **all walk bounds** (`W`). Excludes all four FALSE counterexamples (§3) | metadata lemma (never changes) |
| `shMemaddrs = sharedDomain` | `evaluateDecls_meta.shMemaddrs` | input/output scans (`input_blob`, `output_write`, RLP decoders over the input window). These are bounded by `inputSize = 2^30` (folded into `W`, since `2^30 < W`) | never changes |
| `baseAddr = sourceBase` | `evaluateDecls_meta.baseAddr` | `mem_init` sets `heap_ptr := baseAddr`. Without this, `heap_ptr ≤ 0xb0000000` would not survive `mem_init` | never changes |
| `topAddr = heapEnd` | `evaluateDecls_meta.topAddr` | **no leaf**: `Exp.topAddr` occurs 0 times in the AST. Kept only because the brief lists it as a minimum conjunct. It is free (never changes) and can be dropped | never changes |
| `GlobalsWellShaped` (all 67 globals hold a word) | `postDecls_globals` (proved: every global decl is `const 0`) | gives meaning to the global conjuncts below. It also lets leaves evaluate `journal_n`, `ev`, `cur_cont`, … as words | Pancake `assign` requires `isValidValueHOLFinite`, i.e. an existing binding of the same shape. Obligation: the same for call-result writes to globals (`some (global, x)`) |
| `heap_ptr ≤ 0xb0000000` | value 0 | `alloc` never wraps: a successful `alloc(n)` implies `n ≤ 0xb0000000 − heap_ptr`. This drives the `merkleize_progressive` argument in SPECFIX (`alloc(2^33)` traps) and the `htab_keys`/`htab_new` size products | `alloc` (checked, `HeapPotential.alloc_bounds_of_lt_heapEnd`), `mem_init` (needs `baseAddr`). **Obligation:** `heap_release(m)` is called only with `m ≤ 0xb0000000`. Callers obtain `m` from `heap_mark` and keep it in a local, so this is a per-caller local invariant (`CallEntryOn GuestInv (GuestInv ∧ m ≤ cMax)`) |
| `ArenaOK frame_mem_ptr scratch_ptr` (both 0, or `0xb0000000 ≤ fm ≤ sp ≤ 0xb0bee000`) | both 0 (first branch) | scratch explicit stacks (RLP validation, `trie_walk`): depth ≤ `(0xb0bee000 − 0xb0000000)/24 = 521216`. Frame records and EVM memory live in disjoint halves (used by `EvmFramesWF`). In the 0/0 branch `scratch_alloc` and `frame_mem_alloc` always trap, since `0 − 0 < n` | `mem_init` moves 0/0 to `(0xb0000000, 0xb0bee000)`. `scratch_alloc` keeps `q ≥ fm`; `frame_mem_alloc` keeps `q ≤ sp`. **Obligation:** `scratch_release(m)` / `frame_mem_release(m)` are called with marks taken earlier, in LIFO order (`frame_new`/`frame_epilogue`/`finish_child` discipline). See Q3 |
| `journal_n ≤ journal_cap ≤ 524288` | both 0 | `state_restore` loop ≤ `journal_cap ≤ 2^19` iterations, which gives `K_state_restore = J·(K_htab_set + K_htab_del + 256) + 8192` | `jset`/`jdel` trap when `journal_n ≥ journal_cap` before `+1`. `state_restore` decrements only while `snap < journal_n`. `state_init` sets `cap := 524288` (old `n ≤` old `cap ≤ 2^19`), then `n := 0`. Line 33478 sets `n := 0`. `htab_*` never write globals |

`GuestInvReady` (= `GuestInv` ∧ `heap_ptr ≥ sourceBase` ∧ `frame_mem_ptr ≥ 0xb0000000`) is
the post-`mem_init` form (`mem_init_ready`, `sorry`). `EvmFramesWF`, `MsgGasCapped` and
`BlockGasCapped` build on it.

Two further guards are used only at the top. They are not part of `GuestInv`:

- `CoveredFfi`: `F = Guest.HostMemory` and the FFI replays the oracle of an input with
  `declaredGasLimit ≤ 2·10^8`. It is preserved by every evaluation
  (`B2Oracle.evaluate_consistent`) and holds at entry (`coveredFfi_postDecls`, proved).
  `GuestInvCovered = GuestInv ∧ CoveredFfi`.
- `InitialMemory`: `memory = sourceMemory`, i.e. the startup header and zero elsewhere. It
  holds at entry (`initialMemory_postDecls`, proved). Only `main` gets it
  (`MainEntry = GuestInvCovered ∧ InitialMemory`): `alloc` never zeroes, so the body of
  `main` may rely on untouched heap cells being 0. Leaves below `main` do **not** get it.

Why `GuestInv` needs nothing from "what main does first": the arena conjunct admits the
uninitialised 0/0 state, so `GuestInv` already holds at `main` entry. `mem_init` is the step
that reaches `GuestInvReady`.

## 3. Why each FALSE counterexample is excluded

| Leaf | Counterexample (SPECFIX) | Excluded by |
|---|---|---|
| `frame_epilogue` | 1024 journal records `(T,1,1,0)`; `htab_set` → `memeq(1,1,2^63)` → 2^70 ticks | Pointer `1` aligns to `0 ∉ ordinaryDomain`: the first `memeq` load errors. With in-domain pointers, each scan is ≤ `W` (§1). `journal_n ≤ 2^19`. The missing callee cost is now explicit: `K_frame_epilogue = K_state_restore + 256` |
| `finish_child` | same restoration run | same, and `K_finish_child` sums all direct callees, including `state_restore` and `create_finish` |
| `htab_keys` | `n = 2^20`, `stride = 2^63`: `alloc(n·stride+8)` wraps to 8, then 2^20 `memcpy`s of length 2^63 | Each `memcpy` is a domain walk ≤ `W`. The loop loads `order + 8i`, a fresh address each iteration, so it runs ≤ `W/8 + 1` times. With `HtabWF`, `n ≤ ncap ≤ H/32` and `stride ≤ 56` (`htab_keys_on_wf`) |
| `htab_set` | `key_len = 2^63`, `memeq(1,1,2^63)` | Odd pointer excluded. With in-domain pointers `memeq`/`first_diff` ≤ `W`; `find_leaf`'s `n` must index `nodes + 32n ∈ domain` (≤ 4W distinct values; read-only loop, so no repeats without timeout). With `HtabWF`, key length ≤ 52 and node indices ≤ `ncap` (`htab_set_on_wf`) |

None of these is a kernel-checked proof of the restated bound. They are the argument each
leaf prover should formalise.

## 4. Guarded combinators

| Theorem | Status | Notes |
|---|---|---|
| `TerminatingFunBoundedOn.weaken` / `.mono` / `.of_unconditional` | proved | the frozen all-state leaves (e.g. the arithmetic ones) can be reused as-is |
| `callee_body_bound`, `TerminatingProgBoundedOn.call_on` | proved | verbatim port of Opus's `PanTerminatingCallOn` (`wave8/step0-opus55`) |
| `call_guestInv` | proved | `call_on` + `callEntryOn_guestInv`; no call-site work |
| `decCall_guestInv` | proved | Opus's `decCall` with `hresume` replaced by callee preservation (`FunPreservesOn GuestInv GuestInv f`) and `LocalsFree`. Opus's `hresume` quantified over arbitrary `post`, which `GuestInv` cannot satisfy |
| `seq_on` | proved | needs `PreservesOn P P first` |
| `ite_on`, `dec_on` | proved | `dec_on` needs `LocalsFree P` |
| `callHandle_guestInv` | **sorry** | exception-handler calls (`run_frames` → `op_dispatch` with `EvmErr`, `verify_stateless_new_payload`). The proof is the `decCall` case analysis on the `.exception` branch |
| `PreservesOn.call_guestInv` | **sorry** | preservation through a handler-free call (globals from callee post, caller locals restored) |

## 5. Bridge

`coveredSourceTicksConsumedBounded_of_terminatingMainOnP` is proved for an arbitrary guard
`P` that holds at every covered `main` entry state
`callEntryStateHOLFinite {s_decls with clock := k} callee`. It is the repaired frozen bridge
proof with the guard threaded in. `main`'s parameter list `[]` comes from `lookup_main`, so
the old `hmain_zero_args` hypothesis is gone. Instances, all proved:

- `…_of_terminatingMainOn` (guard `GuestInv`);
- `…_of_terminatingMainOnCovered` (guard `GuestInvCovered`);
- `…_of_terminatingMainOnEntry` (guard `MainEntry`, used for `K_pan`) and `…EntryWordGas`.

The post-declarations facts are fully proved, with no `sorry`:

- `evaluateDecls_zero_globals`: an induction over `evaluateDeclsHOLFinite` showing every
  declared global evaluates to word 0;
- `guestAst_zero`: `decide` on the literal AST that every global decl is `const 0`;
- `guestGlobalNames_declared` and `astGlobalNames_eq`: the 67-name list matches the AST;
- `mem_guestAst_of_mem_sourceDeclarations`: `mainFirstHOL` only reorders.

`coveredSourceTicksConsumedBounded_K_pan : CoveredSourceTicksConsumedBounded K_pan` is a proved
term whose only `sorry` dependency is `main_on_entry`. The `wordGas` variant likewise depends
only on `main_on_entry_wordGas`.

## 6. Restated leaf interface and K

Symbols (namespace `R`):

- `W = domainBytes ≈ 3.1·10^10` (single walk);
- `H = heapArenaBytes = 251 658 240` (any one heap table);
- `J = 524288` (journal cap);
- `D = 1025` (frames);
- `G = maxCoveredGas = 2·10^8`;
- `KL = 52` (key length).

Every frozen `2^64 − 1` factor is replaced by the bound of the data structure the loop walks:

- `W` for walks over memory, input slices and arrays;
- `J` for the journal;
- `2050·Gas + 2·D` for `run_frames` (`evmFramePotential`);
- `H/32` for table capacities when `HtabWF` is assumed.

Callee costs omitted from the frozen constants are added: `state_restore` in
`frame_epilogue`/`finish_child`/`generic_*`; `keccak256` in `op_keccak`/`create`; and
`create_finish`, `get_account`, `walk` in `finish_child`.

Guards:

| Family | Guard | Leaves |
|---|---|---|
| G (measure in locals/globals; memory walks bounded by `W`) | `GuestInv` | all of §6e, `htab_set/del/find_leaf/keys`, `state_restore`, `get_*`/`set_storage`, `frame_epilogue`, `finish_child` |
| W (loop measure lives in memory, or is read from memory once at entry) | `HtabArgWF` = `HtabLocalWF "t"`; `HtabLocalWF "src"` | `htab_truncate` (count `t+24` re-read and rewritten by each delete; WF of `t` must be preserved by `htab_del`), `htab_union_into` (trip count `cap := src+24` cached at entry, so WF of `src` at entry suffices and no `dst`/`src` disjointness is needed), refinements `htab_set_on_wf`, `htab_keys_on_wf` |
| F (EVM frames) | `EvmFramesWF G`, `MsgGasCapped G`, `BlockGasCapped G` | `run_frames`, `process_message`, `process_transaction` |
| top | `GuestInvCovered` / `MainEntry` | `run_attempt`, `main`; `…_wordGas` fallbacks use plain `GuestInv` / `MainEntryWordGas` with gas `2^64` |

Why family W/F cannot be `GuestInv`-only: with arbitrary memory, an in-loop store can alias
the loop measure (e.g. EVM memory overlapping `ev+64`, or a node write overlapping `t+24`).
The only remaining bound is a pigeonhole over the mutable domain, about 2^(2.5·10^11), which is
far over budget. So these leaves take a memory well-formedness precondition. The offsets come
from `htab_new` (4869), `htab_grow` (5119), `frame_new` (15372), `charge_gas` (14951),
`extend_memory` (15208), `run_frames` (18665) and `run_attempt` (33817).

Constants are **proposals with derivation sketches** (comments in the file), not audited tick
counts. The slack of 10^230 is there so leaf provers can enlarge any constant.

## 7. Every `sorry` (94 theorem bodies; no definition contains `sorry`)

Combinators (2): `TerminatingProgBoundedOn.callHandle_guestInv`, `PreservesOn.call_guestInv`.

FALSE leaves restated (6): `frame_epilogue_on`, `finish_child_on`, `htab_keys_on`,
`htab_keys_on_wf`, `htab_set_on`, `htab_set_on_wf`.

Journal/state (6): `htab_find_leaf_on`, `htab_del_on`, `state_restore_on`, `get_account_on`,
`get_storage_on`, `set_storage_on`.

Memory-measure / EVM / top (10): `htab_truncate_on_wf`, `htab_union_into_on_wf`,
`run_frames_on`, `process_message_on`, `process_transaction_on`, `run_attempt_on`,
`run_attempt_on_wordGas`, `mem_init_ready`, `main_on_entry`, `main_on_entry_wordGas`.

UNCLEAR leaves restated over `GuestInv` (70): `rlp_validate_items_body_on`,
`rlp_list_count_on`, `rlp_list_to_slices_on`, `decode_account_from_leaf_on`,
`tx_scalar_word_on`, `hdr_word_field_on`, `decode_access_list_on`, `decode_authorizations_on`,
`decode_blob_hashes_on`, `decode_witness_node_body_on`, `trie_walk_on`, `node_rlp_finish_on`,
`node_rlp_fill_on`, `collapse_branch_on`, `mpt_insert_node_on`, `mpt_delete_node_body_on`,
`build_mpt_indexed_on`, `nodedb_build_on`, `modinv_bin_on`, `fp_inv_on`, `fn_inv_on`,
`u256_addmod_on`, `u256_mulmod_on`, `pre_modexp_on`, `p256_fp_mul_on`, `p256_fp_sqr_on`,
`pre_p256verify_on`, `secp256k1_ecrecover_on`, `pre_ecrecover_on`, `bn_divmnu_on`,
`fq12_inv_on`, `pre_alt_bn128_add_on`, `pre_alt_bn128_mul_on`,
`pre_alt_bn128_pairing_check_on`, `bls_fp_inv_raw_on`, `bls_fp_inv_on`, `fp2_inv_on`,
`fp12_inv_on`, `g1_mul_on`, `g2_mul_on`, `pre_kzg_point_evaluation_on`, `pre_bls_g1_add_on`,
`pre_bls_g1_msm_on`, `pre_bls_g2_add_on`, `pre_bls_g2_msm_on`, `pre_bls_pairing_on`,
`pre_bls_map_fp_to_g1_on`, `pre_bls_map_fp2_to_g2_on`, `pack_bytes_on`, `merkleize_on`,
`merkleize_progressive_on`, `htr_bytes_list_on`, `htr_plist_chunks_on`, `htr_payload_on`,
`htr_new_payload_request_on`, `sort_elems_on`, `compute_state_root_on`,
`build_block_access_list_rlp_on`, `compute_jumpdests_on`, `run_precompile_on`, `op_exp_on`,
`op_keccak_on`, `op_extcodecopy_on`, `op_balance_on`, `op_extcodehash_on`, `op_sstore_on`,
`generic_call_on`, `generic_create_on`, `op_selfdestruct_on`, `op_dispatch_on`.

Proved terms that depend on a `sorry`: `coveredSourceTicksConsumedBounded_K_pan` (via
`main_on_entry`) and `coveredSourceTicksConsumedBounded_K_pan_wordGas` (via
`main_on_entry_wordGas`).

## 8. Open questions

- **Q1 (gas link).** `run_attempt_on`/`main_on_entry` must show that header `+104`, stored to
  `be+8`, is ≤ `declaredGasLimit input`, i.e. a parsing-correctness fact through the oracle.
  If this is too costly, use the proved `wordGas` route (`K_pan_wordGas ≈ 5.8·10^56`, also
  within budget). In that route `process_transaction` takes `BlockGasCapped (2^64)`, which is
  trivially true.
- **Q2 (frame potential).** Do `refill_frame_state_gas` and `credit_state_gas_refund`
  (EIP-8037 state-gas refunds) let the summed chain gas increase? If so, `FrameChainWF`'s
  budget must count refunds (bounded by `G` per tx). `EvmFramesWF` also does not yet
  constrain where `cur_cont` records live, or the stack pointer `e+8` / jumpdest map `e+80`.
  It may be too weak.
- **Q3 (arena LIFO).** Preservation of `ArenaOK` needs every `scratch_release(m)` /
  `frame_mem_release(m)` to restore a mark taken in the same activation. In the
  `finish_child` path, check that the child's marks are released before the parent's
  scratch allocations resume.
- **Q4 (resolved, `htab_union_into`).** The parameters are `(dst, src)`. The loop bound is
  `cap := load(src+24)`, cached in a local, so the guard is `HtabLocalWF "src"`. An earlier
  draft guarded local `t`, which does not exist in this function and would have made the
  statement vacuous. **Reviewers:** check every `LocalWord` guard names a real parameter
  (`t` for `htab_set`/`htab_keys`/`htab_truncate`, `msg` for `process_message`).
- **Q5 (W-family soundness).** Each §6e statement claims every loop either has a local/global
  measure or touches a fresh address per iteration. The audit's C-class loops (LOOPS.md) must
  be re-checked against this: `_rlp_validate_items_body` (go/top), `_mpt_delete_node_body`
  (level), `sort_elems`. Any loop whose measure lives in memory moves to family W with an
  explicit WF guard.
- **Q6 (`topAddr`).** It is unused by the AST; drop it from `GuestInv` if the quorum agrees.
- **Q7 (heap invariant for the `_wf` refinements).** Using `htab_set_on_wf` instead of
  `htab_set_on` requires every caller to carry `HtabWF` of its tables, i.e. a heap
  separation invariant from `state_init`. The composition behind `K_pan` uses only the
  `GuestInv` versions, so this is optional, except for family W/F, where it is unavoidable.

## 9. How this was checked

```
lake env lean campaign/specs-proposed/GuestInv.lean   # no errors; only "declaration uses sorry" warnings (94)
```

`#print axioms` was run on a scratch copy with `#print axioms` lines appended.

- `[propext, Classical.choice, Quot.sound]`:
  `coveredSourceTicksConsumedBounded_of_terminatingMainOn{P,,Covered,Entry,EntryWordGas}`,
  `guestInv_postDecls`, `postDecls_globals`, `coveredFfi_postDecls`,
  `initialMemory_postDecls`, `TerminatingProgBoundedOn.{call_on,call_guestInv,decCall_guestInv,seq_on,ite_on,dec_on}`.
- `[propext]`: `K_pan_budget`, `K_pan_wordGas_budget`, `K_pan_lt`, `K_pan_wordGas_lt`.
- No axioms: `domainBytes_eq`, `heapArenaBytes_eq`.
- `coveredSourceTicksConsumedBounded_K_pan` additionally shows `sorryAx`, through
  `main_on_entry` only.

`turbo-lean` was not used: this is a proposal file outside the lake package, so
`lake env lean <file>` was used as the brief instructs.
