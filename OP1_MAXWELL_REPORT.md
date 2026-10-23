# Maxwell Op 1: pass deduplication and build acceleration

Local branch: `op1-init-e-dedup`; baseline `4cb9619cd6`. Implementation commits: `9cef5a409d`, `4235d533da`. No upstream push, Maxwell record or research-governor record. Rocq baseline `64ed8464a5` was inspected; no Rocq changes were needed.

## Delivered patch

`Tools/WordStageData.lean` shares literal rendering, ToExpr instances and the Expr-keyed Word DAG interner between GenWordStages and GenSmallStages. Both generators retain this cache across passes, emitting only new nodes. The cache is reconstructed from the current guest on every invocation, including airgapped regeneration; it introduces no trusted native proof step. Generated equations retain kernel verification.

`tools/dedup-word-passes.py` performs structural sharing on existing pipelines, with string-aware tokenization, dry-run metrics, complete-pipeline preflight and idempotence. Proof splitting imports earlier data dependencies; sparse compaction preserves nodes referenced by later modules.

The artifact commit contains eleven fully checked pipelines: 64, 79, 121, 184, 234, 240, 270, 274, 276, 341, 345 (121 pass modules, 102 files changed). Other pipelines retain their baseline sources. The current generator enumerates 814 source functions; the repository has 78 standalone eleven-pass pipelines, rather than the brief’s historical 96-function scope.

## Exact measurements

| Scope | Before | After |
|---|---:|---:|
| Eleven delivered pipelines, source lines | 524,355 | 198,654 |
| Eleven delivered pipelines, source bytes | 19,155,835 | 7,142,763 |
| Eleven delivered pipelines, pass modules | 121 | 121 |
| Function 79, source lines | 28,106 | 16,118 |
| Function 79, sum of eleven .olean bytes | 24,757,176 | 13,449,824 |
| Function 79, isolated pass-10 export bytes | 1,663,028 | 1,533,809 |
| Fresh function 64 generation, lines | 23,153 | 12,892 |
| Fresh small function 335, nine modules, lines | 29,221 | 15,849 |
| Small335 Data .olean bytes | 16,569,312 | 12,125,096 |

Delivered artifacts save **325,701 lines and 12,013,072 bytes**. This includes current-guest repairs of stale bundles 240, 270, 276 and 341: those repairs account for 102,035 lines and 3,622,585 bytes beyond sharing alone. In particular SSA argument counts change in Pass240_2 (1 → 4) and Pass276_2 (3 → 2), matching current Source declarations. Sharing-only theorem statements are preserved.

Function 79 .olean size falls **45.67%**. NanoDA accepted baseline and changed exports with the same permitted axioms (propext, Quot.sound, Classical.choice). Individual replay times were 0.600/0.467 seconds; pass-10 compilation was 12.43/4.53 seconds under varying load. These are illustrative single runs, not controlled end-to-end benchmarks.

An exploratory transformation of all 78 pipelines saved 2,937,879 lines / 117,345,999 bytes through sharing alone (6,975,851 → 4,037,972 lines; 713,926 duplicate nodes removed). This broader transformation is **not delivered or fully kernel verified**. Its uncommitted sources are preserved in `work/lean-perf/op1/experimental-unverified-pipelines.tar.gz`.

## Verification

- `lake build Tools.GenWordStages Tools.GenSmallStages`: passed.
- `turbo-lean check ... --json`: WordStageData and both generators report `file_verified`; corresponding audit-spec checks report `ok=true`. Template audits do not replace generated-proof checking.
- All 121 delivered pass modules passed Lean kernel checking; per-label evidence is in `work/lean-perf/op1/kernel-passes/`.
- Fresh regular and fused function64 generation checked; fused .olean is 9,784,472 bytes. All nine fresh Small335 modules and all 44 temporary Parallel79/Sparse79 data/proof modules checked. Temporary Parallel/Sparse outputs are preserved outside the source tree to retain compatibility with existing agreement modules.
- Three structural-sharing regression tests pass (including strings, token boundaries, idempotence and later-pass references). `git diff --check` passes.
- Baseline and changed function79 lean4export/NanoDA checks pass (`nanoda79-results.json`).
- All twelve direct downstream consumers checked: six Optimize modules and six StackAnalysis Data modules. The latter passed after building the missing, unchanged StackFrameComputation support module (`downstream-results.json`).

Reproduce generator checks with `lake build Tools.GenWordStages Tools.GenSmallStages` and `python3 tools/test-dedup-word-passes.py`. Measure existing pipelines using `python3 tools/dedup-word-passes.py LABEL`; add `--write` to apply sharing. Fresh pass generation uses `lake env lean --run Tools/GenWordStagesMain.lean 1 OFFSET --passes --word-data-dag` (OFFSET indexes the current guest source list; first label is 64). Exact final metrics and verification evidence are retained under `work/lean-perf/op1/`.

Prepared source artifacts were stale; rebuilding unchanged Source64 and Source224 resolved their initial failures. All 78 Source artifacts were refreshed. Copied setup metadata was localized atomically in 2,030 cache files to avoid dependence on another worktree; no tracked compiler semantics changed.

## Limits and follow-up

Full-submission build/export/replay has not been measured. A broader bulk gate encountered a monolithic CSE proof (151/4) near 15 GiB RSS under the mission’s 16 GiB limit. Its partial checks are not counted as a verified pipeline. Experimental launchers were stopped deliberately when narrowing the delivered patch; their evidence remains under `work/lean-perf/op1/`.

A future bounded-memory CSE proof generator can certify exact Knowledge checkpoints and compose seq/ite/loop equations, preserving kernel verification. Cross-function interning also requires respecting allocator inputs and function names. Neither is needed for this delivered within-function sharing patch. Rocq uses hash-checked byte/bitmap proposals and a vm_compute compilation certificate rather than analogous Lean pass DAGs, so no speculative Rocq patch was made.
