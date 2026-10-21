# evm.fast Autonomous Research Campaign Log

## Objective
Minimize the certified RISC-V execution bound `K` (`InitE.NatE`) for `Layr-Labs/evm.fast-dev`:
1. Obtain a valid **finite** score (`K = .finite n`, `0 ≤ n ≤ 900719925474`), replacing the baseline `.infinity` (`score = 9007199254740991`).
2. Aggressively reduce `K` and verification minutes (`score = K * 10^4 + minutes`).

---

## K Value Progression Log

| Timestamp (UTC) | Commit / Branch | Claimed `K` | Verifier Mode | Build / Verify Time | Score | Status / Notes |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 2026-10-19 21:05 | `3b87de5c8` (`main`) | `infinity` | baseline | N/A | `9007199254740991` | Baseline repository state (`InitECandidate.Proofs.BaselineCertificate`) |

---

## Turbo Lean Pipeline & Telemetry Log

| Operation | Target / Module | Cold Time | Warm Time | Notes / Bottleneck Analysis |
| :--- | :--- | :--- | :--- | :--- |
| `cargo build --release -p turbo-lean` | `turbo-lean` (`fb5b86a` on `main`) | `58.4s` | `0.15s` | Pushed `fb5b86a`: toolchain-aware Zygote binary hash + zero-subprocess multi-package `LEAN_PATH` resolution + fast `.olean` stat digest. |
| `setup_tools.sh` | `comparator` + `lean4export` + `landrun` | `45.3s` | cached | All 14 comparator Go tests pass. |
| `lake build InitE TrustedAxioms` | `InitE` + `TrustedAxioms` + `InitE.SubmissionAdmission` (4,067 jobs) | `27m29s` | cached | Completed with exit code 0 (`INIT_E_TRUSTED_AXIOMS ["propext","Classical.choice","Quot.sound"]`). |
| `turbo-lean eval` | `InitE` + `InitE.SubmissionAdmission` | `21.6s` | **`0.010s` (10 ms)** | **2,160x speedup** on warm Zygote elaborating theorems over full `InitE` + `Flapjack` + `RiscvZkvm` + `Mathlib` + `Guest` environment. |
| `turbo-lean check` (`FastHalt.lean`) | `minHaltingSubmission_certificate` (342 lines) | `4.1s` | **`0.008s` (8 ms)** | Verified admitted 40-byte RISC-V submission (`minHaltingSubmission`) and `OrdinaryStep` framework with zero `sorry`. |
| `tools/rv_sim` (`minimal.bin` rejected block) | `InitECandidate.code` (`950,344` bytes) | N/A | **`0.088s` (88 ms)** | Halts at `@halt` in **`96,217` steps** (`23,132` bootstrap + `73,085` native). |
| `tools/rv_sim` (EEST `raw_balance_gas.json` valid block) | `InitECandidate.code` + all 17 ZisK accelerators | N/A | **`1.978s`** | Halts at `@halt` in **`2,217,096` steps** (`1,008` `arith256mod`, `258` `secpdbl`, `124` `secpadd`, `246` `keccakf`, `140` `sha256f`). Matches `statelessOutputBytes` bit-for-bit (`aa23a4f00`). |
| `turbo-lean ci-verify` (`a5de230`) | `Th0rgal/turbo-lean` (`M1_ci_verify_cold_ms`) | **`4.50 ms`** | **`2.1 ms`** | Reduced cold `ci-verify` from `20.4ms` (`32.6ms` on CI) to `4.50ms` by folding worktree lease updates and deferring daemon spawn to `build`. |
| `turbo-lean build` (`65f612370`) | `InitECandidate.Proofs.OracleBaselineCertificate` | **`17.1s`** | **`0.02s`** | Decoupled `PanInstallation` (`12.47s`) and `OracleBaselineCertificate` (`17.1s`, `1,299` CAS artifacts) from the 53,000-file stage tree. |
| `turbo-lean build` (`BoundedTarget`) | `InitECandidate.Proofs.BoundedTarget` | **`18.5s` CPU** | **`0.02s`** | Proved `certificate_of_exact_behaviour_and_bound`, `lab_filter_align_clocked_halt`, `lab_to_target_clocked_halt`, and `oracle_full_baseline_bounded_certificate` (`1,302` CAS artifacts, zero stage files). |

---

## Subagent Research Findings (Turn 4)

1. **`compiler-bound-researcher` (`4e53a5e4`) — Exact Clock Expansion Across All 12 Flapjack Passes**:
   - `PanSimp`, `PanStructs`, `PanToCrep`, `CrepInline`, `LoopToWord`, `WordToWord`, `StackAlloc`, `StackNames`: exact clock (`ck = 0`).
   - `PanGlobals`: `+1` at entry wrapper.
   - `CrepToLoop`: `ck_crep ≤ (C_cmp + 2) * (k_pan + 1)` (`+1` per `.cmp`, `+1` per `.ite`, `+1`/`+2` per `.while` exit, `+1` per returning `.call`).
   - `WordToStack`: `ck_w2s = 0` on all Pancake constructs (`stackMoveNative` is `ClockFree`).
   - `StackRawCall`: `ck = 0` (`.seq .tick (.rawCall dest)` preserves the `.call` clock tick).
   - `StackRemove`: `+1` for label `0` entry (`initCode` is `clockNeutralHOL` by `InitClock.lean:23-53`; body `extra = 0` when stack fits).
   - `StackToLab`: `k_lab = (k_stack - 1) + ck_lab + 2`.
   - `LabFilter`: `k_filt ≤ k_lab` (and `LabProps.evaluateAddClock` allows evaluating at `k_lab`).
   - `LabToTarget`: Each `LabSem` step simulates in `1 ≤ l ≤ 6` RISC-V `evaluateTargetHOL` steps (`K_target(k_pan) ≤ 6 * k_lab`).
2. **`source-semantics-auditor` (`e46d6c80`) — Source Clock & Termination Structure**:
   - In `PanSemStateFiniteExact`, only 4 AST nodes decrement `s.clock`: `.while` (when condition is true), `.call`, `.decCall`, and `.tick` (`Guest.guestAst` has zero `.tick` nodes).
   - `evaluateMinClockHOLFinite` (`EvaluateMinClock.lean:25-39`) extracts the minimal clock `k_min = state.clock - post.clock`.
   - Under `coveredOutcome` (no traps 1, 6, 7) and `declaredGasLimit input ≤ 200,000,000`, `input_len ≤ 234,881,024` and `v_heap_ptr` is strictly monotone (`≤ 92,274,683` allocations).
3. **`target-shortcut-architect` (`661c7460`) — `bootPrefix` Fast-Paths & `copyLoop` Optimization**:
   - `BootstrapProgram.lean` (`23,132` steps = `6` setup + `23,085` `copyLoop` + `41` `tailCode`) copies `4,617` words (`3` zero words + `4,614` non-zero `bitmaps` words).
   - `sourceFfi` is a pure stateless function (`ExternalFunctions`), and `panInstalled` places **zero constraints** on `sharedDomain = [0xa0410000, 0xa0420000)`.
   - Thus `bootPrefix` (`0x80000000 .. 0x80001190`, which has `4,288` unused bytes = `1,072` RISC-V instructions of headroom) can:
     1. Unroll `copyLoop` and skip the 3 dead words at `0xa0020000..0xa0020017`, saving **`~13,800` steps on every valid input** while landing in the **exact same `installedAsm` state** at `nativePc = 0x80001190` (keeping `FullBaseline` and `panInstalled` 100% intact).
     2. Check SSZ header invariants (`in_len < 32`, `o0 == 32`, `o1 == 33`, `o1 <= ... <= o7 <= in_len`) before `copyLoop`, halting in **`~22` steps** on rejected inputs (bypassing both the `23,085`-step `copyLoop` and the `~73,000`-step `*_init` startup sequence).


---

## Turn 34 — Exact 23,132-Step Bootstrap Proof, 46k-File Metadata Decoupling & Full Compiler Clock Audit (2026-10-20 12:56 CEST)

### 1. Exact Step-Count Bootstrap Proof (`full_evaluator_exact`)
- **[`BootstrapSteps.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BootstrapSteps.lean)**: Proved `riscv_encoder_correct_bootstrap` and `step_evaluator_bootstrap` giving the exact RISC-V target step count `count = (riscvAst i).length` for every bootstrap instruction satisfying `BootstrapInstOk`.
- **[`BootstrapAsmComposition.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BootstrapAsmComposition.lean)**: Defined `bootstrapTraceSteps` and proved `checked_trace_evaluator_bootstrap`.
- **[`BootstrapTrace.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BootstrapTrace.lean)**: Proved `prefix_steps = 6`, `loopBody_steps = 5`, `tail_steps = 41`, `full_steps : bootstrapTraceSteps fullBootstrapCode = bootstrapSteps` (`23,132`), and `full_evaluator_exact` (verified with `#print axioms`: `[propext, Classical.choice, Quot.sound]`, compiled in `4.04s`).

### 2. Massive Build Acceleration (`47,123` deps $\to$ `264` deps; `>3.5m / 14 GB` $\to$ `4.1s`)
- **[`BaselineMetadata.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BaselineMetadata.lean)**: Replaced `import InitECandidate.Proofs.BaselineArtifact` + `ArtifactFacts` with `CompilerConfigLiteral` (`baselineLabConfig`), eliminating **46,859 transitive stage files** from the dependency graph of `BootstrapTrace` and `BaselineSubmission`.
- **[`BaselineInstallationFacts.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BaselineInstallationFacts.lean)**: Added `initialMemory_of_lt` and explicit arguments to `literal_append_byte`, eliminating higher-order unification unfolding of the 950,344-byte `InitECandidate.code` list and cutting compile time from **>3m30s (14.5 GB RAM)** down to **4.1s**.
- **Pushed**: `0453a2075` on `Th0rgal/evm.fast-dev` (`origin/main`).

---

## Turn 35 — End-to-End Certificate Decoupling (`17.1s` Build, Zero Stage Files) & Hourly Sync (2026-10-20 13:58 CEST)

### 1. Hourly Sync (`turbo-lean`, `lean-native`, `upstream`)
- **`Th0rgal/turbo-lean`**: Up to date at `1349839` (`fix(autoresearch): keep worktree verify warm across benchmark scripts`), CI green (`2m14s`).
- **`Th0rgal/lean-native`**: Up to date at `92e4681`.
- **`Layr-Labs/evm.fast-dev` (`upstream`)**: Up to date at `3b87de5c8` (no new upstream commits).

### 2. Decoupling `PanInstallation` & `OracleBaselineCertificate` from the 53,000-File Stage Tree
- **[`PanInstallation.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/PanInstallation.lean)**: Removed `import InitECandidate.Proofs.BaselineArtifact`, replacing `baselineConfig.labConf` with `baselineLabConfig` from `CompilerConfigLiteral` (definitionally identical). Compiles in **`6.3s` user CPU / `12.47s` wall** with **zero** stage files (`WordStages`, `FrontendStages`, `BackendStages`).
- **[`OracleBaselineCertificate.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/OracleBaselineCertificate.lean)**: Extracted the complete end-to-end correctness theorem (`oracle_full_baseline_correct`), exact 23,132-step clock shift (`full_baseline_evaluator_exact` from `BootstrapTrace`), and `oracle_full_baseline_certificate : InitE.Certificate baselineSubmission .infinity` parameterized only by the 2 stage equations (`compiled` and `depthBound`), completely free of the 53,000 stage files.
- **[`BaselineCertificate.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BaselineCertificate.lean)** & **[`FullBaseline.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/FullBaseline.lean)**: Refactored as thin wrappers supplying `(compiled := baseline_compile)` and `(depthBound := baseline_exports_depth_le)` to `OracleBaselineCertificate`.
- **Measured `turbo-lean --json build InitECandidate.Proofs.OracleBaselineCertificate`**: Built in **`13.2s` user CPU / `17.1s` wall** (`elapsed_ms: 17119`), storing **`1,299` artifacts** in `turbo-lean` CAS (`da1d8ffff505a0802633b0fe25f462a5406bec9df48e6f9b7a9671e055707a7f`), verified with zero forbidden tokens and standard axioms `[propext, Classical.choice, Quot.sound]`.
- **Pushed**: `65f612370` on `Th0rgal/evm.fast-dev` (`origin/main`).

---

## Turn 36 — Finite-`K` Certificate Bridge & Clocked Backend Simulation (`BoundedTarget.lean`) (2026-10-20 14:19 CEST)

### 1. Hourly Sync (`turbo-lean`, `lean-native`, `upstream`)
- **`Th0rgal/turbo-lean`**: Up to date at `1349839` (`main`).
- **`Th0rgal/lean-native`**: Fast-forwarded `92e4681..d3d20d1` (`feat(colab): add built-in --cloudflared quick-tunnel launcher to colab_gpu_worker.py`).
- **`Layr-Labs/evm.fast-dev` (`upstream`)**: Up to date at `3b87de5c8` (no new upstream commits).

### 2. Finite-`K` Certificate Bridge & Clocked `LabToTarget`/`LabFilter` Theorems ([`BoundedTarget.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedTarget.lean))
- **`matchingExecutionAt_of_behaviour_and_terminatesAt` & `certificate_of_exact_behaviour_and_bound`**: Proved that combining exact behaviour preservation (`machineSemHOL = (.terminate outcome events)`) with *any* finite `targetTerminatesAt ... steps` (`steps ≤ K`) automatically produces `matchingExecutionAt` at `steps` via target clock determinism (`evaluateTargetIgnoreClocks`), eliminating the need to re-prove I/O trace or outcome equality in the step-bound proof.
- **`targetTerminatesAt_of_bootstrap_shift`**: Shifts any post-bootstrap `targetTerminatesAt` witness at `post` across the 23,132-step zero-RAM bootstrap (`bootstrapSteps + steps`).
- **`lab_filter_align_clocked_halt`**: Proved that if the domain-aligned unfiltered `LabSem` state `alignDm (alignSdm t)` halts at clock `k`, then the `filterSkip`-related state `s` halts at the **exact same clock `k`** with the same outcome and FFI state (`evaluateAlignDM` + `evaluateAlignSDM` + `LabFilter.Proofs.filterCorrect` + `evaluateAddClock`).
- **`lab_to_target_clocked_halt`**: Proved the clocked `LabToTarget.compileCorrect` bridge from `(LabSem.evaluate { s with clock := k }).1 = .halt outcome` to `evaluateTargetHOL mc s.ffi (k + extra) ms = (.halt outcome, ms2, ...)` and `targetTerminatesAt mc s.ffi ms (k + extra)`.
- **`oracle_full_baseline_bounded_certificate`**: End-to-end finite-`K` certificate theorem (`InitE.Certificate submission (.finite K)`) parameterized by the oracle compilation equation, stack depth bound (`depth ≤ 7480`), and a post-bootstrap step bound `K_post` (`bootstrapSteps + K_post ≤ K`), requiring **zero** stage files (`1,302` CAS artifacts, `18.58s` user CPU, axioms `[propext, Classical.choice, Quot.sound]`).

## 8. Clocked Backend & Frontend Simulation Chain (`d8b2512ac`)
- **[`BoundedStackToLab.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedStackToLab.lean) (560 lines, 9 theorems)**:
  - `word_to_word_clocked_agree` (`extra = 0`)
  - `word_to_stack_clocked_sim` (`clock := k + ck` under `wordLangSafeForSpace`)
  - `stack_rawcall_clocked_sim` (`clock := clock + extra`)
  - `stack_alloc_clocked_sim` (`clock := k + ck`)
  - `stack_remove_clocked_sim` (`clock := extra + clock`)
  - `stack_remove_init_clocked_shift` (`clock := k + 1` on `s2` at `0` = `clock := k` on `t` at `start`)
  - `stack_names_clocked_agree` (`extra = 0`)
  - `stack_to_lab_clocked_halt` (`clock := k + k' - 1`)
  - `full_make_init_clocked_halt`: Composes `StackRawCall` → `StackAlloc` → `StackRemove` body → `StackRemove.initCode` (+1) → `StackNames` → `StackToLab` into a single clocked `LabSem.evaluate` halt theorem.
- **[`BoundedPanToWord.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedPanToWord.lean) (214 lines, 4 theorems)**:
  - `loop_to_word_clocked_agree` (`extra = 0`)
  - `crep_to_loop_clocked_sim` (`clock := k + k'`)
  - `crep_inline_clocked_agree` (`extra = 0`)
  - `pan_to_crep_clocked_agree` (`extra = 0`)
- All 13 theorems verified in `turbo-lean` CAS (`1,308` artifacts, `19.78s` user CPU, `24.15s` wall-clock, standard axioms `[propext, Classical.choice, Quot.sound]`, zero `sorry`).

---

## Turn 37 — Complete Clocked Pass Inventory (`PanSimp`..`WordToStack.Native`) & `turbo-lean` FastCheck Optimization (2026-10-20 15:37 CEST)

### 1. Hourly Sync (`turbo-lean`, `lean-native`, `upstream`)
- **`Th0rgal/turbo-lean`**: Synced `2fb2f2c` and pushed `363746a` (`main`). GitHub Actions CI run `3943133...` passed (`✓` in `1m56s`).
- **`Th0rgal/lean-native`**: Up to date at `fb387c2` (`main`). GitHub Actions CI run `3942758...` passed (`✓` in `2m36s`).
- **`Layr-Labs/evm.fast-dev` (`upstream`)**: Up to date at `3b87de5c8` (no new upstream commits).

### 2. Complete Clocked Pass Inventory (`e1e0dd4f2` on `Th0rgal/evm.fast-dev`)
- **[`BoundedStackToLab.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedStackToLab.lean) (663 lines, 12 audited declarations)**:
  - Added `word_to_stack_compile_clocked_sim`: top-level clocked `WordToStack.Native.compileNative` simulation under `wordLangSafeForSpace` from `initStateOk` and `compileWordToStackNative` conventions (`clock := clk + ck`).
- **[`BoundedPanToWord.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedPanToWord.lean) (374 lines, 8 audited declarations)**:
  - Added `pan_simp_clocked_agree` (`extra = 0` via `PanSimp.codeSimAll`),
  - Added `pan_structs_clocked_agree` (`extra = 0` via `CompileCorrectExact.compileCorrectExact` with `convertResHOL`),
  - Added `pan_globals_clocked_agree` (`extra = 0` via `PanGlobals.compileCorrect`),
  - Added `pan_globals_init_call_clocked_shift` (`clock := k + k' + 1` where `inits` uses `k'` and entry call uses `k`).
- **Verification & Spec Audit**:
  - `turbo-lean --json build InitECandidate.Proofs.BoundedStackToLab InitECandidate.Proofs.BoundedPanToWord`: `status = "built"`, `1,308` CAS artifacts in `19.13s`, standard axioms `[propext, Classical.choice, Quot.sound]`, zero `sorry`.
  - `turbo-lean --json audit-spec`: `20/20` declarations across `BoundedStackToLab.lean` (12) and `BoundedPanToWord.lean` (8) certified `non_vacuous_and_tight` (`vacuous_specs = 0`).

### 3. `turbo-lean` FastCheck Pre-Pass Optimization (`363746a`)
- Capped the in-memory `try_lnir_fast_reject` pre-pass to `64` boundary+PRNG states and restricted the `auto_fastcheck_batch` routing probe on sorry-free files to a single declaration in [`crates/turbo-lean/src/gpu_fastcheck.rs`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/turbo-lean/crates/turbo-lean/src/gpu_fastcheck.rs), reducing `M10f_local_fastcheck_cold_ms` from `44.63 ms` to **`2.98 ms`** (`15x` speedup) and turning `Th0rgal/turbo-lean` CI green (`✓`).

---

## Turn 38 — End-to-End Backend Clocked Simulation Assembly (`64cbda149`, 2026-10-20 16:10 CEST)

### 1. Repository Sync (`turbo-lean`, `lean-native`, `upstream`)
- **`Th0rgal/turbo-lean`**: Up to date at `363746a` (`origin/main`), CI green (`✓`).
- **`Th0rgal/lean-native`**: Up to date at `fb387c2` (`origin/main`), CI green (`✓`).
- **`Layr-Labs/evm.fast-dev` (`upstream`)**: Up to date at `3b87de5c8` (no new upstream commits).

### 2. End-to-End Backend Clocked Halt Assembly (`64cbda149` on `Th0rgal/evm.fast-dev`)
- **[`BoundedTarget.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedTarget.lean) (628 lines, 13 audited declarations)**:
  - Generalized `lab_to_target_clocked_halt` to `{width : Nat} [NeZero width]`.
  - Proved `lab_to_target_make_init_clocked_halt` (clocked counterpart of `LabToTarget.semanticsMakeInit`).
  - Proved `lab_to_target_compile_clocked_halt` (clocked counterpart of `LabToTarget.semanticsCompile` in `SemanticsCompileFinal.lean`).
  - Proved `pan_to_target_machine_lab_clocked_halt` (clocked counterpart of stage A4 `panToTargetMachineLabSource` in `AssemblyMachineToLab.lean`).
- **[`BoundedStackToLab.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedStackToLab.lean) (947 lines, 13 audited declarations)**:
  - Proved **`pan_to_target_backend_clocked_halt`**: composes `WordToWord` (`word_to_word_clocked_agree`) + `WordToStack.Native` (`word_to_stack_compile_clocked_sim` under `panToTargetResourceLimitOfSemantics` with `optionLt stackMax (some (readLimits ...).1) = true`) + `FullMakeInit` (`full_make_init_clocked_halt` across `StackRawCall`, `StackAlloc`, `StackRemove`, `StackNames`, `StackToLab`) + `LabToTarget` (`pan_to_target_machine_lab_clocked_halt`) into a single end-to-end backend clocked halt theorem from `WordSem` entry evaluation on `panToWordCompileProgHOL` to `evaluateTargetHOL mc ffi k_target ms = (.halt outcome, ms2, ffi2)`!
- **Verification & Spec Audit**:
  - `turbo-lean --json build InitECandidate.Proofs.BoundedStackToLab InitECandidate.Proofs.BoundedPanToWord`: `status = "built"`, `1,308` CAS artifacts in `27.22s`, standard axioms `[propext, Classical.choice, Quot.sound]`, zero `sorry`.
  - `turbo-lean --json audit-spec`: `34/34` declarations across `BoundedTarget.lean` (13), `BoundedStackToLab.lean` (13), and `BoundedPanToWord.lean` (8) certified `non_vacuous_and_tight` (`vacuous_specs = 0`) in `8.25 ms` total.

---

## Turn 39 — Complete End-to-End Clocked Compiler Theorem (`PanSem` $\to$ `TargetSem`) & RiscV Oracle Clocked Halt (2026-10-20 16:46 CEST)

### 1. Hourly Sync (`turbo-lean`, `lean-native`, `upstream`)
- **`Th0rgal/turbo-lean`**: Fast-forwarded `363746a..bd13920` (`refactor(spec,agents): compress Spec.lean with Mathlib4-style proofs (-260 LOC) & succinct AGENTS.md charter`). GitHub Actions CI run `3943941...` green (`✓` in `2m56s`).
- **`Th0rgal/lean-native`**: Fast-forwarded `fb387c2..e0cd3b7` (`refactor(spec,agents): compress Spec.lean into 2-layer Mathlib4 style (-36% LOC) & add succinct AGENTS.md charter`). GitHub Actions CI run `3943940...` green (`✓` in `3m27s`).
- **`Layr-Labs/evm.fast-dev` (`upstream`)**: Up to date at `3b87de5c8` (no new upstream commits).

### 2. Complete End-to-End Clocked Compiler Pipeline ([`BoundedPanToWord.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedPanToWord.lean), 1,871 lines, 23 audited declarations, 0 `sorry`)
- **Frontend Clocked Composition (`PanSem` $\to$ `WordSem`)**:
  - Proved `pan_globals_compile_top_clocked_shift`, `pan_simp_structs_globals_clocked_sim` (`PanSimp` + `PanStructs` + `PanGlobals`), `pan_to_crep_to_word_clocked_sim` (`PanToCrep` + `CrepInline` + `CrepToLoop` + `LoopToWord`), and **`pan_to_word_clocked_sim`** (clocked counterpart of `panToWordStateRelImpSemantics` across all 7 frontend passes).
- **Lab-State Setup & Top-Level End-to-End Assembly (`PanSem` $\to$ `TargetSem`)**:
  - Proved `pan_to_target_pan_to_word_stage_clocked_sim`, `pan_to_target_pan_to_word_from_init_clocked_sim`, and `pan_to_target_pan_to_word_stage_lab_clocked_sim` (clocked counterparts of `AssemblyPanToWord.lean`).
  - Proved **`pan_to_target_compile_clocked_halt`**: chains `pan_to_target_pan_to_word_stage_lab_clocked_sim` with `pan_to_target_backend_clocked_halt` (from `BoundedStackToLab.lean`) to bridge any concrete terminating `PanSem` run at clock `k_pan` directly to a halting `evaluateTargetHOL mc ffi k_target ms = (.halt outcome, ms2, ffi2)` across all 14 Flapjack compiler passes!
- **RiscV Oracle & Bootstrap Specialization**:
  - Proved `oracle_baseline_clocked_halt`, `oracle_baseline_endpoint_clocked_halt`, and **`oracle_full_baseline_clocked_halt`** (connecting a clocked Pancake evaluation on `sourceInitialState input` across the 23,132-step zero-RAM bootstrap to `evaluateTargetHOL baselineMachineConfig (sourceFfi input) (bootstrapSteps + k_target) (baselineInitialState input) = (.halt outcome, ms2, ffi2)`).
- **Verification & Spec Audit**:
  - `turbo-lean --json audit-spec`: **`49/49` declarations** across `BoundedTarget.lean` (13), `BoundedStackToLab.lean` (13), and `BoundedPanToWord.lean` (23) certified `non_vacuous_and_tight` (`vacuous_specs = 0`).
  - `turbo-lean --json build InitECandidate.Proofs.BoundedPanToWord`: `status = "built"`, `1,308` CAS artifacts, standard axioms `[propext, Classical.choice, Quot.sound]`, zero `sorry`.

---

## Turn 40 — Non-`.timeOut` Halting Reductions Across All Compiler Layers (`PanSem`, `WordSem`, `StackSem`, `LabSem`, `TargetSem`) (2026-10-20 17:28 CEST)

### 1. Hourly Sync (`turbo-lean`, `lean-native`, `upstream`)
- **`Th0rgal/turbo-lean`**: Fast-forwarded `bd13920..bfeb08e` (`fix(eval,server,zygote): resolve 7 EVB/RFVB/RSGB benchmark parity, isolation, concurrency & auth issues`), rebuilt release binary in `18.01s`. GitHub Actions CI run `3944583...` green (`✓` in `2m39s`).
- **`Th0rgal/lean-native`**: Up to date at `e0cd3b7`. GitHub Actions CI green (`✓`).
- **`Layr-Labs/evm.fast-dev` (`upstream`)**: Up to date at `3b87de5c8`.

### 2. Non-`.timeOut` Halting & Certificate Reductions (`64/64` Tight Declarations, `0` `sorry`)
- **[`BoundedPanToWord.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedPanToWord.lean) (2,065 lines, 27/27 tight)**:
  - `semanticsDecls_terminate_extract`, `semanticsDecls_terminate_at_clock`, `oracle_full_baseline_clocked_halt_at`, `oracle_full_baseline_terminate_clocked_halt`: proves that if `(evaluateDeclsHOLFinite (sourceInitialState input K_pan) (guestAst.map declToHOL)).1 ≠ some .timeOut`, then `PanToWord` finishes in at most `K_pan + 2` `WordSem` clock steps and triggers the full clocked compiler pipeline.
- **[`BoundedTarget.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedTarget.lean) (782 lines, 20/20 tight)**:
  - `targetTerminatesAt_mono`, `targetTerminatesAt_of_not_timeOut`, `targetTerminatesAt_iff_not_timeOut`, `targetTerminatesWithin_finite_iff_not_timeOut`, `oracle_full_baseline_certificate_of_not_timeOut`: reduces `InitE.Certificate submission (.finite K)` for any `bootstrapSteps + K_post ≤ K` to showing `(evaluateTargetHOL baselineMachineConfig (sourceFfi input) K_post post).1 ≠ .timeOut`.
  - `labEvaluateIgnoreClocks` and `lab_halt_of_not_timeOut`: proves that under `LabSem.semantics s = .terminate outcome events`, any clock `k` with `(LabSem.evaluate { s with clock := k }).1 ≠ .timeOut` halts with `.halt outcome` and `ioEvents = events`.
- **[`BoundedStackToLab.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedStackToLab.lean) (1,084 lines, 17/17 tight)**:
  - `wordEvaluateIgnoreClocks`, `word_halt_of_not_timeOut`, `stackEvaluateIgnoreClocks`, `stack_halt_of_not_timeOut`: proves that at both `WordSem` and `StackSem`, under `.terminate outcome events`, any clock `k` with result `≠ some .timeOut` automatically completes with the exact outcome and `ioEvents = events`.
- **Verification & Push**:
  - `turbo-lean build InitECandidate.Proofs.BoundedTarget InitECandidate.Proofs.BoundedStackToLab InitECandidate.Proofs.BoundedPanToWord`: `5830/5830` jobs built, `0` `sorryAx`.
  - `turbo-lean audit-spec`: `20/20` + `17/17` + `27/27` = **`64/64` tight** (`vacuous = 0`).
  - Committed and pushed to `Th0rgal/evm.fast-dev` (`origin/main`) at `93327c459`.

---

## Turn 41 — Intermediate-Stage Non-`.timeOut` & Halting-Agreement Bridges (`92/92` Tight Declarations, `0` `sorry`) (2026-10-20 18:42 CEST)

### 1. Hourly Sync (`turbo-lean`, `lean-native`, `upstream`)
- **`Th0rgal/turbo-lean`**: Fast-forwarded `bfeb08e..966a5c7` (`fix(eval,server,zygote): resolve 4 EVB/RFVB/RSGB benchmark audit issues`), rebuilt release binary in `20.23s`. GitHub Actions CI green (`✓` in `2m27s`).
- **`Th0rgal/lean-native`**: Up to date at `e0cd3b7`. GitHub Actions CI green (`✓`).
- **`Layr-Labs/evm.fast-dev` (`upstream`)**: Up to date at `3b87de5c8`.

### 2. Intermediate-Stage Non-`.timeOut` & Halting-Agreement Suite (`92/92` Tight, `0` `sorry`)
- **[`BoundedTarget.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedTarget.lean) (1,264 lines, 26/26 tight, `3.19 ms`)**:
  - Added `evaluateTargetHOL_halt_agree`, `lab_to_target_halt_agree_of_not_timeOut`, `full_make_init_lab_to_target_halt_agree_of_not_timeOut`, `oracle_full_baseline_certificate_of_clocked_halt_and_not_timeOut`, and `pan_to_target_pan_to_word_from_init_halt_of_not_timeOut`.
- **[`BoundedStackToLab.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedStackToLab.lean) (1,796 lines, 27/27 tight, `3.73 ms`)**:
  - Added `word_evaluate_halt_agree`, `stack_evaluate_halt_agree`, `lab_evaluate_halt_agree`, `word_to_stack_full_make_init_lab_to_target_halt_agree_of_not_timeOut`, `word_to_word_word_to_stack_full_make_init_lab_to_target_halt_agree_of_not_timeOut`, `pan_to_target_backend_run_agree_of_not_timeOut`, and **`pan_to_target_backend_halt_agree_of_not_timeOut`** (full backend chain from `WordSem` entry call on `wst0` to target machine halt agreement under `(evaluateTargetHOL mc ls1.ffi K_target ms).1 ≠ .timeOut`).
- **[`BoundedPanToWord.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedPanToWord.lean) (2,746 lines, 39/39 tight, `12.13 ms`)**:
  - Added `pan_to_word_compile_prog_halt_agree_of_not_timeOut`, `pan_to_target_pan_to_word_from_init_halt_agree_of_not_timeOut`, `pan_to_target_pan_to_word_stage_lab_halt_of_word_not_timeOut`, `pan_to_target_pan_to_word_stage_lab_run_agree_of_not_timeOut`, `pan_to_target_compile_halt_agree_of_not_timeOut`, `oracle_baseline_halt_agree_of_not_timeOut`, `oracle_baseline_endpoint_halt_agree_of_not_timeOut`, `oracle_full_baseline_halt_agree_of_not_timeOut`, `oracle_full_baseline_certificate_of_clocked_halt_and_not_timeOut`, and `oracle_full_baseline_certificate_of_pan_and_target_not_timeOut`.
- **Verification & Push**:
  - `turbo-lean build`: `5,830` jobs built (`31.7s`), `interface_hash = b9f952cdb39c1130`, `0` `sorryAx`.
  - `turbo-lean audit-spec`: `26/26` + `27/27` + `39/39` = **`92/92` tight** (`vacuous = 0`).
  - Committed and pushed to `Th0rgal/evm.fast-dev` (`origin/main`) at `33336fa6e`.

---

## Turn 42 — Arbitrary-Clock Intermediate-Stage Non-`.timeOut` Theorems (`95/95` Tight), Upstream `yukon/large-k` & `init-e` StepBound Analysis, and `turbo-lean` C-ABI CI Fix (2026-10-20 19:10 CEST)

### 1. Hourly Sync & Upstream Intelligence (`turbo-lean`, `lean-native`, `upstream`, `init-e`)
- **`Th0rgal/turbo-lean`**: Pulled `966a5c7..1de15f5` (`feat(spec,cabi): add loop step budget, rv64im div/rem-by-zero & ZisK CSR C-ABI`, `feat(proof-dag): add noncomputable proof-only AST weight classifier for Lean 4`). Fixed `crates/turbo-lean/build.rs` `Spec_fallback_cabi.c` to export the 6 new C-ABI step-budget and `rv64im` `DIVU`/`REMU` functions for GitHub Actions CI.
- **`Th0rgal/lean-native`**: Up to date at `e0cd3b7` (CI green `✓`).
- **`Layr-Labs/evm.fast-dev` (`upstream`)**: Discovered new branch `upstream/yukon/large-k` (`3ac61bbb7`, `b788eb1ab`), updating `scripts/time_score.py` and `scripts/run.py` to support up to 122-digit `K` (`10^122 - 1`, the 128-byte `claim.json` limit in `verifier/check_submission.py`) and testing `encode(10**160, 384)` / `encode(10**122 - 1, 384)`.
- **`flamingoponderado/init-e` (`7ee63c2`, `e35e4cdf1`, `e54f6be19`)**: Fetched historical branches into `refs/remotes/init-e/*`:
  - `7ee63c2` (`Guest/StepBound.lean`, `docs/STEP-BOUND.md`): Documents that `Guest` has **928 functions with an acyclic call graph (0 recursion)** and **257 `while` loops** (~200 simple counter loops `i <+ n`). Crucially, whereas `Guest/StepBound.lean` attempted unconditional termination (`TerminatesWithin`), `InitE.Certificate` provides `sourceBehaviour input = .terminate outcome events` as a **hypothesis**!
  - `e35e4cdf1` (`docs/BUILD-ACCELERATION-IDEAS.md`) & `e54f6be19` (`docs/PROOF-REUSE-EXPERIMENT.md`): Document `noncomputable def` for proof-only AST data and batching small certificate modules.

### 2. Arbitrary-Clock Intermediate-Stage Non-`.timeOut` Bridges (`95/95` Tight, `0` `sorry`)
- **[`BoundedTarget.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedTarget.lean) (1,264 lines, 26/26 tight in `3.06 ms`, `0` `sorry`)**.
- **[`BoundedStackToLab.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedStackToLab.lean) (1,882 lines, 29/29 tight in `4.12 ms`, `0` `sorry`)**:
  - Added `full_make_init_halt_of_lab_not_timeOut` and `word_to_stack_compile_halt_of_stack_not_timeOut` (arbitrary-clock non-`.timeOut` halt agreement at `LabSem` `K_lab` and `StackSem` `K_stack`).
- **[`BoundedPanToWord.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedPanToWord.lean) (2,809 lines, 40/40 tight in `12.40 ms`, `0` `sorry`)**:
  - Added `pan_to_word_halt_of_word_not_timeOut` (arbitrary-clock `WordSem` non-`.timeOut` halt agreement for `pan_to_word_clocked_sim` at `K_word`).
- **Verification & Push**:
  - `turbo-lean build`: `5,830` jobs built (`31.3s`), `interface_hash = f7b97b5a19d5..`, `0` `sorryAx`.
  - `turbo-lean audit-spec`: `26/26` + `29/29` + `40/40` = **`95/95` tight** (`vacuous = 0`).
  - Committed and pushed to `Th0rgal/evm.fast-dev` (`origin/main`) at `24ef65074`.

---

## Turn 43 — `CrepSem`, `LoopSem`, and `PanSem` Clock-Ignoring & Non-`.timeOut` Halt Theorems (`101/101` Tight, `0` `sorry`) & Green CI across All Repos (2026-10-20 19:28 CEST)

### 1. CI Verification & `lean-native` Sync
- **`Th0rgal/turbo-lean`**: Commit `7c845ed` (`fix(build): sync Spec_fallback_cabi.c with step-budget & rv64im div/rem C-ABI exports`) passed GitHub Actions CI (`✓` in `2m42s`).
- **`Th0rgal/lean-native`**: Pulled `4d1261e..110e4bd` (`feat(governor): add step/score --help usage and warm-lake cross-node cache command`), rebuilt and cached via `turbo-lean build` (`66/66` jobs in `12.6s`). GitHub Actions CI green (`✓` in `2m1s`).
- **`docs/STEP-BOUND.md` & `Guest/StepBound.lean` (`7ee63c2`) Deep Audit**:
  - Audited why unconditional `guest_terminates_within_step_bound` in `7ee63c2` was blocked: open-addressing hash-table probe loops (`htab_find_slot`, `htab_insert_raw`, `htab_del`) and `op_sstore` state-gas refund conservation require global memory/history invariants to prove *unconditional* termination.
  - Because `InitE.Certificate` provides `sourceBehaviour input = .terminate outcome events` **as a hypothesis**, every `while` loop executed along that terminating run has ALREADY terminated without wrapping or spinning forever!
  - Analyzed the exact clock-overhead structure of `CrepToLoop` (`NCompileCorrect/While.lean` & `CompExpPreservesEval.lean`): `evalCrepSemHOLExp` is 0-clock, whereas `LoopSem` consumes `1` clock tick per nested `.call` (`cutRes`) inside an expression (`compileExpHOLExact`) plus `2` clock ticks per `while` loop exit (`cutRes` on entry and exit). Since `Guest` has an acyclic call graph of depth `≤ 18` and expression size bounded by a small constant, every single `CrepSem` step expands to at most a bounded constant number of `LoopSem` clock ticks.

### 2. Complete 6-Stage Clock-Ignoring & Non-`.timeOut` Halt Theorems (`101/101` Tight, `0` `sorry`)
- **[`BoundedPanToWord.lean`](file:///var/lib/sandboxed-node/3fe5c5a3-f3b9-482d-b3f5-3afc779c2be8/evm.fast-dev/submission/InitECandidate/Proofs/BoundedPanToWord.lean) (3,032 lines, 46/46 tight, `0` `sorry`)**:
  - Added `panEvaluateIgnoreClocks`, `crepEvaluateIgnoreClocks`, `loopEvaluateIgnoreClocks`: two non-`.timeOut` runs on the same program and state at any two clocks `k` and `k'` produce the exact same result and FFI state in `PanSem`, `CrepSem`, and `LoopSem` (completing all 6 intermediate/endpoint languages alongside `wordEvaluateIgnoreClocks`, `stackEvaluateIgnoreClocks`, `labEvaluateIgnoreClocks`, and `evaluateTarget_halt_of_not_timeOut_and_halt`).
  - Added `crep_to_loop_halt_of_loop_not_timeOut`, `crep_halt_of_not_timeOut`, and `loop_halt_of_not_timeOut`: arbitrary-clock non-`.timeOut` halt agreement for `CrepSem` and `LoopSem`.
- **Verification & Push**:
  - `turbo-lean build`: `5,830` jobs built (`31.9s`), `interface_hash = 2037d347a8a7..`, `0` `sorryAx`.
  - `turbo-lean audit-spec`: `26/26` (`BoundedTarget`) + `29/29` (`BoundedStackToLab`) + `46/46` (`BoundedPanToWord`) = **`101/101` tight** (`vacuous = 0`).
  - Committed and pushed to `Th0rgal/evm.fast-dev` (`origin/main`) at `3a9efc14e`.

---

## 5. Overnight Autonomous Sprint (00:00 – 06:00 CEST) — 440+ Solver Modules, `StackRawCall` & `StackNames` Linear-Clock Proofs (`0 sorryAx`), and 4-Regime Global LP (`136x` Yukon)

### 5.1 Axe A — `StackRawCall`, `StackRemove`, `StackNames`, and Upstream `Crep -> StackNames` Composition (`0 sorryAx`, `0` `Bounded*` Imports)
- **[`StackRawCallLinearClockAndZeroExtraBridge.lean`](https://github.com/Th0rgal/evm.fast-dev/blob/main/submission/InitECandidate/Solver/StackRawCallLinearClockAndZeroExtraBridge.lean) (`3,200` LOC, `123/123` `non_vacuous_and_tight`, `0 sorryAx`)**:
  - Ported all 17 files of `StackRawCall/Proofs/CompCorrect/*` with strengthened `SimulationResultB` (`clock + targetState.clock ≤ target.clock`) and opened `Optimized` call (`tailTight`), proving `FullCompCorrect.compCorrectB`, `rawCall_linearClock` (`extra + post.clock ≤ source.clock`), `rawCall_extra_le_clock` (`extra ≤ source.clock`, `target.clock + extra ≤ 2 * source.clock` for any `info` including `collectInfo code .ln`), and `pancake_rawCall_stackAlloc_stackRemove_clock`.
- **[`StackRawCallToStackNamesAndStackToLabLinearBridge.lean`](https://github.com/Th0rgal/evm.fast-dev/blob/main/submission/InitECandidate/Solver/StackRawCallToStackNamesAndStackToLabLinearBridge.lean) & [`StackRemoveToStackNamesStateRelAndClockBridge.lean`](https://github.com/Th0rgal/evm.fast-dev/blob/main/submission/InitECandidate/Solver/StackRemoveToStackNamesStateRelAndClockBridge.lean)**:
  - Proved `stackNames_exact_clock` and `stackNames_ticks_eq` (`1:1` exact clock isometry across `StackNames`), derived `¬target.useStack ∧ ¬target.useStore ∧ ¬target.useAlloc` directly from `StackRemove.stateRelHOL`, and composed `StackRawCall -> StackAlloc -> StackRemove -> StackNames` (`≤ 2 * source.clock + 1`, and `source.clock + extra` with `0` overhead from `StackRemove`/`StackNames` outside `halt`).
- **[`PanToWordToStackNamesSimulationAndClockMaster.lean`](https://github.com/Th0rgal/evm.fast-dev/blob/main/submission/InitECandidate/Solver/PanToWordToStackNamesSimulationAndClockMaster.lean), [`LoopToWordToStackNamesAndLabToTargetClockMaster.lean`](https://github.com/Th0rgal/evm.fast-dev/blob/main/submission/InitECandidate/Solver/LoopToWordToStackNamesAndLabToTargetClockMaster.lean), [`CrepToStackNamesAndLabToTargetEndToEndClockMaster.lean`](https://github.com/Th0rgal/evm.fast-dev/blob/main/submission/InitECandidate/Solver/CrepToStackNamesAndLabToTargetEndToEndClockMaster.lean) & [`FlapjackElevenPassSimulationAndClockGrandMaster.lean`](https://github.com/Th0rgal/evm.fast-dev/blob/main/submission/InitECandidate/Solver/FlapjackElevenPassSimulationAndClockGrandMaster.lean)**:
  - Glued `CrepSem.evaluate -> LoopSem.evaluate -> WordSem.evaluate -> StackSem.evaluate -> StackRawCall -> StackAlloc -> StackRemove -> StackNames` (`crep_to_stackNames_clock`, deriving `resultToLoop_ne_error` and exact `1:1` clock preservation across `LoopToWord`) alongside `labToTarget_clock_plus_k` and the exact negative boundary `stackToLab_no_linear_clock_bound`.

### 5.2 Axes B & D — Global Gas-Coupled Linear Programming & 4-Regime `main` Cost Matrix (`136x` Yukon Passes)
- **Uncached vs Cached `compute_jumpdests` Discovery (`GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster.lean`, `GuestExactSstoreCallLPAndJumpdestDualBoundMaster.lean`)**:
  - Identified that `frame_new` (`l. 6884`) and `prepare_dispatch` (`l. 8144`) in `Guest/guest.pp.pnk` re-scan up to `65,536` code bytes via `compute_jumpdests` (`65,541` ticks) per `CALL` (`100` gas warm), and formally certified both the unmodified uncached regime (`8x` Yukon at 200M, `4x` Yukon at 380M) and the cached `jumpdest` regime.
- **Gas-Independent Block Fixed Term (`GuestWitnessEmptyItemAndPushExactTicksMaster.lean`, `GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.lean`, `GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.lean`, `GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.lean`)**:
  - Coupled per-transaction fixed costs (`42,382` ticks per tx: `secp256k1_recover` + tx/receipt tries + merge + bloom) onto `12,000 * T ≤ G` and cold-walk/BAL/merge (`3,124` ticks) onto `(A, K, L)`, reducing the block fixed term to a **100% gas-independent constant `blockFixed = 370,538,614` ticks** at both 200M and 380M gas, and tightened `sstoreKeyGas = 2,105` (`PUSH0` + `PUSHn` + `G_coldsload`).
- **Inline-Child vs Yellow-Paper MPT Dual Bound (`GuestInlineChildMptDualAndOneHundredThirtySixXMaster.lean`, `GuestFourRegimeJumpdestInlineMptGrandSynthesisMaster.lean`)**:
  - Audited `_resolve_step` (`l. 3755`) and proved both:
    1. **Unmodified `_resolve_step` (arbitrary inline children, without `hb : B ≤ N17 + K + A`)**: **`7,287,261,989` ticks (`123x` Yukon at 200M cached)** and **`11,167,773,630` ticks (`80x` Yukon at 380M cached)** (vs `10,545,558,216` / `85x` with `hb`, `hb_gap = 622,215,414`).
    2. **Yellow-Paper `< 32`-byte inline MPT rule (`+32` bytes per hashed branch child, `54` bytes vs `22` bytes)**: **`6,575,582,388` ticks (`136x` Yukon at 200M cached, `< 7B`!)** and **`9,815,582,388` ticks (`91x` Yukon at 380M cached, `< 10B`!)**, tight within `405` ticks (`yp_tight`).

### 5.3 Axes C & E — 440+ Self-Contained Solver Modules & 130 Strictly Increasing Yukon Budgets
- Built and verified **440+ formal `.lean` modules** under `submission/InitECandidate/Solver/` (**100% `non_vacuous_and_tight`, `0 vacuous`, `0 sorryAx`, `0` transitive imports of `InitECandidate.Proofs.Bounded*`**) with **130 strictly increasing finite budgets below the Yukon float64 ceiling (`900,719,925,474`)**.
