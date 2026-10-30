# Wave 8 campaign base (private)

Base: Layr-Labs/evm.fast-dev `main` @ `6957805e26`. Only `submission/InitECandidate/Solver/**`
differs from it (editable paths per `benchmark.json`); `campaign/` is campaign metadata and must be
dropped before any submission.

Contents:
- `submission/InitECandidate/Solver/`: Wave 7 staged tree from mission `0c532a32`
  (`wave7_slim_6957805e26.tar.xz` on `wave7/sync-6957805e26`, 2026-10-30 08:13Z). 106 files,
  21 still containing `sorry` (116 occurrences): 18 `Leaf*` + `ConcreteStage1To3ClockBounds`,
  `ConcreteStage4StackToLabBound`, `ConcreteStage5LabToTargetTransfer`. `Solution.lean` still claims infinity.
- `campaign/wave7-frozen-specs/`: Wave 7 frozen leaf statements + `MANIFEST.sha256` (verified).

Known spec defects (to be repaired in Wave 8, each after a counterexample check):
- `PanTerminatingBounded` has no `while` / `call` / `decCall` combinators for the terminating interface.
- `TerminatingProgBounded` quantifies over arbitrary states, so `run_frames` (memory-mutating loop) is false
  without a `ValidEvmArena`-style precondition; `K_finish_child` is too small for `state_restore`;
  `K_merkleize_progressive` needs re-checking against 64-bit shift wrap.

Internal gate: `turbo-lean audit-spec` + `turbo-lean check --decl` + `turbo-lean pr-verify --mode untrusted`.
`verifier/verify.py` runs once at the end.
