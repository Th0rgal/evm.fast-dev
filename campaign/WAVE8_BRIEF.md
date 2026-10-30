# Wave 8 worker brief (read fully before starting)

Repo: `https://github.com/Th0rgal/evm-fast-pilot`, base branch `wave8/base` (on Layr-Labs main `6957805e26`).
Goal of the campaign: first verified finite K for `InitE.Challenge.certificate`. The only open mathematical
obligation is `CoveredSourceTicksConsumedBounded K_pan` (`Solver/UniformSourceClock.lean:201`); target side is
`concreteTargetK` (`Solver/ConcreteStage1To5Transfer.lean`).

## Hard rules (violations = rejected)
1. Edit ONLY `submission/InitECandidate/Solver/**` (plus your own notes under `campaign/notes/<your-track>/`).
   Never touch `Guest/`, `InitE/`, `verifier/`, `submission/InitECandidate/Proofs/`.
2. No `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`, `implemented_by`, `extern`, `unsafe`.
   `#print axioms` of every theorem you deliver must be within `[propext, Classical.choice, Quot.sound]`.
3. Never edit a frozen statement you were given. If you believe it is false, STOP proving it and deliver a Lean
   counterexample (or precise argument) in `campaign/notes/<track>/COUNTEREXAMPLE.md`, status `NOT_FEASIBLE`.
4. Use `turbo-lean` (https://github.com/th0rgal/turbo-lean; check `turbo-lean --help` for exact flags), not raw
   `lake build`, for all checks:
   - per theorem: `turbo-lean agent-step <file> --decl <thm>` / `turbo-lean check <file> --decl <thm> --timeout 300`
   - module: `turbo-lean build InitECandidate.Solver.<Mod> --seed-shards --max-memory-mb 24000`
   - spec pin: `turbo-lean audit-spec` against the statement file you were given.
   Toolchain is `leanprover/lean4:v4.33.1` (see `lean-toolchain`); do not use another version.
   Never build `InitECandidate.Proofs.FullBaseline`, `CheckedCompilerConfig` or `ConcreteOracleWitness` on a 32 GiB VM.
5. Work on your own branch `wave8/<track>-<model>` off `wave8/base`; commit and push early (every meaningful
   verified step) so a reaped VM loses nothing. Signed commits via the provisioned identity.
6. Finish with: branch + head SHA, list of delivered theorems, the exact check commands run and their output
   tail, `#print axioms` output, limitations, and one of `DONE` / `BLOCKED` / `NOT_FEASIBLE`.

## Known facts (verified by coordinator on the 08:13Z snapshot)
- `PanTerminatingBounded.lean` defines `TerminatingRunBounded`, `TerminatingProgBoundedOn`,
  `TerminatingProgBounded`, `TerminatingFunBounded` and only `weaken`/`straight`/`seq`/`ite`/`dec` combinators.
  `while`/`call`/`decCall` exist only for total runs in `PanRunBounded.lean` / `PanRunBoundedExt.lean`.
- `TerminatingProgBounded` quantifies over ALL states with `code = originalRuntimeCode`, so memory-mutating loops
  (e.g. `run_frames`) need a precondition via `TerminatingProgBoundedOn`.
- Read-only loops can be bounded unconditionally by a no-repeat (pigeonhole) argument: a non-timeOut run cannot revisit
  a loop-head (locals) configuration when memory/globals are unchanged, provided evaluation is clock-irrelevant up to
  timeOut. Look for that lemma in Flapjack `Flapjack/Pancake/Semantics/PanSem/EvaluateClock.lean` and
  `PanProps/EvaluateClockSubAssembly.lean` before proving it yourself.
- K budget is loose: any `K_pan` with `32 * K_pan + bootstrapSteps ≤ (10^299-1)/10^4` is acceptable.
