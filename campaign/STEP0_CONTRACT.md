# Step 0 statement contract (frozen for Wave 8 / Step 0)

Deliver `submission/InitECandidate/Solver/PanTerminatingCombinators.lean`, importing
`InitECandidate.Solver.PanTerminatingBounded` (which must stay byte-identical, SHA256 in
`campaign/wave7-frozen-specs/MANIFEST.sha256`). All results are about the existing frozen definitions
`TerminatingRunBounded` / `TerminatingProgBoundedOn` / `TerminatingProgBounded` / `TerminatingFunBounded`.

Required results (names fixed; exact binder shapes are yours, but each must be usable as a compositional rule
and must not add hypotheses that trivialise it, e.g. no hypothesis mentioning the conclusion's run):

1. `evalP_code` — evaluating any `ProgHOL 64` preserves `state.code`.
2. `TerminatingProgBounded.tick` — `.tick` is bounded by `1`.
3. `TerminatingProgBoundedOn.while_measure` (and the unconditional corollary) — a `while` whose body is bounded by
   `B` and which strictly decreases a `Nat` measure `μ` bounded by `M` on every iteration that continues, from states
   satisfying an invariant `P` preserved by the body, is bounded by `(M + 1) * (B + c)` for an explicit constant `c`.
   Must handle `break` / `continue` / `return` / `exception` / `finalFfi` outcomes.
4. `TerminatingProgBoundedOn.while_noRepeat` — a `while` whose body leaves `memory`, `globals` and all non-local
   state unchanged, and whose loop-head configuration ranges over a finite set of size `N` (e.g. `N = 2^64` for one
   word-valued local), is bounded by `(N + 1) * (B + c)`. Prove (or import from Flapjack) the clock-irrelevance
   lemma it needs and state it as a separate theorem `evaluate_clock_irrelevant` (or cite the Flapjack name).
5. `TerminatingProgBounded.call` — a call to `fname` with `TerminatingFunBounded fname B` and matching arity is
   bounded by `B + 1` (+ argument-evaluation constant if needed, stated explicitly).
6. `TerminatingProgBounded.decCall` — `.decCall name shape fname args cont` with `TerminatingFunBounded fname B`
   and `TerminatingProgBounded cont Bc` is bounded by `B + Bc + 1` (+ explicit constant).
7. `On` variants of 5 and 6 where the callee bound is `TerminatingProgBoundedOn`, with the precondition discharged
   at the call site.

Acceptance: `turbo-lean check` passes on the file, `#print axioms` for every result is within the three standard
axioms, and the coordinator plus an independent reviewer confirm the statements are non-vacuous (each is
instantiated once in `campaign/notes/step0-<model>/Smoke.lean` on a real guest loop, e.g. `ceil_log2` for 3 and
`htab_find_leaf` or `trie_walk` for 4).
