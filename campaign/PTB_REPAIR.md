# Proof-only repair of PanTerminatingBounded.lean (wave8/base2)

The Wave 7 frozen file (sha256 e2be511111af2720b2dc4b64ac048005f02ea38a1020ec4d35f9411b39463fb4) did not compile on Lean v4.33.1 + Flapjack 034bb5a1
(found by the Opus 5.5 Step 0 racer, campaign/notes/step0-opus55/NOTES.md). Four proofs failed:
TerminatingProgBounded.seq / .ite / .dec and coveredSourceTicksConsumedBounded_of_terminatingMain.

Repair (proof bodies only):
- seq/ite/dec: intro already unfolds TerminatingRunBounded in this Lean; unfold before intro of
  the non-timeout hypothesis, `dsimp only` the let; `split at hnt ⊢` → `revert hnt; split <;> intro hnt`;
  `.weaken` dot-notation → explicit TerminatingRunBounded.weaken; dsimp projections before omega.
- main bridge: obtain *some* callee via Flapjack lookupCodeHOLFinite_eq_none_iff/_eq_some
  (the old proof insisted on HolFiniteMapExact.empty and got stuck on a dependent match; the
  callee is irrelevant since the body bound is over all states with this code); dropped a
  fixClockHOLFinite rewrite that Flapjack's call equation already performs.

Evidence:
- `lake build InitECandidate.Solver.PanTerminatingBounded`: Build completed successfully (5556 jobs).
- All 22 declarations have byte-identical statements (scripted comparison of header text before `:=`).
- #print axioms for seq, ite, dec, coveredSourceTicksConsumedBounded_of_terminatingMain:
  [propext, Classical.choice, Quot.sound].
- New sha256: 3d9e63e09d52de53584f7c2563ca838ed2a44892f465f60b45129699806f02fe (MANIFEST.sha256 updated; frozen copy updated).
