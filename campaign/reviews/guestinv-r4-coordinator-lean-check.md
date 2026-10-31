# Coordinator Lean check of revision 4 (commit 0f8dea8c7)

Run by coordinator mission 9409f9a9 on 2026-10-31 at about 09:15Z, on a fresh clone at 0f8dea8c7. Setup:
- Lean from `lean-toolchain` (4.33.1), installed via elan;
- `lake exe cache get`;
- the `wave8-cone-cache` release extracted;
- `LEAN_NUM_THREADS=4 lake env lean campaign/specs-proposed/GuestInv.lean`.

| Check | Result |
|---|---|
| Exit code | 0 (3 m 45 s) |
| Errors | 0 |
| `declaration uses 'sorry'` warnings | 918 |

`#print axioms` (run on a copy of the file with the prints appended before the final `end`):

```
assembly                     : [propext, Classical.choice, Quot.sound]
assembly_main                : [propext, Classical.choice, Quot.sound]
K_pan_budget                 : [propext]
coveredSourceTicksConsumedBounded_of_terminatingMainOnEntry : [propext, Classical.choice, Quot.sound]
```

`assembly (P : Primitives) : CoveredSourceTicksConsumedBounded K_pan` is proved with no `sorryAx`. The finite-K target therefore follows from a value of `Primitives`, i.e. from proofs of the 918 primitive obligations. Nothing else is admitted between the primitives and the target.
