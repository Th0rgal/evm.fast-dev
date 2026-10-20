import InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis`

Hand transcription of `guest.pp.pnk` (wt-2).

Journal (no `state_checkpoint` / `state_commit` exist):
* `state_snapshot` (l.5478) returns `journal_n`; `state_restore(snap)` (l.5481) pops entries down to
  `snap`, `htab_set` if `present`, else `htab_del`. Commit = do nothing (entries stay).
* Callers: `start_child` (l.8481/8494) snapshots, `finish_child` (l.8385/8392) restores on child
  failure, `process_message` (l.8538–8561), `process_create_message` (l.8587–8608),
  `frame_epilogue` (l.8363). A tx-level failure restores to the tx-start snapshot.
* `journal_n = 0` in `state_fresh_tx` and `journal_cap = 524,288` (l.5413).
  An entry is undone at most once: after `state_restore` it is popped.

`htab_find_slot` loop step: `ld8 used`, `memeq` call (52 bytes: ≤ 6 loads), index update:
1 loop tick + 1 call tick = **2 ticks** (calls 1 tick, loads 0). `htab_del` backward-shift step:
1 loop tick + `htab_hash` call (1) + `memcpy` call (1) = **3 ticks**.

Convex coupling: per tx, `k` transient keys cost `5k(k−1)/2` ticks for `≥ 106k` gas, so ticks per
100-gas unit `≤ 250(k − 1)/106 ≤ 373,022` (`k ≤ 158,162`). Storage regime slope `≤ 75,965`.
So under one budget `G_tstore + G_storage ≤ 200M` everything is `≤ 373,022 · 2,000,000`
(`746,044,000,000`), versus the additive `740.95 G + 156.09 G`. Lower witness (all gas on `ts+64`):
`740,946,409,660`. `1×` passes Yukon with margin `150,516,361,240`; `2×` fails.
-/

namespace InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis

open InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit (buildTicks)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Journal model: list of `present` flags; restore actions. -/
def restoreDels (j : List Bool) : Nat := j.count false

/-- 1. Journal: a fresh key journaled absent is undone by `htab_del`, a rewrite by `htab_set`. -/
theorem journal_actions : restoreDels [false, true, false] = 2 ∧ restoreDels [true, true] = 0 := by
  decide

/-- 2. Restore pops each entry once: deletes ≤ journal length ≤ `journal_cap`. -/
theorem restore_once (j : List Bool) (h : j.length ≤ 524288) : restoreDels j ≤ 524288 :=
  le_trans (List.count_le_length) h

/-- 3. Per-step ticks of the two probe loops. -/
theorem step_ticks : (1 + 1 : Nat) = 2 ∧ (1 + 1 + 1 : Nat) = 3 := by decide

/-- 4. Per-unit slope of `ts+64` in a tx with `k ≥ 1` keys: `100·5k(k−1)/2 ≤ 373,022 · 106k / …`,
stated as `250 (k − 1) ≤ 106 · 373,022` for `k ≤ 158,162`. -/
theorem tstore_slope (k : Nat) (hk : k ≤ 158162) : 250 * (k - 1) ≤ 106 * 373022 := by omega

/-- 5. The slope constant is tight (`373,021` fails at the cap). -/
theorem tstore_slope_tight : ¬ (250 * (158162 - 1) ≤ 106 * 373021) := by decide

/-- 6. Per-tx ticks against gas: `100 · buildTicks k ≤ 373,022 · 106 k`. -/
theorem tstore_per_gas (k : Nat) (hk : k ≤ 158162) : 100 * buildTicks k ≤ 373022 * (106 * k) := by
  unfold buildTicks
  have h1 : 250 * (k - 1) ≤ 106 * 373022 := by omega
  have h2 : 250 * (k - 1) * k ≤ 106 * 373022 * k := Nat.mul_le_mul_right _ h1
  have h3 : 100 * (5 * (k * (k - 1)) / 2) ≤ 250 * (k * (k - 1)) := by omega
  have e : 250 * (k * (k - 1)) = 250 * (k - 1) * k := by ring
  have e2 : 106 * 373022 * k = 373022 * (106 * k) := by ring
  omega

/-- 7. Storage-regime slope (`S/20 + 13 M/84`) is far below the transient slope. -/
theorem storage_slope : 2000000 / 20 / 2 + 13 * 167772 / 84 + 1 = 75965 ∧ 75965 < 373022 := by decide

/-- 8. **Convex coupling**: two regimes with slopes `≤ 373,022` on `u₁ + u₂ ≤ 2,000,000` units. -/
theorem coupled_le (u1 u2 t1 t2 : Nat) (hu : u1 + u2 ≤ 2000000)
    (h1 : t1 ≤ 373022 * u1) (h2 : t2 ≤ 373022 * u2) : t1 + t2 ≤ 746044000000 := by omega

/-- 9. Lower witness (all gas on `ts+64`) and gap to the coupled bound. -/
theorem bracket :
    11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
      746044000000 - 740946409660 = 5097590340 := by decide

/-- 10. Coupled bound is below the additive sum `740.95 G + 156.09 G`. -/
theorem coupled_vs_additive : 746044000000 < 740946409660 + 156088992805 := by decide

/-- 11. With linear terms (`4,159,564,234`): `1×` passes Yukon, `2×` fails. -/
theorem slopes :
    746044000000 + 4159564234 < yukon ∧
      yukon - (746044000000 + 4159564234) = 150516361240 ∧
      yukon < 2 * (740946409660 + 4159564234) := by decide

end InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis
