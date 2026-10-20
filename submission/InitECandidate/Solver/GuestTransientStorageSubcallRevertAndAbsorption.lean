import InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption`

Hand transcription of `guest.pp.pnk` (wt-2).

* `op_call` (l.8855): warm access `100` gas (cold `3,000`), memory expansion, then
  `calculate_message_call_gas` (EIP-150: child gets `≤ 63/64` of the remainder). `start_child`
  (l.8481/8494) takes `state_snapshot`; `finish_child` (l.8385/8392) calls `state_restore` on failure.
  Minimal reverting sub-call: `≥ 100` gas plus a constant number of PUSHes.
* After a child `REVERT`, its `ts+64` inserts are deleted, so the next child rebuilds from an empty
  collision run. Hence `m` reverting chunks `k₁ + … + k_m = K` cost `Σ buildTicks kᵢ ≤ buildTicks K`
  (superadditivity of `k(k−1)`): the worst case per tx is one `REVERT` at the end.
* Absorption threshold (hypothetical cap `L` on a collision run — **the current Guest has none**:
  runs reach `158,162`): with `REVERT`, `10 L` ticks per `TSTORE` (≥ 1 unit) gives slope `≤ 50,000`
  iff `L ≤ 5,000`; without `REVERT`, `5 L ≤ 50,000` iff `L ≤ 10,000`. Below the threshold `ts+64`
  is absorbed by `general_side_regime_absorption` into the storage envelope (`156,088,992,805`, `5×`).
-/

namespace InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption

open InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit (buildTicks)
open InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption
  (general_side_regime_absorption)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- 1. Superadditivity of `k(k−1)`. -/
theorem q_super (a b : Nat) : a * (a - 1) + b * (b - 1) ≤ (a + b) * (a + b - 1) := by
  rcases a with _ | a
  · simp
  rcases b with _ | b
  · simp
  have e1 : a + 1 - 1 = a := by omega
  have e2 : b + 1 - 1 = b := by omega
  have e3 : a + 1 + (b + 1) - 1 = a + b + 1 := by omega
  rw [e1, e2, e3]
  nlinarith

/-- 2. Two reverting chunks cost no more than one. -/
theorem build_super (a b : Nat) : buildTicks a + buildTicks b ≤ buildTicks (a + b) := by
  unfold buildTicks
  have := q_super a b
  omega

/-- 3. **Splitting into reverting sub-calls never helps**: `Σ buildTicks kᵢ ≤ buildTicks (Σ kᵢ)`. -/
theorem split_le (l : List Nat) : (l.map buildTicks).sum ≤ buildTicks l.sum := by
  induction l with
  | nil => simp [buildTicks]
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons]
    have := build_super x t.sum
    omega

/-- 4. Strict for `m ≥ 2` non-trivial chunks: `2 + 2` gives `10 < 30`. -/
theorem split_strict : buildTicks 2 + buildTicks 2 = 10 ∧ buildTicks 4 = 30 := by decide

/-- 5. Per-tx worst case with revert: one end-of-tx `REVERT` on `158,162` keys, build + undo. -/
theorem tx_worst_revert : 2 * buildTicks 158162 = 125075300410 := by decide

/-- 6. Halving a tx into two reverting sub-calls loses about half the quadratic term. -/
theorem half_split : 2 * buildTicks 79081 = 31268627400 ∧ buildTicks 158162 = 62537650205 := by
  decide

/-- 7. Threshold with `REVERT`: `10 L ≤ 50,000 ↔ L ≤ 5,000`. -/
theorem lmax_revert (L : Nat) : 10 * L ≤ 50000 ↔ L ≤ 5000 := by omega

/-- 8. Threshold without `REVERT`: `5 L ≤ 50,000 ↔ L ≤ 10,000`. -/
theorem lmax_norevert (L : Nat) : 5 * L ≤ 50000 ↔ L ≤ 10000 := by omega

/-- 9. Both thresholds are sharp. -/
theorem lmax_sharp : 10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001 := by
  decide

/-- 10. **Absorption under a run cap `L ≤ 5,000`**: `n` reverting `TSTORE`s (≥ 1 unit each, ≤ `10 L`
ticks each) share the budget with storage and stay `≤ 10¹¹`. -/
theorem absorbed_with_cap (L n u B blk : Nat) (hL : L ≤ 5000) (hu : n ≤ u)
    (hS : B + u ≤ 2000000) (hblk : 40 * blk ≤ B * B) :
    blk + 10 * L * n ≤ 100000000000 := by
  have hT : 10 * L * n ≤ 50000 * u := by
    have : 10 * L ≤ 50000 := by omega
    calc 10 * L * n ≤ 50000 * n := Nat.mul_le_mul_right _ this
      _ ≤ 50000 * u := Nat.mul_le_mul_left _ hu
  have := general_side_regime_absorption [(10 * L * n, u)] B blk (by simpa [InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption.S] using hS) hblk
    (by simpa using hT)
  simpa using this

/-- 11. The current Guest violates the cap (runs reach `158,162`), and under the cap the envelope
`156,088,992,805` passes `5×`. -/
theorem guest_vs_cap : 5000 < 158162 ∧ 5 * 156088992805 < yukon := by decide

end InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption
