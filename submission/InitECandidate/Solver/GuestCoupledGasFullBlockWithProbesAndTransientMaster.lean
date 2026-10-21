import InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster`

Coupling `ts+64` with the storage envelope on the **same** `200M` gas budget.

The average slope `156,088,992,805 / 2,000,000 ≈ 78,044` ticks per 100-gas unit (not `780`: that is
per gas) is not the right exchange rate: the envelope is `blk + linear` with the quadratic block
term `blk ≤ B²/40 ≤ 10¹¹` (`GuestExhaustiveHtabInventoryAndSlopeAbsorption`). The proven exchange
rule is `general_side_regime_absorption`: any side regime of slope `≤ 50,000` ticks/unit sharing the
budget with `B` is absorbed in the `10¹¹` term, and `50,001` is sharp (`threshold_sharp`).

So with `ts+64` at `≤ 10 L` ticks/unit:
* `L ≤ 5,000`: absorbed, block total **unchanged** (`224,985,309,693` / `195,654,540,749`);
* `L > 5,000`: excess `≤ (10 L − 50,000) · 2,000,000` over the subtotal.
-/

namespace InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster (subHeap subMemo sub_vals)
open InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (general_side_regime_absorption S)

/-- Coupled excess of `ts+64` over the subtotal. -/
def excess (L : Nat) : Nat := (10 * L - 50000) * 2000000

def coupled (sub L : Nat) : Nat := sub + excess L

/-- 1. Exchange rate is per unit: `≈ 78,044` ticks/unit average, not `780`. -/
theorem avg_slope : 156088992805 / 2000000 = 78044 ∧ 156088992805 / 200000000 = 780 := by decide

/-- 2. **Absorption**: with `L ≤ 5,000`, `n ≤ u` reverting `TSTORE`s plus storage on one budget stay
in `10¹¹`. -/
theorem absorbed (L n u B blk : Nat) (hL : L ≤ 5000) (hu : n ≤ u) (hS : B + u ≤ 2000000)
    (hblk : 40 * blk ≤ B * B) : blk + 10 * L * n ≤ 100000000000 := by
  have hT : 10 * L * n ≤ 50000 * u := by
    have : 10 * L ≤ 50000 := by omega
    calc 10 * L * n ≤ 50000 * n := Nat.mul_le_mul_right _ this
      _ ≤ 50000 * u := Nat.mul_le_mul_left _ hu
  have := general_side_regime_absorption [(10 * L * n, u)] B blk (by simpa [S] using hS) hblk
    (by simpa using hT)
  simpa using this

/-- 3. No excess for `L ≤ 5,000`; first excess at `5,001`. -/
theorem excess_zero (L : Nat) (h : L ≤ 5000) : excess L = 0 := by
  unfold excess
  have : 10 * L - 50000 = 0 := by omega
  rw [this]

theorem excess_first : excess 5001 = 20000000 := by decide

/-- 4. **For every `L ≤ 5,000` the full block equals the subtotals**. -/
theorem block_unchanged (L : Nat) (h : L ≤ 5000) :
    coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749 := by
  unfold coupled; rw [excess_zero L h, sub_vals.1, sub_vals.2]; decide

/-- 5. The user's `L ≤ 78` is inside the absorbed range. -/
theorem seventy_eight_inside : 78 ≤ 5000 ∧ excess 78 = 0 := by decide

/-- 6. **`1×` coupled, heap**: `L_max = 38,786`. -/
theorem lmax1_heap : coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787 := by decide

/-- 7. **`1×` coupled, memo**: `L_max = 40,253`. -/
theorem lmax1_memo : coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254 := by decide

/-- 8. **`4×` coupled, heap**: `L_max = 5,009` (was `9` additively). -/
theorem lmax4_heap : 4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010 := by
  decide

/-- 9. **`4×` coupled, memo**: `L_max = 6,476` (was `1,476`). -/
theorem lmax4_memo : 4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477 := by
  decide

/-- 10. Unsalted Guest still fails: the attacker run `158,162` exceeds `1×` in both cases. -/
theorem unsalted_still_fails : 40253 < 158162 ∧ yukon < coupled subMemo 158162 ∧
    yukon < coupled subHeap 158162 := by decide

/-- 11. Absorption threshold is sharp at the slope level: `50,001` ticks/unit is not absorbed. -/
theorem sharp : ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B → T ≤ 50001 * U →
    blk + T ≤ 100000000000) :=
  InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption.threshold_sharp

end InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster
