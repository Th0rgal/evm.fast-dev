import InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis
import InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster`

Block total = gas envelope (no `ts+64`) `156,088,992,805` + MPT/`nodedb` builds `20,036,870,848`
+ witness decode (`31,092,374,808` heap / `10,938,743,528` memo) + `_resolve_step` probes at
`r = 8` (`17,767,071,232` / `8,589,933,568`).

`ts+64` under a collision-run cap `L` (salted hash or any mechanism capping runs): per 100-gas
unit (`TSTORE` costs ≥ 100 gas) the insert find and the `REVERT` `htab_del` shift cost
`≤ 10 · L` ticks (`2` per find step, `3` per shift step, both runs `≤ L`, model of
`GuestTransientStorageSubcallRevertAndAbsorption.lmax_revert`). Over `2,000,000` units:
`≤ 20,000,000 · L`. Added **additively** to the subtotal (conservative: it ignores that `ts+64`
gas is taken from the same `200M` budget as the storage envelope).

Unsalted Guest: `L` is attacker-controlled up to `158,162`; then only the convex coupling
`746,044,000,000` (without `REVERT`) of `GuestTransientStorageGrowthAndJournalAnalysis` holds, and
`REVERT` breaks `1×`. So the bounds below are conditional on a run cap `L`.
-/

namespace InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def subHeap : Nat := 207218238461 + 2 * 8 * 1110441952
def subMemo : Nat := 187064607181 + 2 * 8 * 536870848

/-- `ts+64` ticks under run cap `L` over the block. -/
def tsTicks (L : Nat) : Nat := 20000000 * L

def total (sub L : Nat) : Nat := sub + tsTicks L

/-- 1. Subtotals with probes at `r = 8`. -/
theorem sub_vals : subHeap = 224985309693 ∧ subMemo = 195654540749 := by decide

/-- 2. `4×` of the memo subtotal fits; `4×` heap subtotal fits too; `5×` fails both. -/
theorem sub_slopes : 4 * subMemo = 782618162996 ∧ 4 * subMemo < yukon ∧ 4 * subHeap < yukon ∧
    yukon < 5 * subMemo := by decide

/-- 3. `ts+64` per-unit cost under cap `L`, over `2,000,000` units. -/
theorem ts_block (L u t : Nat) (hu : u ≤ 2000000) (ht : t ≤ 10 * L * u) : t ≤ tsTicks L := by
  unfold tsTicks
  have : 10 * L * u ≤ 10 * L * 2000000 := Nat.mul_le_mul_left _ hu
  have e : 10 * L * 2000000 = 20000000 * L := by ring
  omega

/-- 4. **`1×`, heap case**: `L_max = 33,786`. -/
theorem lmax1_heap : total subHeap 33786 < yukon ∧ yukon ≤ total subHeap 33787 := by decide

/-- 5. **`1×`, memo case**: `L_max = 35,253`. -/
theorem lmax1_memo : total subMemo 35253 < yukon ∧ yukon ≤ total subMemo 35254 := by decide

/-- 6. **`4×`, heap case**: `L_max = 9`. -/
theorem lmax4_heap : 4 * total subHeap 9 < yukon ∧ yukon ≤ 4 * total subHeap 10 := by decide

/-- 7. **`4×`, memo case**: `L_max = 1,476`. -/
theorem lmax4_memo : 4 * total subMemo 1476 < yukon ∧ yukon ≤ 4 * total subMemo 1477 := by decide

/-- 8. Monotone: any `L ≤ L_max` stays under Yukon (`1×`, memo). -/
theorem under_cap_memo (L : Nat) (h : L ≤ 35253) : total subMemo L < yukon := by
  have hs : subMemo = 195654540749 := sub_vals.2
  unfold total tsTicks
  rw [hs]
  have : 20000000 * L ≤ 20000000 * 35253 := Nat.mul_le_mul_left _ h
  have hy : yukon = 900719925474 := rfl
  omega

/-- 9. Monotone at `4×`, memo. -/
theorem under_cap_memo4 (L : Nat) (h : L ≤ 1476) : 4 * total subMemo L < yukon := by
  have hs : subMemo = 195654540749 := sub_vals.2
  unfold total tsTicks
  rw [hs]
  have : 20000000 * L ≤ 20000000 * 1476 := Nat.mul_le_mul_left _ h
  have hy : yukon = 900719925474 := rfl
  omega

/-- 10. Unsalted Guest: the attacker run `158,162` breaks the `1×` cap in both cases. -/
theorem unsalted_exceeds : 35253 < 158162 ∧ yukon < total subMemo 158162 ∧
    yukon < total subHeap 158162 := by decide

/-- 11. Salt target: with expected runs `≤ 8` (salted, load `≤ 1/2`) the full block is `4×`
under Yukon even in the heap case. -/
theorem salted_four : 4 * total subHeap 8 < yukon ∧ 4 * total subMemo 8 < yukon := by decide

end InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster
