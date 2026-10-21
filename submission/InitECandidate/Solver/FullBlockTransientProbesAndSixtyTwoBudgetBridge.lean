import InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster
import InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyBudgetBridge
import InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.FullBlockTransientProbesAndSixtyTwoBudgetBridge`

Bridge between the full-block total with transient storage and probes, the 60-budget
resolve bridge, and the 62-budget master.

* Subtotals at probe run `r = 8`: `224,985,309,693` without memoization and
  `195,654,540,749` with DAG memoization, whose fourfold `782,618,162,996` stays under Yukon.
* Collision-chain caps on `ts+64` at `20,000,000 · L` ticks: at slope one,
  `L ≤ 33,786` (heap) and `L ≤ 35,253` (memoized); at slope four, `L ≤ 9` and `L ≤ 1,476`.
* The 62 budgets grow strictly under Yukon `900,719,925,474`.
-/

namespace InitECandidate.Solver.FullBlockTransientProbesAndSixtyTwoBudgetBridge

open InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster
open InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster

/-- 1. Subtotals with `r = 8` probes: `224,985,309,693` and `195,654,540,749`. -/
theorem subtotals_non_vacuous_and_tight : subHeap = 224985309693 ∧ subMemo = 195654540749 :=
  sub_vals

/-- 2. Fourfold memoized subtotal: `782,618,162,996`, under Yukon; the heap subtotal is too. -/
theorem subtotal_slopes_non_vacuous_and_tight :
    4 * subMemo = 782618162996 ∧ 4 * subMemo < GuestJointBlockGasHtabBound.yukon ∧
      4 * subHeap < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon < 5 * subMemo :=
  sub_slopes

/-- 3. At slope one, the heap cap is exact: `L = 33,786` fits, `33,787` crosses Yukon. -/
theorem lmax_one_heap_non_vacuous_and_tight :
    total subHeap 33786 < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon ≤ total subHeap 33787 :=
  lmax1_heap

/-- 4. At slope one, the memoized cap is exact: `L = 35,253` fits, `35,254` crosses. -/
theorem lmax_one_memo_non_vacuous_and_tight :
    total subMemo 35253 < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon ≤ total subMemo 35254 :=
  lmax1_memo

/-- 5. At slope four, the heap cap drops to `L = 9`; `10` crosses. -/
theorem lmax_four_heap_non_vacuous_and_tight :
    4 * total subHeap 9 < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon ≤ 4 * total subHeap 10 :=
  lmax4_heap

/-- 6. At slope four, the memoized cap is `L = 1,476`; `1,477` crosses. -/
theorem lmax_four_memo_non_vacuous_and_tight :
    4 * total subMemo 1476 < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon ≤ 4 * total subMemo 1477 :=
  lmax4_memo

/-- 7. Every chain at most the memoized cap stays under Yukon, at both slopes. -/
theorem under_cap_non_vacuous_and_tight (L : Nat) (h1 : L ≤ 35253) (h4 : L ≤ 1476) :
    total subMemo L < GuestJointBlockGasHtabBound.yukon ∧
      4 * total subMemo L < GuestJointBlockGasHtabBound.yukon :=
  ⟨under_cap_memo L h1, under_cap_memo4 L h4⟩

/-- 8. A salt of 8 keeps both fourfold totals under Yukon. -/
theorem salted_non_vacuous_and_tight :
    4 * total subHeap 8 < GuestJointBlockGasHtabBound.yukon ∧
      4 * total subMemo 8 < GuestJointBlockGasHtabBound.yukon :=
  salted_four

/-- 9. Without a salt the per-tx key cap `158,162` exceeds both memoized thresholds. -/
theorem unsalted_non_vacuous_and_tight :
    35253 < 158162 ∧ GuestJointBlockGasHtabBound.yukon < total subMemo 158162 ∧
      GuestJointBlockGasHtabBound.yukon < total subHeap 158162 :=
  unsalted_exceeds

/-- 10. The 62 budgets grow strictly under Yukon `900,719,925,474`, payloads included. -/
theorem portfolio_62_non_vacuous_and_tight : SixtyTwoShape ∧ ClaimPayloads :=
  ⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight⟩

end InitECandidate.Solver.FullBlockTransientProbesAndSixtyTwoBudgetBridge
