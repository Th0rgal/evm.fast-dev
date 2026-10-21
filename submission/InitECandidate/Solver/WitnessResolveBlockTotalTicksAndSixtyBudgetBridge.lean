import InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis
import InitECandidate.Solver.WitnessDecodeExactTicksAndFiftyEightBudgetBridge
import InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyBudgetBridge`

Bridge between the block-total tick synthesis, the exact per-node decode rates, and the
60-budget master.

* `_resolve_step` calls: `≤ 1,110,441,952` on the full heap, `≤ 536,870,848` with DAG
  memoization. At probe run `r = 8` that is `17,767,071,232` and `8,589,933,568` ticks,
  and the Yukon margin holds up to `r ≤ 312` (heap) and `r ≤ 664` (memoized).
* Block total excluding the quadratic `ts+64` term: `207,218,238,461` (margin
  `693,501,687,013`), memoized `187,064,607,181` (margin `713,655,318,293`), and
  `4 × 187,064,607,181 = 748,258,428,724` stays under Yukon.
* Per-node rates stay strictly below one byte per tick (`43/98`, `48/90`, `326/448`), and
  the 60 budgets grow strictly under Yukon `900,719,925,474`.
-/

namespace InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyBudgetBridge

open InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis
open InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster

/-- 1. Heap resolves: `≤ 69,402,622` branches give `≤ 1,110,441,952` calls. -/
theorem resolve_heap_non_vacuous_and_tight (B : Nat) (h : B ≤ 69402622) :
    resolveCalls 0 B ≤ 1110441952 :=
  resolve_heap B h

/-- 2. Memoized resolves: any mix of extensions and branches totalling `≤ 33,554,428`
gives `≤ 536,870,848` calls. -/
theorem resolve_memo_non_vacuous_and_tight (E B : Nat) (h : E + B ≤ 33554428) :
    resolveCalls E B ≤ 536870848 :=
  resolve_memo E B h

/-- 3. Probe ticks at `r = 8`: `17,767,071,232` on the heap, `8,589,933,568` memoized. -/
theorem probes_at_8_non_vacuous_and_tight :
    2 * 8 * 1110441952 = 17767071232 ∧ 2 * 8 * 536870848 = 8589933568 :=
  probe_at_8

/-- 4. Block total without memoization: `207,218,238,461`, margin `693,501,687,013`. -/
theorem block_total_non_vacuous_and_tight :
    gasEnv + GuestMptNodedbAndTransientStorageBridge.mptPlusBuild + decodeHeap = 207218238461 ∧
      GuestJointBlockGasHtabBound.yukon -
        (gasEnv + GuestMptNodedbAndTransientStorageBridge.mptPlusBuild + decodeHeap) =
        693501687013 :=
  block_total

/-- 5. Block total with memoization: `187,064,607,181`, margin `713,655,318,293`. -/
theorem block_total_memo_non_vacuous_and_tight :
    gasEnv + GuestMptNodedbAndTransientStorageBridge.mptPlusBuild + decodeMemo = 187064607181 ∧
      GuestJointBlockGasHtabBound.yukon -
        (gasEnv + GuestMptNodedbAndTransientStorageBridge.mptPlusBuild + decodeMemo) =
        713655318293 :=
  block_total_memo

/-- 6. Slope `4×` fits; the memoized total gives `748,258,428,724`. -/
theorem slope_four_non_vacuous_and_tight :
    4 * 207218238461 < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon < 5 * 207218238461 ∧
      4 * 187064607181 = 748258428724 ∧ 4 * 187064607181 < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon < 5 * 187064607181 :=
  slope_four

/-- 7. Probe-run thresholds: `r ≤ 312` on the heap, `r ≤ 664` memoized, both sharp. -/
theorem r_thresholds_non_vacuous_and_tight :
    (2 * 312 * 1110441952 ≤ 693501687013 ∧ 693501687013 < 2 * 313 * 1110441952) ∧
      (2 * 664 * 536870848 ≤ 713655318293 ∧ 713655318293 < 2 * 665 * 536870848) :=
  ⟨r_threshold_heap, r_threshold_memo⟩

/-- 8. Per-node rates stay strictly under one heap byte per tick: `43/98`, `48/90`, `326/448`. -/
theorem tau_per_node_non_vacuous_and_tight :
    WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster.ExactTicks :=
  node_ticks_non_vacuous_and_tight

/-- 9. Decode ticks stay under the heap bytes, and a heap-fitting witness decodes in
`≤ 31,092,374,808` ticks. -/
theorem ticks_under_heap_non_vacuous_and_tight :
    (∀ L E B,
      GuestWitnessDecodeExactTicksPerByteAudit.decodeTicks L E B ≤
        GuestWitnessDagMemoizationAndHeapBound.heapOf L E B) ∧
      (∀ L E B,
        GuestWitnessDagMemoizationAndHeapBound.heapOf L E B ≤
          GuestWitnessDagMemoizationAndHeapBound.heapAvail →
        GuestWitnessDecodeExactTicksPerByteAudit.decodeTicks L E B ≤ 31092374808) ∧
      GuestWitnessDecodeExactTicksPerByteAudit.decodeTicks 1 0 0 = 43 ∧
      GuestWitnessDecodeExactTicksPerByteAudit.decodeTicks 0 1 0 = 48 ∧
      GuestWitnessDecodeExactTicksPerByteAudit.decodeTicks 0 0 1 = 326 :=
  ticks_le_heap_non_vacuous_and_tight

/-- 10. The 60 budgets grow strictly under Yukon `900,719,925,474`, payloads included. -/
theorem portfolio_60_non_vacuous_and_tight : SixtyShape ∧ ClaimPayloads :=
  ⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight⟩

end InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyBudgetBridge
