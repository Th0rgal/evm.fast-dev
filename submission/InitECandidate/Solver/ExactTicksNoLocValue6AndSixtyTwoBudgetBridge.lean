import InitECandidate.Solver.ExactTicksNoLocValue6AndFiftyEightBudgetBridge
import InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster
import InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# ExactTicksNoLocValue6AndSixtyTwoBudgetBridge

Wave 5 bridge (W5_173). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.ExactTicksNoLocValue6AndSixtyTwoBudgetBridge

open InitECandidate.Solver.ExactTicksNoLocValue6AndFiftyEightBudgetBridge
open InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster
open InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Exact per-node decode ticks: leaf 43, extension 48, branch 326. -/
theorem exact_ticks_per_node_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tLeaf = 43 ∧
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tExt = 48 ∧
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tBranch = 326 :=
  ⟨exact_ticks_per_node_non_vacuous_and_tight.1,
   exact_ticks_per_node_non_vacuous_and_tight.2.1,
   exact_ticks_per_node_non_vacuous_and_tight.2.2.1⟩

/-- 2. Decode ticks stay under the heap bytes, hence under 31_092_374_808. -/
theorem ticks_le_heap_bridge_non_vacuous_and_tight (L E B : Nat)
    (h : InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapOf L E B ≤
      InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapAvail) :
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.decodeTicks L E B ≤
      31092374808 :=
  (ticks_le_heap_bound_non_vacuous_and_tight L E B h).2

/-- 3. Memoized DAG decode is exactly 10_938_743_528 ticks. -/
theorem decode_memo_val_bridge_non_vacuous_and_tight (L E B n : Nat)
    (hn : 4 * n ≤ 134217712) (h : L + E + B ≤ n) :
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.decodeTicks L E B ≤
      326 * 33554428 ∧
    326 * 33554428 = 10938743528 :=
  ⟨(decode_memo_value_non_vacuous_and_tight L E B n hn h).1,
   (decode_memo_value_non_vacuous_and_tight L E B n hn h).2.1⟩

/-- 4. Resolve-step subtotals at r = 8: 224_985_309_693 without memoization,
195_654_540_749 with DAG memoization. -/
theorem resolve_step_subtotals_at_eight_non_vacuous_and_tight :
    subHeap = 224985309693 ∧ subMemo = 195654540749 ∧ subMemo < subHeap :=
  ⟨sub_vals.1, sub_vals.2, by decide⟩

/-- 5. ts+64 thresholds at 1x: L ≤ 33_786 on the heap model, L ≤ 35_253 on the memoized model. -/
theorem lmax_one_times_non_vacuous_and_tight :
    total subHeap 33786 < yukon ∧ yukon ≤ total subHeap 33787 ∧
    total subMemo 35253 < yukon ∧ yukon ≤ total subMemo 35254 :=
  ⟨lmax1_heap.1, lmax1_heap.2, lmax1_memo.1, lmax1_memo.2⟩

/-- 6. ts+64 thresholds at 4x: L ≤ 9 on the heap model, L ≤ 1_476 on the memoized model. -/
theorem lmax_four_times_non_vacuous_and_tight :
    4 * total subHeap 9 < yukon ∧ yukon ≤ 4 * total subHeap 10 ∧
    4 * total subMemo 1476 < yukon ∧ yukon ≤ 4 * total subMemo 1477 :=
  ⟨lmax4_heap.1, lmax4_heap.2, lmax4_memo.1, lmax4_memo.2⟩

/-- 7. Resolve-call bounds: at most 1_110_441_952 calls on the heap, 536_870_848 memoized. -/
theorem resolve_call_bounds_non_vacuous_and_tight :
    (∀ B, B ≤ 69402622 →
      InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis.resolveCalls 0 B ≤
        1110441952) ∧
    (∀ E B, E + B ≤ 33554428 →
      InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis.resolveCalls E B ≤
        536870848) :=
  ⟨resolve_heap_non_vacuous_and_tight.1, resolve_memo_non_vacuous_and_tight.1⟩

/-- 8. The 62-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem sixty_two_portfolio_under_yukon_non_vacuous_and_tight :
    SixtyTwoShape ∧ ClaimPayloads ∧ yukon = 900719925474 :=
  ⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight, rfl⟩

/-- 9. Every one of the 62 budgets carries a finite certificate, from one base certificate. -/
theorem sixty_two_certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    SixtyTwoShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  certificates_non_vacuous_and_tight cert

/-- 10. Grand bridge: exact ticks, memoized decode, resolve-step subtotals, both ts+64
thresholds, and the 62-budget portfolio under Yukon. -/
theorem exact_ticks_no_loc_value6_and_sixty_two_budget_bridge_master_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tLeaf = 43 ∧
      InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tExt = 48 ∧
      InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tBranch = 326 ∧
      326 * 33554428 = 10938743528) ∧
    (subHeap = 224985309693 ∧ subMemo = 195654540749) ∧
    (total subHeap 33786 < yukon ∧ total subMemo 35253 < yukon ∧
      4 * total subHeap 9 < yukon ∧ 4 * total subMemo 1476 < yukon) ∧
    (SixtyTwoShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨exact_ticks_per_node_non_vacuous_and_tight.1,
    exact_ticks_per_node_non_vacuous_and_tight.2.1,
    exact_ticks_per_node_non_vacuous_and_tight.2.2.1,
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.decode_memo_val.1⟩,
   ⟨sub_vals.1, sub_vals.2⟩,
   ⟨lmax1_heap.1, lmax1_memo.1, lmax4_heap.1, lmax4_memo.1⟩,
   certificates_non_vacuous_and_tight cert⟩

end InitECandidate.Solver.ExactTicksNoLocValue6AndSixtyTwoBudgetBridge
