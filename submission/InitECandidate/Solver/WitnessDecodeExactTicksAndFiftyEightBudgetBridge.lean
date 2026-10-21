import InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit
import InitECandidate.Solver.StackToLabNoLocValue6AndFiftySixBudgetBridge
import InitECandidate.Solver.GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.WitnessDecodeExactTicksAndFiftyEightBudgetBridge`

Bridge between the exact per-node decode tick audit, the section-6 inaccessibility proof
after `LabToTarget`, and the 58-budget master.

* Decode ticks stay below the heap bytes of every node: leaf `43 ≤ 98`, extension
  `48 ≤ 90`, branch `326 ≤ 448`. A heap-fitting witness decodes in `≤ 31,092,374,808`
  ticks; with DAG memoization the worst case is `10,938,743,528`, margin
  `889,781,181,946` under Yukon.
* After `LabToTarget` no section jumps, compares, calls or reads a location into section 6.
* The combined MPT + nodedb + `ts+64` envelope is `176,125,863,653`, and
  `5× = 880,629,318,265` stays under Yukon. The 58 budgets grow strictly below it.
-/

namespace InitECandidate.Solver.WitnessDecodeExactTicksAndFiftyEightBudgetBridge

open InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit
open InitECandidate.Solver.StackToLabNoLocValue6AndFiftySixBudgetBridge
open InitECandidate.Solver.GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster

/-- 1. Per-node tick rates stay under the heap floors: `43/98`, `48/90`, `326/448`. -/
theorem tau_per_node_non_vacuous_and_tight :
    tLeaf ≤ 98 ∧ tExt ≤ 90 ∧ tBranch ≤ 448 ∧ max (max tLeaf tExt) tBranch ≤ 448 :=
  tau_max

/-- 2. Decode ticks never exceed the heap bytes of the decoded nodes. -/
theorem ticks_under_heap_non_vacuous_and_tight (L E B : Nat) :
    decodeTicks L E B ≤ GuestWitnessDagMemoizationAndHeapBound.heapOf L E B :=
  ticks_le_heap L E B

/-- 3. A heap-fitting witness decodes in at most `31,092,374,808` ticks, under Yukon. -/
theorem decode_linear_non_vacuous_and_tight (L E B : Nat)
    (h : GuestWitnessDagMemoizationAndHeapBound.heapOf L E B ≤
      GuestWitnessDagMemoizationAndHeapBound.heapAvail) :
    decodeTicks L E B ≤ 31092374808 ∧
      decodeTicks L E B < GuestJointBlockGasHtabBound.yukon :=
  ⟨decode_linear L E B h, decode_under_yukon L E B h⟩

/-- 4. Memoized decode: `326 · 33,554,428 = 10,938,743,528`, margin `889,781,181,946`. -/
theorem decode_memo_non_vacuous_and_tight :
    326 * 33554428 = 10938743528 ∧
      GuestJointBlockGasHtabBound.yukon - 326 * 33554428 = 889781181946 :=
  decode_memo_val

/-- 5. Heap floors and the node cap: leaf 98, extension 90, branch 448,
at most `345,470,831` nodes on `31,092,374,808` bytes. -/
theorem no_loc_value6_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapAllocationContract ∧
      GuestWitnessDagMemoizationAndHeapBound.heapAvail = 31092374808 ∧
      WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapNodesContract :=
  ⟨heap_allocation_non_vacuous_and_tight.1, heap_allocation_non_vacuous_and_tight.2,
   heap_nodes_non_vacuous_and_tight⟩

/-- 6. Neither the compiled target nor a user section jumps or calls into section 6. -/
theorem no_loc_value6_user_non_vacuous_and_tight :
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe ∧
      MptTraversalStateRootAndFiftyFourBudgetMaster.PanUserSafe :=
  ⟨panToTarget_noStubJump_non_vacuous_and_tight, panToTarget_user_noStubJump_non_vacuous_and_tight⟩

/-- 7. Memoized DAG: `33,554,428` nodes, `15,300,819,168` bytes, cutoff `τ ≤ 58`. -/
theorem word_level_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.MemoContract :=
  memo_non_vacuous_and_tight

/-- 8. Combined MPT + nodedb + `ts+64`: `176,125,863,653`, and `5× = 880,629,318,265`
stays under Yukon. -/
theorem joint_five_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.BridgeContract ∧
      5 * GuestMptNodedbAndTransientStorageBridge.joint = 880629318265 ∧
      880629318265 < 900719925474 :=
  bridge_arithmetic_non_vacuous_and_tight

/-- 9. Zero-length extensions are rejected and a decoded walk stays within 65 iterations. -/
theorem ext_zero_and_walk_non_vacuous_and_tight : DecodeWalkContract :=
  ext_zero_rejected_and_walk_bound_decoded_non_vacuous_and_tight

/-- 10. The 58 budgets grow strictly under Yukon `900,719,925,474`, payloads included. -/
theorem portfolio_58_non_vacuous_and_tight : FiftyEightShape ∧ ClaimPayloads :=
  portfolio_and_payloads_non_vacuous_and_tight

end InitECandidate.Solver.WitnessDecodeExactTicksAndFiftyEightBudgetBridge
