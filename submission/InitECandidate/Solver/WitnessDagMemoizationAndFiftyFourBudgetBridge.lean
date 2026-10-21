import InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound
import InitECandidate.Solver.WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge
import InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.WitnessDagMemoizationAndFiftyFourBudgetBridge`

Arithmetic bridge between three certified modules:

* `GuestWitnessDagMemoizationAndHeapBound`: per-node heap floors (leaf 98, extension 90,
  branch 448), `heapAvail = 31,092,374,808`, node cap `345,470,831`, tick-rate thresholds
  `τ ≤ 28` (1×) and `τ ≤ 5` (5×), and the DAG-memoized cap `33,554,428` nodes at
  `15,300,819,168` bytes (`τ ≤ 58`).
* `WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge`: zero-length extensions are rejected
  and a decoded walk stays `≤ 65`.
* `MptTraversalStateRootAndFiftyFourBudgetMaster`: the walk contract, the absence of jumps
  and calls into section 6, and a strictly increasing portfolio of 54 budgets under Yukon
  `900,719,925,474`.
-/

namespace InitECandidate.Solver.WitnessDagMemoizationAndFiftyFourBudgetBridge

open InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound
open InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- 1. Heap available and the per-node floors: one leaf, one extension, one branch. -/
theorem heap_floors_non_vacuous_and_tight :
    heapAvail = 31092374808 ∧ heapOf 1 0 0 = 98 ∧ heapOf 0 1 0 = 90 ∧ heapOf 0 0 1 = 448 := by
  refine ⟨heap_avail_val, ?_, ?_, ?_⟩ <;> decide

/-- 2. Node cap under the heap, tight at pure extensions. -/
theorem nodes_cap_non_vacuous_and_tight (L E B : Nat) (h : heapOf L E B ≤ heapAvail) :
    L + E + B ≤ 345470831 ∧
      heapOf 0 345470831 0 ≤ heapAvail ∧ heapAvail < heapOf 0 345470832 0 :=
  ⟨nodes_by_heap L E B h, nodes_by_heap_tight⟩

/-- 3. Tick rate `τ ≤ 28` stays under Yukon; `τ = 29` crosses it. -/
theorem tau_one_non_vacuous_and_tight :
    28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808 := heap_threshold

/-- 4. At slope `5×`, the rate drops to `τ ≤ 5`. -/
theorem tau_five_non_vacuous_and_tight :
    5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808) := heap_threshold_5x

/-- 5. DAG memoization: `≤ 33,554,428` nodes, `15,300,819,168` bytes, threshold `τ ≤ 58`. -/
theorem memo_non_vacuous_and_tight (L E B n : Nat) (hn : 4 * n ≤ 134217712)
    (h : L + E + B ≤ n) :
    L + E + B ≤ 33554428 ∧
      448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail ∧
      58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168 :=
  ⟨nodes_memo L E B n hn h, memo_heap.1, memo_heap.2, memo_threshold⟩

/-- 6. Zero-length extensions stall the walk, and 64 branches reach exactly 65 iterations. -/
theorem ext_zero_non_vacuous_and_tight : WalkContract := traversal_non_vacuous_and_tight

/-- 7. Accesses and the state root stay inside the decoded walk bound. -/
theorem walk_decoded_non_vacuous_and_tight : AccessContract ∧ RootContract :=
  ⟨accesses_non_vacuous_and_tight, state_root_non_vacuous_and_tight⟩

/-- 8. The compiled program neither jumps nor calls into section 6, and neither does a
user section. -/
theorem no_stub_jump_non_vacuous_and_tight : PanTargetSafe ∧ PanUserSafe :=
  ⟨panToTarget_noStubJump_non_vacuous_and_tight,
   panToTarget_user_noStubJump_non_vacuous_and_tight⟩

/-- 9. The 54-budget portfolio is strictly increasing and stays under Yukon. -/
theorem portfolio_54_non_vacuous_and_tight :
    portfolio.length = 54 ∧ portfolio.Pairwise (· < ·) ∧
      (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) := by
  have h := portfolio_non_vacuous_and_tight
  refine ⟨h.1, h.2.1, ?_⟩
  intro K hK
  have hk := h.2.2.1 K hK
  exact ⟨hk.1, lt_of_lt_of_eq hk.2 rfl⟩

/-- 10. Claim payloads match the portfolio and each finite claim is valid. -/
theorem payloads_54_non_vacuous_and_tight : ClaimPayloads := payloads_non_vacuous_and_tight

end InitECandidate.Solver.WitnessDagMemoizationAndFiftyFourBudgetBridge
