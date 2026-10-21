import InitECandidate.Solver.WitnessDagMemoizationAndFiftyFourBudgetBridge
import InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster
import InitECandidate.Solver.GuestMptNodedbAndFiftyFourBudgetBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.WitnessDagMemoizationAndFiftySixBudgetBridge`

Bridge between the 54-budget heap/DAG memoization envelope, the 56-budget master, and the
MPT + nodedb bridge.

* Heap floors: leaf 98, extension 90, branch 448; node cap `345,470,831` on
  `31,092,374,808` bytes; rates `τ ≤ 28` (1×) and `τ ≤ 5` (5×); DAG memoization at
  `33,554,428` nodes and `15,300,819,168` bytes (`τ ≤ 58`).
* Combined MPT + nodedb budget `20,036,870,848`; joint envelope `176,125,863,653`;
  `5× = 880,629,318,265`, margin `20,090,607,209` under Yukon.
* Zero-length extensions stall the walk, a decoded walk stays within 65 iterations, neither
  the compiled program nor a user section jumps or calls section 6, and the 56 budgets grow
  strictly under Yukon `900,719,925,474`.
-/

namespace InitECandidate.Solver.WitnessDagMemoizationAndFiftySixBudgetBridge

open InitECandidate.Solver.WitnessDagMemoizationAndFiftyFourBudgetBridge
open InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster
open InitECandidate.Solver.GuestMptNodedbAndFiftyFourBudgetBridge

/-- 1. Per-node heap floors: one leaf, one extension, one branch. -/
theorem heap_floors_non_vacuous_and_tight : HeapAllocationContract :=
  heap_allocation_non_vacuous_and_tight

/-- 2. Node cap under the heap, tight at pure extensions. -/
theorem nodes_cap_non_vacuous_and_tight : HeapNodesContract :=
  heap_nodes_non_vacuous_and_tight

/-- 3. Tick rates: `τ ≤ 28` at 1×, `τ ≤ 5` at 5×. -/
theorem tau_rates_non_vacuous_and_tight : HeapRateContract :=
  heap_rates_non_vacuous_and_tight

/-- 4. DAG memoization: `≤ 33,554,428` nodes, `15,300,819,168` bytes, threshold `τ ≤ 58`. -/
theorem memo_non_vacuous_and_tight : MemoContract :=
  WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.memo_non_vacuous_and_tight

/-- 5. MPT plus bounded-run nodedb: `20,036,870,848` ticks, between 44× and 45× under Yukon. -/
theorem mpt_nodedb_non_vacuous_and_tight :
    GuestMptNodedbAndTransientStorageBridge.mptPlusBuild = 20036870848 ∧
      44 * GuestMptNodedbAndTransientStorageBridge.mptPlusBuild <
        GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon ≤
        45 * GuestMptNodedbAndTransientStorageBridge.mptPlusBuild :=
  GuestMptNodedbAndFiftyFourBudgetBridge.mpt_plus_nodedb_budget_non_vacuous_and_tight

/-- 6. Joint envelope `176,125,863,653`; at 5× it is `880,629,318,265`, margin `20,090,607,209`. -/
theorem joint_five_non_vacuous_and_tight : BridgeContract :=
  bridge_arithmetic_non_vacuous_and_tight

/-- 7. Absorption of both builds and of a capped `ts+64` run into the joint envelope. -/
theorem absorption_non_vacuous_and_tight : AbsorptionContract :=
  bridge_absorption_non_vacuous_and_tight

/-- 8. Zero-length extensions stall the walk, and a decoded walk stays within 65 iterations. -/
theorem ext_zero_and_walk_non_vacuous_and_tight :
    MptTraversalStateRootAndFiftyFourBudgetMaster.WalkContract ∧
      (MptTraversalStateRootAndFiftyFourBudgetMaster.AccessContract ∧
        MptTraversalStateRootAndFiftyFourBudgetMaster.RootContract) :=
  And.intro WitnessDagMemoizationAndFiftyFourBudgetBridge.ext_zero_non_vacuous_and_tight
    WitnessDagMemoizationAndFiftyFourBudgetBridge.walk_decoded_non_vacuous_and_tight

/-- 9. Neither the compiled program nor a user section jumps or calls section 6. -/
theorem no_stub_jump_non_vacuous_and_tight :
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe ∧
      MptTraversalStateRootAndFiftyFourBudgetMaster.PanUserSafe :=
  And.intro WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.panToTarget_noStubJump_non_vacuous_and_tight
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.panToTarget_user_noStubJump_non_vacuous_and_tight

/-- 10. The 56-budget portfolio grows strictly and stays under Yukon, payloads included. -/
theorem portfolio_56_non_vacuous_and_tight : FiftySixShape ∧ ClaimPayloads :=
  ⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight⟩

end InitECandidate.Solver.WitnessDagMemoizationAndFiftySixBudgetBridge
