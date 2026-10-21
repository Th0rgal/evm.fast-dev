import InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit
import InitECandidate.Solver.WitnessDagMemoizationAndFiftySixBudgetBridge
import InitECandidate.Solver.GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# ExactTicksNoLocValue6AndFiftyEightBudgetBridge

Wave 5 bridge (W5_166). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.ExactTicksNoLocValue6AndFiftyEightBudgetBridge

open InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit
open InitECandidate.Solver.WitnessDagMemoizationAndFiftySixBudgetBridge
open InitECandidate.Solver.GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Exact per-node decode ticks: leaf 43, extension 48, branch 326, each under its heap floor. -/
theorem exact_ticks_per_node_non_vacuous_and_tight :
    tLeaf = 43 ∧ tExt = 48 ∧ tBranch = 326 ∧
    tLeaf ≤ 98 ∧ tExt ≤ 90 ∧ tBranch ≤ 448 :=
  ⟨rfl, rfl, rfl, tau_leaf, tau_ext, tau_branch⟩

/-- 2. Decode ticks never exceed heap bytes, hence stay under 31_092_374_808 for any heap-fitting
node set. -/
theorem ticks_le_heap_bound_non_vacuous_and_tight (L E B : Nat)
    (h : InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapOf L E B ≤
      InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapAvail) :
    decodeTicks L E B ≤
      InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapOf L E B ∧
    decodeTicks L E B ≤ 31092374808 :=
  ⟨ticks_le_heap L E B, decode_linear L E B h⟩

/-- 3. The all-branch extreme holds at most 69_402_622 branches and decodes under Yukon. -/
theorem all_branch_extreme_non_vacuous_and_tight (B : Nat)
    (h : InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapOf 0 0 B ≤
      InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapAvail) :
    decodeTicks 0 0 B < yukon ∧ B ≤ 69402622 :=
  all_branch B h

/-- 4. Memoized DAG decode: at most 10_938_743_528 ticks, margin 889_781_181_946 under Yukon. -/
theorem decode_memo_value_non_vacuous_and_tight (L E B n : Nat)
    (hn : 4 * n ≤ 134217712) (h : L + E + B ≤ n) :
    decodeTicks L E B ≤ 326 * 33554428 ∧
    326 * 33554428 = 10938743528 ∧ yukon - 326 * 33554428 = 889781181946 :=
  ⟨(decode_memo L E B n hn h).1, decode_memo_val.1, decode_memo_val.2⟩

/-- 5. Combined MPT + nodedb budget: 20_036_870_848 ticks, between 44x and 45x under Yukon. -/
theorem mpt_nodedb_budget_non_vacuous_and_tight :
    InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.mptPlusBuild = 20036870848 ∧
    44 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.mptPlusBuild < yukon ∧
    yukon ≤ 45 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.mptPlusBuild :=
  mpt_nodedb_non_vacuous_and_tight

/-- 6. Joint envelope 176_125_863_653; at 5x it is 880_629_318_265, margin 20_090_607_209. -/
theorem joint_five_times_non_vacuous_and_tight :
    InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 176125863653 ∧
    5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 880629318265 ∧
    yukon - 5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint =
      20090607209 ∧
    5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint < yukon := by
  have hb := bridge_arithmetic_non_vacuous_and_tight
  exact ⟨hb.1.2.1, hb.2.1, hb.1.2.2.2.2.2.2.1, hb.2.2⟩

/-- 7. Neither the compiled target nor a user section jumps or calls section 6. -/
theorem panToTarget_no_stub_jump_non_vacuous_and_tight :
    InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe ∧
    InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.PanUserSafe :=
  ⟨panToTarget_noStubJump_non_vacuous_and_tight, panToTarget_user_noStubJump_non_vacuous_and_tight⟩

/-- 8. The 58-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem fifty_eight_portfolio_under_yukon_non_vacuous_and_tight :
    FiftyEightShape ∧ ClaimPayloads ∧ yukon = 900719925474 :=
  ⟨portfolio_and_payloads_non_vacuous_and_tight.1,
   portfolio_and_payloads_non_vacuous_and_tight.2, rfl⟩

/-- 9. Every one of the 58 budgets carries a finite certificate, from one base certificate. -/
theorem fifty_eight_certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    FiftyEightShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  certificates_non_vacuous_and_tight cert

/-- 10. Grand bridge: exact per-node ticks, memoized decode, 5x MPT+nodedb envelope, section-6
inaccessibility, and the 58-budget portfolio under Yukon. -/
theorem exact_ticks_no_loc_value6_and_fifty_eight_budget_bridge_master_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) (B : Nat)
    (hB : InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapOf 0 0 B ≤
      InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapAvail) :
    (tLeaf = 43 ∧ tExt = 48 ∧ tBranch = 326) ∧
    (326 * 33554428 = 10938743528 ∧ B ≤ 69402622) ∧
    (InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.mptPlusBuild = 20036870848 ∧
      InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 176125863653 ∧
      5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 880629318265 ∧
      yukon - 5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint =
        20090607209) ∧
    InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe ∧
    (FiftyEightShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨rfl, rfl, rfl⟩,
   ⟨decode_memo_val.1, (all_branch B hB).2⟩,
   (by
     have hb := bridge_arithmetic_non_vacuous_and_tight
     exact ⟨hb.1.1, hb.1.2.1, hb.2.1, hb.1.2.2.2.2.2.2.1⟩),
   panToTarget_noStubJump_non_vacuous_and_tight,
   certificates_non_vacuous_and_tight cert⟩

end InitECandidate.Solver.ExactTicksNoLocValue6AndFiftyEightBudgetBridge
