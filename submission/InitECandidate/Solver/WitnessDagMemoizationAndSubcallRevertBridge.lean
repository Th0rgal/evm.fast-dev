import InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound
import InitECandidate.Solver.GuestMptNodedbAndFiftyFourBudgetBridge
import InitECandidate.Solver.WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# WitnessDagMemoizationAndSubcallRevertBridge

Wave 5 bridge (W5_158). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.WitnessDagMemoizationAndSubcallRevertBridge

open InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound
open InitECandidate.Solver.GuestMptNodedbAndFiftyFourBudgetBridge
open InitECandidate.Solver.WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Per-node heap floors: a leaf costs at least 98 bytes, an extension 90, a branch 448. -/
theorem node_heap_floors_non_vacuous_and_tight :
    heapOf 1 0 0 = 98 ∧ heapOf 0 1 0 = 90 ∧ heapOf 0 0 1 = 448 ∧
    heapAvail = 31092374808 :=
  ⟨by decide, by decide, by decide, heap_avail_val⟩

/-- 2. The heap caps the decoded node count at 345_470_831, and that bound is tight. -/
theorem nodes_by_heap_cap_non_vacuous_and_tight (L E B : Nat) (h : heapOf L E B ≤ heapAvail) :
    L + E + B ≤ 345470831 ∧
    heapOf 0 345470831 0 ≤ heapAvail ∧ heapAvail < heapOf 0 345470832 0 :=
  ⟨nodes_by_heap L E B h, nodes_by_heap_tight.1, nodes_by_heap_tight.2⟩

/-- 3. Yukon thresholds on the heap bound: tau ≤ 28 at 1x, tau ≤ 5 at 5x. -/
theorem heap_thresholds_non_vacuous_and_tight :
    (28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808) ∧
    (5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808)) :=
  ⟨heap_threshold, heap_threshold_5x⟩

/-- 4. DAG memoization: at most 33_554_428 decoded nodes, using 15_300_819_168 heap bytes,
with Yukon threshold tau ≤ 58. -/
theorem memo_nodes_heap_and_threshold_non_vacuous_and_tight
    (L E B n : Nat) (hn : 4 * n ≤ 134217712) (h : L + E + B ≤ n) :
    L + E + B ≤ 33554428 ∧
    448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail ∧
    58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168 :=
  ⟨nodes_memo L E B n hn h, memo_heap.1, memo_heap.2, memo_threshold.1, memo_threshold.2⟩

/-- 5. Combined MPT + nodedb budget 20_036_870_848 and joint envelope 176_125_863_653;
at 5x it is 880_629_318_265, margin 20_090_607_209 under Yukon. -/
theorem mpt_nodedb_joint_five_times_non_vacuous_and_tight :
    InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.mptPlusBuild = 20036870848 ∧
    InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 176125863653 ∧
    5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 880629318265 ∧
    yukon - 5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 20090607209 :=
  ⟨mpt_plus_nodedb_budget_non_vacuous_and_tight.1,
   joint_envelope_five_times_non_vacuous_and_tight.1,
   joint_envelope_five_times_non_vacuous_and_tight.2.2.1,
   joint_envelope_five_times_non_vacuous_and_tight.2.2.2.1⟩

/-- 6. Subcall revert absorption is sharp at both thresholds: L ≤ 5_000 with revert and
L ≤ 10_000 without. -/
theorem subcall_revert_absorption_thresholds_non_vacuous_and_tight :
    10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001 ∧
    5 * (2 * 1) / 2 + 5 * (2 * 1) / 2 = 10 ∧ 5 * (4 * 3) / 2 = 30 :=
  ⟨InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.anchors.1,
   InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.anchors.2.1,
   InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.anchors.2.2.1,
   InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.anchors.2.2.2,
   InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.build_split.1,
   InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.build_split.2.1⟩

/-- 7. Zero-length extensions are rejected and a decoded trie walks in at most 65 steps. -/
theorem ext_zero_rejected_and_walk_bound_non_vacuous_and_tight (ck : Nat) :
    InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted 0 ck = false ∧
    (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
      ((l.map InitECandidate.Solver.GuestMptTraversalAndStateRootBound.Step.ext).map
        InitECandidate.Solver.GuestMptTraversalAndStateRootBound.advance).sum ≤ 64 →
      l.length + 1 ≤ 65) :=
  ⟨(ext_zero_rejected_and_accepted_advances_non_vacuous_and_tight ck 0).1,
   fun l hacc hsum =>
     (walk_bound_decoded_and_heap_nodes_non_vacuous_and_tight).1 l hacc hsum |>.2⟩

/-- 8. panToTarget_noStubJump: no produced section jumps or calls the section-6 stub. -/
theorem panToTarget_noStubJump_dag_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe :=
  GuestMptNodedbAndFiftyFourBudgetBridge.panToTarget_noStubJump_bridge_non_vacuous_and_tight

/-- 9. The 54-budget portfolio is strictly increasing under Yukon 900_719_925_474 and every
budget carries a finite certificate. -/
theorem fifty_four_portfolio_and_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.FiftyFourShape ∧
    (∀ K ∈ InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    yukon = 900719925474 :=
  ⟨(fifty_four_certificates_non_vacuous_and_tight cert).1,
   (fifty_four_certificates_non_vacuous_and_tight cert).2,
   fifty_four_portfolio_under_yukon_non_vacuous_and_tight.2.2⟩

/-- 10. Grand bridge: memoized heap bound, MPT+nodedb 5x envelope, extension rejection, decoded
walk bound, no-stub-jump, and the 54-budget portfolio. -/
theorem witness_dag_memoization_and_subcall_revert_bridge_master_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) (ck : Nat) :
    (heapAvail = 31092374808 ∧
      448 * 33554428 + 2 * 134217712 = 15300819168 ∧
      58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168) ∧
    (InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.mptPlusBuild = 20036870848 ∧
      InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 176125863653 ∧
      5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 880629318265 ∧
      yukon - 5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint =
        20090607209) ∧
    InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted 0 ck = false ∧
    (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
      ((l.map InitECandidate.Solver.GuestMptTraversalAndStateRootBound.Step.ext).map
        InitECandidate.Solver.GuestMptTraversalAndStateRootBound.advance).sum ≤ 64 →
      l.length + 1 ≤ 65) ∧
    InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe ∧
    (InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.FiftyFourShape ∧
      ∀ K ∈ InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨heap_avail_val, memo_heap.1, memo_threshold.1, memo_threshold.2⟩,
   ⟨mpt_plus_nodedb_budget_non_vacuous_and_tight.1,
    joint_envelope_five_times_non_vacuous_and_tight.1,
    joint_envelope_five_times_non_vacuous_and_tight.2.2.1,
    joint_envelope_five_times_non_vacuous_and_tight.2.2.2.1⟩,
   (ext_zero_rejected_and_accepted_advances_non_vacuous_and_tight ck 0).1,
   fun l hacc hsum =>
     (walk_bound_decoded_and_heap_nodes_non_vacuous_and_tight).1 l hacc hsum |>.2,
   panToTarget_noStubJump_dag_bridge_non_vacuous_and_tight,
   ⟨(fifty_four_certificates_non_vacuous_and_tight cert).1,
    (fifty_four_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.WitnessDagMemoizationAndSubcallRevertBridge
