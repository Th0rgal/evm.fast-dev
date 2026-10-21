import InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound
import InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge
import InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_152. Heap and DAG arithmetic, conditional storage absorption, compiler safety,
and 56 finite tiers. Heap costs and memoized costs retain the imported model contracts;
no arithmetic envelope supplies the semantic base certificate or a Guest collision cap. -/
namespace InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster

open InitECandidate.Solver
open GuestWitnessDagMemoizationAndHeapBound
open GuestMptNodedbAndTransientStorageBridge
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

abbrev Previous := MptTraversalStateRootAndFiftyFourBudgetMaster.portfolio

def portfolio : List Nat := Previous ++ [880629318265, 880629318266]

def fiftySixClaims : List (Nat × String) :=
  MptTraversalStateRootAndFiftyFourBudgetMaster.fiftyFourClaims ++
  [(880629318265, "{\"K\":880629318265}"),
   (880629318266, "{\"K\":880629318266}")]

def HeapAllocationContract : Prop :=
  (∀ L E B : Nat, 98 * L + 90 * E + 448 * B = heapOf L E B) ∧
  98 ≤ heapOf 1 0 0 ∧ 90 ≤ heapOf 0 1 0 ∧ 448 ≤ heapOf 0 0 1 ∧
  heapOf 1 0 0 = 98 ∧ heapOf 0 1 0 = 90 ∧ heapOf 0 0 1 = 448

theorem heap_allocation_non_vacuous_and_tight : HeapAllocationContract := by
  exact ⟨fun _ _ _ => rfl, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

def HeapNodesContract : Prop :=
  heapAvail = 31092374808 ∧
  (∀ L E B : Nat, heapOf L E B ≤ heapAvail → L + E + B ≤ 345470831) ∧
  heapOf 0 345470831 0 ≤ heapAvail ∧ heapAvail < heapOf 0 345470832 0

theorem heap_nodes_non_vacuous_and_tight : HeapNodesContract :=
  ⟨heap_avail_val, nodes_by_heap, nodes_by_heap_tight⟩

def HeapRateContract : Prop :=
  (∀ τ bytes : Nat, bytes ≤ heapAvail → τ * bytes ≤ τ * 31092374808) ∧
  (∀ τ : Nat, τ * 31092374808 < yukon ↔ τ ≤ 28) ∧
  (∀ τ : Nat, 5 * (τ * 31092374808) < yukon ↔ τ ≤ 5) ∧
  28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808 ∧
  5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808)

theorem heap_rates_non_vacuous_and_tight : HeapRateContract := by
  refine ⟨decode_heap_bound, ?_, ?_, heap_threshold.1, heap_threshold.2,
    heap_threshold_5x⟩
  · intro τ; unfold GuestJointBlockGasHtabBound.yukon; omega
  · intro τ; unfold GuestJointBlockGasHtabBound.yukon; omega

def MemoContract : Prop :=
  (∀ L E B n : Nat, 4 * n ≤ 134217712 → L + E + B ≤ n → L + E + B ≤ 33554428) ∧
  4 * 33554428 = 134217712 ∧ 134217712 < 4 * 33554429 ∧
  448 * 33554428 + 2 * 134217712 = 15300819168 ∧
  15300819168 < heapAvail ∧ 2 * 15300819168 ≤ heapAvail ∧
  (∀ τ : Nat, τ * 15300819168 < yukon ↔ τ ≤ 58) ∧
  58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168

theorem memo_non_vacuous_and_tight : MemoContract := by
  refine ⟨nodes_memo, by decide, by decide, memo_heap.1, memo_heap.2,
    memo_gain, ?_, memo_threshold⟩
  intro τ; unfold GuestJointBlockGasHtabBound.yukon; omega

def BridgeContract : Prop :=
  mptPlusBuild = 20036870848 ∧ joint = 176125863653 ∧
  19500000000 + 536870848 = 20036870848 ∧
  156088992805 + 20036870848 = 176125863653 ∧
  5 * joint = 880629318265 ∧ 5 * joint < yukon ∧
  yukon - 5 * joint = 20090607209 ∧
  5 * joint + 20090607209 = yukon ∧ ¬ 5 * joint + 20090607210 ≤ yukon

theorem bridge_arithmetic_non_vacuous_and_tight : BridgeContract := by
  exact ⟨sum_val, joint_val, by decide, by decide, joint_five.1,
    by decide, joint_five.2, by decide, by decide⟩

def AbsorptionContract : Prop :=
  (∀ ns nc : Nat, 4 * (ns + nc) ≤ GuestNodedbAndWitnessTableBound.maxInput →
    156088992805 + 19500000000 +
      GuestNodedbAndWitnessTableBound.boundedBuild 8 ns +
      GuestNodedbAndWitnessTableBound.boundedBuild 8 nc ≤ joint) ∧
  (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
    40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
  (∀ L : Nat, 10 * L ≤ 50000 ↔ L ≤ 5000) ∧
  (∀ L : Nat, 5 * L ≤ 50000 ↔ L ≤ 10000) ∧
  10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧
  5 * 10000 = 50000 ∧ 50000 < 5 * 10001 ∧
  4 * (33554428 + 0) = GuestNodedbAndWitnessTableBound.maxInput ∧
  0 + 10 * 5000 * 2000000 = 100000000000

theorem bridge_absorption_non_vacuous_and_tight : AbsorptionContract :=
  ⟨joint_covers, GuestTransientStorageSubcallRevertAndAbsorption.absorbed_with_cap,
   GuestTransientStorageSubcallRevertAndAbsorption.lmax_revert,
   GuestTransientStorageSubcallRevertAndAbsorption.lmax_norevert,
   anchors.1, anchors.2.1, anchors.2.2.1, anchors.2.2.2, by decide, by decide⟩

theorem panToTarget_noStubJump_non_vacuous_and_tight :
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe :=
  MptTraversalStateRootAndFiftyFourBudgetMaster.panToTarget_noStubJump_non_vacuous_and_tight

theorem panToTarget_user_noStubJump_non_vacuous_and_tight :
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanUserSafe :=
  MptTraversalStateRootAndFiftyFourBudgetMaster.panToTarget_user_noStubJump_non_vacuous_and_tight

def FiftySixShape : Prop :=
  portfolio.length = 56 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
  portfolio.take 54 = Previous ∧
  portfolio.drop 54 = [5 * joint, 5 * joint + 1]

theorem portfolio_non_vacuous_and_tight : FiftySixShape := by
  unfold FiftySixShape
  decide

def ClaimPayloads : Prop :=
  fiftySixClaims.length = 56 ∧ fiftySixClaims.map Prod.fst = portfolio ∧
  (∀ e ∈ fiftySixClaims, e.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim e.1 e.2 = true) ∧
  fiftySixClaims.take 54 = MptTraversalStateRootAndFiftyFourBudgetMaster.fiftyFourClaims

theorem payloads_non_vacuous_and_tight : ClaimPayloads := by
  unfold ClaimPayloads
  decide

theorem certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (portfolio_non_vacuous_and_tight.2.2.1 K hK).1 cert

/-- Model arithmetic and compiler safety are unconditional; finite execution certificates
are lifted only from the explicit base certificate. -/
theorem integrated_master_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧
    BridgeContract ∧ AbsorptionContract ∧
    MptTraversalStateRootAndFiftyFourBudgetMaster.FrontendSafe ∧
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanLabSafe ∧
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe ∧
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanUserSafe ∧
    FiftySixShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨heap_allocation_non_vacuous_and_tight, heap_nodes_non_vacuous_and_tight,
   heap_rates_non_vacuous_and_tight, memo_non_vacuous_and_tight,
   bridge_arithmetic_non_vacuous_and_tight, bridge_absorption_non_vacuous_and_tight,
   SelfContainedTransientStorageJournalAndFiftyBudgetSynth.unconditional_pan_to_word_and_word_to_word_no_stub_call_non_vacuous_and_tight,
   MptTraversalStateRootAndFiftyFourBudgetMaster.panToLab_lines_non_vacuous_and_tight,
   panToTarget_noStubJump_non_vacuous_and_tight, panToTarget_user_noStubJump_non_vacuous_and_tight,
   portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight,
   certificates_non_vacuous_and_tight cert⟩

#print axioms heap_allocation_non_vacuous_and_tight
#print axioms heap_nodes_non_vacuous_and_tight
#print axioms heap_rates_non_vacuous_and_tight
#print axioms memo_non_vacuous_and_tight
#print axioms bridge_arithmetic_non_vacuous_and_tight
#print axioms bridge_absorption_non_vacuous_and_tight
#print axioms panToTarget_noStubJump_non_vacuous_and_tight
#print axioms panToTarget_user_noStubJump_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms payloads_non_vacuous_and_tight
#print axioms certificates_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster
