import InitECandidate.Solver.GuestMptNodedbAndFiftyFourBudgetBridge
import InitECandidate.Solver.WitnessDagMemoizationAndFiftyFourBudgetBridge
import InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_160. Integration of the guest MPT/nodedb and DAG bridges, with the exact
56-budget prefix extended to 58 budgets. Heap and storage bounds retain their
model hypotheses; finite execution certificates require the explicit base certificate. -/
namespace InitECandidate.Solver.GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

abbrev Previous := WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.portfolio

def portfolio : List Nat := Previous ++ [880629318267, 880629318268]

def fiftyEightClaims : List (Nat × String) :=
  WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.fiftySixClaims ++
  [(880629318267, "{\"K\":880629318267}"),
   (880629318268, "{\"K\":880629318268}")]

/-- 1. Exact leaf, extension and branch heap floors, with attaining witnesses. -/
theorem heap_allocation_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapAllocationContract ∧
    GuestWitnessDagMemoizationAndHeapBound.heapAvail = 31092374808 :=
  ⟨WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.heap_allocation_non_vacuous_and_tight,
   WitnessDagMemoizationAndFiftyFourBudgetBridge.heap_floors_non_vacuous_and_tight.1⟩

/-- 2. The heap node cap is attained by pure extensions; one extra node exceeds it. -/
theorem heap_nodes_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapNodesContract :=
  WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.heap_nodes_non_vacuous_and_tight

/-- 3. Exact rate cutoffs: 28 at slope one and 5 at slope five. -/
theorem heap_rates_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapRateContract :=
  WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.heap_rates_non_vacuous_and_tight

/-- 4. Memoized DAG: 33,554,428 nodes, 15,300,819,168 bytes, rate cutoff 58. -/
theorem memo_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.MemoContract :=
  WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.memo_non_vacuous_and_tight

/-- 5. MPT plus nodedb and ts+64: exact joint envelope and maximal Yukon margin. -/
theorem bridge_arithmetic_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.BridgeContract ∧
    5 * GuestMptNodedbAndTransientStorageBridge.joint = 880629318265 ∧
    880629318265 < 900719925474 :=
  ⟨WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.bridge_arithmetic_non_vacuous_and_tight,
   GuestMptNodedbAndFiftyFourBudgetBridge.joint_envelope_five_times_non_vacuous_and_tight.2.2.1,
   by decide⟩

/-- 6. Bounded nodedb builds and conditional transient-storage absorption. -/
theorem bridge_absorption_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.AbsorptionContract :=
  WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.bridge_absorption_non_vacuous_and_tight

/-- Accepted extensions advance; decoded walks have at most 65 iterations,
with 64 branches attaining the bound in the traversal contract. -/
def DecodeWalkContract : Prop :=
  (∀ ck : Nat, GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted 0 ck = false) ∧
  (∀ l ck : Nat, GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted l ck = true →
    1 ≤ GuestMptTraversalAndStateRootBound.advance (.ext l)) ∧
  (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
    ((l.map GuestMptTraversalAndStateRootBound.Step.ext).map
      GuestMptTraversalAndStateRootBound.advance).sum ≤ 64 →
    l.length ≤ 64 ∧ l.length + 1 ≤ 65) ∧
  MptTraversalStateRootAndFiftyFourBudgetMaster.WalkContract ∧
  MptTraversalStateRootAndFiftyFourBudgetMaster.AccessContract ∧
  MptTraversalStateRootAndFiftyFourBudgetMaster.RootContract

/-- 7. Zero extensions are rejected and the decoded walk remains bounded. -/
theorem ext_zero_rejected_and_walk_bound_decoded_non_vacuous_and_tight :
    DecodeWalkContract :=
  ⟨GuestWitnessDecodeAndExtensionNibbleAudit.ext_zero_rejected,
   GuestWitnessDecodeAndExtensionNibbleAudit.accepted_advances,
   GuestMptNodedbAndFiftyFourBudgetBridge.walk_bound_decoded_and_heap_nodes_non_vacuous_and_tight.1,
   WitnessDagMemoizationAndFiftyFourBudgetBridge.ext_zero_non_vacuous_and_tight,
   WitnessDagMemoizationAndFiftyFourBudgetBridge.walk_decoded_non_vacuous_and_tight⟩

/-- 8. The compiled target neither jumps nor calls into section 6. -/
theorem panToTarget_noStubJump_non_vacuous_and_tight :
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe :=
  GuestMptNodedbAndFiftyFourBudgetBridge.panToTarget_noStubJump_bridge_non_vacuous_and_tight

/-- 9. User sections neither jump nor call into section 6. -/
theorem panToTarget_user_noStubJump_non_vacuous_and_tight :
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanUserSafe :=
  GuestMptNodedbAndFiftyFourBudgetBridge.panToTarget_user_noStubJump_bridge_non_vacuous_and_tight

def FiftyEightShape : Prop :=
  portfolio.length = 58 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 56 = Previous ∧
  portfolio.drop 56 = [880629318267, 880629318268] ∧
  portfolio.getLast? = some 880629318268 ∧ yukon = 900719925474

def ClaimPayloads : Prop :=
  fiftyEightClaims.length = 58 ∧ fiftyEightClaims.map Prod.fst = portfolio ∧
  (∀ e ∈ fiftyEightClaims, e.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim e.1 e.2 = true) ∧
  fiftyEightClaims.take 56 =
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.fiftySixClaims

/-- 10. All 58 tiers strictly increase below Yukon, preserving all 56 budgets
and payloads, and attaining the specified last tier. -/
theorem portfolio_and_payloads_non_vacuous_and_tight : FiftyEightShape ∧ ClaimPayloads := by
  constructor
  · unfold FiftyEightShape
    decide
  · unfold ClaimPayloads
    decide

/-- 11. Each of the 58 finite certificates is conditional on the base certificate. -/
theorem certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    FiftyEightShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨portfolio_and_payloads_non_vacuous_and_tight.1, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (portfolio_and_payloads_non_vacuous_and_tight.1.2.2.1 K hK).1 cert

/-- 12. Integrated bridge: tight heap and DAG budgets, conditional absorption,
rejection and walk bounds, compiler safety, and all 58 conditional finite claims. -/
theorem integrated_master_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapAllocationContract ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapNodesContract ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapRateContract ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.MemoContract ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.BridgeContract ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.AbsorptionContract ∧
    DecodeWalkContract ∧
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe ∧
    MptTraversalStateRootAndFiftyFourBudgetMaster.PanUserSafe ∧
    FiftyEightShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨heap_allocation_non_vacuous_and_tight.1, heap_nodes_non_vacuous_and_tight,
   heap_rates_non_vacuous_and_tight, memo_non_vacuous_and_tight,
   bridge_arithmetic_non_vacuous_and_tight.1, bridge_absorption_non_vacuous_and_tight,
   ext_zero_rejected_and_walk_bound_decoded_non_vacuous_and_tight,
   panToTarget_noStubJump_non_vacuous_and_tight,
   panToTarget_user_noStubJump_non_vacuous_and_tight,
   portfolio_and_payloads_non_vacuous_and_tight.1,
   portfolio_and_payloads_non_vacuous_and_tight.2,
   (certificates_non_vacuous_and_tight cert).2⟩

#print axioms heap_allocation_non_vacuous_and_tight
#print axioms heap_nodes_non_vacuous_and_tight
#print axioms heap_rates_non_vacuous_and_tight
#print axioms memo_non_vacuous_and_tight
#print axioms bridge_arithmetic_non_vacuous_and_tight
#print axioms bridge_absorption_non_vacuous_and_tight
#print axioms ext_zero_rejected_and_walk_bound_decoded_non_vacuous_and_tight
#print axioms panToTarget_noStubJump_non_vacuous_and_tight
#print axioms panToTarget_user_noStubJump_non_vacuous_and_tight
#print axioms portfolio_and_payloads_non_vacuous_and_tight
#print axioms certificates_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster
