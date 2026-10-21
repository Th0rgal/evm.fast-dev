import InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster
import InitECandidate.Solver.ExactTicksNoLocValue6AndFiftyEightBudgetBridge
import InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_174. Full-block arithmetic includes probes at r = 8 and additive ts+64
cost under an explicit collision-run cap. Salt alone is not a deterministic
run-cap proof. The unsalted Guest has no unconditional bound here. Section-6
safety concerns non-stub user sections after LabToTarget, including locValue.
Finite execution certificates remain conditional on the semantic base certificate. -/
namespace InitECandidate.Solver.FullBlockTransientProbesAndSixtyFourBudgetMaster

open InitECandidate.Solver
open GuestFullBlockWithTransientStorageAndProbesMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

abbrev Previous := WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster.portfolio

def portfolio : List Nat := Previous ++ [880629318273, 880629318274]

def sixtyFourClaims : List (Nat × String) :=
  WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster.sixtyTwoClaims ++
  [(880629318273, "{\"K\":880629318273}"),
   (880629318274, "{\"K\":880629318274}")]

def SixtyFourShape : Prop :=
  portfolio.length = 64 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 62 = Previous ∧
  portfolio.drop 62 = [880629318273, 880629318274] ∧
  portfolio.getLast? = some 880629318274 ∧ yukon = 900719925474

def ClaimPayloads : Prop :=
  sixtyFourClaims.length = 64 ∧ sixtyFourClaims.map Prod.fst = portfolio ∧
  (∀ e ∈ sixtyFourClaims, e.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim e.1 e.2 = true) ∧
  sixtyFourClaims.take 62 = WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster.sixtyTwoClaims

/-- Exact eight-probe subtotals in the heap and memoized models. -/
theorem subtotals_non_vacuous_and_tight :
    subHeap = 224985309693 ∧ subMemo = 195654540749 := sub_vals

/-- Fourfold subtotals fit; the next integer factor fails for both. -/
theorem slopes_non_vacuous_and_tight :
    4 * subMemo = 782618162996 ∧ 4 * subMemo < yukon ∧
    4 * subHeap < yukon ∧ yukon < 5 * subMemo ∧ yukon < 5 * subHeap := by decide

/-- The per-unit collision cap yields an attained additive block envelope. -/
theorem transient_ticks_non_vacuous_and_tight :
    (∀ L u t, u ≤ 2000000 → t ≤ 10 * L * u → t ≤ tsTicks L) ∧
    (∀ L, tsTicks L = 20000000 * L ∧ tsTicks L = 10 * L * 2000000) := by
  refine ⟨ts_block, ?_⟩
  intro L
  constructor
  · rfl
  · unfold tsTicks; ring

/-- Exact cap: all admissible L and the first rejected collision run. -/
theorem one_heap_non_vacuous_and_tight :
    (∀ L : Nat, 1 * total subHeap L < yukon ↔ L ≤ 33786) ∧
    1 * total subHeap 33786 < yukon ∧
    yukon ≤ 1 * total subHeap 33787 := by
  constructor
  · intro L
    unfold total tsTicks subHeap yukon
    omega
  · decide

/-- Exact cap: all admissible L and the first rejected collision run. -/
theorem one_memo_non_vacuous_and_tight :
    (∀ L : Nat, 1 * total subMemo L < yukon ↔ L ≤ 35253) ∧
    1 * total subMemo 35253 < yukon ∧
    yukon ≤ 1 * total subMemo 35254 := by
  constructor
  · intro L
    unfold total tsTicks subMemo yukon
    omega
  · decide

/-- Exact cap: all admissible L and the first rejected collision run. -/
theorem four_heap_non_vacuous_and_tight :
    (∀ L : Nat, 4 * total subHeap L < yukon ↔ L ≤ 9) ∧
    4 * total subHeap 9 < yukon ∧
    yukon ≤ 4 * total subHeap 10 := by
  constructor
  · intro L
    unfold total tsTicks subHeap yukon
    omega
  · decide

/-- Exact cap: all admissible L and the first rejected collision run. -/
theorem four_memo_non_vacuous_and_tight :
    (∀ L : Nat, 4 * total subMemo L < yukon ↔ L ≤ 1476) ∧
    4 * total subMemo 1476 < yukon ∧
    yukon ≤ 4 * total subMemo 1477 := by
  constructor
  · intro L
    unfold total tsTicks subMemo yukon
    omega
  · decide

/-- A deterministic cap L ≤ 8 suffices, including the endpoint L = 8. -/
theorem salted_cap_non_vacuous_and_tight :
    (∀ L : Nat, L ≤ 8 →
      4 * total subHeap L < yukon ∧ 4 * total subMemo L < yukon) ∧
    (4 * total subHeap 8 < yukon ∧ 4 * total subMemo 8 < yukon) ∧
    (35253 < 158162 ∧ yukon < total subMemo 158162 ∧
      yukon < total subHeap 158162) := by
  refine ⟨?_, salted_four, unsalted_exceeds⟩
  intro L hL
  constructor
  · exact (four_heap_non_vacuous_and_tight.1 L).2 (by omega)
  · exact (four_memo_non_vacuous_and_tight.1 L).2 (by omega)

/-- JumpOk after label removal excludes jump, jumpCmp, call and locValue
into section 6 in every user section. Exact decode ticks are retained too. -/
theorem no_loc_value_6_and_exact_ticks_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
    (GuestWitnessDecodeExactTicksPerByteAudit.tLeaf = 43 ∧
     GuestWitnessDecodeExactTicksPerByteAudit.tExt = 48 ∧
     GuestWitnessDecodeExactTicksPerByteAudit.tBranch = 326 ∧
     GuestWitnessDecodeExactTicksPerByteAudit.tLeaf ≤ 98 ∧
     GuestWitnessDecodeExactTicksPerByteAudit.tExt ≤ 90 ∧
     GuestWitnessDecodeExactTicksPerByteAudit.tBranch ≤ 448) :=
  ⟨NoLocValue6WitnessDagAndFiftySixBudgetMaster.panToTarget_noStubLoc6_non_vacuous_and_tight,
   NoLocValue6WitnessDagAndFiftySixBudgetMaster.panToTarget_user_noStubLoc6_non_vacuous_and_tight,
   ExactTicksNoLocValue6AndFiftyEightBudgetBridge.exact_ticks_per_node_non_vacuous_and_tight⟩

/-- Strictly increasing 64-budget portfolio with the exact 62-budget prefix. -/
theorem portfolio_non_vacuous_and_tight : SixtyFourShape := by
  unfold SixtyFourShape
  decide

/-- Valid finite JSON payloads preserve the exact 62-claim prefix. -/
theorem payloads_non_vacuous_and_tight : ClaimPayloads := by
  unfold ClaimPayloads
  decide

/-- Only the execution certificates require the explicit base certificate. -/
theorem certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    SixtyFourShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (portfolio_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms subtotals_non_vacuous_and_tight
#print axioms slopes_non_vacuous_and_tight
#print axioms transient_ticks_non_vacuous_and_tight
#print axioms one_heap_non_vacuous_and_tight
#print axioms one_memo_non_vacuous_and_tight
#print axioms four_heap_non_vacuous_and_tight
#print axioms four_memo_non_vacuous_and_tight
#print axioms salted_cap_non_vacuous_and_tight
#print axioms no_loc_value_6_and_exact_ticks_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms payloads_non_vacuous_and_tight
#print axioms certificates_non_vacuous_and_tight

end InitECandidate.Solver.FullBlockTransientProbesAndSixtyFourBudgetMaster
