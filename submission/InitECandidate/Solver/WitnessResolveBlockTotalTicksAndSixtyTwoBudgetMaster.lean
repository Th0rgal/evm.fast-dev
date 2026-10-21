import InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis
import InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster
import InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_168. Resolve/probe and block arithmetic in the imported model, section-6
safety after LabToTarget, and 62 conditional finite budgets. The block totals
exclude the quadratic ts+64 term: these are not unconditional Guest execution
bounds. Finite execution certificates require the explicit base certificate. -/
namespace InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster

open InitECandidate.Solver
open GuestWitnessResolveAndBlockTotalTicksSynthesis
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge (mptPlusBuild)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

abbrev Previous := WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster.portfolio

def portfolio : List Nat := Previous ++ [880629318271, 880629318272]

def sixtyTwoClaims : List (Nat × String) :=
  WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster.sixtyClaims ++
  [(880629318271, "{\"K\":880629318271}"),
   (880629318272, "{\"K\":880629318272}")]

/-- The heap call bound is attained by the maximal branch population. -/
theorem resolve_heap_non_vacuous_and_tight :
    (∀ B, B ≤ 69402622 → resolveCalls 0 B ≤ 1110441952) ∧
    resolveCalls 0 69402622 = 1110441952 :=
  ⟨resolve_heap, by decide⟩

/-- The DAG call bound is attained by an all-branch population. -/
theorem resolve_memo_non_vacuous_and_tight :
    (∀ E B, E + B ≤ 33554428 → resolveCalls E B ≤ 536870848) ∧
    resolveCalls 0 33554428 = 536870848 :=
  ⟨resolve_memo, by decide⟩

/-- Exact eight-probe ticks in both models, with a positive probe witness. -/
theorem probes_at_eight_non_vacuous_and_tight :
    2 * 8 * resolveCalls 0 69402622 = 17767071232 ∧
    2 * 8 * resolveCalls 0 33554428 = 8589933568 := by decide

/-- Full-population probe thresholds are exact, including rejection of the next run. -/
theorem probe_thresholds_non_vacuous_and_tight :
    (∀ r : Nat, 2 * r * 1110441952 ≤ 693501687013 ↔ r ≤ 312) ∧
    (∀ r : Nat, 2 * r * 536870848 ≤ 713655318293 ↔ r ≤ 664) ∧
    (2 * 312 * 1110441952 ≤ 693501687013 ∧
      693501687013 < 2 * 313 * 1110441952) ∧
    (2 * 664 * 536870848 ≤ 713655318293 ∧
      713655318293 < 2 * 665 * 536870848) := by
  refine ⟨?_, ?_, r_threshold_heap, r_threshold_memo⟩
  · intro r; omega
  · intro r; omega

/-- Heap total and exact Yukon margin, excluding quadratic transient storage. -/
theorem block_total_non_vacuous_and_tight :
    gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
    yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013 := block_total

/-- DAG total and exact Yukon margin, under the same ts+64 exclusion. -/
theorem block_total_memo_non_vacuous_and_tight :
    gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
    yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293 := block_total_memo

/-- Fourfold totals fit; fivefold totals fail. Decode memoization saving is exact. -/
theorem slope_four_non_vacuous_and_tight :
    (4 * 207218238461 < yukon ∧ yukon < 5 * 207218238461 ∧
      4 * 187064607181 = 748258428724 ∧ 4 * 187064607181 < yukon ∧
      yukon < 5 * 187064607181) ∧
    decodeHeap - decodeMemo = 20153631280 := ⟨slope_four, memo_saving⟩

/-- All output sections are stubs or safe; every user section avoids section 6
for jump, jumpCmp, call and locValue, as captured by JumpOk. -/
theorem no_loc_value_6_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.MemoContract :=
  ⟨NoLocValue6WitnessDagAndFiftySixBudgetMaster.panToTarget_noStubLoc6_non_vacuous_and_tight,
   NoLocValue6WitnessDagAndFiftySixBudgetMaster.panToTarget_user_noStubLoc6_non_vacuous_and_tight,
   NoLocValue6WitnessDagAndFiftySixBudgetMaster.memo_non_vacuous_and_tight⟩

def SixtyTwoShape : Prop :=
  portfolio.length = 62 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 60 = Previous ∧
  portfolio.drop 60 = [880629318271, 880629318272] ∧
  portfolio.getLast? = some 880629318272 ∧ yukon = 900719925474

def ClaimPayloads : Prop :=
  sixtyTwoClaims.length = 62 ∧ sixtyTwoClaims.map Prod.fst = portfolio ∧
  (∀ e ∈ sixtyTwoClaims, e.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim e.1 e.2 = true) ∧
  sixtyTwoClaims.take 60 = WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster.sixtyClaims

/-- The entire sixty-budget prefix is retained, followed by exactly two new budgets. -/
theorem portfolio_non_vacuous_and_tight : SixtyTwoShape := by
  unfold SixtyTwoShape
  decide

/-- Sixty-two valid finite JSON claims with the exact sixty-claim prefix. -/
theorem payloads_non_vacuous_and_tight : ClaimPayloads := by
  unfold ClaimPayloads
  decide

/-- Certificates are conditional on the explicit semantic base certificate. -/
theorem certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    SixtyTwoShape ∧ (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨portfolio_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (portfolio_non_vacuous_and_tight.2.2.1 K hK).1 cert

/-- Joint synthesis keeps compiler, witness and budget facts unconditional;
execution certificates retain the base-certificate premise. -/
theorem integrated_master_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.MemoContract ∧
    WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster.ExactTicks ∧
    (∀ B r, B ≤ 69402622 → r ≤ 312 →
      gasEnv + mptPlusBuild + decodeHeap + 2 * r * resolveCalls 0 B < yukon) ∧
    (∀ E B r, E + B ≤ 33554428 → r ≤ 664 →
      gasEnv + mptPlusBuild + decodeMemo + 2 * r * resolveCalls E B < yukon) ∧
    (gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
      yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013) ∧
    (gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
      yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293) ∧
    SixtyTwoShape ∧ ClaimPayloads ∧
    (CertificateAt 1212035192 →
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨no_loc_value_6_non_vacuous_and_tight.1,
    no_loc_value_6_non_vacuous_and_tight.2.1,
    no_loc_value_6_non_vacuous_and_tight.2.2,
    WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster.node_ticks_non_vacuous_and_tight,
    total_with_probes, ?_, block_total_non_vacuous_and_tight,
    block_total_memo_non_vacuous_and_tight, portfolio_non_vacuous_and_tight,
    payloads_non_vacuous_and_tight, fun cert => (certificates_non_vacuous_and_tight cert).2⟩
  intro E B r hEB hr
  have hc := resolve_memo E B hEB
  have hp : 2 * r * resolveCalls E B ≤ 2 * 664 * 536870848 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr) hc
  have ht : gasEnv + mptPlusBuild + decodeMemo + 2 * 664 * 536870848 < yukon := by decide
  omega

#print axioms resolve_heap_non_vacuous_and_tight
#print axioms resolve_memo_non_vacuous_and_tight
#print axioms probes_at_eight_non_vacuous_and_tight
#print axioms probe_thresholds_non_vacuous_and_tight
#print axioms block_total_non_vacuous_and_tight
#print axioms block_total_memo_non_vacuous_and_tight
#print axioms slope_four_non_vacuous_and_tight
#print axioms no_loc_value_6_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms payloads_non_vacuous_and_tight
#print axioms certificates_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster
