import InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster
import InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster
import InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredBudgetCampaignBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact arithmetic for the imported conditional guest cost model. The joint LP
bounds assume the stated gas, dirty-node and witness-byte constraints; arithmetic
bounds are not semantic runtime certificates. Finite certificates remain
conditional on the base certificate. -/
namespace InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev oneHundredTwoExplicitFiniteKBugdetTable := ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster.oneHundredTwoExplicitFiniteKBugdetTable

def oneHundredFourExplicitFiniteKBugdetTable : List Nat :=
  oneHundredTwoExplicitFiniteKBugdetTable ++ [891000000000, 892500000000]

abbrev portfolio := oneHundredFourExplicitFiniteKBugdetTable

def OneHundredFourShape : Prop :=
  portfolio.length = 104 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 102 = oneHundredTwoExplicitFiniteKBugdetTable ∧
  portfolio.drop 102 = [891000000000, 892500000000] ∧
  portfolio.getLast? = some 892500000000 ∧ yukon = 900719925474

theorem ratios_non_vacuous_and_tight : jumpdestTicks = 5 ∧ addTicks = 9 ∧ addTicks ≤ 18 * 3 ∧ jumpdestTicks ≤ 18 * 1 ∧
    push31Ticks = 18 * 3 :=
  GuestEvmStepDispatchAndNinetyXMaster.ratios

theorem sload_inside_non_vacuous_and_tight : sloadWarmTicks = 226 ∧ sloadWarmTicks ≤ 18 * 100 :=
  GuestEvmStepDispatchAndNinetyXMaster.sload_inside

theorem joint_non_vacuous_and_tight (a b : Nat) : sloadWarmTicks * a + 18 * b ≤ 18 * (100 * a + b) :=
  GuestEvmStepDispatchAndNinetyXMaster.joint a b

theorem removed_non_vacuous_and_tight : 336 * 2000000 = 672000000 ∧ 450000000 + 336 * 3800000 = 1726800000 :=
  GuestEvmStepDispatchAndNinetyXMaster.removed

theorem main200_slope_non_vacuous_and_tight : main200 = 11546768760 ∧ 78 * main200 < yukon ∧ yukon < 79 * main200 :=
  GuestEvmStepDispatchAndNinetyXMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight : main380 = 17251948659 ∧ 52 * main380 < yukon ∧ yukon < 53 * main380 :=
  GuestEvmStepDispatchAndNinetyXMaster.main380_slope

theorem margins_non_vacuous_and_tight : yukon - 78 * main200 = 71962194 ∧ yukon - 52 * main380 = 3618595206 :=
  GuestEvmStepDispatchAndNinetyXMaster.margins

/-- Strict gain at 200M, compared with the previous unconditional multi-trie row. -/
theorem improvement200_non_vacuous_and_tight :
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 = 12218768760 ∧
    main200 < GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 ∧
    73 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 < yukon ∧
    yukon < 74 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 ∧
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 - main200 = 672000000 := by decide

/-- Strict gain at 380M, with the old passing and failing factors pinned. -/
theorem improvement380_non_vacuous_and_tight :
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 = 18978748659 ∧
    main380 < GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 ∧
    47 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 < yukon ∧
    yukon < 48 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 ∧
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 - main380 = 1726800000 := by decide

theorem one_hundred_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredFourShape := by
  unfold OneHundredFourShape
  decide

theorem one_hundred_four_budget_last_margin_non_vacuous_and_tight :
    oneHundredFourExplicitFiniteKBugdetTable.length = 104 ∧
    oneHundredFourExplicitFiniteKBugdetTable.getLast? = some 892500000000 ∧
    900719925474 - 892500000000 = 8219925474 ∧
    yukon - 892500000000 = 8219925474 := by decide

theorem one_hundred_four_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredFourShape ∧
    (∀ K ∈ oneHundredFourExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms ratios_non_vacuous_and_tight
#print axioms sload_inside_non_vacuous_and_tight
#print axioms joint_non_vacuous_and_tight
#print axioms removed_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms improvement200_non_vacuous_and_tight
#print axioms improvement380_non_vacuous_and_tight
#print axioms one_hundred_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_four_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_four_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster
