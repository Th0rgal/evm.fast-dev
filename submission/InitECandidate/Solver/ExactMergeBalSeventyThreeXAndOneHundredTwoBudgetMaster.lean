import InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster
import InitECandidate.Solver.TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster
import InitECandidate.Solver.TwoItemNodeRehashSeventyXAndNinetyEightBudgetCampaignBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact arithmetic for the imported conditional guest cost model. The joint LP
bounds assume the stated gas, dirty-node and witness-byte constraints; arithmetic
bounds are not semantic runtime certificates. Finite certificates remain
conditional on the base certificate. -/
namespace InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev oneHundredExplicitFiniteKBugdetTable := TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster.oneHundredExplicitFiniteKBugdetTable

def oneHundredTwoExplicitFiniteKBugdetTable : List Nat :=
  oneHundredExplicitFiniteKBugdetTable ++ [888000000000, 889500000000]

abbrev portfolio := oneHundredTwoExplicitFiniteKBugdetTable

def OneHundredTwoShape : Prop :=
  portfolio.length = 102 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 100 = oneHundredExplicitFiniteKBugdetTable ∧
  portfolio.drop 100 = [888000000000, 889500000000] ∧
  portfolio.getLast? = some 889500000000 ∧ yukon = 900719925474

theorem merge_vals_non_vacuous_and_tight : mergeTicks 200000000 = 65422992 ∧ mergeTicks 380000000 = 101802000 ∧
    mergeTicks 380000000 < 500000000 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.merge_vals

theorem bal_vals_non_vacuous_and_tight : balTicks 200000000 = 144000000 ∧ balTicks 380000000 = 273600000 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.bal_vals

theorem entry_charge_non_vacuous_and_tight : 12 + 2 * 8 ≤ 60 ∧ 2100 / 100 = 21 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.entry_charge

theorem no_75_non_vacuous_and_tight : yukon / 75 = 12009599006 ∧ yukon < 75 * main200 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.no_75

theorem main200_slope_non_vacuous_and_tight : main200 = 12218768760 ∧ 73 * main200 < yukon ∧ yukon < 74 * main200 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight : main380 = 18978748659 ∧ 47 * main380 < yukon ∧ yukon < 48 * main380 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380_slope

theorem margins_non_vacuous_and_tight : yukon - 73 * main200 = 8749805994 ∧ yukon - 47 * main380 = 8718738501 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.margins

/-- Strict gain at 200M, compared with the previous unconditional multi-trie row. -/
theorem improvement200_non_vacuous_and_tight :
    GuestTwoItemNodeRehashAndSeventyXMaster.main200 = 12809345768 ∧
    main200 < GuestTwoItemNodeRehashAndSeventyXMaster.main200 ∧
    70 * GuestTwoItemNodeRehashAndSeventyXMaster.main200 < yukon ∧
    yukon < 71 * GuestTwoItemNodeRehashAndSeventyXMaster.main200 ∧
    GuestTwoItemNodeRehashAndSeventyXMaster.main200 - main200 = 590577008 := by decide

/-- Strict gain at 380M, with the old passing and failing factors pinned. -/
theorem improvement380_non_vacuous_and_tight :
    GuestTwoItemNodeRehashAndSeventyXMaster.main380 = 19403346659 ∧
    main380 < GuestTwoItemNodeRehashAndSeventyXMaster.main380 ∧
    46 * GuestTwoItemNodeRehashAndSeventyXMaster.main380 < yukon ∧
    yukon < 47 * GuestTwoItemNodeRehashAndSeventyXMaster.main380 ∧
    GuestTwoItemNodeRehashAndSeventyXMaster.main380 - main380 = 424598000 := by decide

theorem one_hundred_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredTwoShape := by
  unfold OneHundredTwoShape
  decide

theorem one_hundred_two_budget_last_margin_non_vacuous_and_tight :
    oneHundredTwoExplicitFiniteKBugdetTable.length = 102 ∧
    oneHundredTwoExplicitFiniteKBugdetTable.getLast? = some 889500000000 ∧
    900719925474 - 889500000000 = 11219925474 ∧
    yukon - 889500000000 = 11219925474 := by decide

theorem one_hundred_two_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwoShape ∧
    (∀ K ∈ oneHundredTwoExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms merge_vals_non_vacuous_and_tight
#print axioms bal_vals_non_vacuous_and_tight
#print axioms entry_charge_non_vacuous_and_tight
#print axioms no_75_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms improvement200_non_vacuous_and_tight
#print axioms improvement380_non_vacuous_and_tight
#print axioms one_hundred_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_two_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_two_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster
