import InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster
import InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! The uncached jumpdest scans invalidate the previous global gas estimate for
the current Guest. The 106x/75x arithmetic explicitly assumes the proposed
per-code jumpdest cache and the previous model's remaining assumptions.
Finite semantic certificates remain conditional on the base certificate;
none is inferred from the arithmetic cost estimates. -/
namespace InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixXAndOneHundredEightBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev Previous := GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster.oneHundredSixExplicitFiniteKBugdetTable

def oneHundredEightExplicitBudgets : List Nat := Previous ++ [896500000000, 898500000000]
abbrev portfolio := oneHundredEightExplicitBudgets

def OneHundredEightShape : Prop :=
  portfolio.length = 108 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 106 = Previous ∧
  portfolio.drop 106 = [896500000000, 898500000000] ∧
  portfolio.getLast? = some 898500000000 ∧ yukon = 900719925474

theorem charges_ok_non_vacuous_and_tight : sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
    sloadBaseTicks + 7 * 28 ≤ 18 * 100 :=
  GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster.charges_ok

theorem scan_ratio_non_vacuous_and_tight : 18 * callGas < maxCode ∧ 28 * (18 * callGas) < maxCode :=
  GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster.scan_ratio

theorem attack200_non_vacuous_and_tight : jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon ∧
    yukon < 9 * jumpdestTicks 200000000 :=
  GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster.attack200

theorem attack380_non_vacuous_and_tight : jumpdestTicks 380000000 = 197648252928 ∧ 4 * jumpdestTicks 380000000 < yukon ∧
    yukon < 5 * jumpdestTicks 380000000 :=
  GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster.attack380

theorem previous_broken_non_vacuous_and_tight : 12 * 8298113205 < jumpdestTicks 200000000 :=
  GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster.previous_broken

theorem cached_non_vacuous_and_tight : 8298113205 + 134217712 = 8432330917 ∧ 106 * 8432330917 < yukon ∧
    yukon < 107 * 8432330917 ∧ 11858770499 + 134217712 = 11992988211 ∧
    75 * 11992988211 < yukon ∧ yukon < 76 * 11992988211 :=
  GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster.cached

theorem tx_count_non_vacuous_and_tight : 200000000 / 12000 = 16666 ∧ 200000000 / 21000 = 9523 :=
  GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster.tx_count

/-- Exact margins for the proposed cached model. -/
theorem cached_margins_non_vacuous_and_tight :
    yukon - 106 * 8432330917 = 6892848272 ∧
    yukon - 75 * 11992988211 = 1245809649 := by decide

theorem one_hundred_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredEightShape := by
  unfold OneHundredEightShape
  decide

theorem one_hundred_eight_budget_last_margin_non_vacuous_and_tight :
    oneHundredEightExplicitBudgets.length = 108 ∧
    oneHundredEightExplicitBudgets.getLast? = some 898500000000 ∧
    yukon - 898500000000 = 2219925474 := by decide

theorem one_hundred_eight_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredEightExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredEightExplicitBudgets, K < 900719925474) := by
  refine ⟨one_hundred_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.1, ?_⟩
  intro K hK
  exact (one_hundred_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2

theorem one_hundred_eight_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredEightShape ∧
    (∀ K ∈ oneHundredEightExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms charges_ok_non_vacuous_and_tight
#print axioms scan_ratio_non_vacuous_and_tight
#print axioms attack200_non_vacuous_and_tight
#print axioms attack380_non_vacuous_and_tight
#print axioms previous_broken_non_vacuous_and_tight
#print axioms cached_non_vacuous_and_tight
#print axioms tx_count_non_vacuous_and_tight
#print axioms cached_margins_non_vacuous_and_tight
#print axioms one_hundred_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_eight_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_eight_budgets_under_yukon_non_vacuous_and_tight
#print axioms one_hundred_eight_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixXAndOneHundredEightBudgetMaster
