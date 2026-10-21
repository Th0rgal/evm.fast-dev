import InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster
import InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! The uncached jumpdest scans invalidate the previous global gas estimate for
the current Guest. The 123x/85x arithmetic explicitly assumes the proposed
per-code jumpdest cache and the previous model's remaining assumptions.
Finite semantic certificates remain conditional on the base certificate;
none is inferred from the arithmetic cost estimates. -/
namespace InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster (trueFixed200 trueFixed380)
open _root_.InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev Previous := TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster.oneHundredTwentyExplicitBudgets

def oneHundredTwentyTwoExplicitBudgets : List Nat := Previous ++ [900719805000, 900719810000]
abbrev portfolio := oneHundredTwentyTwoExplicitBudgets

def OneHundredTwentyTwoShape : Prop :=
  portfolio.length = 122 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 120 = Previous ∧
  portfolio.drop 120 = [900719805000, 900719810000] ∧
  portfolio.getLast? = some 900719810000 ∧ yukon = 900719925474

theorem decomposition_non_vacuous_and_tight : gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
    trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
    coldRow = 3124 ∧ perTx = 42382 ∧ blockFixed = 370538614 :=
  ⟨GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.decomposition.1, GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.decomposition.2.1, GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.decomposition.2.2.1, GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.decomposition.2.2.2.1, GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.decomposition.2.2.2.2.1, GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.decomposition.2.2.2.2.2, rfl⟩

theorem cached200_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    99 * costC A K L B E n2 n17 md ms P T ≤ 671624630120 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.cached200 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

theorem cached380_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.cached380 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

theorem uncached200_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.uncached200 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

theorem uncached380_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.uncached380 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

theorem cached_slopes_non_vacuous_and_tight : mainCached200 = 7288843499 ∧ 123 * mainCached200 < yukon ∧
    yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧
    yukon < 86 * mainCached380 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.cached_slopes

theorem uncached_slopes_non_vacuous_and_tight : mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.uncached_slopes

theorem no_sub_seven_non_vacuous_and_tight : 7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 288843499 ∧
    mainCached200 - 6993799055 = 295044444 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.no_sub_seven

theorem one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredTwentyTwoShape := by
  unfold OneHundredTwentyTwoShape
  decide

theorem one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight :
    oneHundredTwentyTwoExplicitBudgets.length = 122 ∧
    oneHundredTwentyTwoExplicitBudgets.getLast? = some 900719810000 ∧
    yukon - 900719810000 = 115474 := by decide

theorem one_hundred_twenty_two_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredTwentyTwoExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwentyTwoExplicitBudgets, K < 900719925474) := by
  refine ⟨one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.1, ?_⟩
  intro K hK
  exact (one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2

theorem one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentyTwoShape ∧
    (∀ K ∈ oneHundredTwentyTwoExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms decomposition_non_vacuous_and_tight
#print axioms cached200_non_vacuous_and_tight
#print axioms cached380_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms uncached_slopes_non_vacuous_and_tight
#print axioms no_sub_seven_non_vacuous_and_tight
#print axioms one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_twenty_two_budgets_under_yukon_non_vacuous_and_tight
#print axioms one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster
