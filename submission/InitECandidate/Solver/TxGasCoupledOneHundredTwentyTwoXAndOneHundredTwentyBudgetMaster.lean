import InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
import InitECandidate.Solver.WitnessEmptyItemPushOneHundredTwelveXAndOneHundredEighteenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! The uncached jumpdest scans invalidate the previous global gas estimate for
the current Guest. The 122x/82x arithmetic explicitly assumes the proposed
per-code jumpdest cache and the previous model's remaining assumptions.
Finite semantic certificates remain conditional on the base certificate;
none is inferred from the arithmetic cost estimates. -/
namespace InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev Previous := WitnessEmptyItemPushOneHundredTwelveXAndOneHundredEighteenBudgetMaster.oneHundredEighteenExplicitBudgets

def oneHundredTwentyExplicitBudgets : List Nat := Previous ++ [900719700000, 900719800000]
abbrev portfolio := oneHundredTwentyExplicitBudgets

def OneHundredTwentyShape : Prop :=
  portfolio.length = 120 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 118 = Previous ∧
  portfolio.drop 118 = [900719700000, 900719800000] ∧
  portfolio.getLast? = some 900719800000 ∧ yukon = 900719925474

theorem decomposition_non_vacuous_and_tight : perTx = 40782 ∧ perTx * 16666 = 679672812 ∧
    trueFixed200 + perTx * 16666 = oldFixed200 ∧ trueFixed380 + perTx * 16666 = oldFixed380 ∧
    trueFixed200 = 711625206 ∧ trueFixed380 = 996044214 :=
  GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.decomposition

theorem cached200_non_vacuous_and_tight (A K B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    33 * costC A K B E n2 n17 md ms P T ≤ 214138410040 :=
  GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.cached200 A K B E n2 n17 md ms P T hg h1 h2 hb he hw

theorem cached380_non_vacuous_and_tight (A K B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K B E n2 n17 md ms P T ≤ 114947567578464 :=
  GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.cached380 A K B E n2 n17 md ms P T hg h1 h2 hb he hw

theorem uncached200_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280 :=
  GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.uncached200 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

theorem uncached380_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280 :=
  GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.uncached380 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

theorem cached_slopes_non_vacuous_and_tight : mainCached200 = 7334885647 ∧ 122 * mainCached200 < yukon ∧
    yukon < 123 * mainCached200 ∧ mainCached380 = 10869105236 ∧ 82 * mainCached380 < yukon ∧
    yukon < 83 * mainCached380 :=
  GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.cached_slopes

theorem uncached_slopes_non_vacuous_and_tight : mainUncached200 = 110934832221 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 208196394086 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 :=
  GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.uncached_slopes

theorem no_sub_seven_non_vacuous_and_tight : 7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 334885647 :=
  GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.no_sub_seven

theorem one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredTwentyShape := by
  unfold OneHundredTwentyShape
  decide

theorem one_hundred_twenty_budget_last_margin_non_vacuous_and_tight :
    oneHundredTwentyExplicitBudgets.length = 120 ∧
    oneHundredTwentyExplicitBudgets.getLast? = some 900719800000 ∧
    yukon - 900719800000 = 125474 := by decide

theorem one_hundred_twenty_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredTwentyExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwentyExplicitBudgets, K < 900719925474) := by
  refine ⟨one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.1, ?_⟩
  intro K hK
  exact (one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2

theorem one_hundred_twenty_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentyShape ∧
    (∀ K ∈ oneHundredTwentyExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms decomposition_non_vacuous_and_tight
#print axioms cached200_non_vacuous_and_tight
#print axioms cached380_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms uncached_slopes_non_vacuous_and_tight
#print axioms no_sub_seven_non_vacuous_and_tight
#print axioms one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_twenty_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_twenty_budgets_under_yukon_non_vacuous_and_tight
#print axioms one_hundred_twenty_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster
