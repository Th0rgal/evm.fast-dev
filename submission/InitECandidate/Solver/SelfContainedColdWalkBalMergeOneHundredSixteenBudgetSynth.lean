import InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster
import InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_314: self-contained cold-walk, BAL and merge gas-coupled LP synthesis
(`blockFixed = 370538614`, `mainCached200 = 7288843499` at `123x` Yukon,
`mainCached380 = 10545558216` at `85x` Yukon, `mainUncached200 = 110593745629` at `8x`,
`mainUncached380 = 207570888486` at `4x`, `no_sub_seven`) and conditional finite
certificates across the budget portfolio below Yukon. -/
namespace InitECandidate.Solver.SelfContainedColdWalkBalMergeOneHundredSixteenBudgetSynth

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster
open _root_.InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
  (trueFixed200 trueFixed380)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev oneHundredTwentyExplicitBudgets :=
  TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster.oneHundredTwentyExplicitBudgets
abbrev portfolio := oneHundredTwentyExplicitBudgets
abbrev OneHundredTwentyShape :=
  TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster.OneHundredTwentyShape

/-- 1. Exact decomposition of gas-dependent rows (`blockFixed = 370538614`, `coldRow = 3124`, `perTx = 42382`). -/
theorem decomposition_non_vacuous_and_tight :
    blockFixed = 370538614 ∧ gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
    trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
    coldRow = 3124 ∧ perTx = 42382 :=
  ⟨rfl, GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.decomposition⟩

/-- 2. Cached cold-walk, BAL and merge gas-coupled LP at 200M gas. -/
theorem cached200_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    99 * costC A K L B E n2 n17 md ms P T ≤ 671624630120 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.cached200 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

/-- 3. Cached cold-walk, BAL and merge gas-coupled LP at 380M gas. -/
theorem cached380_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.cached380 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

/-- 4. Uncached cold-walk, BAL and merge gas-coupled LP at 200M gas. -/
theorem uncached200_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.uncached200 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 5. Uncached cold-walk, BAL and merge gas-coupled LP at 380M gas. -/
theorem uncached380_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.uncached380 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 6. Cached slopes: `mainCached200 = 7,288,843,499` (`123x` Yukon) and `mainCached380 = 10,545,558,216` (`85x` Yukon). -/
theorem cached_slopes_non_vacuous_and_tight :
    mainCached200 = 7288843499 ∧ 123 * mainCached200 < yukon ∧
    yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧
    yukon < 86 * mainCached380 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.cached_slopes

/-- 7. Uncached slopes: `mainUncached200 = 110,593,745,629` (`8x` Yukon) and `mainUncached380 = 207,570,888,486` (`4x` Yukon). -/
theorem uncached_slopes_non_vacuous_and_tight :
    mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.uncached_slopes

/-- 8. Sub-7B gap when cold rows remain on `A` and `K`. -/
theorem no_sub_seven_non_vacuous_and_tight :
    7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 288843499 ∧
    mainCached200 - 6993799055 = 295044444 :=
  GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.no_sub_seven

/-- 9. Portfolio shape: strictly increasing finite budgets below Yukon. -/
theorem budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredTwentyShape :=
  TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster.one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

/-- 10. Portfolio last entry and exact Yukon margin, plus cached `123x`/`85x` margins. -/
theorem budget_last_and_cached_margins_non_vacuous_and_tight :
    (oneHundredTwentyExplicitBudgets.length = 120 ∧
      oneHundredTwentyExplicitBudgets.getLast? = some 900719800000 ∧
      yukon - 900719800000 = 125474) ∧
    (yukon - 123 * mainCached200 = 4192175097 ∧
      yukon - 85 * mainCached380 = 4347477114) :=
  ⟨TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster.one_hundred_twenty_budget_last_margin_non_vacuous_and_tight,
   by decide⟩

/-- 11. Pairwise strict monotonicity and Yukon ceiling across the budget table. -/
theorem budgets_under_yukon_non_vacuous_and_tight :
    oneHundredTwentyExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwentyExplicitBudgets, K < 900719925474) :=
  TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster.one_hundred_twenty_budgets_under_yukon_non_vacuous_and_tight

/-- 12. Conditional finite certificates across all portfolio budgets. -/
theorem budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentyShape ∧
    (∀ K ∈ oneHundredTwentyExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster.one_hundred_twenty_budget_certificates_non_vacuous_and_tight cert

#print axioms decomposition_non_vacuous_and_tight
#print axioms cached200_non_vacuous_and_tight
#print axioms cached380_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms uncached_slopes_non_vacuous_and_tight
#print axioms no_sub_seven_non_vacuous_and_tight
#print axioms budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms budget_last_and_cached_margins_non_vacuous_and_tight
#print axioms budgets_under_yukon_non_vacuous_and_tight
#print axioms budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedColdWalkBalMergeOneHundredSixteenBudgetSynth
