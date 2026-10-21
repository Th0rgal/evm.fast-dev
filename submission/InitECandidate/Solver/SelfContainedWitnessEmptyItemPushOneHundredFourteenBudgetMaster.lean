import InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
import InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_302: exact imported witness-entry/PUSH cost-model arithmetic, full
cached and uncached LP hypotheses, and 114 conditional finite certificates.
The cached model requires a per-code jumpdest cache. Cost estimates do not
establish execution-derived semantic runtime certificates; finite certificates
remain conditional on the base semantic certificate. -/
namespace InitECandidate.Solver.SelfContainedWitnessEmptyItemPushOneHundredFourteenBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev oneHundredFourteenExplicitBudgets := JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.oneHundredFourteenExplicitBudgets
abbrev portfolio := oneHundredFourteenExplicitBudgets
abbrev OneHundredFourteenShape := JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.OneHundredFourteenShape

theorem leaf_counts_non_vacuous_and_tight : keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.leaf_counts

theorem cached200_non_vacuous_and_tight (A K B E n2 n17 md ms P : Nat)
    (hg : 2400 * A + 2100 * K + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    33 * costC A K B E n2 n17 md ms P ≤ 214138410040 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.cached200 A K B E n2 n17 md ms P hg h1 h2 hb he hw

theorem cached380_non_vacuous_and_tight (A K B E n2 n17 md ms P : Nat)
    (hg : 2400 * A + 2100 * K + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K B E n2 n17 md ms P ≤ 114947567578464 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.cached380 A K B E n2 n17 md ms P hg h1 h2 hb he hw

theorem uncached200_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.uncached200 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

theorem uncached380_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.uncached380 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

theorem cached_slopes_non_vacuous_and_tight : mainCached200 = 8014558459 ∧ 112 * mainCached200 < yukon ∧
    yukon < 113 * mainCached200 ∧ mainCached380 = 11548778048 ∧ 77 * mainCached380 < yukon ∧
    yukon < 78 * mainCached380 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.cached_slopes

theorem uncached_slopes_non_vacuous_and_tight : mainUncached200 = 111614505033 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 208876066898 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.uncached_slopes

theorem no_135_non_vacuous_and_tight : yukon / 135 = 6671999447 ∧ yukon < 135 * mainCached200 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.no_135

theorem one_hundred_fourteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredFourteenShape :=
  JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.one_hundred_fourteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

theorem one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight :
    oneHundredFourteenExplicitBudgets.length = 114 ∧
    oneHundredFourteenExplicitBudgets.getLast? = some 900715000000 ∧
    yukon - 900715000000 = 4925474 :=
  JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight

theorem one_hundred_fourteen_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredFourteenExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredFourteenExplicitBudgets, K < 900719925474) :=
  JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.one_hundred_fourteen_budgets_under_yukon_non_vacuous_and_tight

theorem one_hundred_fourteen_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredFourteenShape ∧
    (∀ K ∈ oneHundredFourteenExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.one_hundred_fourteen_budget_certificates_non_vacuous_and_tight cert

#print axioms leaf_counts_non_vacuous_and_tight
#print axioms cached200_non_vacuous_and_tight
#print axioms cached380_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms uncached_slopes_non_vacuous_and_tight
#print axioms no_135_non_vacuous_and_tight
#print axioms one_hundred_fourteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_fourteen_budgets_under_yukon_non_vacuous_and_tight
#print axioms one_hundred_fourteen_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedWitnessEmptyItemPushOneHundredFourteenBudgetMaster
