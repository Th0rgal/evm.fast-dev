import InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
import InitECandidate.Solver.PanToWordToStackNamesAndOneHundredTwentySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_329: full imported SSTORE dirty-key gas LP contracts and 126 conditional
finite certificates. All gas, dirty-node and witness-byte hypotheses are
retained, including the 2105-gas key charge and the additional key-work ticks.
Cached slopes require the proposed per-code jumpdest cache. These cost-model
arithmetic results do not establish execution-derived semantic runtime
certificates; finite certificates remain conditional on the base certificate. -/
namespace InitECandidate.Solver.SelfContainedPanToWordToStackNamesOneHundredTwentySixBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
open _root_.InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster (trueFixed200 trueFixed380)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev oneHundredTwentySixExplicitBudgets := PanToWordToStackNamesAndOneHundredTwentySixBudgetMaster.oneHundredTwentySixExplicitBudgets
abbrev portfolio := oneHundredTwentySixExplicitBudgets
abbrev OneHundredTwentySixShape := PanToWordToStackNamesAndOneHundredTwentySixBudgetMaster.OneHundredTwentySixShape

theorem decomposition_non_vacuous_and_tight : gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
    trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
    coldRow = 3124 ∧ perTx = 42382 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.decomposition

theorem cached200_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    451 * costC A K L B E n2 n17 md ms P T ≤ 3058910053880 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.cached200 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

theorem cached380_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.cached380 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

theorem uncached200_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.uncached200 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

theorem uncached380_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.uncached380 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

theorem cached_slopes_non_vacuous_and_tight : mainCached200 = 7287261989 ∧ 123 * mainCached200 < yukon ∧
    yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧
    yukon < 86 * mainCached380 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.cached_slopes

theorem uncached_slopes_non_vacuous_and_tight : mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.uncached_slopes

theorem no_sub_seven_non_vacuous_and_tight : 7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 287261989 ∧
    7288843499 - mainCached200 = 1581510 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.no_sub_seven

theorem one_hundred_twenty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredTwentySixShape :=
  PanToWordToStackNamesAndOneHundredTwentySixBudgetMaster.one_hundred_twenty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

theorem one_hundred_twenty_six_budget_last_margin_non_vacuous_and_tight :
    oneHundredTwentySixExplicitBudgets.length = 126 ∧
    oneHundredTwentySixExplicitBudgets.getLast? = some 900719830000 ∧
    yukon - 900719830000 = 95474 :=
  PanToWordToStackNamesAndOneHundredTwentySixBudgetMaster.one_hundred_twenty_six_budget_last_margin_non_vacuous_and_tight

theorem one_hundred_twenty_six_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredTwentySixExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwentySixExplicitBudgets, K < 900719925474) :=
  PanToWordToStackNamesAndOneHundredTwentySixBudgetMaster.one_hundred_twenty_six_budgets_under_yukon_non_vacuous_and_tight

theorem one_hundred_twenty_six_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentySixShape ∧
    (∀ K ∈ oneHundredTwentySixExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  PanToWordToStackNamesAndOneHundredTwentySixBudgetMaster.one_hundred_twenty_six_budget_certificates_non_vacuous_and_tight cert

#print axioms decomposition_non_vacuous_and_tight
#print axioms cached200_non_vacuous_and_tight
#print axioms cached380_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms uncached_slopes_non_vacuous_and_tight
#print axioms no_sub_seven_non_vacuous_and_tight
#print axioms one_hundred_twenty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_twenty_six_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_twenty_six_budgets_under_yukon_non_vacuous_and_tight
#print axioms one_hundred_twenty_six_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedPanToWordToStackNamesOneHundredTwentySixBudgetMaster
