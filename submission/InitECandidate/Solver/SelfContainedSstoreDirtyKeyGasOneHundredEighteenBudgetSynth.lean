import InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
import InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_320: self-contained SSTORE dirty-key gas (`2,105` gas per cold key with
stack push overhead `90` ticks) and cold-walk/BAL/merge gas-coupled LP synthesis
(`blockFixed = 370538614`, `mainCached200 = 7287261989` at `123x` Yukon,
`mainCached380 = 10545558216` at `85x` Yukon, `mainUncached200 = 110593745629` at `8x`,
`mainUncached380 = 207570888486` at `4x`, `no_sub_seven`) and conditional finite
certificates across the 122-budget portfolio below Yukon (`last = 900719810000`,
margin `115474`). -/
namespace InitECandidate.Solver.SelfContainedSstoreDirtyKeyGasOneHundredEighteenBudgetSynth

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
open _root_.InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
  (trueFixed200 trueFixed380)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev oneHundredTwentyTwoExplicitBudgets :=
  ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster.oneHundredTwentyTwoExplicitBudgets
abbrev portfolio := oneHundredTwentyTwoExplicitBudgets
abbrev OneHundredTwentyTwoShape :=
  ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster.OneHundredTwentyTwoShape

/-- 1. Exact decomposition of gas-dependent rows (`blockFixed = 370538614`, `coldRow = 3124`, `perTx = 42382`). -/
theorem decomposition_non_vacuous_and_tight :
    blockFixed = 370538614 ∧ gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
    trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
    coldRow = 3124 ∧ perTx = 42382 :=
  ⟨rfl, GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.decomposition⟩

/-- 2. Cached SSTORE dirty-key (`2,105` gas) and cold-walk/BAL/merge LP at 200M gas. -/
theorem cached200_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    451 * costC A K L B E n2 n17 md ms P T ≤ 3058910053880 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.cached200 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

/-- 3. Cached SSTORE dirty-key (`2,105` gas) and cold-walk/BAL/merge LP at 380M gas. -/
theorem cached380_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.cached380 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

/-- 4. Uncached SSTORE dirty-key (`2,105` gas) and cold-walk/BAL/merge LP at 200M gas. -/
theorem uncached200_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.uncached200 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 5. Uncached SSTORE dirty-key (`2,105` gas) and cold-walk/BAL/merge LP at 380M gas. -/
theorem uncached380_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.uncached380 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 6. Cached slopes: `mainCached200 = 7,287,261,989` (`123x` Yukon) and `mainCached380 = 10,545,558,216` (`85x` Yukon). -/
theorem cached_slopes_non_vacuous_and_tight :
    mainCached200 = 7287261989 ∧ 123 * mainCached200 < yukon ∧
    yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧
    yukon < 86 * mainCached380 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.cached_slopes

/-- 7. Uncached slopes: `mainUncached200 = 110,593,745,629` (`8x` Yukon) and `mainUncached380 = 207,570,888,486` (`4x` Yukon). -/
theorem uncached_slopes_non_vacuous_and_tight :
    mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.uncached_slopes

/-- 8. Sub-7B gap (`287,261,989` ticks above `7,000,000,000`) and `1,581,510` tick gain over `7,288,843,499`. -/
theorem no_sub_seven_non_vacuous_and_tight :
    7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 287261989 ∧
    7288843499 - mainCached200 = 1581510 :=
  GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.no_sub_seven

/-- 9. Portfolio shape: 122 strictly increasing finite budgets below Yukon. -/
theorem one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredTwentyTwoShape :=
  ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster.one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

/-- 10. Portfolio last entry (`900,719,810,000`), exact Yukon margin (`115,474`), and cached `123x`/`85x` margins. -/
theorem one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight :
    (oneHundredTwentyTwoExplicitBudgets.length = 122 ∧
      oneHundredTwentyTwoExplicitBudgets.getLast? = some 900719810000 ∧
      yukon - 900719810000 = 115474) ∧
    (yukon - 123 * mainCached200 = 4386700827 ∧
      yukon - 85 * mainCached380 = 4347477114) :=
  ⟨ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster.one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight,
   by decide⟩

/-- 11. Pairwise strict monotonicity and Yukon ceiling across all 122 budgets. -/
theorem one_hundred_twenty_two_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredTwentyTwoExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwentyTwoExplicitBudgets, K < 900719925474) :=
  ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster.one_hundred_twenty_two_budgets_under_yukon_non_vacuous_and_tight

/-- 12. Conditional finite certificates across all 122 portfolio budgets. -/
theorem one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentyTwoShape ∧
    (∀ K ∈ oneHundredTwentyTwoExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster.one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight cert

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

end InitECandidate.Solver.SelfContainedSstoreDirtyKeyGasOneHundredEighteenBudgetSynth
