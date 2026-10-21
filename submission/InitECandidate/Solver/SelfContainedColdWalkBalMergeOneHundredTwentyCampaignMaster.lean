import InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster
import InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedColdWalkBalMergeOneHundredTwentyCampaignMaster` (`W5_311`)

Self-contained dual LP campaign synthesis (`0 sorryAx`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster`**:
   - Exact decomposition of gas-dependent rows (`gasRows200 = 341,086,592`, `gasRows380 = 625,505,600`,
     `coldRow = 3,124`, `perTx = 42,382`) leaving a single `G`-independent constant
     `blockFixed = 370,538,614`,
   - Cached LP (`99 * costC ≤ 671,624,630,120` at 200M, `11803 * costC ≤ 118,511,584,702,912` at 380M)
     yielding `mainCached200 = 7,288,843,499` (`123×` Yukon passes, `124×` fails) and
     `mainCached380 = 10,545,558,216` (`85×` Yukon passes, `86×` fails), with `no_sub_seven`
     (`7,000,000,000 < mainCached200`),
   - Uncached LP (`231 * costU ≤ 25,461,560,820,280` at 200M, `231 * costU ≤ 47,863,280,820,280` at 380M)
     yielding `mainUncached200 = 110,593,745,629` (`8×` Yukon passes, `9×` fails) and
     `mainUncached380 = 207,570,888,486` (`4×` Yukon passes, `5×` fails).
2. **`TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster`**:
   - Strict reduction from the `122×`/`82×` tx-gas-coupled LP (`7,334,885,647` / `10,869,105,236` cached,
     `110,934,832,221` / `208,196,394,086` uncached) to the cold-walk/BAL/merge LP
     (`7,288,843,499` / `10,545,558,216` cached, `110,593,745,629` / `207,570,888,486` uncached),
   - 120-budget portfolio (`OneHundredTwentyShape`, max `900,719,800,000`, margin `125,474` below Yukon),
   - Conditional `InitE.Certificate (baselineWithFiniteK K) (.finite K)` integration across all 120 budgets.
-/

namespace InitECandidate.Solver.SelfContainedColdWalkBalMergeOneHundredTwentyCampaignMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster (
  inputBytes
  coldRow
  perTx
  gasRows200
  gasRows380
  blockFixed
  costC
  costU
  mainCached200
  mainCached380
  mainUncached200
  mainUncached380
  decomposition
  cached200
  cached380
  uncached200
  uncached380
  cached_slopes
  uncached_slopes
  no_sub_seven
)
open _root_.InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster (
  trueFixed200
  trueFixed380
  oldFixed200
  oldFixed380
)
open _root_.InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster (
  oneHundredTwentyExplicitBudgets
  OneHundredTwentyShape
  one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  one_hundred_twenty_budget_last_margin_non_vacuous_and_tight
  one_hundred_twenty_budgets_under_yukon_non_vacuous_and_tight
  one_hundred_twenty_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.WitnessEmptyItemPushOneHundredTwelveXAndOneHundredEighteenBudgetMaster (
  oneHundredEighteenExplicitBudgets
  OneHundredEighteenShape
  one_hundred_eighteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev portfolio : List Nat := oneHundredTwentyExplicitBudgets

/-- 1. Exact `G`-independent block constant `blockFixed = 370,538,614` and decomposition of
`trueFixed200 = 711,625,206` (`blockFixed + 341,086,592`), `trueFixed380 = 996,044,214`
(`blockFixed + 625,505,600`), `oldFixed200 = 1,391,298,018`, and `oldFixed380 = 1,675,717,026`,
together with `coldRow = 3,124` and `perTx = 42,382`. -/
theorem block_fixed_and_gas_rows_decomposition_non_vacuous_and_tight :
    (blockFixed = 370538614 ∧ gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
      coldRow = 3124 ∧ perTx = 42382) ∧
    (trueFixed200 = 711625206 ∧ trueFixed380 = 996044214 ∧
      trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380) ∧
    (oldFixed200 = 1391298018 ∧ oldFixed380 = 1675717026 ∧
      oldFixed200 - blockFixed = 1020759404 ∧ oldFixed380 - blockFixed = 1305178412) := by
  decide

/-- 2. Cached cold-walk/BAL/merge LP at 200M (`99 * costC ≤ 671,624,630,120`) yielding
`mainCached200 = 7,288,843,499` (`123×` Yukon passes, `124×` fails, margin `4,192,175,097`),
and `no_sub_seven` (`7,000,000,000 < mainCached200`). -/
theorem cached200_lp_and_one_hundred_twenty_three_x_slope_non_vacuous_and_tight
    (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (99 * costC A K L B E n2 n17 md ms P T ≤ 671624630120 ∧
      blockFixed + inputBytes + costC A K L B E n2 n17 md ms P T ≤ mainCached200) ∧
    (mainCached200 = 7288843499 ∧ 123 * mainCached200 < yukon ∧ yukon < 124 * mainCached200 ∧
      yukon - 123 * mainCached200 = 4192175097) ∧
    (7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 288843499 ∧
      mainCached200 - 6993799055 = 295044444) := by
  have hc := cached200 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw
  refine ⟨⟨hc, ?_⟩, by decide, no_sub_seven⟩
  unfold mainCached200 blockFixed inputBytes at *
  omega

/-- 3. Cached cold-walk/BAL/merge LP at 380M (`11803 * costC ≤ 118,511,584,702,912`) yielding
`mainCached380 = 10,545,558,216` (`85×` Yukon passes, `86×` fails, margin `4,347,477,114`). -/
theorem cached380_lp_and_eighty_five_x_slope_non_vacuous_and_tight
    (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912 ∧
      blockFixed + inputBytes + costC A K L B E n2 n17 md ms P T ≤ mainCached380) ∧
    (mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380 ∧
      yukon - 85 * mainCached380 = 4347477114) := by
  have hc := cached380 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw
  refine ⟨⟨hc, ?_⟩, by decide⟩
  unfold mainCached380 blockFixed inputBytes at *
  omega

/-- 4. Uncached cold-walk/BAL/merge LP at 200M (`231 * costU ≤ 25,461,560,820,280`) and 380M
(`231 * costU ≤ 47,863,280,820,280`) yielding `mainUncached200 = 110,593,745,629` (`8×` Yukon
passes, `9×` fails, margin `15,969,960,442`) and `mainUncached380 = 207,570,888,486` (`4×` Yukon
passes, `5×` fails, margin `70,436,371,530`). -/
theorem uncached200_uncached380_lp_and_eight_x_four_x_slopes_non_vacuous_and_tight
    (A K L B E n2 n17 md ms P C T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 200000000 →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280 ∧
      blockFixed + costU A K L B E n2 n17 md ms P C T ≤ mainUncached200) ∧
    (12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 380000000 →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280 ∧
      blockFixed + costU A K L B E n2 n17 md ms P C T ≤ mainUncached380) ∧
    (mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200 ∧
      yukon - 8 * mainUncached200 = 15969960442) ∧
    (mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380 ∧
      yukon - 4 * mainUncached380 = 70436371530) := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro hg
    have hu := uncached200 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw
    refine ⟨hu, ?_⟩
    unfold mainUncached200 blockFixed at *
    omega
  · intro hg
    have hu := uncached380 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw
    refine ⟨hu, ?_⟩
    unfold mainUncached380 blockFixed at *
    omega

/-- 5. Strict reduction from the `122×`/`82×` tx-gas-coupled LP
(`GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster`: `7,334,885,647` / `10,869,105,236`
cached, `110,934,832,221` / `208,196,394,086` uncached) to the `123×`/`85×` cold-walk/BAL/merge LP
(`7,288,843,499` / `10,545,558,216` cached, `110,593,745,629` / `207,570,888,486` uncached). -/
theorem cold_walk_bal_merge_strict_reduction_over_tx_gas_coupled_lp_non_vacuous_and_tight :
    (GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 = 7334885647 ∧
      mainCached200 = 7288843499 ∧
      mainCached200 < GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 - mainCached200 = 46042148) ∧
    (GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached380 = 10869105236 ∧
      mainCached380 = 10545558216 ∧
      mainCached380 < GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached380 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached380 - mainCached380 = 323547020) ∧
    (GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainUncached200 = 110934832221 ∧
      mainUncached200 = 110593745629 ∧
      mainUncached200 < GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainUncached200 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainUncached200 - mainUncached200 = 341086592) ∧
    (GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainUncached380 = 208196394086 ∧
      mainUncached380 = 207570888486 ∧
      mainUncached380 < GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainUncached380 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainUncached380 - mainUncached380 = 625505600) := by
  decide

/-- 6. Multi-stage slope progression from `106×` (`8,432,330,917`), `108×` (`8,298,113,205`),
`110×` (`8,145,414,250`), `112×` (`8,014,558,459`), and `122×` (`7,334,885,647`) to `123×`
(`7,288,843,499`) at 200M, and from `75×` (`11,992,988,211`), `77×` (`11,669,833,258` /
`11,548,778,048`), and `82×` (`10,869,105,236`) to `85×` (`10,545,558,216`) at 380M. -/
theorem campaign_slope_progression_one_hundred_six_to_one_hundred_twenty_three_x_non_vacuous_and_tight :
    (123 * mainCached200 < yukon ∧ yukon < 124 * mainCached200 ∧
      122 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 < yukon ∧
      yukon < 123 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 ∧
      112 * GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached200 < yukon ∧
      yukon < 113 * GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached200 ∧
      110 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 < yukon ∧
      yukon < 111 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 ∧
      108 * 8298113205 < yukon ∧ yukon < 109 * 8298113205 ∧
      106 * 8432330917 < yukon ∧ yukon < 107 * 8432330917 ∧
      8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200) ∧
    (85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380 ∧
      82 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached380 < yukon ∧
      yukon < 83 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached380 ∧
      77 * GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached380 < yukon ∧
      yukon < 78 * GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached380 ∧
      77 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 < yukon ∧
      yukon < 78 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 ∧
      75 * 11992988211 < yukon ∧ yukon < 76 * 11992988211 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) := by
  decide

/-- 7. Dual gap between uncached (`110,593,745,629` at 200M / `207,570,888,486` at 380M) and
cached (`7,288,843,499` at 200M / `10,545,558,216` at 380M) totals under the unified
`blockFixed = 370,538,614` decomposition. -/
theorem dual_uncached_vs_cached_gap_under_unified_block_fixed_non_vacuous_and_tight :
    (blockFixed = 370538614 ∧ inputBytes = 134217712 ∧
      mainCached200 = 7288843499 ∧ mainUncached200 = 110593745629 ∧
      mainCached200 < mainUncached200 ∧
      mainUncached200 - mainCached200 = 103304902130 ∧
      15 * mainCached200 < mainUncached200 ∧ mainUncached200 < 16 * mainCached200) ∧
    (mainCached380 = 10545558216 ∧ mainUncached380 = 207570888486 ∧
      mainCached380 < mainUncached380 ∧
      mainUncached380 - mainCached380 = 197025330270 ∧
      19 * mainCached380 < mainUncached380 ∧ mainUncached380 < 20 * mainCached380) := by
  decide

/-- 8. Strictly increasing 120-budget portfolio (`OneHundredTwentyShape`, max `900,719,800,000`,
margin `125,474` below Yukon) extending `OneHundredEighteenShape` (118 budgets, max `900,719,500,000`,
margin `425,474`). -/
theorem one_hundred_twenty_and_one_hundred_eighteen_budget_hierarchy_non_vacuous_and_tight :
    OneHundredTwentyShape ∧
    OneHundredEighteenShape ∧
    oneHundredTwentyExplicitBudgets.length = 120 ∧
    oneHundredTwentyExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwentyExplicitBudgets, 1212035192 ≤ K ∧ K < 900719925474) ∧
    oneHundredTwentyExplicitBudgets.take 118 = oneHundredEighteenExplicitBudgets ∧
    oneHundredTwentyExplicitBudgets.drop 118 = [900719700000, 900719800000] ∧
    oneHundredTwentyExplicitBudgets.getLast? = some 900719800000 ∧
    yukon - 900719800000 = 125474 ∧
    yukon - 900719700000 = 225474 :=
  have h120 := one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h118 := one_hundred_eighteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  ⟨h120,
   h118,
   h120.1,
   h120.2.1,
   h120.2.2.1,
   h120.2.2.2.1,
   h120.2.2.2.2.1,
   h120.2.2.2.2.2.1,
   by decide,
   by decide⟩

/-- 9. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)`
across all 120 portfolio budgets, plus explicit certificates at the cold-walk/BAL/merge dual LP
budgets (`mainCached200 = 7,288,843,499`, `mainCached380 = 10,545,558,216`,
`mainUncached200 = 110,593,745,629`, `mainUncached380 = 207,570,888,486`) and at the new
endpoints `900,719,700,000` and `900,719,800,000`. -/
theorem one_hundred_twenty_budget_and_cold_walk_lp_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentyShape ∧
    (∀ K ∈ oneHundredTwentyExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK mainCached200) (.finite mainCached200) ∧
    InitE.Certificate (baselineWithFiniteK mainCached380) (.finite mainCached380) ∧
    InitE.Certificate (baselineWithFiniteK mainUncached200) (.finite mainUncached200) ∧
    InitE.Certificate (baselineWithFiniteK mainUncached380) (.finite mainUncached380) ∧
    InitE.Certificate (baselineWithFiniteK 900719700000) (.finite 900719700000) ∧
    InitE.Certificate (baselineWithFiniteK 900719800000) (.finite 900719800000) := by
  have hcert := one_hundred_twenty_budget_certificates_non_vacuous_and_tight cert
  refine ⟨hcert.1, hcert.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainCached200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainCached380 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainUncached200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainUncached380 (by decide) cert
  · exact hcert.2 900719700000 (by decide)
  · exact hcert.2 900719800000 (by decide)

/-- 10. Grand cold-walk/BAL/merge 120-budget campaign master synthesis: `blockFixed = 370,538,614`,
`cached200`, `cached380`, `uncached200`, `uncached380`, `mainCached200 = 7,288,843,499` (`123×`),
`mainCached380 = 10,545,558,216` (`85×`), `mainUncached200 = 110,593,745,629` (`8×`),
`mainUncached380 = 207,570,888,486` (`4×`), 120 budgets `< yukon` (`last = 900,719,800,000`,
margin `125,474`), and conditional `InitE.Certificate (baselineWithFiniteK K) (.finite K)`. -/
theorem grand_cold_walk_bal_merge_one_hundred_twenty_campaign_master_non_vacuous_and_tight
    (A K L B E n2 n17 md ms P C T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes)
    (cert : CertificateAt 1212035192) :
    (blockFixed = 370538614 ∧ gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
      trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
      coldRow = 3124 ∧ perTx = 42382) ∧
    (12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 200000000 →
      99 * costC A K L B E n2 n17 md ms P T ≤ 671624630120) ∧
    (12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 380000000 →
      11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912) ∧
    (12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 200000000 →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280) ∧
    (12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 380000000 →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280) ∧
    (mainCached200 = 7288843499 ∧ 123 * mainCached200 < yukon ∧ yukon < 124 * mainCached200 ∧
      mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380) ∧
    (mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200 ∧
      mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) ∧
    OneHundredTwentyShape ∧
    oneHundredTwentyExplicitBudgets.getLast? = some 900719800000 ∧
    yukon - 900719800000 = 125474 ∧
    (∀ K_b ∈ oneHundredTwentyExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K_b) (.finite K_b)) := by
  have hcert := one_hundred_twenty_budget_certificates_non_vacuous_and_tight cert
  refine ⟨by decide, ?_, ?_, ?_, ?_, cached_slopes, uncached_slopes, hcert.1, by decide, by decide, hcert.2⟩
  · intro hg
    exact cached200 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw
  · intro hg
    exact cached380 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw
  · intro hg
    exact uncached200 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw
  · intro hg
    exact uncached380 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

#print axioms block_fixed_and_gas_rows_decomposition_non_vacuous_and_tight
#print axioms cached200_lp_and_one_hundred_twenty_three_x_slope_non_vacuous_and_tight
#print axioms cached380_lp_and_eighty_five_x_slope_non_vacuous_and_tight
#print axioms uncached200_uncached380_lp_and_eight_x_four_x_slopes_non_vacuous_and_tight
#print axioms cold_walk_bal_merge_strict_reduction_over_tx_gas_coupled_lp_non_vacuous_and_tight
#print axioms campaign_slope_progression_one_hundred_six_to_one_hundred_twenty_three_x_non_vacuous_and_tight
#print axioms dual_uncached_vs_cached_gap_under_unified_block_fixed_non_vacuous_and_tight
#print axioms one_hundred_twenty_and_one_hundred_eighteen_budget_hierarchy_non_vacuous_and_tight
#print axioms one_hundred_twenty_budget_and_cold_walk_lp_certificates_non_vacuous_and_tight
#print axioms grand_cold_walk_bal_merge_one_hundred_twenty_campaign_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedColdWalkBalMergeOneHundredTwentyCampaignMaster
