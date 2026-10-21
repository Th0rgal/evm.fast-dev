import InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
import InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedSstoreDirtyKeyGasOneHundredTwentyTwoCampaignMaster` (`W5_319`)

Self-contained dual LP campaign synthesis (`0 sorryAx`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestSstoreDirtyKeyGasAndSubSevenBillionMaster`**:
   - Exact SSTORE dirty-key stack-push gas coupling (`sstoreKeyGas = 2105` gas per cold key via
     `2100 + PUSH0 (2) + PUSHn (3)`, with `2060 + 90 + coldRow = 5274` per-key ticks),
   - Exact `G`-independent block constant `blockFixed = 370,538,614` (`gasRows200 = 341,086,592`,
     `gasRows380 = 625,505,600`, `coldRow = 3,124`, `perTx = 42,382`),
   - Cached LP (`451 * costC ≤ 3,058,910,053,880` at 200M, `11803 * costC ≤ 118,511,584,702,912` at 380M)
     yielding `mainCached200 = 7,287,261,989` (`123×` Yukon passes, `124×` fails) and
     `mainCached380 = 10,545,558,216` (`85×` Yukon passes, `86×` fails), with `no_sub_seven`
     (`7,000,000,000 < mainCached200`, saving `1,581,510` ticks over `7,288,843,499`),
   - Uncached LP (`231 * costU ≤ 25,461,560,820,280` at 200M, `231 * costU ≤ 47,863,280,820,280` at 380M)
     yielding `mainUncached200 = 110,593,745,629` (`8×` Yukon passes, `9×` fails) and
     `mainUncached380 = 207,570,888,486` (`4×` Yukon passes, `5×` fails).
2. **`ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster`**:
   - 122-budget portfolio (`OneHundredTwentyTwoShape`, max `900,719,810,000`, margin `115,474` below Yukon)
     extending `OneHundredTwentyShape` (120 budgets, max `900,719,800,000`, margin `125,474`),
   - Conditional `InitE.Certificate (baselineWithFiniteK K) (.finite K)` integration across all 122 budgets.
-/

namespace InitECandidate.Solver.SelfContainedSstoreDirtyKeyGasOneHundredTwentyTwoCampaignMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster (
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
open _root_.InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster (
  oneHundredTwentyTwoExplicitBudgets
  OneHundredTwentyTwoShape
  one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight
  one_hundred_twenty_two_budgets_under_yukon_non_vacuous_and_tight
  one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster (
  oneHundredTwentyExplicitBudgets
  OneHundredTwentyShape
  one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- Cold `SSTORE` key-plus-value stack-push gas lower bound (`2100 + 2 + 3 = 2105`). -/
def sstoreKeyGas : Nat := 2105

abbrev portfolio : List Nat := oneHundredTwentyTwoExplicitBudgets

/-- 1. Exact `sstoreKeyGas = 2105`, per-key coefficient `2060 + 90 + coldRow = 5274`, and
`G`-independent block constant `blockFixed = 370,538,614` (`trueFixed200 = 711,625,206`,
`trueFixed380 = 996,044,214`, `gasRows200 = 341,086,592`, `gasRows380 = 625,505,600`,
`coldRow = 3,124`, `perTx = 42,382`). -/
theorem sstore_key_gas_and_block_fixed_decomposition_non_vacuous_and_tight :
    (sstoreKeyGas = 2105 ∧ sstoreKeyGas = 2100 + 2 + 3 ∧ 2060 + 90 + coldRow = 5274) ∧
    (blockFixed = 370538614 ∧ gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
      coldRow = 3124 ∧ perTx = 42382) ∧
    (trueFixed200 = 711625206 ∧ trueFixed380 = 996044214 ∧
      trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
      oldFixed200 = 1391298018 ∧ oldFixed380 = 1675717026) := by
  decide

/-- 2. Cached SSTORE-dirty-key LP at 200M (`451 * costC ≤ 3,058,910,053,880` under `2105 * K`)
yielding `mainCached200 = 7,287,261,989` (`123×` Yukon passes, `124×` fails, margin `4,386,700,827`),
and `no_sub_seven` (`7,000,000,000 < mainCached200`, saving `1,581,510` over `7,288,843,499`). -/
theorem cached200_lp_and_one_hundred_twenty_three_x_slope_non_vacuous_and_tight
    (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (451 * costC A K L B E n2 n17 md ms P T ≤ 3058910053880 ∧
      blockFixed + inputBytes + costC A K L B E n2 n17 md ms P T ≤ mainCached200) ∧
    (mainCached200 = 7287261989 ∧ 123 * mainCached200 < yukon ∧ yukon < 124 * mainCached200 ∧
      yukon - 123 * mainCached200 = 4386700827) ∧
    (7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 287261989 ∧
      7288843499 - mainCached200 = 1581510) := by
  have hc := cached200 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw
  refine ⟨⟨hc, ?_⟩, by decide, no_sub_seven⟩
  unfold mainCached200 blockFixed inputBytes at *
  omega

/-- 3. Cached SSTORE-dirty-key LP at 380M (`11803 * costC ≤ 118,511,584,702,912` under `2105 * K`)
yielding `mainCached380 = 10,545,558,216` (`85×` Yukon passes, `86×` fails, margin `4,347,477,114`). -/
theorem cached380_lp_and_eighty_five_x_slope_non_vacuous_and_tight
    (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
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

/-- 4. Uncached SSTORE-dirty-key LP at 200M (`231 * costU ≤ 25,461,560,820,280`) and 380M
(`231 * costU ≤ 47,863,280,820,280`) yielding `mainUncached200 = 110,593,745,629` (`8×` Yukon
passes, `9×` fails, margin `15,969,960,442`) and `mainUncached380 = 207,570,888,486` (`4×` Yukon
passes, `5×` fails, margin `70,436,371,530`). -/
theorem uncached200_uncached380_lp_and_eight_x_four_x_slopes_non_vacuous_and_tight
    (A K L B E n2 n17 md ms P C T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 200000000 →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280 ∧
      blockFixed + costU A K L B E n2 n17 md ms P C T ≤ mainUncached200) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 380000000 →
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

/-- 5. Strict 200M cached tightening (`1,581,510` ticks) from `sstoreKeyGas = 2105` over the
`2100`-gas cold-walk/BAL/merge LP (`7,288,843,499 → 7,287,261,989`) and `47,623,658` ticks over
the tx-gas-coupled LP (`7,334,885,647 → 7,287,261,989`), while preserving exact 380M cached and
200M/380M uncached totals. -/
theorem sstore_dirty_key_gas_tightening_over_cold_walk_and_tx_coupled_non_vacuous_and_tight :
    (sstoreKeyGas = 2105 ∧
      GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 = 7288843499 ∧
      mainCached200 = 7287261989 ∧
      mainCached200 < GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 ∧
      GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 - mainCached200 = 1581510) ∧
    (GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 = 7334885647 ∧
      mainCached200 < GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 - mainCached200 = 47623658) ∧
    (mainCached380 = GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached380 ∧
      mainUncached200 = GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainUncached200 ∧
      mainUncached380 = GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainUncached380) := by
  decide

/-- 6. Multi-stage slope and budget progression from `106×` (`8,432,330,917`), `108×` (`8,298,113,205`),
`110×` (`8,145,414,250`), `112×` (`8,014,558,459`), `122×` (`7,334,885,647`), and `123×` cold-walk
(`7,288,843,499`) to `123×` dirty-key-gas (`7,287,261,989`) at 200M, and `85×` (`10,545,558,216`) at 380M. -/
theorem campaign_slope_progression_one_hundred_six_to_sstore_dirty_key_one_hundred_twenty_three_x_non_vacuous_and_tight :
    (mainCached200 < GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 ∧
      GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 <
        GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 <
        GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached200 ∧
      GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached200 <
        GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200) ∧
    (123 * mainCached200 < yukon ∧ yukon < 124 * mainCached200 ∧
      123 * GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 < yukon ∧
      122 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 < yukon ∧
      112 * GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached200 < yukon ∧
      110 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 < yukon ∧
      85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380 ∧
      8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) := by
  decide

/-- 7. Dual gap between uncached (`110,593,745,629` at 200M / `207,570,888,486` at 380M) and
cached (`7,287,261,989` at 200M / `10,545,558,216` at 380M) totals under `sstoreKeyGas = 2105`
and `blockFixed = 370,538,614`. -/
theorem dual_uncached_vs_cached_gap_under_sstore_dirty_key_gas_non_vacuous_and_tight :
    (sstoreKeyGas = 2105 ∧ blockFixed = 370538614 ∧ inputBytes = 134217712 ∧
      mainCached200 = 7287261989 ∧ mainUncached200 = 110593745629 ∧
      mainCached200 < mainUncached200 ∧
      mainUncached200 - mainCached200 = 103306483640 ∧
      15 * mainCached200 < mainUncached200 ∧ mainUncached200 < 16 * mainCached200) ∧
    (mainCached380 = 10545558216 ∧ mainUncached380 = 207570888486 ∧
      mainCached380 < mainUncached380 ∧
      mainUncached380 - mainCached380 = 197025330270 ∧
      19 * mainCached380 < mainUncached380 ∧ mainUncached380 < 20 * mainCached380) := by
  decide

/-- 8. Strictly increasing 122-budget portfolio (`OneHundredTwentyTwoShape`, max `900,719,810,000`,
margin `115,474` below Yukon) extending `OneHundredTwentyShape` (120 budgets, max `900,719,800,000`,
margin `125,474`). -/
theorem one_hundred_twenty_two_and_one_hundred_twenty_budget_hierarchy_non_vacuous_and_tight :
    OneHundredTwentyTwoShape ∧
    OneHundredTwentyShape ∧
    oneHundredTwentyTwoExplicitBudgets.length = 122 ∧
    oneHundredTwentyTwoExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwentyTwoExplicitBudgets, 1212035192 ≤ K ∧ K < 900719925474) ∧
    oneHundredTwentyTwoExplicitBudgets.take 120 = oneHundredTwentyExplicitBudgets ∧
    oneHundredTwentyTwoExplicitBudgets.drop 120 = [900719805000, 900719810000] ∧
    oneHundredTwentyTwoExplicitBudgets.getLast? = some 900719810000 ∧
    yukon - 900719810000 = 115474 ∧
    yukon - 900719805000 = 120474 :=
  have h122 := one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h120 := one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  ⟨h122,
   h120,
   h122.1,
   h122.2.1,
   h122.2.2.1,
   h122.2.2.2.1,
   h122.2.2.2.2.1,
   h122.2.2.2.2.2.1,
   by decide,
   by decide⟩

/-- 9. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)`
across all 122 portfolio budgets, plus explicit certificates at the SSTORE dirty-key dual LP
budgets (`mainCached200 = 7,287,261,989`, `mainCached380 = 10,545,558,216`,
`mainUncached200 = 110,593,745,629`, `mainUncached380 = 207,570,888,486`) and at the new
endpoints `900,719,805,000` and `900,719,810,000`. -/
theorem one_hundred_twenty_two_budget_and_sstore_dirty_key_lp_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentyTwoShape ∧
    (∀ K ∈ oneHundredTwentyTwoExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK mainCached200) (.finite mainCached200) ∧
    InitE.Certificate (baselineWithFiniteK mainCached380) (.finite mainCached380) ∧
    InitE.Certificate (baselineWithFiniteK mainUncached200) (.finite mainUncached200) ∧
    InitE.Certificate (baselineWithFiniteK mainUncached380) (.finite mainUncached380) ∧
    InitE.Certificate (baselineWithFiniteK 900719805000) (.finite 900719805000) ∧
    InitE.Certificate (baselineWithFiniteK 900719810000) (.finite 900719810000) := by
  have hcert := one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight cert
  refine ⟨hcert.1, hcert.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainCached200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainCached380 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainUncached200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainUncached380 (by decide) cert
  · exact hcert.2 900719805000 (by decide)
  · exact hcert.2 900719810000 (by decide)

/-- 10. Grand SSTORE dirty-key gas 122-budget campaign master synthesis: `sstoreKeyGas = 2105`,
`blockFixed = 370,538,614`, `cached200`, `cached380`, `uncached200`, `uncached380`,
`mainCached200 = 7,287,261,989` (`123×`), `mainCached380 = 10,545,558,216` (`85×`),
`mainUncached200 = 110,593,745,629` (`8×`), `mainUncached380 = 207,570,888,486` (`4×`),
122 budgets `< yukon` (`last = 900,719,810,000`, margin `115,474`), and conditional
`InitE.Certificate (baselineWithFiniteK K) (.finite K)`. -/
theorem grand_sstore_dirty_key_gas_one_hundred_twenty_two_campaign_master_non_vacuous_and_tight
    (A K L B E n2 n17 md ms P C T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes)
    (cert : CertificateAt 1212035192) :
    (sstoreKeyGas = 2105 ∧ blockFixed = 370538614 ∧ gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
      trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
      coldRow = 3124 ∧ perTx = 42382) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000 →
      451 * costC A K L B E n2 n17 md ms P T ≤ 3058910053880) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000 →
      11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 200000000 →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 380000000 →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280) ∧
    (mainCached200 = 7287261989 ∧ 123 * mainCached200 < yukon ∧ yukon < 124 * mainCached200 ∧
      mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380) ∧
    (mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200 ∧
      mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) ∧
    OneHundredTwentyTwoShape ∧
    oneHundredTwentyTwoExplicitBudgets.getLast? = some 900719810000 ∧
    yukon - 900719810000 = 115474 ∧
    (∀ K_b ∈ oneHundredTwentyTwoExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K_b) (.finite K_b)) := by
  have hcert := one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight cert
  refine ⟨by decide, ?_, ?_, ?_, ?_, cached_slopes, uncached_slopes, hcert.1, by decide, by decide, hcert.2⟩
  · intro hg
    exact cached200 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw
  · intro hg
    exact cached380 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw
  · intro hg
    exact uncached200 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw
  · intro hg
    exact uncached380 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

#print axioms sstore_key_gas_and_block_fixed_decomposition_non_vacuous_and_tight
#print axioms cached200_lp_and_one_hundred_twenty_three_x_slope_non_vacuous_and_tight
#print axioms cached380_lp_and_eighty_five_x_slope_non_vacuous_and_tight
#print axioms uncached200_uncached380_lp_and_eight_x_four_x_slopes_non_vacuous_and_tight
#print axioms sstore_dirty_key_gas_tightening_over_cold_walk_and_tx_coupled_non_vacuous_and_tight
#print axioms campaign_slope_progression_one_hundred_six_to_sstore_dirty_key_one_hundred_twenty_three_x_non_vacuous_and_tight
#print axioms dual_uncached_vs_cached_gap_under_sstore_dirty_key_gas_non_vacuous_and_tight
#print axioms one_hundred_twenty_two_and_one_hundred_twenty_budget_hierarchy_non_vacuous_and_tight
#print axioms one_hundred_twenty_two_budget_and_sstore_dirty_key_lp_certificates_non_vacuous_and_tight
#print axioms grand_sstore_dirty_key_gas_one_hundred_twenty_two_campaign_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedSstoreDirtyKeyGasOneHundredTwentyTwoCampaignMaster
