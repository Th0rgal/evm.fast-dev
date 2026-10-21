import InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster
import InitECandidate.Solver.LoopToStackNamesLabToTargetAndOneHundredTwentyEightBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedInlineChildMptDualOneHundredTwentyEightCampaignMaster` (`W5_337`)

Self-contained dual-regime MPT inline-child & Yellow-Paper LP campaign synthesis (`0 sorryAx`, `0` imports
from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`GuestInlineChildMptDualAndOneHundredThirtySixXMaster`**:
   - **Regime 1 (current Guest `_resolve_step` without `hb : B ≤ n17 + K + A`)**:
     `451 * cost1 ≤ 3,058,910,053,880` at 200M (`inline200 = 7,287,261,989`, `123×` Yukon passes, `124×` fails)
     and `451 * cost1 ≤ 4,809,020,803,880` at 380M (`inline380 = 11,167,773,630`, `80×` Yukon passes, `81×` fails),
     with `hb_gap : inline380 - 10,545,558,216 = 622,215,414` and `inline200 = 7,287,261,989`,
   - **Regime 2 (Yellow-Paper `< 32`-byte inline child rule with `22 * d + 54 * r ≤ inputBytes + 32 * (A + K)`
     and `B ≤ r + K + A`)**:
     `11 * cost2 ≤ 66,779,086,680` at 200M (`yp200 = 6,575,582,388`, `136×` Yukon passes, `137×` fails,
     attained at `PUSH31` + `6,100,805` dead-end branches) and `11 * cost2 ≤ 102,419,086,680` at 380M
     (`yp380 = 9,815,582,388`, `91×` Yukon passes, `92×` fails).
2. **`LoopToStackNamesLabToTargetAndOneHundredTwentyEightBudgetMaster`**:
   - 128-budget portfolio (`OneHundredTwentyEightShape`, max `900,719,840,000`, margin `85,474` below Yukon)
     extending `OneHundredTwentySixShape` (126 budgets, max `900,719,830,000`, margin `95,474`),
   - Conditional `InitE.Certificate (baselineWithFiniteK K) (.finite K)` integration across all 128 budgets.
-/

namespace InitECandidate.Solver.SelfContainedInlineChildMptDualOneHundredTwentyEightCampaignMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster (
  inputBytes
  blockFixed
  cost1
  cost2
  inline200
  inline380
  yp200
  yp380
  inline_200
  inline_380
  yp_200
  yp_380
  yp_tight
  inline_slopes
  yp_slopes
  hb_gap
)
open _root_.InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster (
  coldRow
  perTx
  gasRows200
  gasRows380
  mainCached200
  mainCached380
  mainUncached200
  mainUncached380
)
open _root_.InitECandidate.Solver.LoopToStackNamesLabToTargetAndOneHundredTwentyEightBudgetMaster (
  oneHundredTwentyEightExplicitBudgets
  OneHundredTwentyEightShape
  one_hundred_twenty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight
  one_hundred_twenty_eight_budgets_under_yukon_non_vacuous_and_tight
  one_hundred_twenty_eight_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.PanToWordToStackNamesAndOneHundredTwentySixBudgetMaster (
  oneHundredTwentySixExplicitBudgets
  OneHundredTwentySixShape
  one_hundred_twenty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.SstoreDirtyKeyGasOneHundredTwentyThreeXAndOneHundredTwentyFourBudgetMaster (
  oneHundredTwentyFourExplicitBudgets
  OneHundredTwentyFourShape
  one_hundred_twenty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev portfolio : List Nat := oneHundredTwentyEightExplicitBudgets

/-- 1. Regime 1 (inline child without `hb`) at 200M: `451 * cost1 ≤ 3,058,910,053,880`,
`inline200 = 7,287,261,989` (`= mainCached200`), `123×` Yukon passes, `124×` fails, with margin
`4,386,700,827`. -/
theorem inline200_lp_and_one_hundred_twenty_three_x_slope_non_vacuous_and_tight
    (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (451 * cost1 A K L B E n2 n17 md ms P T ≤ 3058910053880 ∧
      blockFixed + inputBytes + cost1 A K L B E n2 n17 md ms P T ≤ inline200) ∧
    (inline200 = 7287261989 ∧ inline200 = mainCached200 ∧
      123 * inline200 < yukon ∧ yukon < 124 * inline200 ∧
      yukon - 123 * inline200 = 4386700827) := by
  have hi := inline_200 A K L B E n2 n17 md ms P T hg h1 h2 he hw
  refine ⟨⟨hi, ?_⟩, by decide⟩
  unfold inline200 blockFixed inputBytes at *
  omega

/-- 2. Regime 1 (inline child without `hb`) at 380M: `451 * cost1 ≤ 4,809,020,803,880`,
`inline380 = 11,167,773,630`, `80×` Yukon passes, `81×` fails, and `hb_gap :
inline380 - 10,545,558,216 = 622,215,414` (`85× → 80×`). -/
theorem inline380_lp_eighty_x_slope_and_hb_gap_non_vacuous_and_tight
    (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (451 * cost1 A K L B E n2 n17 md ms P T ≤ 4809020803880 ∧
      blockFixed + inputBytes + cost1 A K L B E n2 n17 md ms P T ≤ inline380) ∧
    (inline380 = 11167773630 ∧ 80 * inline380 < yukon ∧ yukon < 81 * inline380 ∧
      yukon - 80 * inline380 = 7298035074) ∧
    (inline380 - 10545558216 = 622215414 ∧ inline200 = 7287261989) := by
  have hi := inline_380 A K L B E n2 n17 md ms P T hg h1 h2 he hw
  refine ⟨⟨hi, ?_⟩, by decide, hb_gap⟩
  unfold inline380 blockFixed inputBytes at *
  omega

/-- 3. Regime 2 (Yellow-Paper hashed children `22 * d + 54 * r ≤ inputBytes + 32 * (A + K)` and
`B ≤ r + K + A`) at 200M: `11 * cost2 ≤ 66,779,086,680`, `yp200 = 6,575,582,388` (sub-7·10⁹ by
`424,417,612`), `136×` Yukon passes, `137×` fails, and tightness witness (`6,100,805` dead-end branches). -/
theorem yp200_lp_one_hundred_thirty_six_x_slope_and_tightness_non_vacuous_and_tight
    (A K L B E n2 d r md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    (11 * cost2 A K L B E n2 d r md ms P T ≤ 66779086680 ∧
      blockFixed + inputBytes + cost2 A K L B E n2 d r md ms P T ≤ yp200) ∧
    (yp200 = 6575582388 ∧ yp200 < 7000000000 ∧ 7000000000 - yp200 = 424417612 ∧
      136 * yp200 < yukon ∧ yukon < 137 * yp200 ∧
      yukon - 136 * yp200 = 6440720706) ∧
    (11 * cost2 0 0 0 0 0 0 6100805 0 0 0 200000000 0 ≤ 66779086680 ∧
      66779086680 - 11 * cost2 0 0 0 0 0 0 6100805 0 0 0 200000000 0 < 11 * 405 ∧
      7 * 0 + 22 * 6100805 ≤ inputBytes) := by
  have hy := yp_200 A K L B E n2 d r md ms P T hg h1 h2 hb he hw
  refine ⟨⟨hy, ?_⟩, by decide, yp_tight⟩
  unfold yp200 blockFixed inputBytes at *
  omega

/-- 4. Regime 2 (Yellow-Paper hashed children) at 380M: `11 * cost2 ≤ 102,419,086,680`,
`yp380 = 9,815,582,388` (sub-10·10⁹ by `184,417,612`), `91×` Yukon passes, `92×` fails, margin
`7,501,928,166`. -/
theorem yp380_lp_and_ninety_one_x_slope_non_vacuous_and_tight
    (A K L B E n2 d r md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    (11 * cost2 A K L B E n2 d r md ms P T ≤ 102419086680 ∧
      blockFixed + inputBytes + cost2 A K L B E n2 d r md ms P T ≤ yp380) ∧
    (yp380 = 9815582388 ∧ yp380 < 10000000000 ∧ 10000000000 - yp380 = 184417612 ∧
      91 * yp380 < yukon ∧ yukon < 92 * yp380 ∧
      yukon - 91 * yp380 = 7501928166) := by
  have hy := yp_380 A K L B E n2 d r md ms P T hg h1 h2 hb he hw
  refine ⟨⟨hy, ?_⟩, by decide⟩
  unfold yp380 blockFixed inputBytes at *
  omega

/-- 5. Dual comparison between Regime 1 (`inline200 = 7,287,261,989`, `inline380 = 11,167,773,630`),
the `hb`-constrained cached LP (`mainCached200 = 7,287,261,989`, `mainCached380 = 10,545,558,216`),
and Regime 2 (`yp200 = 6,575,582,388`, `yp380 = 9,815,582,388`), including `hb_gap = 622,215,414`
at 380M and the Yellow-Paper gain `711,679,601` at 200M / `1,352,191,242` at 380M. -/
theorem inline_vs_yellow_paper_and_hb_gap_synthesis_non_vacuous_and_tight :
    (inline200 = 7287261989 ∧ mainCached200 = 7287261989 ∧ yp200 = 6575582388 ∧
      yp200 < inline200 ∧ inline200 - yp200 = 711679601) ∧
    (inline380 = 11167773630 ∧ mainCached380 = 10545558216 ∧ yp380 = 9815582388 ∧
      yp380 < mainCached380 ∧ mainCached380 < inline380 ∧
      inline380 - mainCached380 = 622215414 ∧
      mainCached380 - yp380 = 729975828 ∧
      inline380 - yp380 = 1352191242) ∧
    (inline380 - 10545558216 = 622215414 ∧ inline200 = 7287261989) := by
  refine ⟨by decide, by decide, hb_gap⟩

/-- 6. Full slope hierarchy across Yellow-Paper Regime 2 (`136×` / `91×`), `hb`-constrained cached
(`123×` / `85×`), unconditional inline Regime 1 (`123×` / `80×`), and uncached (`8×` / `4×`). -/
theorem campaign_dual_regime_slope_hierarchy_non_vacuous_and_tight :
    (136 * yp200 < yukon ∧ yukon < 137 * yp200 ∧
      123 * inline200 < yukon ∧ yukon < 124 * inline200 ∧
      123 * mainCached200 < yukon ∧ yukon < 124 * mainCached200 ∧
      8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200) ∧
    (91 * yp380 < yukon ∧ yukon < 92 * yp380 ∧
      85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380 ∧
      80 * inline380 < yukon ∧ yukon < 81 * inline380 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) := by
  decide

/-- 7. Unified block-fixed decomposition (`blockFixed = 370,538,614`, `inputBytes = 134,217,712`,
`gasRows200 = 341,086,592`, `gasRows380 = 625,505,600`, `coldRow = 3,124`, `perTx = 42,382`)
underlying both Regime 1 and Regime 2. -/
theorem unified_block_fixed_and_regime_constants_non_vacuous_and_tight :
    (blockFixed = 370538614 ∧ inputBytes = 134217712 ∧
      blockFixed + inputBytes = 504756326 ∧
      gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
      coldRow = 3124 ∧ perTx = 42382) ∧
    (inline200 - (blockFixed + inputBytes) = 6782505663 ∧
      inline380 - (blockFixed + inputBytes) = 10663017304 ∧
      yp200 - (blockFixed + inputBytes) = 6070826062 ∧
      yp380 - (blockFixed + inputBytes) = 9310826062) := by
  decide

/-- 8. Strictly increasing 128-budget portfolio (`OneHundredTwentyEightShape`, max `900,719,840,000`,
margin `85,474` below Yukon) extending `OneHundredTwentySixShape` (126 budgets, max `900,719,830,000`,
margin `95,474`) and `OneHundredTwentyFourShape` (124 budgets, max `900,719,820,000`, margin `105,474`). -/
theorem one_hundred_twenty_eight_and_one_hundred_twenty_six_budget_hierarchy_non_vacuous_and_tight :
    OneHundredTwentyEightShape ∧
    OneHundredTwentySixShape ∧
    OneHundredTwentyFourShape ∧
    oneHundredTwentyEightExplicitBudgets.length = 128 ∧
    oneHundredTwentyEightExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwentyEightExplicitBudgets, 1212035192 ≤ K ∧ K < 900719925474) ∧
    oneHundredTwentyEightExplicitBudgets.take 126 = oneHundredTwentySixExplicitBudgets ∧
    oneHundredTwentyEightExplicitBudgets.drop 126 = [900719835000, 900719840000] ∧
    oneHundredTwentyEightExplicitBudgets.getLast? = some 900719840000 ∧
    yukon - 900719840000 = 85474 ∧
    yukon - 900719835000 = 90474 :=
  have h128 := one_hundred_twenty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h126 := one_hundred_twenty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h124 := one_hundred_twenty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  ⟨h128,
   h126,
   h124,
   h128.1,
   h128.2.1,
   h128.2.2.1,
   h128.2.2.2.1,
   h128.2.2.2.2.1,
   h128.2.2.2.2.2.1,
   by decide,
   by decide⟩

/-- 9. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)`
across all 128 portfolio budgets, plus explicit certificates at both Regime 1 (`inline200 = 7,287,261,989`,
`inline380 = 11,167,773,630`) and Regime 2 (`yp200 = 6,575,582,388`, `yp380 = 9,815,582,388`)
budgets and at the new endpoints `900,719,835,000` and `900,719,840,000`. -/
theorem one_hundred_twenty_eight_budget_and_dual_regime_lp_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentyEightShape ∧
    (∀ K ∈ oneHundredTwentyEightExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK inline200) (.finite inline200) ∧
    InitE.Certificate (baselineWithFiniteK inline380) (.finite inline380) ∧
    InitE.Certificate (baselineWithFiniteK yp200) (.finite yp200) ∧
    InitE.Certificate (baselineWithFiniteK yp380) (.finite yp380) ∧
    InitE.Certificate (baselineWithFiniteK 900719835000) (.finite 900719835000) ∧
    InitE.Certificate (baselineWithFiniteK 900719840000) (.finite 900719840000) := by
  have hcert := one_hundred_twenty_eight_budget_certificates_non_vacuous_and_tight cert
  refine ⟨hcert.1, hcert.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ inline200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ inline380 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ yp200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ yp380 (by decide) cert
  · exact hcert.2 900719835000 (by decide)
  · exact hcert.2 900719840000 (by decide)

/-- 10. Grand inline-child vs Yellow-Paper MPT dual LP 128-budget campaign master synthesis:
`inline_200` (`inline200 = 7,287,261,989`, `123×`), `inline_380` (`inline380 = 11,167,773,630`, `80×`),
`yp_200` (`yp200 = 6,575,582,388`, `136×`), `yp_380` (`yp380 = 9,815,582,388`, `91×`),
`hb_gap = 622,215,414`, 128 budgets `< yukon` (`last = 900,719,840,000`, margin `85,474`), and
conditional `InitE.Certificate (baselineWithFiniteK K) (.finite K)`. -/
theorem grand_inline_child_mpt_dual_one_hundred_twenty_eight_campaign_master_non_vacuous_and_tight
    (A K L B E n2 n17 d r md ms P T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (cert : CertificateAt 1212035192) :
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000 →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      451 * cost1 A K L B E n2 n17 md ms P T ≤ 3058910053880) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000 →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      451 * cost1 A K L B E n2 n17 md ms P T ≤ 4809020803880) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000 →
      B ≤ r + K + A →
      7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K) →
      11 * cost2 A K L B E n2 d r md ms P T ≤ 66779086680) ∧
    (12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000 →
      B ≤ r + K + A →
      7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K) →
      11 * cost2 A K L B E n2 d r md ms P T ≤ 102419086680) ∧
    (inline200 = 7287261989 ∧ 123 * inline200 < yukon ∧ yukon < 124 * inline200 ∧
      inline380 = 11167773630 ∧ 80 * inline380 < yukon ∧ yukon < 81 * inline380) ∧
    (yp200 = 6575582388 ∧ 136 * yp200 < yukon ∧ yukon < 137 * yp200 ∧
      yp380 = 9815582388 ∧ 91 * yp380 < yukon ∧ yukon < 92 * yp380) ∧
    (inline380 - 10545558216 = 622215414 ∧ inline200 = 7287261989) ∧
    OneHundredTwentyEightShape ∧
    oneHundredTwentyEightExplicitBudgets.getLast? = some 900719840000 ∧
    yukon - 900719840000 = 85474 ∧
    (∀ K_b ∈ oneHundredTwentyEightExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K_b) (.finite K_b)) := by
  have hcert := one_hundred_twenty_eight_budget_certificates_non_vacuous_and_tight cert
  refine ⟨?_, ?_, ?_, ?_, inline_slopes, yp_slopes, hb_gap, hcert.1, by decide, by decide, hcert.2⟩
  · intro hg hw
    exact inline_200 A K L B E n2 n17 md ms P T hg h1 h2 he hw
  · intro hg hw
    exact inline_380 A K L B E n2 n17 md ms P T hg h1 h2 he hw
  · intro hg hb hw
    exact yp_200 A K L B E n2 d r md ms P T hg h1 h2 hb he hw
  · intro hg hb hw
    exact yp_380 A K L B E n2 d r md ms P T hg h1 h2 hb he hw

#print axioms inline200_lp_and_one_hundred_twenty_three_x_slope_non_vacuous_and_tight
#print axioms inline380_lp_eighty_x_slope_and_hb_gap_non_vacuous_and_tight
#print axioms yp200_lp_one_hundred_thirty_six_x_slope_and_tightness_non_vacuous_and_tight
#print axioms yp380_lp_and_ninety_one_x_slope_non_vacuous_and_tight
#print axioms inline_vs_yellow_paper_and_hb_gap_synthesis_non_vacuous_and_tight
#print axioms campaign_dual_regime_slope_hierarchy_non_vacuous_and_tight
#print axioms unified_block_fixed_and_regime_constants_non_vacuous_and_tight
#print axioms one_hundred_twenty_eight_and_one_hundred_twenty_six_budget_hierarchy_non_vacuous_and_tight
#print axioms one_hundred_twenty_eight_budget_and_dual_regime_lp_certificates_non_vacuous_and_tight
#print axioms grand_inline_child_mpt_dual_one_hundred_twenty_eight_campaign_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedInlineChildMptDualOneHundredTwentyEightCampaignMaster
