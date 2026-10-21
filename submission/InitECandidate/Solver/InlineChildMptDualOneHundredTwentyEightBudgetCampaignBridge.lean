import InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster
import InitECandidate.Solver.LoopToStackNamesLabToTargetAndOneHundredTwentyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.InlineChildMptDualOneHundredTwentyEightBudgetCampaignBridge

open InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster
open InitECandidate.Solver.LoopToStackNamesLabToTargetAndOneHundredTwentyEightBudgetMaster
open _root_.InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
  (trueFixed200 trueFixed380)
open _root_.InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
  (gasRows200 gasRows380 coldRow perTx mainCached200 mainCached380 mainUncached200 mainUncached380)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

theorem inline_child_mpt_regime_one_lp_200_and_380_non_vacuous_and_tight :
    (∀ A K L B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      451 * cost1 A K L B E n2 n17 md ms P T ≤ 3058910053880) ∧
    (∀ A K L B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      451 * cost1 A K L B E n2 n17 md ms P T ≤ 4809020803880) :=
  ⟨inline_200, inline_380⟩

theorem inline_child_mpt_regime_two_yp_lp_200_and_380_non_vacuous_and_tight :
    (∀ A K L B E n2 d r md ms P T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ r + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K) →
      11 * cost2 A K L B E n2 d r md ms P T ≤ 66779086680) ∧
    (∀ A K L B E n2 d r md ms P T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ r + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K) →
      11 * cost2 A K L B E n2 d r md ms P T ≤ 102419086680) :=
  ⟨yp_200, yp_380⟩

theorem inline_child_mpt_regime_one_slopes_and_hb_gap_non_vacuous_and_tight :
    (inline200 = 7287261989 ∧ 123 * inline200 < yukon ∧
      yukon < 124 * inline200 ∧ inline380 = 11167773630 ∧
      80 * inline380 < yukon ∧ yukon < 81 * inline380) ∧
    (inline380 - 10545558216 = 622215414 ∧ inline200 = 7287261989) ∧
    (inline200 = mainCached200 ∧ inline380 - mainCached380 = 622215414 ∧
      yukon - 123 * inline200 = 4386700827 ∧
      yukon - 80 * inline380 = 7298035074) := by
  refine ⟨inline_slopes, hb_gap, ?_⟩
  decide

theorem inline_child_mpt_regime_two_yp_slopes_and_tightness_non_vacuous_and_tight :
    (yp200 = 6575582388 ∧ 136 * yp200 < yukon ∧ yukon < 137 * yp200 ∧
      yp380 = 9815582388 ∧ 91 * yp380 < yukon ∧ yukon < 92 * yp380) ∧
    (11 * cost2 0 0 0 0 0 0 6100805 0 0 0 200000000 0 ≤ 66779086680 ∧
      66779086680 - 11 * cost2 0 0 0 0 0 0 6100805 0 0 0 200000000 0 < 11 * 405 ∧
      7 * 0 + 22 * 6100805 ≤ inputBytes) ∧
    (inline200 - yp200 = 711679601 ∧ inline380 - yp380 = 1352191242 ∧
      mainCached380 - yp380 = 729975828) := by
  refine ⟨yp_slopes, yp_tight, ?_⟩
  decide

theorem sstore_dirty_key_gas_decomposition_and_slopes_one_hundred_twenty_eight_bridge_non_vacuous_and_tight :
    (blockFixed = 370538614 ∧ inputBytes = 134217712 ∧
      gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
      trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
      coldRow = 3124 ∧ perTx = 42382) ∧
    (mainCached200 = 7287261989 ∧ 123 * mainCached200 < yukon ∧
      yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧
      85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380) ∧
    (mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) :=
  ⟨⟨rfl, rfl, decomposition_non_vacuous_and_tight⟩,
   cached_slopes_non_vacuous_and_tight,
   uncached_slopes_non_vacuous_and_tight⟩

theorem sstore_dirty_key_gas_cached_lp_one_hundred_twenty_eight_bridge_non_vacuous_and_tight :
    (∀ A K L B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      451 * GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.costC A K L B E n2 n17 md ms P T ≤ 3058910053880) ∧
    (∀ A K L B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      11803 * GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.costC A K L B E n2 n17 md ms P T ≤ 118511584702912) :=
  ⟨cached200_non_vacuous_and_tight, cached380_non_vacuous_and_tight⟩

theorem sstore_dirty_key_gas_uncached_lp_one_hundred_twenty_eight_bridge_non_vacuous_and_tight :
    (∀ A K L B E n2 n17 md ms P C T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.costU A K L B E n2 n17 md ms P C T ≤ 25461560820280) ∧
    (∀ A K L B E n2 n17 md ms P C T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * GuestSstoreDirtyKeyGasAndSubSevenBillionMaster.costU A K L B E n2 n17 md ms P C T ≤ 47863280820280) :=
  ⟨uncached200_non_vacuous_and_tight, uncached380_non_vacuous_and_tight⟩

theorem one_hundred_twenty_eight_budget_portfolio_below_yukon_and_margin_non_vacuous_and_tight :
    OneHundredTwentyEightShape ∧
    oneHundredTwentyEightExplicitBudgets.length = 128 ∧
    oneHundredTwentyEightExplicitBudgets.getLast? = some 900719840000 ∧
    yukon - 900719840000 = 85474 ∧
    (oneHundredTwentyEightExplicitBudgets.Pairwise (· < ·) ∧
      (∀ K ∈ oneHundredTwentyEightExplicitBudgets, K < 900719925474)) :=
  ⟨one_hundred_twenty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.2.2,
   one_hundred_twenty_eight_budgets_under_yukon_non_vacuous_and_tight⟩

theorem one_hundred_twenty_eight_budget_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentyEightShape ∧
      oneHundredTwentyEightExplicitBudgets.length = 128 ∧
      oneHundredTwentyEightExplicitBudgets.getLast? = some 900719840000 ∧
      yukon - 900719840000 = 85474 ∧
      (∀ K ∈ oneHundredTwentyEightExplicitBudgets,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(one_hundred_twenty_eight_budget_certificates_non_vacuous_and_tight cert).1,
   one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.2.2,
   (one_hundred_twenty_eight_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem inline_child_mpt_dual_one_hundred_twenty_eight_budget_campaign_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (inline200 = 7287261989 ∧ 123 * inline200 < yukon ∧
      yukon < 124 * inline200 ∧ inline380 = 11167773630 ∧
      80 * inline380 < yukon ∧ yukon < 81 * inline380 ∧
      inline380 - 10545558216 = 622215414) ∧
    (yp200 = 6575582388 ∧ 136 * yp200 < yukon ∧ yukon < 137 * yp200 ∧
      yp380 = 9815582388 ∧ 91 * yp380 < yukon ∧ yukon < 92 * yp380) ∧
    (mainCached200 = 7287261989 ∧ mainCached380 = 10545558216 ∧
      mainUncached200 = 110593745629 ∧ mainUncached380 = 207570888486) ∧
    (OneHundredTwentyEightShape ∧
      oneHundredTwentyEightExplicitBudgets.length = 128 ∧
      oneHundredTwentyEightExplicitBudgets.getLast? = some 900719840000 ∧
      yukon - 900719840000 = 85474 ∧
      yukon = 900719925474) ∧
    (∀ K ∈ oneHundredTwentyEightExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨inline_slopes.1, inline_slopes.2.1, inline_slopes.2.2.1,
    inline_slopes.2.2.2.1, inline_slopes.2.2.2.2.1, inline_slopes.2.2.2.2.2,
    hb_gap.1⟩,
   yp_slopes,
   ⟨cached_slopes_non_vacuous_and_tight.1,
    cached_slopes_non_vacuous_and_tight.2.2.2.1,
    uncached_slopes_non_vacuous_and_tight.1,
    uncached_slopes_non_vacuous_and_tight.2.2.2.1⟩,
   ⟨(one_hundred_twenty_eight_budget_certificates_non_vacuous_and_tight cert).1,
    one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.1,
    one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.2.1,
    one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.2.2,
    rfl⟩,
   (one_hundred_twenty_eight_budget_certificates_non_vacuous_and_tight cert).2⟩

#print axioms inline_child_mpt_regime_one_lp_200_and_380_non_vacuous_and_tight
#print axioms inline_child_mpt_regime_two_yp_lp_200_and_380_non_vacuous_and_tight
#print axioms inline_child_mpt_regime_one_slopes_and_hb_gap_non_vacuous_and_tight
#print axioms inline_child_mpt_regime_two_yp_slopes_and_tightness_non_vacuous_and_tight
#print axioms sstore_dirty_key_gas_decomposition_and_slopes_one_hundred_twenty_eight_bridge_non_vacuous_and_tight
#print axioms sstore_dirty_key_gas_cached_lp_one_hundred_twenty_eight_bridge_non_vacuous_and_tight
#print axioms sstore_dirty_key_gas_uncached_lp_one_hundred_twenty_eight_bridge_non_vacuous_and_tight
#print axioms one_hundred_twenty_eight_budget_portfolio_below_yukon_and_margin_non_vacuous_and_tight
#print axioms one_hundred_twenty_eight_budget_certificates_campaign_non_vacuous_and_tight
#print axioms inline_child_mpt_dual_one_hundred_twenty_eight_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.InlineChildMptDualOneHundredTwentyEightBudgetCampaignBridge
