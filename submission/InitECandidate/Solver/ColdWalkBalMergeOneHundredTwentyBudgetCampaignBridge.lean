import InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster
import InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyBudgetCampaignBridge

open InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster
open InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster
open _root_.InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
  (trueFixed200 trueFixed380 oldFixed200 oldFixed380)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

theorem cold_walk_bal_merge_block_fixed_and_decomposition_non_vacuous_and_tight :
    blockFixed = 370538614 ∧
    (gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
      trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
      coldRow = 3124 ∧ perTx = 42382) ∧
    (GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.perTx = 40782 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.perTx * 16666 = 679672812 ∧
      trueFixed200 + GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.perTx * 16666 = oldFixed200 ∧
      trueFixed380 + GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.perTx * 16666 = oldFixed380 ∧
      trueFixed200 = 711625206 ∧ trueFixed380 = 996044214) :=
  ⟨rfl, decomposition, decomposition_non_vacuous_and_tight⟩

theorem cold_walk_bal_merge_cached_lp_200_and_380_non_vacuous_and_tight :
    (∀ A K L B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      99 * costC A K L B E n2 n17 md ms P T ≤ 671624630120) ∧
    (∀ A K L B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912) :=
  ⟨cached200, cached380⟩

theorem cold_walk_bal_merge_uncached_lp_200_and_380_non_vacuous_and_tight :
    (∀ A K L B E n2 n17 md ms P C T : Nat,
      12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280) ∧
    (∀ A K L B E n2 n17 md ms P C T : Nat,
      12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280) :=
  ⟨uncached200, uncached380⟩

theorem cold_walk_bal_merge_cached_one_hundred_twenty_three_x_and_eighty_five_x_slopes_non_vacuous_and_tight :
    (mainCached200 = 7288843499 ∧ 123 * mainCached200 < yukon ∧
      yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧
      85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380) ∧
    (7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 288843499 ∧
      mainCached200 - 6993799055 = 295044444) ∧
    (yukon - 123 * mainCached200 = 4192175097 ∧
      yukon - 85 * mainCached380 = 4347477114) := by
  refine ⟨cached_slopes, no_sub_seven, ?_⟩
  decide

theorem cold_walk_bal_merge_uncached_eight_x_and_four_x_slopes_non_vacuous_and_tight :
    (mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) ∧
    (yukon - 8 * mainUncached200 = 15969960442 ∧
      yukon - 4 * mainUncached380 = 70436371530) := by
  refine ⟨uncached_slopes, ?_⟩
  decide

theorem cold_walk_bal_merge_strictly_improves_tx_gas_coupled_one_hundred_twenty_two_x_non_vacuous_and_tight :
    (GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 = 7334885647 ∧
      122 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 < yukon ∧
      yukon < 123 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached380 = 10869105236 ∧
      82 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached380 < yukon ∧
      yukon < 83 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached380) ∧
    (mainCached200 < GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 ∧
      mainCached380 < GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached380 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached200 - mainCached200 = 46042148 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainCached380 - mainCached380 = 323547020) ∧
    (mainUncached200 < GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainUncached200 ∧
      mainUncached380 < GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainUncached380 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainUncached200 - mainUncached200 = 341086592 ∧
      GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.mainUncached380 - mainUncached380 = 625505600) := by
  refine ⟨cached_slopes_non_vacuous_and_tight, ?_, ?_⟩ <;> decide

theorem tx_gas_coupled_cached_and_uncached_lp_one_hundred_twenty_bridge_non_vacuous_and_tight :
    (∀ A K B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2100 * K + P ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      33 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.costC A K B E n2 n17 md ms P T ≤ 214138410040) ∧
    (∀ A K B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2100 * K + P ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      11803 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.costC A K B E n2 n17 md ms P T ≤ 114947567578464) ∧
    (∀ A K B E n2 n17 md ms P C T : Nat,
      12000 * T + 2400 * A + 2100 * K + P + 126 * C ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.costU A K B E n2 n17 md ms P C T ≤ 25461560820280) ∧
    (∀ A K B E n2 n17 md ms P C T : Nat,
      12000 * T + 2400 * A + 2100 * K + P + 126 * C ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster.costU A K B E n2 n17 md ms P C T ≤ 47863280820280) :=
  ⟨cached200_non_vacuous_and_tight,
   cached380_non_vacuous_and_tight,
   uncached200_non_vacuous_and_tight,
   uncached380_non_vacuous_and_tight⟩

theorem one_hundred_twenty_budget_portfolio_below_yukon_and_margin_non_vacuous_and_tight :
    OneHundredTwentyShape ∧
    oneHundredTwentyExplicitBudgets.length = 120 ∧
    oneHundredTwentyExplicitBudgets.getLast? = some 900719800000 ∧
    yukon - 900719800000 = 125474 ∧
    (oneHundredTwentyExplicitBudgets.Pairwise (· < ·) ∧
      (∀ K ∈ oneHundredTwentyExplicitBudgets, K < 900719925474)) :=
  ⟨one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.2.2,
   one_hundred_twenty_budgets_under_yukon_non_vacuous_and_tight⟩

theorem one_hundred_twenty_budget_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentyShape ∧
      oneHundredTwentyExplicitBudgets.length = 120 ∧
      oneHundredTwentyExplicitBudgets.getLast? = some 900719800000 ∧
      yukon - 900719800000 = 125474 ∧
      (∀ K ∈ oneHundredTwentyExplicitBudgets,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(one_hundred_twenty_budget_certificates_non_vacuous_and_tight cert).1,
   one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.2.2,
   (one_hundred_twenty_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem cold_walk_bal_merge_one_hundred_twenty_budget_campaign_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (blockFixed = 370538614 ∧ gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
      trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
      coldRow = 3124 ∧ perTx = 42382) ∧
    (mainCached200 = 7288843499 ∧ 123 * mainCached200 < yukon ∧
      yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧
      85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380 ∧
      7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 288843499 ∧
      mainCached200 - 6993799055 = 295044444) ∧
    (mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) ∧
    (OneHundredTwentyShape ∧
      oneHundredTwentyExplicitBudgets.length = 120 ∧
      oneHundredTwentyExplicitBudgets.getLast? = some 900719800000 ∧
      yukon - 900719800000 = 125474 ∧
      yukon = 900719925474) ∧
    (∀ K ∈ oneHundredTwentyExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨rfl, decomposition⟩,
   ⟨cached_slopes.1,
    cached_slopes.2.1,
    cached_slopes.2.2.1,
    cached_slopes.2.2.2.1,
    cached_slopes.2.2.2.2.1,
    cached_slopes.2.2.2.2.2,
    no_sub_seven.1,
    no_sub_seven.2.1,
    no_sub_seven.2.2⟩,
   uncached_slopes,
   ⟨(one_hundred_twenty_budget_certificates_non_vacuous_and_tight cert).1,
    one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.1,
    one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.2.1,
    one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.2.2,
    rfl⟩,
   (one_hundred_twenty_budget_certificates_non_vacuous_and_tight cert).2⟩

#print axioms cold_walk_bal_merge_block_fixed_and_decomposition_non_vacuous_and_tight
#print axioms cold_walk_bal_merge_cached_lp_200_and_380_non_vacuous_and_tight
#print axioms cold_walk_bal_merge_uncached_lp_200_and_380_non_vacuous_and_tight
#print axioms cold_walk_bal_merge_cached_one_hundred_twenty_three_x_and_eighty_five_x_slopes_non_vacuous_and_tight
#print axioms cold_walk_bal_merge_uncached_eight_x_and_four_x_slopes_non_vacuous_and_tight
#print axioms cold_walk_bal_merge_strictly_improves_tx_gas_coupled_one_hundred_twenty_two_x_non_vacuous_and_tight
#print axioms tx_gas_coupled_cached_and_uncached_lp_one_hundred_twenty_bridge_non_vacuous_and_tight
#print axioms one_hundred_twenty_budget_portfolio_below_yukon_and_margin_non_vacuous_and_tight
#print axioms one_hundred_twenty_budget_certificates_campaign_non_vacuous_and_tight
#print axioms cold_walk_bal_merge_one_hundred_twenty_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyBudgetCampaignBridge
