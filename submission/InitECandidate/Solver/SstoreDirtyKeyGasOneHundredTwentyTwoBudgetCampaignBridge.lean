import InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
import InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.SstoreDirtyKeyGasOneHundredTwentyTwoBudgetCampaignBridge

open InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
open InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster
open _root_.InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
  (trueFixed200 trueFixed380)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

def sstoreKeyGas : Nat := 2100 + 2 + 3

theorem sstore_dirty_key_gas_and_block_fixed_decomposition_non_vacuous_and_tight :
    (sstoreKeyGas = 2105 ∧ sstoreKeyGas - 2100 = 5 ∧ blockFixed = 370538614) ∧
    (gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
      trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
      coldRow = 3124 ∧ perTx = 42382) ∧
    (2060 + 90 + coldRow = 5274 ∧ 349 + coldRow = 3473) :=
  ⟨⟨rfl, rfl, rfl⟩, decomposition, ⟨rfl, rfl⟩⟩

theorem sstore_dirty_key_gas_cached_lp_200_and_380_non_vacuous_and_tight :
    (∀ A K L B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      451 * costC A K L B E n2 n17 md ms P T ≤ 3058910053880) ∧
    (∀ A K L B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912) :=
  ⟨cached200, cached380⟩

theorem sstore_dirty_key_gas_uncached_lp_200_and_380_non_vacuous_and_tight :
    (∀ A K L B E n2 n17 md ms P C T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280) ∧
    (∀ A K L B E n2 n17 md ms P C T : Nat,
      12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280) :=
  ⟨uncached200, uncached380⟩

theorem sstore_dirty_key_gas_cached_one_hundred_twenty_three_x_and_eighty_five_x_slopes_non_vacuous_and_tight :
    (mainCached200 = 7287261989 ∧ 123 * mainCached200 < yukon ∧
      yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧
      85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380) ∧
    (7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 287261989 ∧
      7288843499 - mainCached200 = 1581510) ∧
    (yukon - 123 * mainCached200 = 4386700827 ∧
      yukon - 85 * mainCached380 = 4347477114) := by
  refine ⟨cached_slopes, no_sub_seven, ?_⟩
  decide

theorem sstore_dirty_key_gas_uncached_eight_x_and_four_x_slopes_non_vacuous_and_tight :
    (mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) ∧
    (yukon - 8 * mainUncached200 = 15969960442 ∧
      yukon - 4 * mainUncached380 = 70436371530) := by
  refine ⟨uncached_slopes, ?_⟩
  decide

theorem sstore_dirty_key_gas_improves_cold_walk_bal_merge_non_vacuous_and_tight :
    (GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 = 7288843499 ∧
      123 * GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 < yukon ∧
      yukon < 124 * GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 ∧
      GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached380 = 10545558216 ∧
      85 * GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached380 < yukon ∧
      yukon < 86 * GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached380) ∧
    (mainCached200 < GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 ∧
      GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached200 - mainCached200 = 1581510 ∧
      mainCached380 = GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainCached380 ∧
      mainUncached200 = GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainUncached200 ∧
      mainUncached380 = GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.mainUncached380) := by
  refine ⟨cached_slopes_non_vacuous_and_tight, ?_⟩
  decide

theorem cold_walk_bal_merge_cached_and_uncached_lp_one_hundred_twenty_two_bridge_non_vacuous_and_tight :
    (∀ A K L B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      99 * GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.costC A K L B E n2 n17 md ms P T ≤ 671624630120) ∧
    (∀ A K L B E n2 n17 md ms P T : Nat,
      12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      11803 * GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.costC A K L B E n2 n17 md ms P T ≤ 118511584702912) ∧
    (∀ A K L B E n2 n17 md ms P C T : Nat,
      12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.costU A K L B E n2 n17 md ms P C T ≤ 25461560820280) ∧
    (∀ A K L B E n2 n17 md ms P C T : Nat,
      12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster.costU A K L B E n2 n17 md ms P C T ≤ 47863280820280) :=
  ⟨cached200_non_vacuous_and_tight,
   cached380_non_vacuous_and_tight,
   uncached200_non_vacuous_and_tight,
   uncached380_non_vacuous_and_tight⟩

theorem one_hundred_twenty_two_budget_portfolio_below_yukon_and_margin_non_vacuous_and_tight :
    OneHundredTwentyTwoShape ∧
    oneHundredTwentyTwoExplicitBudgets.length = 122 ∧
    oneHundredTwentyTwoExplicitBudgets.getLast? = some 900719810000 ∧
    yukon - 900719810000 = 115474 ∧
    (oneHundredTwentyTwoExplicitBudgets.Pairwise (· < ·) ∧
      (∀ K ∈ oneHundredTwentyTwoExplicitBudgets, K < 900719925474)) :=
  ⟨one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.2.2,
   one_hundred_twenty_two_budgets_under_yukon_non_vacuous_and_tight⟩

theorem one_hundred_twenty_two_budget_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwentyTwoShape ∧
      oneHundredTwentyTwoExplicitBudgets.length = 122 ∧
      oneHundredTwentyTwoExplicitBudgets.getLast? = some 900719810000 ∧
      yukon - 900719810000 = 115474 ∧
      (∀ K ∈ oneHundredTwentyTwoExplicitBudgets,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight cert).1,
   one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.2.2,
   (one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem sstore_dirty_key_gas_one_hundred_twenty_two_budget_campaign_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (sstoreKeyGas = 2105 ∧ blockFixed = 370538614 ∧ gasRows200 = 341086592 ∧
      gasRows380 = 625505600 ∧ trueFixed200 = blockFixed + gasRows200 ∧
      trueFixed380 = blockFixed + gasRows380 ∧ coldRow = 3124 ∧ perTx = 42382) ∧
    (mainCached200 = 7287261989 ∧ 123 * mainCached200 < yukon ∧
      yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧
      85 * mainCached380 < yukon ∧ yukon < 86 * mainCached380 ∧
      7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 287261989 ∧
      7288843499 - mainCached200 = 1581510) ∧
    (mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) ∧
    (OneHundredTwentyTwoShape ∧
      oneHundredTwentyTwoExplicitBudgets.length = 122 ∧
      oneHundredTwentyTwoExplicitBudgets.getLast? = some 900719810000 ∧
      yukon - 900719810000 = 115474 ∧
      yukon = 900719925474) ∧
    (∀ K ∈ oneHundredTwentyTwoExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨rfl, rfl, decomposition⟩,
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
   ⟨(one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight cert).1,
    one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.1,
    one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.2.1,
    one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.2.2,
    rfl⟩,
   (one_hundred_twenty_two_budget_certificates_non_vacuous_and_tight cert).2⟩

#print axioms sstore_dirty_key_gas_and_block_fixed_decomposition_non_vacuous_and_tight
#print axioms sstore_dirty_key_gas_cached_lp_200_and_380_non_vacuous_and_tight
#print axioms sstore_dirty_key_gas_uncached_lp_200_and_380_non_vacuous_and_tight
#print axioms sstore_dirty_key_gas_cached_one_hundred_twenty_three_x_and_eighty_five_x_slopes_non_vacuous_and_tight
#print axioms sstore_dirty_key_gas_uncached_eight_x_and_four_x_slopes_non_vacuous_and_tight
#print axioms sstore_dirty_key_gas_improves_cold_walk_bal_merge_non_vacuous_and_tight
#print axioms cold_walk_bal_merge_cached_and_uncached_lp_one_hundred_twenty_two_bridge_non_vacuous_and_tight
#print axioms one_hundred_twenty_two_budget_portfolio_below_yukon_and_margin_non_vacuous_and_tight
#print axioms one_hundred_twenty_two_budget_certificates_campaign_non_vacuous_and_tight
#print axioms sstore_dirty_key_gas_one_hundred_twenty_two_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.SstoreDirtyKeyGasOneHundredTwentyTwoBudgetCampaignBridge
