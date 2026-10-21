import InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster
import InitECandidate.Solver.TwoItemNodeRehashSeventyXAndNinetyEightBudgetBridge
import InitECandidate.Solver.TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredBudgetBridge

open InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster
open InitECandidate.Solver.TwoItemNodeRehashSeventyXAndNinetyEightBudgetBridge
open InitECandidate.Solver.TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. `merge_tx_into_block`: 65,422,992 at 200M and 101,802,000 at 380M, both under the
500,000,000 placeholder. -/
theorem merge_vals_bridge_non_vacuous_and_tight :
    mergeTicks 200000000 = 65422992 ∧ mergeTicks 380000000 = 101802000 ∧
      mergeTicks 380000000 < 500000000 :=
  merge_vals

/-- 2. `build_block_access_list_rlp`: 144,000,000 at 200M and 273,600,000 at 380M, against the
300,000,000 placeholder. -/
theorem bal_vals_bridge_non_vacuous_and_tight :
    balTicks 200000000 = 144000000 ∧ balTicks 380000000 = 273600000 :=
  bal_vals

/-- 3. One salted `htab_set` fits the per-entry merge charge, and a cold SSTORE is 21 gas units. -/
theorem entry_charge_bridge_non_vacuous_and_tight :
    12 + 2 * 8 ≤ 60 ∧ 2100 / 100 = 21 :=
  entry_charge

/-- 4. `main200 = 12,218,768,760`: 73× Yukon passes, 74× fails. -/
theorem main200_slope_bridge_non_vacuous_and_tight :
    main200 = 12218768760 ∧ 73 * main200 < yukon ∧ yukon < 74 * main200 :=
  main200_slope

/-- 5. `main380 = 18,978,748,659`: 47× Yukon passes, 48× fails. -/
theorem main380_slope_bridge_non_vacuous_and_tight :
    main380 = 18978748659 ∧ 47 * main380 < yukon ∧ yukon < 48 * main380 :=
  main380_slope

/-- 6. 75× at 200M would need `main200 ≤ 12,009,599,006`, and the real total is above that. -/
theorem no_75_bridge_non_vacuous_and_tight :
    yukon / 75 = 12009599006 ∧ yukon < 75 * main200 :=
  no_75

/-- 7. Margins at both ceilings. -/
theorem margins_bridge_non_vacuous_and_tight :
    yukon - 73 * main200 = 8749805994 ∧ yukon - 47 * main380 = 8718738501 :=
  margins

/-- 8. The 100-budget table: 100 strictly increasing budgets, last entry 886,500,180,428, all
under Yukon 900,719,925,474. -/
theorem one_hundred_explicit_table_bridge_non_vacuous_and_tight :
    OneHundredShape ∧
    oneHundredExplicitFiniteKBugdetTable.length = 100 ∧
    oneHundredExplicitFiniteKBugdetTable.getLast? = some 886500180428 ∧
    yukon - 886500180428 = 14219745046 :=
  ⟨one_hundred_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_budget_last_margin_non_vacuous_and_tight.2.2.2⟩

/-- 9. Every one of the 100 budgets carries a finite certificate, from one base certificate. -/
theorem one_hundred_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    OneHundredShape ∧
    (∀ K ∈ oneHundredExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  one_hundred_budget_certificates_non_vacuous_and_tight cert

/-- 10. Grand bridge: the exact merge and BAL rows, the 73× total, and the 100-budget table
with finite certificates. -/
theorem exact_merge_bal_seventy_three_x_and_one_hundred_budget_bridge_master_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (mergeTicks 200000000 = 65422992 ∧ balTicks 200000000 = 144000000) ∧
    (main200 = 12218768760 ∧ 73 * main200 < yukon ∧ yukon < 74 * main200) ∧
    (main380 = 18978748659 ∧ 47 * main380 < yukon ∧ yukon < 48 * main380) ∧
    (OneHundredShape ∧
      oneHundredExplicitFiniteKBugdetTable.getLast? = some 886500180428 ∧
      ∀ K ∈ oneHundredExplicitFiniteKBugdetTable,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨merge_vals.1, bal_vals.1⟩,
   main200_slope,
   main380_slope,
   ⟨(one_hundred_budget_certificates_non_vacuous_and_tight cert).1,
    one_hundred_budget_last_margin_non_vacuous_and_tight.2.1,
    (one_hundred_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredBudgetBridge
