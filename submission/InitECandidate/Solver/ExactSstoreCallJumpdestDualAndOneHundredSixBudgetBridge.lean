import InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster
import InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.ExactSstoreCallJumpdestDualAndOneHundredSixBudgetBridge

open InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster
open InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Straight-line charges: `sstoreBaseTicks = 110 ≤ 2000`, `accountAccessBaseTicks = 349 ≤ 10000`,
`sloadBaseTicks + 7 * 28 ≤ 18 * 100`. -/
theorem charges_ok_bridge_non_vacuous_and_tight :
    sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
      sloadBaseTicks + 7 * 28 ≤ 18 * 100 :=
  charges_ok

/-- 2. One `compute_jumpdests` scan costs more than `18` ticks per gas, by more than `28×`. -/
theorem scan_ratio_bridge_non_vacuous_and_tight :
    18 * callGas < maxCode ∧ 28 * (18 * callGas) < maxCode :=
  scan_ratio

/-- 3. Uncached scan at 200M: `104,025,358,336` ticks, so Yukon admits only `8×`. -/
theorem attack200_bridge_non_vacuous_and_tight :
    jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon ∧
      yukon < 9 * jumpdestTicks 200000000 :=
  attack200

/-- 4. Uncached scan at 380M: `197,648,252,928` ticks, so Yukon admits only `4×`. -/
theorem attack380_bridge_non_vacuous_and_tight :
    jumpdestTicks 380000000 = 197648252928 ∧ 4 * jumpdestTicks 380000000 < yukon ∧
      yukon < 5 * jumpdestTicks 380000000 :=
  attack380

/-- 5. The previous `108×` total is broken by more than `12×` once the uncached scan is counted. -/
theorem previous_broken_bridge_non_vacuous_and_tight :
    12 * 8298113205 < jumpdestTicks 200000000 :=
  previous_broken

/-- 6. With one scan per distinct code: `8,432,330,917` ticks (`106×`) at 200M and
`11,992,988,211` ticks (`75×`) at 380M. -/
theorem cached_bridge_non_vacuous_and_tight :
    8298113205 + 134217712 = 8432330917 ∧ 106 * 8432330917 < yukon ∧
      yukon < 107 * 8432330917 ∧ 11858770499 + 134217712 = 11992988211 ∧
      75 * 11992988211 < yukon ∧ yukon < 76 * 11992988211 :=
  cached

/-- 7. Intrinsic gas `12,000` gives `200000000 / 12000 = 16666` user transactions. -/
theorem tx_count_bridge_non_vacuous_and_tight :
    200000000 / 12000 = 16666 ∧ 200000000 / 21000 = 9523 :=
  tx_count

/-- 8. The 106-budget table: 106 strictly increasing budgets, last entry 894,500,000,000, all
under Yukon 900,719,925,474. -/
theorem one_hundred_six_explicit_table_non_vacuous_and_tight :
    OneHundredSixShape ∧
    oneHundredSixExplicitFiniteKBugdetTable.length = 106 ∧
    oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 ∧
    yukon - 894500000000 = 6219925474 :=
  ⟨one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_six_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_six_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_six_budget_last_margin_non_vacuous_and_tight.2.2.2⟩

/-- 9. Every one of the 106 budgets carries a finite certificate, from one base certificate. -/
theorem one_hundred_six_certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    OneHundredSixShape ∧
    (∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  one_hundred_six_budget_certificates_non_vacuous_and_tight cert

/-- 10. Grand bridge: the uncached jumpdest attack, the cached 106× bound, and the 106-budget
table with finite certificates. -/
theorem global_gas_coupled_one_hundred_eight_x_and_one_hundred_six_budget_master_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon) ∧
    (8298113205 + 134217712 = 8432330917 ∧ 106 * 8432330917 < yukon) ∧
    (200000000 / 12000 = 16666) ∧
    (OneHundredSixShape ∧
      oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 ∧
      ∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨attack200.1, attack200.2.1⟩,
   ⟨cached.1, cached.2.1⟩,
   tx_count.1,
   ⟨(one_hundred_six_budget_certificates_non_vacuous_and_tight cert).1,
    one_hundred_six_budget_last_margin_non_vacuous_and_tight.2.1,
    (one_hundred_six_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.ExactSstoreCallJumpdestDualAndOneHundredSixBudgetBridge
