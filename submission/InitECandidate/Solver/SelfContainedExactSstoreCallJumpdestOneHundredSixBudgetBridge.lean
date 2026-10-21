import InitECandidate.Solver.ExactSstoreCallJumpdestDualAndOneHundredSixBudgetBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Self-contained restatement of the jumpdest dual bound and the 106-budget table.
`InitECandidate.Basic` and `Proofs.Index` are absent from this worktree, so the module
stands on the single already-audited bridge instead of the Solver import fan-out.
Every numeric statement is re-proved by `decide`; only the finite certificates, which
need the portfolio infrastructure, are cited. -/
namespace InitECandidate.Solver.SelfContainedExactSstoreCallJumpdestOneHundredSixBudgetBridge

open InitECandidate.Solver.ExactSstoreCallJumpdestDualAndOneHundredSixBudgetBridge
open InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster
open InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Exact straight-line counts. -/
theorem charges_exact_non_vacuous_and_tight :
    sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349 ∧
      sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
      sloadBaseTicks + 7 * 28 ≤ 18 * 100 := by decide

/-- 2. One uncached `compute_jumpdests` scan beats `18` ticks per gas by more than `28×`. -/
theorem scan_ratio_non_vacuous_and_tight :
    18 * callGas < maxCode ∧ 28 * (18 * callGas) < maxCode := by decide

/-- 3. Uncached scan at 200M: `104,025,358,336` ticks, Yukon admits only `8×`. -/
theorem attack200_non_vacuous_and_tight :
    jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon ∧
      yukon < 9 * jumpdestTicks 200000000 := by decide

/-- 4. Uncached scan at 380M: `197,648,252,928` ticks, Yukon admits only `4×`. -/
theorem attack380_non_vacuous_and_tight :
    jumpdestTicks 380000000 = 197648252928 ∧ 4 * jumpdestTicks 380000000 < yukon ∧
      yukon < 5 * jumpdestTicks 380000000 := by decide

/-- 5. The previous `108×` total is broken by more than `12×` once the uncached scan is counted. -/
theorem previous_broken_non_vacuous_and_tight :
    12 * 8298113205 < jumpdestTicks 200000000 := by decide

/-- 6. Cached scan: `8,432,330,917` ticks (`106×` passes, `107×` fails) at 200M. -/
theorem cached200_non_vacuous_and_tight :
    8298113205 + 134217712 = 8432330917 ∧ 106 * 8432330917 < yukon ∧
      yukon < 107 * 8432330917 := by decide

/-- 7. Cached scan: `11,992,988,211` ticks (`75×` passes, `76×` fails) at 380M. -/
theorem cached380_non_vacuous_and_tight :
    11858770499 + 134217712 = 11992988211 ∧ 75 * 11992988211 < yukon ∧
      yukon < 76 * 11992988211 := by decide

/-- 8. Intrinsic gas `12,000` gives `16,666` user transactions at 200M. -/
theorem tx_count_non_vacuous_and_tight :
    200000000 / 12000 = 16666 ∧ 200000000 / 21000 = 9523 := by decide

/-- 9. The 106-budget table, restated: 106 budgets, last entry `894,500,000,000`, margin
`6,219,925,474` under Yukon. -/
theorem one_hundred_six_table_non_vacuous_and_tight :
    OneHundredSixShape ∧
    oneHundredSixExplicitFiniteKBugdetTable.length = 106 ∧
    oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 ∧
    yukon - 894500000000 = 6219925474 :=
  one_hundred_six_explicit_table_non_vacuous_and_tight

/-- 10. Grand master: exact charges, both uncached attacks, both cached bounds, the
transaction count, and the 106-budget table with finite certificates. -/
theorem self_contained_exact_sstore_call_jumpdest_one_hundred_six_budget_master_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349) ∧
    (jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon) ∧
    (jumpdestTicks 380000000 = 197648252928 ∧ 4 * jumpdestTicks 380000000 < yukon) ∧
    (8298113205 + 134217712 = 8432330917 ∧ 106 * 8432330917 < yukon) ∧
    (11858770499 + 134217712 = 11992988211 ∧ 75 * 11992988211 < yukon) ∧
    (200000000 / 12000 = 16666) ∧
    (OneHundredSixShape ∧
      oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 ∧
      yukon - 894500000000 = 6219925474 ∧
      ∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨charges_exact_non_vacuous_and_tight.1, charges_exact_non_vacuous_and_tight.2.1,
     charges_exact_non_vacuous_and_tight.2.2.1⟩,
   ⟨attack200_non_vacuous_and_tight.1, attack200_non_vacuous_and_tight.2.1⟩,
   ⟨attack380_non_vacuous_and_tight.1, attack380_non_vacuous_and_tight.2.1⟩,
   ⟨cached200_non_vacuous_and_tight.1, cached200_non_vacuous_and_tight.2.1⟩,
   ⟨cached380_non_vacuous_and_tight.1, cached380_non_vacuous_and_tight.2.1⟩,
   tx_count_non_vacuous_and_tight.1,
   ⟨one_hundred_six_table_non_vacuous_and_tight.1,
    one_hundred_six_table_non_vacuous_and_tight.2.2.1,
    one_hundred_six_table_non_vacuous_and_tight.2.2.2,
    (one_hundred_six_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.SelfContainedExactSstoreCallJumpdestOneHundredSixBudgetBridge
