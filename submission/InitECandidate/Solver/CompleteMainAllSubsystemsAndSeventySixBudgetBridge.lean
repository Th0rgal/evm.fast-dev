import InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
import InitECandidate.Solver.WithdrawalsSszLimitAndSeventyFourBudgetBridge
import InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventySixBudgetBridge`

Bridge between the complete-`main` synthesis, the 74-budget withdrawal bridge, and the
76-budget master.

* At the `200M` gas budget, `main200 = 200,485,906,743` splits into `gasEnv200 =
  156,088,992,805`, `witnessMpt = 38,946,487,944` and `restTerms = 5,450,425,994`. The
  slope-one margin is `700,234,018,731`, and `4 · main200 < yukon < 5 · main200` with a
  quarter margin of `24,694,074,625`.
* At the adversarial `380M` budget (six extra `30M` system calls), `gasEnv380 =
  467,569,086,329` and `main380 = 511,966,000,267`, still under Yukon by
  `388,753,925,207` while `2×` crosses. The BAL row bounds `≤ 190,000` cold keys inside
  `300,000,000` ticks.
* The 76 budgets grow strictly under Yukon `900,719,925,474`.
-/

namespace InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventySixBudgetBridge

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
open InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster

/-- 1. The two extra system contracts: `2 + 4 = 6`, budget `380,000,000` gas. -/
theorem system_gas_non_vacuous_and_tight :
    2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000 :=
  system_gas

/-- 2. The six residual rows sum to `5,450,425,994`. -/
theorem rest_non_vacuous_and_tight : restTerms = 5450425994 := rest_val

/-- 3. Main total at `200M`: `200,485,906,743`. -/
theorem main_non_vacuous_and_tight :
    gasEnv200 = 156088992805 ∧ witnessMpt = 38946487944 ∧ restTerms = 5450425994 ∧
      main200 = 200485906743 := by
  decide

/-- 4. Slope one leaves `700,234,018,731`; fourfold passes with quarter margin
`24,694,074,625`; fivefold crosses. -/
theorem main_slopes_non_vacuous_and_tight :
    yukon - main200 = 700234018731 ∧ 4 * main200 < yukon ∧
      yukon / 4 - main200 = 24694074625 ∧ yukon < 5 * main200 :=
  main_slopes

/-- 5. Rescaled envelope at `380M`: `467,569,086,329`. -/
theorem env380_non_vacuous_and_tight : gasEnv380 = 467569086329 := env380_val

/-- 6. Main total at `380M`: `511,966,000,267`. -/
theorem main380_non_vacuous_and_tight : main380 = 511966000267 := main380_val

/-- 7. Slope one still passes at `380M` (margin `388,753,925,207`); twofold crosses. -/
theorem main380_slopes_non_vacuous_and_tight :
    yukon - main380 = 388753925207 ∧ yukon < 2 * main380 :=
  main380_slopes

/-- 8. Without memoization, fourfold fails at `200M`. -/
theorem heap_fails_non_vacuous_and_tight :
    yukon < 4 * (gasEnv200 + 68277256888 + restTerms) :=
  heap_4x_fails

/-- 9. BAL bound: `≤ 190,000` cold keys, two passes of `18` levels at `40` ticks,
inside `300,000,000`. -/
theorem bal_bound_non_vacuous_and_tight (k : Nat) (h : 2000 * k ≤ 380000000) :
    k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp :=
  bal_bound k h

/-- 10. The 76 budgets grow strictly under Yukon, and each finite certificate needs the
base certificate. -/
theorem portfolio_76_non_vacuous_and_tight
    (cert : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    SeventySixShape ∧
      (∀ K ∈ portfolio,
        InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K)
          (.finite K)) :=
  seventy_six_budget_certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventySixBudgetBridge
