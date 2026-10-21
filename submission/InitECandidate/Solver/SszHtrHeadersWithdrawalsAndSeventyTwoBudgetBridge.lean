import InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound
import InitECandidate.Solver.PrologueSecp256k1AndSeventyBudgetBridge
import InitECandidate.Solver.SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyTwoBudgetBridge`

Bridge between the SSZ/HTR header bound, the 70-budget prologue bridge, and the
72-budget master.

* The prologue costs `ρ = 2` ticks per input byte: `2 · 134,217,712 = 268,435,424`,
  inside both residuals (`2 ≤ 188` at fourfold memoized, `2 ≤ 5,003` at slope one).
* RLP withdrawals are capped at `nwdMax = 335,544` (`25 · n ≤ 8,388,608`). At slope one
  the linear close leaves `604,116,573,707`, which absorbs `f ≤ 5` unsalted colliding
  finds. At fourfold, `≤ 125,080` withdrawals fit and `125,081` cross.
* The 72 budgets grow strictly under Yukon `900,719,925,474`, and each finite certificate
  is conditional on the base certificate.
-/

namespace InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyTwoBudgetBridge

open InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound
open InitECandidate.Solver.SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster

/-- 1. Prologue at `ρ = 2`: `268,435,424` ticks. -/
theorem prologue_non_vacuous_and_tight : 2 * maxInput = 268435424 := prologue_val

/-- 2. That rate sits inside both residuals. -/
theorem rho_inside_non_vacuous_and_tight :
    2 ≤ 188 ∧ 188 * maxInput ≤ r4 ∧ 5003 * maxInput ≤ r1 :=
  rho_inside

/-- 3. Withdrawal cap: `25 · n ≤ 8,388,608` gives `n ≤ 335,544`, and it is tight. -/
theorem nwd_cap_non_vacuous_and_tight (n : Nat) (h : 25 * n ≤ 8388608) :
    n ≤ nwdMax ∧ 25 * 335544 ≤ 8388608 ∧ 8388608 < 25 * 335545 :=
  ⟨nwd_le n h, nwd_tight⟩

/-- 4. Slope-one linear close: margin `604,116,573,707` after prologue and withdrawals. -/
theorem close_linear_non_vacuous_and_tight :
    r1 - 2 * maxInput - 200000 * nwdMax = 604116573707 :=
  close_1x_linear

/-- 5. Slope-one unsalted collisions: `f ≤ 5` fits, `f = 6` crosses. -/
theorem close_quad_non_vacuous_and_tight :
    5 * 112589440392 ≤ 604116573707 ∧ 604116573707 < 6 * 112589440392 :=
  close_1x_quad

/-- 6. Fourfold fails on the full withdrawal list, even without collisions. -/
theorem fourfold_fails_non_vacuous_and_tight :
    r4 < 2 * maxInput + 200000 * nwdMax :=
  fourx_fails

/-- 7. Fourfold withdrawal threshold: `125,080` fits, `125,081` crosses. -/
theorem fourfold_threshold_non_vacuous_and_tight :
    2 * maxInput + 200000 * 125080 ≤ r4 ∧ r4 < 2 * maxInput + 200000 * 125081 :=
  fourx_wd_threshold

/-- 8. The withdrawal term dominates the prologue by at least `249×`. -/
theorem withdrawals_dominate_non_vacuous_and_tight :
    249 * (2 * maxInput) ≤ 200000 * nwdMax :=
  wd_dominates

/-- 9. Quadratic cost of the full unsalted withdrawal run. -/
theorem withdrawal_quadratic_non_vacuous_and_tight :
    nwdMax * (nwdMax - 1) = 112589440392 :=
  wd_quad

/-- 10. The 72 budgets grow strictly under Yukon, and each finite certificate needs the
base certificate. -/
theorem portfolio_72_non_vacuous_and_tight
    (cert : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    SeventyTwoShape ∧
      (∀ K ∈ portfolio,
        InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K)
          (.finite K)) :=
  seventy_two_budget_certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyTwoBudgetBridge
