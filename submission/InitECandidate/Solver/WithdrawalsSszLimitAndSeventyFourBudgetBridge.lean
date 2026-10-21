import InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit
import InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyTwoBudgetBridge
import InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.WithdrawalsSszLimitAndSeventyFourBudgetBridge`

Bridge between the SSZ withdrawal-limit audit, the 72-budget header bridge, and the
74-budget master.

* The SSZ length cap does not bind: `nwdMax = 335,544` is below
  `9,223,372,036,854,775,807` and far above the spec cap `16`. The linear term at the
  cap is `132,000 · 335,544 = 44,291,808,000`.
* Salted, slope one closes with margin `626,933,565,707`. Unsalted, the caps are
  `n ≤ 323,652` at `f = 6` and `n ≤ 281,528` at `f = 8`. At fourfold the linear cap is
  `n ≤ 189,516`, but the spec cap `n ≤ 16` closes even unsalted at `f = 8`, with margin
  `25,014,084,625`.
* The prologue stays `268,435,424` ticks at `ρ = 2`, and the 74 budgets grow strictly
  under Yukon `900,719,925,474`.
-/

namespace InitECandidate.Solver.WithdrawalsSszLimitAndSeventyFourBudgetBridge

open InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit
open InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster

/-- 1. The SSZ cap does not bind, and the guest cap is `20,971×` the spec cap. -/
theorem ssz_diagnosis_non_vacuous_and_tight :
    nwdMax ≤ sszLim ∧ 16 < nwdMax ∧ 335544 / 16 = 20971 :=
  ⟨ssz_no_cap.1, ssz_no_cap.2, spec_vs_guest.2⟩

/-- 2. Linear withdrawal term at the cap: `44,291,808,000`. -/
theorem linear_non_vacuous_and_tight : 132000 * nwdMax = 44291808000 := linear_val

/-- 3. Salted slope-one close: margin `626,933,565,707`. -/
theorem close_salted_non_vacuous_and_tight :
    wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707 :=
  close_1x_salted

/-- 4. Unsalted cap at `f = 6`: `323,652` fits, `323,653` crosses. -/
theorem nmax_f6_non_vacuous_and_tight :
    wdTicks 6 323652 ≤ r1 ∧ r1 < wdTicks 6 323653 :=
  nmax_f6

/-- 5. Unsalted cap at `f = 8`: `281,528` fits, `281,529` crosses. -/
theorem nmax_f8_non_vacuous_and_tight :
    wdTicks 8 281528 ≤ r1 ∧ r1 < wdTicks 8 281529 :=
  nmax_f8

/-- 6. Fourfold linear cap: `189,516` fits, `189,517` crosses. -/
theorem nmax_fourfold_non_vacuous_and_tight :
    wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517 :=
  nmax_4x

/-- 7. Under the spec cap `n ≤ 16`, fourfold closes even unsalted at `f = 8`,
margin `25,014,084,625`. -/
theorem spec_cap_non_vacuous_and_tight (n : Nat) (h : n ≤ 16) :
    wdTicks 8 n ≤ wdTicks 8 16 ∧ wdTicks 8 16 ≤ r4 ∧ r4 - wdTicks 8 16 = 25014084625 :=
  spec_cap_closes n h

/-- 8. Prologue at `ρ = 2`: `268,435,424` ticks, inside both residuals. -/
theorem prologue_non_vacuous_and_tight :
    2 * GuestSszHtrHeadersAndCompleteMainBound.maxInput = 268435424 ∧
      2 ≤ 188 ∧ 5003 * GuestSszHtrHeadersAndCompleteMainBound.maxInput ≤
        GuestSszHtrHeadersAndCompleteMainBound.r1 :=
  ⟨GuestSszHtrHeadersAndCompleteMainBound.prologue_val,
   GuestSszHtrHeadersAndCompleteMainBound.rho_inside.1,
   GuestSszHtrHeadersAndCompleteMainBound.rho_inside.2.2⟩

/-- 9. The fix is one bounded comparison: `16 · 44 = 704` bytes, under the RLP budget. -/
theorem fix_non_vacuous_and_tight : (16 * 44 : Nat) = 704 ∧ 704 < 8388608 := fix_shape

/-- 10. The 74 budgets grow strictly under Yukon, and each finite certificate needs the
base certificate. -/
theorem portfolio_74_non_vacuous_and_tight
    (cert : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    SeventyFourShape ∧
      (∀ K ∈ portfolio,
        InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K)
          (.finite K)) :=
  seventy_four_budget_certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.WithdrawalsSszLimitAndSeventyFourBudgetBridge
