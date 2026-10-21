import InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster
import InitECandidate.Solver.CoupledGasFullBlockAndSixtyFourBudgetBridge
import InitECandidate.Solver.CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.EndToEndStartToHaltCoupledMptAndSixtySixBudgetBridge`

Bridge between the end-to-end start-to-halt master, the 64-budget gas-coupled bridge,
and the 66-budget master.

* Coupling MPT writes to the shared `200,000,000` gas budget saves `619,060,000` ticks:
  the block drops to `224,366,249,693` (heap) and `195,035,480,749` (memoized), whose
  fourfold `780,141,922,996` stays under Yukon.
* The coupled caps rise by the same saving: `L ≤ 38,817` and `L ≤ 40,284` at slope one,
  `L ≤ 5,040` and `L ≤ 6,507` at slope four. The next value crosses Yukon.
* The 66 budgets grow strictly under Yukon `900,719,925,474`, and each finite certificate
  is conditional on the base certificate.
-/

namespace InitECandidate.Solver.EndToEndStartToHaltCoupledMptAndSixtySixBudgetBridge

open InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster
open InitECandidate.Solver.CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster

/-- Block total once the `619,060,000` MPT saving is removed. -/
def mptCoupled (sub : Nat) : Nat := sub - 619060000

/-- Coupled total: the MPT saving plus the `ts+64` excess over the absorbed range. -/
def mptTotal (sub L : Nat) : Nat := mptCoupled sub + (10 * L - 50000) * 2000000

/-- 1. The coupling saves exactly `619,060,000` ticks. -/
theorem coupling_gain_non_vacuous_and_tight : 13000000000 - 130000 * 95238 = 619060000 :=
  coupling_gain

/-- 2. Coupled block totals: `224,366,249,693` and `195,035,480,749`. -/
theorem coupled_totals_non_vacuous_and_tight :
    224985309693 - 619060000 = 224366249693 ∧ 195654540749 - 619060000 = 195035480749 :=
  coupled_totals

/-- 3. The fourfold memoized total stays under Yukon. -/
theorem fourfold_non_vacuous_and_tight :
    4 * 195035480749 = 780141922996 ∧ 4 * 195035480749 < 900719925474 := by
  decide

/-- 4. Coupled cap at slope one, heap: `L = 38,817` fits, `38,818` crosses. -/
theorem lmax_one_heap_non_vacuous_and_tight :
    mptTotal 224985309693 38817 < 900719925474 ∧
      900719925474 ≤ mptTotal 224985309693 38818 := by
  decide

/-- 5. Coupled cap at slope one, memoized: `L = 40,284` fits, `40,285` crosses. -/
theorem lmax_one_memo_non_vacuous_and_tight :
    mptTotal 195654540749 40284 < 900719925474 ∧
      900719925474 ≤ mptTotal 195654540749 40285 := by
  decide

/-- 6. Coupled cap at slope four, heap: `L = 5,040` fits, `5,041` crosses. -/
theorem lmax_four_heap_non_vacuous_and_tight :
    4 * mptTotal 224985309693 5040 < 900719925474 ∧
      900719925474 ≤ 4 * mptTotal 224985309693 5041 := by
  decide

/-- 7. Coupled cap at slope four, memoized: `L = 6,507` fits, `6,508` crosses. -/
theorem lmax_four_memo_non_vacuous_and_tight :
    4 * mptTotal 195654540749 6507 < 900719925474 ∧
      900719925474 ≤ 4 * mptTotal 195654540749 6508 := by
  decide

/-- 8. Written keys on the shared budget: `≤ 95,238`, tight. -/
theorem dirty_keys_non_vacuous_and_tight (k : Nat) (h : 21 * k ≤ 2000000) :
    k ≤ 95238 ∧ 21 * 95238 ≤ 2000000 ∧ 2000000 < 21 * 95239 :=
  ⟨dirty_keys k h, dirty_keys_tight⟩

/-- 9. Residual budgets after the coupled heap total: `676,353,675,781` at slope one. -/
theorem residual_non_vacuous_and_tight :
    900719925474 - 224366249693 = 676353675781 ∧
      900719925474 / 4 - 224366249693 = 813731675 ∧
      900719925474 / 4 - 195035480749 = 30144500619 :=
  ⟨residual_1x, residual_4x⟩

/-- 10. The 66 budgets grow strictly under Yukon, and each finite certificate needs the
base certificate. -/
theorem portfolio_66_non_vacuous_and_tight
    (cert : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    SixtySixShape ∧ ClaimPayloads ∧
      (∀ K ∈ portfolio,
        InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K)
          (.finite K)) :=
  sixty_six_budget_certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.EndToEndStartToHaltCoupledMptAndSixtySixBudgetBridge
