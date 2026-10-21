import InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
import InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.JumpdestDualLPAndOneHundredTenBudgetBridge

open InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
open InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. One call costs `callTicks = 67,884`. -/
theorem call_val_bridge_non_vacuous_and_tight : callTicks = 67884 :=
  call_val

/-- 2. Uncached joint bound at 200M, any mix of accounts, keys, pushes, calls and transactions. -/
theorem uncached200_bridge_non_vacuous_and_tight (A K P C T m : Nat)
    (hg : 2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 200000000) (hw : 4 * m ≤ inputBytes) :
    costU A K P C T m ≤ callTicks * 200000000 / 126 + 90 * (inputBytes / 4) :=
  uncached200 A K P C T m hg hw

/-- 3. Uncached joint bound at 380M. -/
theorem uncached380_bridge_non_vacuous_and_tight (A K P C T m : Nat)
    (hg : 2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 380000000) (hw : 4 * m ≤ inputBytes) :
    costU A K P C T m ≤ callTicks * 380000000 / 126 + 90 * (inputBytes / 4) :=
  uncached380 A K P C T m hg hw

/-- 4. Uncached totals: `112,163,577,490` (`8×` passes, `9×` fails) at 200M and `209,425,139,355`
(`4×` passes, `5×` fails) at 380M. -/
theorem uncached_slopes_bridge_non_vacuous_and_tight :
    mainUncached200 = 112163577490 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 209425139355 ∧ 4 * mainUncached380 < yukon ∧
      yukon < 5 * mainUncached380 :=
  uncached_slopes

/-- 5. Cached joint LP at 200M, bound `6,619,898,520`. -/
theorem cached200_bridge_non_vacuous_and_tight (A K B E n2 n17 m P : Nat)
    (hg : 24 * A + 21 * K + P ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    costC A K B E n2 n17 m P ≤ 6619898520 :=
  cached200 A K B E n2 n17 m P hg h1 h2 hb he hw

/-- 6. Cached joint LP at 380M, bound `9,859,898,520`. -/
theorem cached380_bridge_non_vacuous_and_tight (A K B E n2 n17 m P : Nat)
    (hg : 24 * A + 21 * K + P ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    costC A K B E n2 n17 m P ≤ 9859898520 :=
  cached380 A K B E n2 n17 m P hg h1 h2 hb he hw

/-- 7. Both cached bounds are attained by all-`PUSH31` with empty witness entries. -/
theorem cached_tight_bridge_non_vacuous_and_tight :
    costC 0 0 0 0 0 0 (inputBytes / 4) 2000000 = 6619898520 ∧
      costC 0 0 0 0 0 0 (inputBytes / 4) 3800000 = 9859898520 :=
  cached_tight

/-- 8. Cached totals: `8,145,414,250` (`110×` passes, `111×` fails) at 200M and `11,669,833,258`
(`77×` passes, `78×` fails) at 380M. -/
theorem cached_slopes_bridge_non_vacuous_and_tight :
    mainCached200 = 8145414250 ∧ 110 * mainCached200 < yukon ∧
      yukon < 111 * mainCached200 ∧ mainCached380 = 11669833258 ∧ 77 * mainCached380 < yukon ∧
      yukon < 78 * mainCached380 :=
  cached_slopes

/-- 9. The 110-budget table: 110 strictly increasing budgets, last entry 900,500,000,000, margin
219,925,474 under Yukon. -/
theorem one_hundred_ten_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredTenShape ∧
    oneHundredTenExplicitBudgets.length = 110 ∧
    oneHundredTenExplicitBudgets.getLast? = some 900500000000 ∧
    yukon - 900500000000 = 219925474 :=
  ⟨ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.one_hundred_ten_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_ten_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_ten_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_ten_budget_last_margin_non_vacuous_and_tight.2.2⟩

/-- 10. Every one of the 110 budgets carries a finite certificate, from one base certificate. -/
theorem one_hundred_ten_budget_certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    OneHundredTenShape ∧
    (∀ K ∈ oneHundredTenExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.one_hundred_ten_budget_certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.JumpdestDualLPAndOneHundredTenBudgetBridge
