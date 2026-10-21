import InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
import InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_289: full uncached and cached joint LP propositions and 110 conditional
finite certificates. These are exact arithmetic results in the imported cost
model, retaining all gas, dirty-node and witness-byte hypotheses. The cached
model requires a per-code jumpdest cache. Neither arithmetic model establishes
an execution-derived semantic runtime certificate; finite semantic certificates
remain conditional on the base semantic certificate. -/
namespace InitECandidate.Solver.SelfContainedJumpdestDualLPOneHundredTenBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev oneHundredTenExplicitBudgets := ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.oneHundredTenExplicitBudgets
abbrev portfolio := oneHundredTenExplicitBudgets
abbrev OneHundredTenShape := ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.OneHundredTenShape

theorem call_val_non_vacuous_and_tight : callTicks = 67884 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.call_val

theorem uncached200_non_vacuous_and_tight (A K P C T m : Nat)
    (hg : 2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 200000000) (hw : 4 * m ≤ inputBytes) :
    costU A K P C T m ≤ callTicks * 200000000 / 126 + 90 * (inputBytes / 4) :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.uncached200 A K P C T m hg hw

theorem uncached380_non_vacuous_and_tight (A K P C T m : Nat)
    (hg : 2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 380000000) (hw : 4 * m ≤ inputBytes) :
    costU A K P C T m ≤ callTicks * 380000000 / 126 + 90 * (inputBytes / 4) :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.uncached380 A K P C T m hg hw

theorem uncached_slopes_non_vacuous_and_tight : mainUncached200 = 112163577490 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 209425139355 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.uncached_slopes

theorem cached200_non_vacuous_and_tight (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    costC A K B E n2 n17 m P ≤ 6619898520 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.cached200 A K B E n2 n17 m P hg h1 h2 hb he hw

theorem cached380_non_vacuous_and_tight (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    costC A K B E n2 n17 m P ≤ 9859898520 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.cached380 A K B E n2 n17 m P hg h1 h2 hb he hw

theorem cached_tight_non_vacuous_and_tight : costC 0 0 0 0 0 0 (inputBytes / 4) 2000000 = 6619898520 ∧
    costC 0 0 0 0 0 0 (inputBytes / 4) 3800000 = 9859898520 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.cached_tight

theorem cached_slopes_non_vacuous_and_tight : mainCached200 = 8145414250 ∧ 110 * mainCached200 < yukon ∧
    yukon < 111 * mainCached200 ∧ mainCached380 = 11669833258 ∧ 77 * mainCached380 < yukon ∧
    yukon < 78 * mainCached380 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.cached_slopes

theorem one_hundred_ten_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredTenShape :=
  ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.one_hundred_ten_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

theorem one_hundred_ten_budget_last_margin_non_vacuous_and_tight :
    oneHundredTenExplicitBudgets.length = 110 ∧
    oneHundredTenExplicitBudgets.getLast? = some 900500000000 ∧
    yukon - 900500000000 = 219925474 :=
  ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.one_hundred_ten_budget_last_margin_non_vacuous_and_tight

theorem one_hundred_ten_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredTenExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTenExplicitBudgets, K < 900719925474) :=
  ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.one_hundred_ten_budgets_under_yukon_non_vacuous_and_tight

theorem one_hundred_ten_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTenShape ∧
    (∀ K ∈ oneHundredTenExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.one_hundred_ten_budget_certificates_non_vacuous_and_tight cert

#print axioms call_val_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms uncached_slopes_non_vacuous_and_tight
#print axioms cached200_non_vacuous_and_tight
#print axioms cached380_non_vacuous_and_tight
#print axioms cached_tight_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms one_hundred_ten_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_ten_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_ten_budgets_under_yukon_non_vacuous_and_tight
#print axioms one_hundred_ten_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedJumpdestDualLPOneHundredTenBudgetMaster
