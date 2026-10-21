import InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
import InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! The uncached jumpdest scans invalidate the previous global gas estimate for
the current Guest. The 110x/77x arithmetic explicitly assumes the proposed
per-code jumpdest cache and the previous model's remaining assumptions.
Finite semantic certificates remain conditional on the base certificate;
none is inferred from the arithmetic cost estimates. -/
namespace InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev Previous := ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.oneHundredTenExplicitBudgets

def oneHundredTwelveExplicitBudgets : List Nat := Previous ++ [900600000000, 900700000000]
abbrev portfolio := oneHundredTwelveExplicitBudgets

def OneHundredTwelveShape : Prop :=
  portfolio.length = 112 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 110 = Previous ∧
  portfolio.drop 110 = [900600000000, 900700000000] ∧
  portfolio.getLast? = some 900700000000 ∧ yukon = 900719925474

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

theorem one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredTwelveShape := by
  unfold OneHundredTwelveShape
  decide

theorem one_hundred_twelve_budget_last_margin_non_vacuous_and_tight :
    oneHundredTwelveExplicitBudgets.length = 112 ∧
    oneHundredTwelveExplicitBudgets.getLast? = some 900700000000 ∧
    yukon - 900700000000 = 19925474 := by decide

theorem one_hundred_twelve_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredTwelveExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwelveExplicitBudgets, K < 900719925474) := by
  refine ⟨one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.1, ?_⟩
  intro K hK
  exact (one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2

theorem one_hundred_twelve_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwelveShape ∧
    (∀ K ∈ oneHundredTwelveExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms call_val_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms uncached_slopes_non_vacuous_and_tight
#print axioms cached200_non_vacuous_and_tight
#print axioms cached380_non_vacuous_and_tight
#print axioms cached_tight_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_twelve_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_twelve_budgets_under_yukon_non_vacuous_and_tight
#print axioms one_hundred_twelve_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster
