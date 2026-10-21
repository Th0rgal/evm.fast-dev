import InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
import InitECandidate.Solver.StackRawCallLinearClockAndOneHundredSixteenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! The uncached jumpdest scans invalidate the previous global gas estimate for
the current Guest. The 112x/77x arithmetic explicitly assumes the proposed
per-code jumpdest cache and the previous model's remaining assumptions.
Finite semantic certificates remain conditional on the base certificate;
none is inferred from the arithmetic cost estimates. -/
namespace InitECandidate.Solver.WitnessEmptyItemPushOneHundredTwelveXAndOneHundredEighteenBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev Previous := StackRawCallLinearClockAndOneHundredSixteenBudgetMaster.oneHundredSixteenExplicitBudgets

def oneHundredEighteenExplicitBudgets : List Nat := Previous ++ [900719000000, 900719500000]
abbrev portfolio := oneHundredEighteenExplicitBudgets

def OneHundredEighteenShape : Prop :=
  portfolio.length = 118 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 116 = Previous ∧
  portfolio.drop 116 = [900719000000, 900719500000] ∧
  portfolio.getLast? = some 900719500000 ∧ yukon = 900719925474

theorem leaf_counts_non_vacuous_and_tight : keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.leaf_counts

theorem cached200_non_vacuous_and_tight (A K B E n2 n17 md ms P : Nat)
    (hg : 2400 * A + 2100 * K + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    33 * costC A K B E n2 n17 md ms P ≤ 214138410040 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.cached200 A K B E n2 n17 md ms P hg h1 h2 hb he hw

theorem cached380_non_vacuous_and_tight (A K B E n2 n17 md ms P : Nat)
    (hg : 2400 * A + 2100 * K + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K B E n2 n17 md ms P ≤ 114947567578464 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.cached380 A K B E n2 n17 md ms P hg h1 h2 hb he hw

theorem uncached200_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.uncached200 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

theorem uncached380_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.uncached380 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

theorem cached_slopes_non_vacuous_and_tight : mainCached200 = 8014558459 ∧ 112 * mainCached200 < yukon ∧
    yukon < 113 * mainCached200 ∧ mainCached380 = 11548778048 ∧ 77 * mainCached380 < yukon ∧
    yukon < 78 * mainCached380 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.cached_slopes

theorem uncached_slopes_non_vacuous_and_tight : mainUncached200 = 111614505033 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 208876066898 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.uncached_slopes

theorem no_135_non_vacuous_and_tight : yukon / 135 = 6671999447 ∧ yukon < 135 * mainCached200 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.no_135

theorem one_hundred_eighteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredEighteenShape := by
  unfold OneHundredEighteenShape
  decide

theorem one_hundred_eighteen_budget_last_margin_non_vacuous_and_tight :
    oneHundredEighteenExplicitBudgets.length = 118 ∧
    oneHundredEighteenExplicitBudgets.getLast? = some 900719500000 ∧
    yukon - 900719500000 = 425474 := by decide

theorem one_hundred_eighteen_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredEighteenExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredEighteenExplicitBudgets, K < 900719925474) := by
  refine ⟨one_hundred_eighteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.1, ?_⟩
  intro K hK
  exact (one_hundred_eighteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2

theorem one_hundred_eighteen_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredEighteenShape ∧
    (∀ K ∈ oneHundredEighteenExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_eighteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_eighteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms leaf_counts_non_vacuous_and_tight
#print axioms cached200_non_vacuous_and_tight
#print axioms cached380_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms uncached_slopes_non_vacuous_and_tight
#print axioms no_135_non_vacuous_and_tight
#print axioms one_hundred_eighteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_eighteen_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_eighteen_budgets_under_yukon_non_vacuous_and_tight
#print axioms one_hundred_eighteen_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.WitnessEmptyItemPushOneHundredTwelveXAndOneHundredEighteenBudgetMaster
