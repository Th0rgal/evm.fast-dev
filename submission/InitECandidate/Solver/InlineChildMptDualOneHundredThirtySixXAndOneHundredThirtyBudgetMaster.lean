import InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster
import InitECandidate.Solver.LoopToStackNamesLabToTargetAndOneHundredTwentyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Arithmetic synthesis of two MPT regimes, both assuming cached jumpdest
scans and the imported cost model. Regime 1 permits the current Guest's inline
children; regime 2 additionally assumes the Yellow-Paper child-size rule.
Finite semantic certificates remain conditional on the base certificate and
are not derived from these arithmetic cost estimates. -/
namespace InitECandidate.Solver.InlineChildMptDualOneHundredThirtySixXAndOneHundredThirtyBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster (trueFixed200 trueFixed380)
open _root_.InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev Previous := LoopToStackNamesLabToTargetAndOneHundredTwentyEightBudgetMaster.oneHundredTwentyEightExplicitBudgets

def oneHundredThirtyExplicitBudgets : List Nat := Previous ++ [900719845000, 900719850000]
abbrev portfolio := oneHundredThirtyExplicitBudgets

def OneHundredThirtyShape : Prop :=
  portfolio.length = 130 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 128 = Previous ∧
  portfolio.drop 128 = [900719845000, 900719850000] ∧
  portfolio.getLast? = some 900719850000 ∧ yukon = 900719925474

theorem inline_200_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    451 * cost1 A K L B E n2 n17 md ms P T ≤ 3058910053880 :=
  GuestInlineChildMptDualAndOneHundredThirtySixXMaster.inline_200 A K L B E n2 n17 md ms P T hg h1 h2 he hw

theorem inline_380_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    451 * cost1 A K L B E n2 n17 md ms P T ≤ 4809020803880 :=
  GuestInlineChildMptDualAndOneHundredThirtySixXMaster.inline_380 A K L B E n2 n17 md ms P T hg h1 h2 he hw

theorem yp_200_non_vacuous_and_tight (A K L B E n2 d r md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    11 * cost2 A K L B E n2 d r md ms P T ≤ 66779086680 :=
  GuestInlineChildMptDualAndOneHundredThirtySixXMaster.yp_200 A K L B E n2 d r md ms P T hg h1 h2 hb he hw

theorem yp_380_non_vacuous_and_tight (A K L B E n2 d r md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    11 * cost2 A K L B E n2 d r md ms P T ≤ 102419086680 :=
  GuestInlineChildMptDualAndOneHundredThirtySixXMaster.yp_380 A K L B E n2 d r md ms P T hg h1 h2 hb he hw

theorem yp_tight_non_vacuous_and_tight : 11 * cost2 0 0 0 0 0 0 6100805 0 0 0 200000000 0 ≤ 66779086680 ∧
    66779086680 - 11 * cost2 0 0 0 0 0 0 6100805 0 0 0 200000000 0 < 11 * 405 ∧
    7 * 0 + 22 * 6100805 ≤ inputBytes :=
  GuestInlineChildMptDualAndOneHundredThirtySixXMaster.yp_tight

theorem inline_slopes_non_vacuous_and_tight : inline200 = 7287261989 ∧ 123 * inline200 < yukon ∧
    yukon < 124 * inline200 ∧ inline380 = 11167773630 ∧ 80 * inline380 < yukon ∧
    yukon < 81 * inline380 :=
  GuestInlineChildMptDualAndOneHundredThirtySixXMaster.inline_slopes

theorem yp_slopes_non_vacuous_and_tight : yp200 = 6575582388 ∧ 136 * yp200 < yukon ∧ yukon < 137 * yp200 ∧
    yp380 = 9815582388 ∧ 91 * yp380 < yukon ∧ yukon < 92 * yp380 :=
  GuestInlineChildMptDualAndOneHundredThirtySixXMaster.yp_slopes

theorem hb_gap_non_vacuous_and_tight : inline380 - 10545558216 = 622215414 ∧ inline200 = 7287261989 :=
  GuestInlineChildMptDualAndOneHundredThirtySixXMaster.hb_gap

theorem one_hundred_thirty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredThirtyShape := by
  unfold OneHundredThirtyShape
  decide

theorem one_hundred_thirty_budget_last_margin_non_vacuous_and_tight :
    oneHundredThirtyExplicitBudgets.length = 130 ∧
    oneHundredThirtyExplicitBudgets.getLast? = some 900719850000 ∧
    yukon - 900719850000 = 75474 := by decide

theorem one_hundred_thirty_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredThirtyExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredThirtyExplicitBudgets, K < 900719925474) := by
  refine ⟨one_hundred_thirty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.1, ?_⟩
  intro K hK
  exact (one_hundred_thirty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2

theorem one_hundred_thirty_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredThirtyShape ∧
    (∀ K ∈ oneHundredThirtyExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_thirty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_thirty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms inline_200_non_vacuous_and_tight
#print axioms inline_380_non_vacuous_and_tight
#print axioms yp_200_non_vacuous_and_tight
#print axioms yp_380_non_vacuous_and_tight
#print axioms yp_tight_non_vacuous_and_tight
#print axioms inline_slopes_non_vacuous_and_tight
#print axioms yp_slopes_non_vacuous_and_tight
#print axioms hb_gap_non_vacuous_and_tight
#print axioms one_hundred_thirty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_thirty_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_thirty_budgets_under_yukon_non_vacuous_and_tight
#print axioms one_hundred_thirty_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.InlineChildMptDualOneHundredThirtySixXAndOneHundredThirtyBudgetMaster
