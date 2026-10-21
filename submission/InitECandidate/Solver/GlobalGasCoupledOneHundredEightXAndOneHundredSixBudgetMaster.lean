import InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster
import InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster
import InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredTwoBudgetCampaignBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact arithmetic for the imported conditional guest cost model. The joint LP
bounds assume the stated gas, dirty-node and witness-byte constraints; arithmetic
bounds are not semantic runtime certificates. Finite certificates remain
conditional on the base certificate. -/
namespace InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev oneHundredFourExplicitFiniteKBugdetTable := EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster.oneHundredFourExplicitFiniteKBugdetTable

def oneHundredSixExplicitFiniteKBugdetTable : List Nat :=
  oneHundredFourExplicitFiniteKBugdetTable ++ [893500000000, 894500000000]

abbrev portfolio := oneHundredSixExplicitFiniteKBugdetTable

def OneHundredSixShape : Prop :=
  portfolio.length = 106 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 104 = oneHundredFourExplicitFiniteKBugdetTable ∧
  portfolio.drop 104 = [893500000000, 894500000000] ∧
  portfolio.getLast? = some 894500000000 ∧ yukon = 900719925474

theorem fixed_vals_non_vacuous_and_tight : fixed200 = 1391298018 ∧ fixed380 = 1675717026 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.fixed_vals

theorem joint200_non_vacuous_and_tight (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    3 * cost A K B E n2 n17 m P ≤ 20720445560 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.joint200 A K B E n2 n17 m P hg h1 h2 hb he hw

theorem joint380_non_vacuous_and_tight (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    65 * cost A K B E n2 n17 m P ≤ 661898475728 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.joint380 A K B E n2 n17 m P hg h1 h2 hb he hw

theorem main200_slope_non_vacuous_and_tight : main200 = 8298113205 ∧ 108 * main200 < yukon ∧ yukon < 109 * main200 ∧
    main200 < 9000000000 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight : main380 = 11858770499 ∧ 75 * main380 < yukon ∧ yukon < 76 * main380 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main380_slope

theorem margins_non_vacuous_and_tight : yukon - 108 * main200 = 4523699334 ∧ yukon - 75 * main380 = 11312138049 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.margins

theorem all_push_and_sensitivity_non_vacuous_and_tight :
    (3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560) ∧
    (98 * 9131446538 < yukon ∧ yukon < 99 * 9131446538) :=
  ⟨GuestGlobalGasCoupledEvmAndSubNineBillionMaster.all_push, GuestGlobalGasCoupledEvmAndSubNineBillionMaster.sensitivity⟩

/-- Strict gain at 200M, compared with the previous unconditional multi-trie row. -/
theorem improvement200_non_vacuous_and_tight :
    GuestEvmStepDispatchAndNinetyXMaster.main200 = 11546768760 ∧
    main200 < GuestEvmStepDispatchAndNinetyXMaster.main200 ∧
    78 * GuestEvmStepDispatchAndNinetyXMaster.main200 < yukon ∧
    yukon < 79 * GuestEvmStepDispatchAndNinetyXMaster.main200 ∧
    GuestEvmStepDispatchAndNinetyXMaster.main200 - main200 = 3248655555 := by decide

/-- Strict gain at 380M, with the old passing and failing factors pinned. -/
theorem improvement380_non_vacuous_and_tight :
    GuestEvmStepDispatchAndNinetyXMaster.main380 = 17251948659 ∧
    main380 < GuestEvmStepDispatchAndNinetyXMaster.main380 ∧
    52 * GuestEvmStepDispatchAndNinetyXMaster.main380 < yukon ∧
    yukon < 53 * GuestEvmStepDispatchAndNinetyXMaster.main380 ∧
    GuestEvmStepDispatchAndNinetyXMaster.main380 - main380 = 5393178160 := by decide

theorem one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredSixShape := by
  unfold OneHundredSixShape
  decide

theorem one_hundred_six_budget_last_margin_non_vacuous_and_tight :
    oneHundredSixExplicitFiniteKBugdetTable.length = 106 ∧
    oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 ∧
    900719925474 - 894500000000 = 6219925474 ∧
    yukon - 894500000000 = 6219925474 := by decide

theorem one_hundred_six_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredSixShape ∧
    (∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms fixed_vals_non_vacuous_and_tight
#print axioms joint200_non_vacuous_and_tight
#print axioms joint380_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms all_push_and_sensitivity_non_vacuous_and_tight
#print axioms improvement200_non_vacuous_and_tight
#print axioms improvement380_non_vacuous_and_tight
#print axioms one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_six_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_six_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster
