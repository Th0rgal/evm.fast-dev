import InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster
import InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster
import InitECandidate.Solver.MultiTrieGasSixtyEightXAndNinetySixBudgetCampaignBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact arithmetic for the imported conditional guest cost model. The joint LP
bounds assume the stated gas, dirty-node and witness-byte constraints; arithmetic
bounds are not semantic runtime certificates. Finite certificates remain
conditional on the base certificate. -/
namespace InitECandidate.Solver.TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- The synchronized 98-budget master calls its table `portfolio`. -/
abbrev ninetyEightExplicitFiniteKBugdetTable := MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster.portfolio

def oneHundredExplicitFiniteKBugdetTable : List Nat :=
  ninetyEightExplicitFiniteKBugdetTable ++ [883564749368, 886500180428]

abbrev portfolio := oneHundredExplicitFiniteKBugdetTable

def OneHundredShape : Prop :=
  portfolio.length = 100 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 98 = ninetyEightExplicitFiniteKBugdetTable ∧
  portfolio.drop 98 = [883564749368, 886500180428] ∧
  portfolio.getLast? = some 886500180428 ∧ yukon = 900719925474

theorem node2_val_non_vacuous_and_tight : beginTicks = 58 ∧ finish2Ticks = 227 ∧ keccakTicks532 = 146 ∧ node2Ticks = 439 :=
  GuestTwoItemNodeRehashAndSeventyXMaster.node2_val

theorem joint200_non_vacuous_and_tight (A K B E n2 n17 m : Nat) (hg : 24 * A + 21 * K ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    9 * cost K B E n2 n17 m ≤ 58999236680 :=
  GuestTwoItemNodeRehashAndSeventyXMaster.joint200 A K B E n2 n17 m hg h1 h2 hb he hw

theorem joint380_non_vacuous_and_tight (A K B E n2 n17 m : Nat) (hg : 24 * A + 21 * K ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    135 * cost K B E n2 n17 m ≤ 1179391270576 :=
  GuestTwoItemNodeRehashAndSeventyXMaster.joint380 A K B E n2 n17 m hg h1 h2 hb he hw

theorem near200_non_vacuous_and_tight : 24 * 5556 + 21 * 88888 ≤ 2000000 ∧
    7 * 0 + 22 * 5961084 + 4 * ((inputBytes - 22 * 5961084) / 4) ≤ inputBytes ∧
    6555470742 - cost 88888 (5961084 + 88888 + 5556) 0 0 5961084 ((inputBytes - 22 * 5961084) / 4)
      ≤ 20000 :=
  GuestTwoItemNodeRehashAndSeventyXMaster.near200

theorem main200_slope_non_vacuous_and_tight : main200 = 12809345768 ∧ 70 * main200 < yukon ∧ yukon < 71 * main200 :=
  GuestTwoItemNodeRehashAndSeventyXMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight : main380 = 19403346659 ∧ 46 * main380 < yukon ∧ yukon < 47 * main380 :=
  GuestTwoItemNodeRehashAndSeventyXMaster.main380_slope

theorem margins_non_vacuous_and_tight : yukon - 70 * main200 = 4065721714 ∧ yukon - 46 * main380 = 8165979160 :=
  GuestTwoItemNodeRehashAndSeventyXMaster.margins

/-- Strict gain at 200M, compared with the previous unconditional multi-trie row. -/
theorem improvement200_non_vacuous_and_tight :
    GuestMultiTrieGasAndLeafBranchRehashMaster.main200 = 13167715213 ∧
    main200 < GuestMultiTrieGasAndLeafBranchRehashMaster.main200 ∧
    68 * GuestMultiTrieGasAndLeafBranchRehashMaster.main200 < yukon ∧
    yukon < 69 * GuestMultiTrieGasAndLeafBranchRehashMaster.main200 ∧
    GuestMultiTrieGasAndLeafBranchRehashMaster.main200 - main200 = 358369445 := by decide

/-- Strict gain at 380M, with the old passing and failing factors pinned. -/
theorem improvement380_non_vacuous_and_tight :
    GuestMultiTrieGasAndLeafBranchRehashMaster.main380 = 21085502713 ∧
    main380 < GuestMultiTrieGasAndLeafBranchRehashMaster.main380 ∧
    42 * GuestMultiTrieGasAndLeafBranchRehashMaster.main380 < yukon ∧
    yukon < 43 * GuestMultiTrieGasAndLeafBranchRehashMaster.main380 ∧
    GuestMultiTrieGasAndLeafBranchRehashMaster.main380 - main380 = 1682156054 := by decide

theorem one_hundred_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredShape := by
  unfold OneHundredShape
  decide

theorem one_hundred_budget_last_margin_non_vacuous_and_tight :
    oneHundredExplicitFiniteKBugdetTable.length = 100 ∧
    oneHundredExplicitFiniteKBugdetTable.getLast? = some 886500180428 ∧
    900719925474 - 886500180428 = 14219745046 ∧
    yukon - 886500180428 = 14219745046 := by decide

theorem one_hundred_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredShape ∧
    (∀ K ∈ oneHundredExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms node2_val_non_vacuous_and_tight
#print axioms joint200_non_vacuous_and_tight
#print axioms joint380_non_vacuous_and_tight
#print axioms near200_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms improvement200_non_vacuous_and_tight
#print axioms improvement380_non_vacuous_and_tight
#print axioms one_hundred_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster
