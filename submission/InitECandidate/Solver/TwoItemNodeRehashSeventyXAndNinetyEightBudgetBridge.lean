import InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster
import InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetySixBudgetBridge
import InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# TwoItemNodeRehashSeventyXAndNinetyEightBudgetBridge

Wave 5 bridge (W5_263). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.TwoItemNodeRehashSeventyXAndNinetyEightBudgetBridge

open InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster
open InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetySixBudgetBridge
open InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. A two-item node InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.costs 439 ticks: begin 58, finish 227, keccak 146. -/
theorem node2_val_bridge_non_vacuous_and_tight :
    beginTicks = 58 ∧ finish2Ticks = 227 ∧ keccakTicks532 = 146 ∧ node2Ticks = 439 :=
  node2_val

/-- 2. Joint bound at 200M: 9 times the InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.cost stays under 58_999_236_680. -/
theorem InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.joint200_bridge_non_vacuous_and_tight (A K B E n2 n17 m : Nat)
    (hg : 24 * A + 21 * K ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * m ≤ InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.inputBytes) :
    9 * InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.cost K B E n2 n17 m ≤ 58999236680 :=
  InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.joint200 A K B E n2 n17 m hg h1 h2 hb he hw

/-- 3. Joint bound at 380M: 135 times the InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.cost stays under 1_179_391_270_576. -/
theorem InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.joint380_bridge_non_vacuous_and_tight (A K B E n2 n17 m : Nat)
    (hg : 24 * A + 21 * K ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * m ≤ InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.inputBytes) :
    135 * InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.cost K B E n2 n17 m ≤ 1179391270576 :=
  InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.joint380 A K B E n2 n17 m hg h1 h2 hb he hw

/-- 4. Near-attainment at 200M: A = 5_556, K = 88_888, fed by 5_961_084 witness branches. -/
theorem InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.near200_bridge_non_vacuous_and_tight :
    24 * 5556 + 21 * 88888 ≤ 2000000 ∧
    7 * 0 + 22 * 5961084 + 4 * ((InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.inputBytes - 22 * 5961084) / 4) ≤ InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.inputBytes ∧
    6555470742 - InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.cost 88888 (5961084 + 88888 + 5556) 0 0 5961084
        ((InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.inputBytes - 22 * 5961084) / 4) ≤ 20000 :=
  InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.near200

/-- 5. Two-item totals: 12_809_345_768 passes 70x and 19_403_346_659 passes 46x. -/
theorem main_slopes_bridge_non_vacuous_and_tight :
    (InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main200 = 12809345768 ∧ 70 * InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main200 < yukon ∧ yukon < 71 * InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main200) ∧
    (InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main380 = 19403346659 ∧ 46 * InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main380 < yukon ∧ yukon < 47 * InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main380) :=
  ⟨InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main200_slope, InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main380_slope⟩

/-- 6. Margins at both ceilings. -/
theorem InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.margins_bridge_non_vacuous_and_tight :
    yukon - 70 * InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main200 = 4065721714 ∧ yukon - 46 * InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main380 = 8165979160 :=
  InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.margins

/-- 7. StackAlloc is the identity off label 6, and it stays alloc-free and GC-free. -/
theorem identity_and_noGc_ninety_eight_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool) :
    (∀ y ∈ InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.rawCallSections
        arch prog wc ac perf, y.1 ≠ Flapjack.storeConstsStubLocation →
      Flapjack.Compiler.Backend.StackAlloc.progComp y = y) ∧
    (∀ y ∈ InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.rawCallSections
        arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
          (Flapjack.Compiler.Backend.StackAlloc.progComp y).2 = true ∧
        InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.NoGcCall
          (Flapjack.Compiler.Backend.StackAlloc.progComp y).2 = true) :=
  identity_and_noGc_bridge_non_vacuous_and_tight arch prog wc ac perf

/-- 8. The 98-budget table: 98 strictly increasing budgets, last entry 880_629_318_308, all
under Yukon 900_719_925_474. -/
theorem ninety_eight_explicit_table_bridge_non_vacuous_and_tight :
    NinetyEightShape ∧
    MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster.portfolio.length = 98 ∧
    MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster.portfolio.getLast? =
      some 880629318308 ∧
    (∀ K ∈ MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster.portfolio, K < yukon) :=
  ⟨ninety_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   ninety_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   ninety_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.1,
   fun K hK =>
     (ninety_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 9. Every one of the 98 budgets carries a finite certificate, from one base certificate. -/
theorem ninety_eight_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    NinetyEightShape ∧
    (∀ K ∈ MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(ninety_eight_budget_certificates_non_vacuous_and_tight cert).1,
   (ninety_eight_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 10. Grand bridge: the 70x two-item total, the StackAlloc identity, and the 98-budget table
with finite certificates. -/
theorem two_item_node_rehash_seventy_x_and_ninety_eight_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool)
    (cert : CertificateAt 1212035192) :
    (node2Ticks = 439) ∧
    (InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main200 = 12809345768 ∧ 70 * InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main200 < yukon) ∧
    (∀ y ∈ InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.rawCallSections
        arch prog wc ac perf, y.1 ≠ Flapjack.storeConstsStubLocation →
      Flapjack.Compiler.Backend.StackAlloc.progComp y = y) ∧
    (NinetyEightShape ∧
      ∀ K ∈ MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨node2_val.2.2.2,
   ⟨InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main200_slope.1, InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster.main200_slope.2.1⟩,
   (identity_and_noGc_bridge_non_vacuous_and_tight arch prog wc ac perf).1,
   ⟨(ninety_eight_budget_certificates_non_vacuous_and_tight cert).1,
    (ninety_eight_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.TwoItemNodeRehashSeventyXAndNinetyEightBudgetBridge
