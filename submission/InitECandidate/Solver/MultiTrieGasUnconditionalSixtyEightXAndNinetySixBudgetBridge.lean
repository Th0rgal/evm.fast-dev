import InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster
import InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetBridge
import InitECandidate.Solver.UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# MultiTrieGasUnconditionalSixtyEightXAndNinetySixBudgetBridge

Wave 5 bridge (W5_258). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetySixBudgetBridge

open InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster
open InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetBridge
open InitECandidate.Solver.UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Bases: 6_235_124_040 at 200M and 10_648_364_040 at 380M. -/
theorem bases_bridge_non_vacuous_and_tight :
    base200 = 6235124040 ∧ base380 = 10648364040 :=
  bases

/-- 2. Joint bound at 200M over every (A, K, R) obeying the gas and dirty-node constraints. -/
theorem joint200_bridge_non_vacuous_and_tight (A K R : Nat) (hg : 24 * A + 21 * K ≤ 2000000)
    (h1 : R ≤ 82 * A + 63 * K) (h2 : R ≤ 66 * A + 64 * K)
    (hw : 7 * (R - 3 * K - 3 * A) ≤ inputBytes) :
    rw4 A K R ≤ 27655360747 :=
  joint200 A K R hg h1 h2 hw

/-- 3. Joint bound at 380M. -/
theorem joint380_bridge_non_vacuous_and_tight (A K R : Nat) (hg : 24 * A + 21 * K ≤ 3800000)
    (h1 : R ≤ 82 * A + 63 * K) (h2 : R ≤ 66 * A + 64 * K)
    (hw : 7 * (R - 3 * K - 3 * A) ≤ inputBytes) :
    rw4 A K R ≤ 41673550747 :=
  joint380 A K R hg h1 h2 hw

/-- 4. The near-optimum uses many tries, and one trie costs strictly less. -/
theorem near_optimum_and_multi_worse_bridge_non_vacuous_and_tight :
    (rw4 5555 88888 (82 * 5555 + 63 * 88888) = 27655104258 ∧
      24 * 5555 + 21 * 88888 ≤ 2000000) ∧
    rw4 1 95236 (82 + 63 * 95236) < rw4 5555 88888 (82 * 5555 + 63 * 88888) :=
  ⟨near200, multi_worse⟩

/-- 5. Multi-trie totals: 13_167_715_213 passes 68x and 21_085_502_713 passes 42x. -/
theorem main_slopes_bridge_non_vacuous_and_tight :
    (main200 = 13167715213 ∧ 68 * main200 < yukon ∧ yukon < 69 * main200) ∧
    (main380 = 21085502713 ∧ 42 * main380 < yukon ∧ yukon < 43 * main380) :=
  ⟨main200_slope, main380_slope⟩

/-- 6. Margins at both ceilings. -/
theorem margins_bridge_non_vacuous_and_tight :
    yukon - 68 * main200 = 5315290990 ∧ yukon - 42 * main380 = 15128811528 :=
  margins

/-- 7. StackAlloc is the identity off label 6, and it stays alloc-free and GC-free. -/
theorem identity_and_noGc_bridge_non_vacuous_and_tight
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
  ⟨InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackAlloc_progComp_eq_id_of_ne_six
      arch prog wc ac perf,
   InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackAlloc_noAlloc_noGcCall_unconditional
      arch prog wc ac perf⟩

/-- 8. The 96-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem ninety_six_portfolio_under_yukon_non_vacuous_and_tight :
    NinetySixShape ∧ yukon = 900719925474 ∧
    UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.portfolio.length = 96 ∧
    (∀ K ∈ UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.portfolio, K < yukon) :=
  ⟨ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 9. Every one of the 96 budgets carries a finite certificate, from one base certificate. -/
theorem ninety_six_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    NinetySixShape ∧
    (∀ K ∈ UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(ninety_six_budget_certificates_non_vacuous_and_tight cert).1,
   (ninety_six_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 10. Grand bridge: the 68x multi-trie total, the StackAlloc identity, and the 96-budget
portfolio with finite certificates. -/
theorem multi_trie_gas_unconditional_sixty_eight_x_and_ninety_six_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool)
    (cert : CertificateAt 1212035192) :
    (main200 = 13167715213 ∧ 68 * main200 < yukon) ∧
    (∀ y ∈ InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.rawCallSections
        arch prog wc ac perf, y.1 ≠ Flapjack.storeConstsStubLocation →
      Flapjack.Compiler.Backend.StackAlloc.progComp y = y) ∧
    (NinetySixShape ∧
      ∀ K ∈ UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨main200_slope.1, main200_slope.2.1⟩,
   InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackAlloc_progComp_eq_id_of_ne_six
     arch prog wc ac perf,
   ⟨(ninety_six_budget_certificates_non_vacuous_and_tight cert).1,
    (ninety_six_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetySixBudgetBridge
