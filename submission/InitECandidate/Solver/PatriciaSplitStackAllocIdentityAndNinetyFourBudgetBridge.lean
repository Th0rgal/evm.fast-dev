import InitECandidate.Solver.PatriciaSplitSixtyEightXAndNinetyTwoBudgetBridge
import InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
import InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# PatriciaSplitStackAllocIdentityAndNinetyFourBudgetBridge

Wave 5 bridge (W5_253). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetBridge

open InitECandidate.Solver.PatriciaSplitSixtyEightXAndNinetyTwoBudgetBridge
open InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
open InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Allocation versus path length at 200M. -/
theorem alloc_vs_path_ninety_four_bridge_non_vacuous_and_tight :
    3 * InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.keys
        200000000 = 285714 ∧
    65 * InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.keys
        200000000 = 6190470 :=
  alloc_vs_path_bridge_non_vacuous_and_tight

/-- 2. Dirty levels and the per-level root cost. -/
theorem level_sums_and_root_vals_ninety_four_bridge_non_vacuous_and_tight :
    (InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.dirtyLevels
        95238 = 5784185 ∧
      InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.dirtyLevels
        180952 = 10927025) ∧
    (InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.rootLevel
        200000000 = 3847103205 ∧
      InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.rootLevel
        380000000 = 7269663225) :=
  level_sums_and_root_vals_bridge_non_vacuous_and_tight

/-- 3. Single-trie totals: 13_120_876_751 passes 68x and 20_956_676_771 passes 42x. -/
theorem single_trie_slopes_ninety_four_bridge_non_vacuous_and_tight :
    (InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main200Single =
        13120876751 ∧
      68 * InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main200Single <
        yukon ∧
      yukon <
        69 * InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main200Single) ∧
    (InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main380Single =
        20956676771 ∧
      42 * InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main380Single <
        yukon ∧
      yukon <
        43 * InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main380Single) :=
  single_trie_slopes_bridge_non_vacuous_and_tight

/-- 4. Multi-trie accounting, and the sub-ten-billion floor. -/
theorem multi_trie_and_floor_ninety_four_bridge_non_vacuous_and_tight :
    ((List.range 65).foldl (fun s _ => s + 95238) 0 = 65 * 95238) ∧
    13378055156 -
        InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.rootOld
          200000000 = 9273773546 :=
  multi_trie_and_floor_bridge_non_vacuous_and_tight

/-- 5. No GC call on any StackRawCall section, and none after StackAlloc. -/
theorem noGcCall_unconditional_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool) :
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.NoGcCall y.2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
          (Flapjack.Compiler.Backend.StackAlloc.progComp y).2 = true ∧
        InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.NoGcCall
          (Flapjack.Compiler.Backend.StackAlloc.progComp y).2 = true) :=
  ⟨panToStackRawCall_noGcCall_unconditional arch prog wc ac perf,
   panToStackAlloc_noAlloc_noGcCall_unconditional arch prog wc ac perf⟩

/-- 6. StackAlloc is the identity off label 6, and it really rewrites a tagged storeConsts. -/
theorem stackAlloc_identity_and_exception_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool) (n m : Nat) :
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ Flapjack.storeConstsStubLocation →
      Flapjack.Compiler.Backend.StackAlloc.progComp y = y) ∧
    Flapjack.Compiler.Backend.StackAlloc.comp n m
        (.storeConsts 0 1 (some Flapjack.storeConstsStubLocation) :
          Flapjack.Compiler.Backend.StackLang.HolProg width) ≠
      ((.storeConsts 0 1 (some Flapjack.storeConstsStubLocation) :
          Flapjack.Compiler.Backend.StackLang.HolProg width), m) :=
  ⟨panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf,
   stackAlloc_not_id_on_tagged_storeConsts n m⟩

/-- 7. The 94-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem ninety_four_portfolio_under_yukon_non_vacuous_and_tight :
    NinetyFourShape ∧ yukon = 900719925474 ∧
    PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.portfolio.length = 94 ∧
    (∀ K ∈ PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.portfolio, K < yukon) :=
  ⟨ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 8. Every one of the 94 budgets carries a finite certificate, from one base certificate. -/
theorem ninety_four_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    NinetyFourShape ∧
    (∀ K ∈ PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(ninety_four_budget_certificates_non_vacuous_and_tight cert).1,
   (ninety_four_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 9. The StackAlloc identity and the 68x single-trie total, together. -/
theorem identity_and_single_trie_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool) :
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ Flapjack.storeConstsStubLocation →
      Flapjack.Compiler.Backend.StackAlloc.progComp y = y) ∧
    InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main200Single =
      13120876751 ∧
    68 * InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main200Single <
      yukon :=
  ⟨panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf,
   single_trie_slopes_bridge_non_vacuous_and_tight.1.1,
   single_trie_slopes_bridge_non_vacuous_and_tight.1.2.1⟩

/-- 10. Grand bridge: the 68x total, the StackAlloc identity, and the 94-budget portfolio with
finite certificates. -/
theorem patricia_split_stack_alloc_identity_and_ninety_four_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool)
    (cert : CertificateAt 1212035192) :
    (InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main200Single =
        13120876751 ∧
      68 * InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main200Single <
        yukon) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ Flapjack.storeConstsStubLocation →
      Flapjack.Compiler.Backend.StackAlloc.progComp y = y) ∧
    (NinetyFourShape ∧
      ∀ K ∈ PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨single_trie_slopes_bridge_non_vacuous_and_tight.1.1,
    single_trie_slopes_bridge_non_vacuous_and_tight.1.2.1⟩,
   panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf,
   ⟨(ninety_four_budget_certificates_non_vacuous_and_tight cert).1,
    (ninety_four_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetBridge
