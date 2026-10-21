import InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster
import InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
import InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# PatriciaSplitSixtyEightXAndNinetyTwoBudgetBridge

Wave 5 bridge (W5_248). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.PatriciaSplitSixtyEightXAndNinetyTwoBudgetBridge

open InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster
open InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
open InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Allocation versus path length at 200M. -/
theorem alloc_vs_path_bridge_non_vacuous_and_tight :
    3 * keys 200000000 = 285714 ∧ 65 * keys 200000000 = 6190470 :=
  alloc_vs_path

/-- 2. Dirty levels and the per-level root cost. -/
theorem level_sums_and_root_vals_bridge_non_vacuous_and_tight :
    (dirtyLevels 95238 = 5784185 ∧ dirtyLevels 180952 = 10927025) ∧
    (rootLevel 200000000 = 3847103205 ∧ rootLevel 380000000 = 7269663225) :=
  ⟨⟨level_sums.1, level_sums.2.1⟩, root_vals.1, root_vals.2.1⟩

/-- 3. Single-trie totals: 13_120_876_751 passes 68x and 20_956_676_771 passes 42x. -/
theorem single_trie_slopes_bridge_non_vacuous_and_tight :
    (main200Single = 13120876751 ∧ 68 * main200Single < yukon ∧ yukon < 69 * main200Single) ∧
    (main380Single = 20956676771 ∧ 42 * main380Single < yukon ∧ yukon < 43 * main380Single) :=
  ⟨main200_single, main380_single⟩

/-- 4. Multi-trie accounting, and the sub-ten-billion floor. -/
theorem multi_trie_and_floor_bridge_non_vacuous_and_tight :
    ((List.range 65).foldl (fun s _ => s + 95238) 0 = 65 * 95238) ∧
    13378055156 - rootOld 200000000 = 9273773546 :=
  ⟨multi_trie.1, no_sub_ten.1⟩

/-- 5. StackAlloc is the identity on every section other than label 6. -/
theorem stackAlloc_identity_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ Flapjack.storeConstsStubLocation →
      Flapjack.Compiler.Backend.StackAlloc.progComp y = y :=
  panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf

/-- 6. The 92-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem ninety_two_portfolio_under_yukon_non_vacuous_and_tight :
    NinetyTwoShape ∧ yukon = 900719925474 ∧
    SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster.portfolio.length = 92 ∧
    (∀ K ∈ SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster.portfolio, K < yukon) :=
  ⟨ninety_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   ninety_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   ninety_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (ninety_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 7. Every one of the 92 budgets carries a finite certificate, from one base certificate. -/
theorem ninety_two_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    NinetyTwoShape ∧
    (∀ K ∈ SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(ninety_two_budget_certificates_non_vacuous_and_tight cert).1,
   (ninety_two_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 8. No alloc and no GC call on every StackRawCall section, unconditionally. -/
theorem noAlloc_noGc_unconditional_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config)
    (info : Flapjack.Spt Nat) :
    ∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
          y.2 = true ∧
        InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.NoGcCall y.2 = true :=
  (pancake_stackAllocIdentity_noGc_zeroExtraClock (C := C) (F := F) arch prog wc ac perf dc
    info).1

/-- 9. StackAlloc stays alloc-free and GC-free, and is the identity off label 6. -/
theorem stackAlloc_image_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config)
    (info : Flapjack.Spt Nat) :
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
          (Flapjack.Compiler.Backend.StackAlloc.progComp y).2 = true ∧
        InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.NoGcCall
          (Flapjack.Compiler.Backend.StackAlloc.progComp y).2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ Flapjack.storeConstsStubLocation →
      Flapjack.Compiler.Backend.StackAlloc.progComp y = y) :=
  ⟨(pancake_stackAllocIdentity_noGc_zeroExtraClock (C := C) (F := F) arch prog wc ac perf dc
      info).2.1,
   (pancake_stackAllocIdentity_noGc_zeroExtraClock (C := C) (F := F) arch prog wc ac perf dc
      info).2.2.1⟩

/-- 10. Grand bridge: the 68x single-trie total, the StackAlloc identity, and the 92-budget
portfolio with finite certificates. -/
theorem patricia_split_sixty_eight_x_and_ninety_two_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool)
    (cert : CertificateAt 1212035192) :
    (main200Single = 13120876751 ∧ 68 * main200Single < yukon) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ Flapjack.storeConstsStubLocation →
      Flapjack.Compiler.Backend.StackAlloc.progComp y = y) ∧
    (NinetyTwoShape ∧
      ∀ K ∈ SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨main200_single.1, main200_single.2.1⟩,
   panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf,
   ⟨(ninety_two_budget_certificates_non_vacuous_and_tight cert).1,
    (ninety_two_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.PatriciaSplitSixtyEightXAndNinetyTwoBudgetBridge
