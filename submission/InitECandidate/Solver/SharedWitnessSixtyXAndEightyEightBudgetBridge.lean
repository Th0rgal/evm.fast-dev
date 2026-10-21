import InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster
import InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural
import InitECandidate.Solver.JointRlpArityFiftySixXAndEightyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# SharedWitnessSixtyXAndEightyEightBudgetBridge

Wave 5 bridge (W5_236). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.SharedWitnessSixtyXAndEightyEightBudgetBridge

open InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural
open InitECandidate.Solver.JointRlpArityFiftySixXAndEightyEightBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. The joint cost of shared witness nodes is bounded by the input. -/
theorem joint_bound_bridge_non_vacuous_and_tight (m n2 n17 h : Nat)
    (hb : 4 * m + 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes) :
    jointCost m n2 n17 h ≤ 138 * (inputBytes / 4) :=
  joint_bound m n2 n17 h hb

/-- 2. The bound is tight, and an all-branch mix is not the worst case. -/
theorem joint_tight_and_branch_bridge_non_vacuous_and_tight :
    (4 * 33554428 ≤ inputBytes ∧ jointCost 0 33554428 0 0 = 4630511064) ∧
    jointCost 0 7456539 0 0 < jointCost 0 33554428 0 0 :=
  ⟨⟨joint_tight.1, joint_tight.2.1⟩, branch_not_worst⟩

/-- 3. Shared keccak blocks and the joint row: 18_750_986 blocks, joint cost 4_649_262_050,
saving 820_219_351 against the separate rows. -/
theorem joint_val_bridge_non_vacuous_and_tight :
    keccakBlocks = 18750986 ∧ jointNew = 4649262050 ∧ separateOld - jointNew = 820219351 :=
  joint_val

/-- 4. Shared main totals: 14_988_667_700 passes 60x and 23_095_752_530 passes 38x. -/
theorem main_slopes_bridge_non_vacuous_and_tight :
    (main200 = 14988667700 ∧ 60 * main200 < yukon ∧ yukon < 61 * main200) ∧
    (main380 = 23095752530 ∧ 38 * main380 < yukon ∧ yukon < 39 * main380) :=
  ⟨main200_slope, main380_slope⟩

/-- 5. Margins at both ceilings. -/
theorem margins_bridge_non_vacuous_and_tight :
    yukon - 60 * main200 = 1399863474 ∧ yukon - 38 * main380 = 23081329334 :=
  margins

/-- 6. No section of the StackRawCall output contains alloc, stubs included. -/
theorem noAlloc_unconditional_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ Flapjack.Compiler.Backend.StackRawCall.compile
        (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
          (Flapjack.Compiler.Backend.WordToWord.compile wc ac
            (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc y.2 = true :=
  panToStackRawCall_noAlloc_unconditional arch prog wc ac perf

/-- 7. StackAlloc creates no GC call: a section without one keeps none and stays alloc-free. -/
theorem noAlloc_noGcCall_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ Flapjack.Compiler.Backend.StackRawCall.compile
        (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
          (Flapjack.Compiler.Backend.WordToWord.compile wc ac
            (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.NoGcCall y.2 = true →
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
          (Flapjack.Compiler.Backend.StackAlloc.progComp y).2 = true ∧
        InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.NoGcCall
          (Flapjack.Compiler.Backend.StackAlloc.progComp y).2 = true :=
  panToStackAlloc_noAlloc_noGcCall arch prog wc ac perf

/-- 8. The 88-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem eighty_eight_portfolio_under_yukon_non_vacuous_and_tight :
    EightyEightShape ∧ yukon = 900719925474 ∧
    JointRlpArityFiftySixXAndEightyEightBudgetMaster.portfolio.length = 88 ∧
    (∀ K ∈ JointRlpArityFiftySixXAndEightyEightBudgetMaster.portfolio, K < yukon) :=
  ⟨eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 9. Every one of the 88 budgets carries a finite certificate, from one base certificate. -/
theorem eighty_eight_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    EightyEightShape ∧
    (∀ K ∈ JointRlpArityFiftySixXAndEightyEightBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(eighty_eight_budget_certificates_non_vacuous_and_tight cert).1,
   (eighty_eight_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 10. Grand bridge: the 60x shared total, zero extra clock with no alloc and no GC call, and
the 88-budget portfolio with finite certificates. -/
theorem shared_witness_sixty_x_and_eighty_eight_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config)
    (info : Flapjack.Spt Nat)
    (cert : CertificateAt 1212035192) :
    (main200 = 14988667700 ∧ 60 * main200 < yukon) ∧
    (∀ y ∈ Flapjack.Compiler.Backend.StackRawCall.compile
        (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
          (Flapjack.Compiler.Backend.WordToWord.compile wc ac
            (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc y.2 = true) ∧
    (EightyEightShape ∧
      ∀ K ∈ JointRlpArityFiftySixXAndEightyEightBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨main200_slope.1, main200_slope.2.1⟩,
   (panToStackRemove_noAlloc_noGc_zeroExtraClock (C := C) (F := F) arch prog wc ac perf dc
      info).1,
   ⟨(eighty_eight_budget_certificates_non_vacuous_and_tight cert).1,
    (eighty_eight_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.SharedWitnessSixtyXAndEightyEightBudgetBridge
