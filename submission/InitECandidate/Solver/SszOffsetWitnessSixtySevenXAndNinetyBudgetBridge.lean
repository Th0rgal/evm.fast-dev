import InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster
import InitECandidate.Solver.SharedWitnessSixtyXAndEightyEightBudgetBridge
import InitECandidate.Solver.SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# SszOffsetWitnessSixtySevenXAndNinetyBudgetBridge

Wave 5 bridge (W5_242). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyBudgetBridge

open InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster
open InitECandidate.Solver.SharedWitnessSixtyXAndEightyEightBudgetBridge
open InitECandidate.Solver.SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. The SSZ-offset joint cost is bounded by the input. -/
theorem joint_bound_bridge_non_vacuous_and_tight (m n2 n17 h : Nat)
    (hb : 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes) :
    jointCost m n2 n17 h ≤ 90 * (inputBytes / 4) :=
  joint_bound m n2 n17 h hb

/-- 2. The bound is tight. -/
theorem joint_tight_bridge_non_vacuous_and_tight :
    4 * 33554428 ≤ inputBytes ∧ jointCost 33554428 0 0 0 = 3019898520 :=
  ⟨joint_tight.1, joint_tight.2.1⟩

/-- 3. SSZ joint row: 3_038_649_506, saving 1_610_612_544 against the previous joint row. -/
theorem joint_val_bridge_non_vacuous_and_tight :
    jointSsz = 3038649506 ∧ jointPrev - jointSsz = 1610612544 :=
  joint_val

/-- 4. SSZ main totals: 13_378_055_156 passes 67x and 21_485_139_986 passes 41x. -/
theorem main_slopes_bridge_non_vacuous_and_tight :
    (main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200) ∧
    (main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380) :=
  ⟨main200_slope, main380_slope⟩

/-- 5. Margins at both ceilings, and the gap to 68x. -/
theorem margins_and_gap_bridge_non_vacuous_and_tight :
    (yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048) ∧
    (yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900) :=
  ⟨margins, sixty_eight_gap⟩

/-- 6. No section of the StackRawCall output contains alloc, stubs included. -/
theorem noAlloc_unconditional_ninety_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ Flapjack.Compiler.Backend.StackRawCall.compile
        (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
          (Flapjack.Compiler.Backend.WordToWord.compile wc ac
            (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        y.2 = true :=
  noAlloc_unconditional_bridge_non_vacuous_and_tight arch prog wc ac perf

/-- 7. StackAlloc creates no GC call: a section without one keeps none and stays alloc-free. -/
theorem noAlloc_noGcCall_ninety_bridge_non_vacuous_and_tight
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
  noAlloc_noGcCall_bridge_non_vacuous_and_tight arch prog wc ac perf

/-- 8. The 90-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem ninety_portfolio_under_yukon_non_vacuous_and_tight :
    NinetyShape ∧ yukon = 900719925474 ∧
    SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster.portfolio.length = 90 ∧
    (∀ K ∈ SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster.portfolio, K < yukon) :=
  ⟨ninety_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   ninety_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   ninety_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (ninety_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 9. Every one of the 90 budgets carries a finite certificate, from one base certificate. -/
theorem ninety_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    NinetyShape ∧
    (∀ K ∈ SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(ninety_budget_certificates_non_vacuous_and_tight cert).1,
   (ninety_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 10. Grand bridge: the 67x SSZ total, no alloc, no GC call, and the 90-budget portfolio with
finite certificates. -/
theorem ssz_offset_witness_sixty_seven_x_and_ninety_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (perf : Bool)
    (cert : CertificateAt 1212035192) :
    (main200 = 13378055156 ∧ 67 * main200 < yukon) ∧
    (∀ y ∈ Flapjack.Compiler.Backend.StackRawCall.compile
        (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
          (Flapjack.Compiler.Backend.WordToWord.compile wc ac
            (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        y.2 = true) ∧
    (NinetyShape ∧
      ∀ K ∈ SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨main200_slope.1, main200_slope.2.1⟩,
   noAlloc_unconditional_bridge_non_vacuous_and_tight arch prog wc ac perf,
   ⟨(ninety_budget_certificates_non_vacuous_and_tight cert).1,
    (ninety_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyBudgetBridge
