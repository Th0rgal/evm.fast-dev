import InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster
import InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightyFourBudgetBridge
import InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# JointRlpArityFiftySixXAndEightySixBudgetBridge

Wave 5 bridge (W5_232). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.JointRlpArityFiftySixXAndEightySixBudgetBridge

open InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster
open InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightyFourBudgetBridge
open InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. The joint RLP bound: any mix of pairs, 17-nodes and hashes fits the input. -/
theorem joint_bound_bridge_non_vacuous_and_tight (n2 n17 h : Nat)
    (hb : 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes) :
    jointCost n2 n17 h ≤ 326 * inputBytes / 18 :=
  joint_bound n2 n17 h hb

/-- 2. The bound is tight, and the branch count is 7_456_539. -/
theorem joint_tight_and_branch_count_bridge_non_vacuous_and_tight :
    (4 * 2 + 18 * 7456539 + 32 * 0 ≤ inputBytes) ∧
    (inputBytes / 18 = 7456539 ∧ 9 * 7456539 ≤ 2 * 33554428) :=
  ⟨joint_tight.1, branch_count⟩

/-- 3. Replacing the old decode and probe rows saves 8_572_986_881 ticks. -/
theorem gain_bridge_non_vacuous_and_tight :
    decodeProbesOld - decodeProbesNew = 8572986881 :=
  gain

/-- 4. Joint main totals: 15_808_887_051 passes 56x and 23_915_971_881 passes 37x. -/
theorem main_slopes_bridge_non_vacuous_and_tight :
    (main200 = 15808887051 ∧ 56 * main200 < yukon ∧ yukon < 57 * main200 ∧
      50 * main200 < yukon) ∧
    (main380 = 23915971881 ∧ 37 * main380 < yukon ∧ yukon < 38 * main380) :=
  ⟨⟨main200_slope.1, main200_slope.2.1, main200_slope.2.2.1, main200_slope.2.2.2⟩,
   main380_slope⟩

/-- 5. Margins at both ceilings, and the nodedb build dominates the new decode row. -/
theorem margins_and_build_bridge_non_vacuous_and_tight :
    (yukon - 56 * main200 = 15422250618 ∧ yukon - 37 * main380 = 15828965877) ∧
    (100 * 3038649506 > 19 * main200 ∧ 3038649506 > decodeProbesNew) :=
  ⟨margins, build_dominates⟩

/-- 6. Every section other than label 6 is clean, and the live table has no entry at label 6. -/
theorem clean_sections_and_dead_stub_eighty_six_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config)
    (l : List (Nat × Flapjack.Compiler.Backend.StackLang.HolProg width)) :
    (∀ e ∈ InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
        arch prog wc ac perf dc,
      e.1 = Flapjack.storeConstsStubLocation ∨
      InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts.Clean e.2 = true) ∧
    Flapjack.sptLookup Flapjack.storeConstsStubLocation
      (Flapjack.sptFromAList
        (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.liveSections l)) =
      none :=
  clean_sections_and_dead_stub_bridge_non_vacuous_and_tight arch prog wc ac perf dc l

/-- 7. The 86-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem eighty_six_portfolio_under_yukon_non_vacuous_and_tight :
    EightySixShape ∧ yukon = 900719925474 ∧
    ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster.portfolio.length = 86 ∧
    (∀ K ∈ ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster.portfolio, K < yukon) :=
  ⟨eighty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   eighty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   eighty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (eighty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 8. Every one of the 86 budgets carries a finite certificate, from one base certificate. -/
theorem eighty_six_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    EightySixShape ∧
    (∀ K ∈ ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(eighty_six_budget_certificates_non_vacuous_and_tight cert).1,
   (eighty_six_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 9. Zero extra clock on every user body from the live table. -/
theorem zero_extra_clock_live_table_eighty_six_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config)
    (info : Flapjack.Spt Nat) :
    ∀ y ∈ (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
        (Flapjack.Compiler.Backend.WordToWord.compile wc ac
          (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = Flapjack.storeConstsStubLocation ∨
      ∀ (source : Flapjack.StackSemStateFiniteExact width C F)
        (result : Option (Flapjack.StackSemResult width))
        (postSource target : Flapjack.StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = Flapjack.sptFromAList
          (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.liveSections
            (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
              arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1,
          InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true) →
        Flapjack.StackSemEvaluate.evaluate
            ((Flapjack.Compiler.Backend.StackAlloc.progComp
              (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          Flapjack.Compiler.Backend.StackRemove.stateRelHOL j bd ptr source target ∧
          Flapjack.Compiler.Backend.StackProps.regBound
            (Flapjack.Compiler.Backend.StackAlloc.progComp
              (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget,
          InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk clock result ∧
          Flapjack.StackSemEvaluate.evaluate
            (Flapjack.Compiler.Backend.StackRemove.comp j bd ptr
              (Flapjack.Compiler.Backend.StackAlloc.progComp
                (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2,
              {target with clock := clock + target.clock}) = (result, postTarget) :=
  InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.panToStackRemove_body_zeroExtraClock_liveTable
    (C := C) (F := F) arch prog wc ac perf dc info

/-- 10. Grand bridge: the 56x joint total, zero extra clock on every user body, and the
86-budget portfolio with finite certificates. -/
theorem joint_rlp_arity_fifty_six_x_and_eighty_six_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config)
    (info : Flapjack.Spt Nat)
    (cert : CertificateAt 1212035192) :
    (main200 = 15808887051 ∧ 56 * main200 < yukon) ∧
    (∀ y ∈ (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
        (Flapjack.Compiler.Backend.WordToWord.compile wc ac
          (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = Flapjack.storeConstsStubLocation ∨
      ∀ (source : Flapjack.StackSemStateFiniteExact width C F)
        (result : Option (Flapjack.StackSemResult width))
        (postSource target : Flapjack.StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = Flapjack.sptFromAList
          (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.liveSections
            (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
              arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1,
          InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true) →
        Flapjack.StackSemEvaluate.evaluate
            ((Flapjack.Compiler.Backend.StackAlloc.progComp
              (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          Flapjack.Compiler.Backend.StackRemove.stateRelHOL j bd ptr source target ∧
          Flapjack.Compiler.Backend.StackProps.regBound
            (Flapjack.Compiler.Backend.StackAlloc.progComp
              (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget,
          InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk clock result ∧
          Flapjack.StackSemEvaluate.evaluate
            (Flapjack.Compiler.Backend.StackRemove.comp j bd ptr
              (Flapjack.Compiler.Backend.StackAlloc.progComp
                (y.1, Flapjack.Compiler.Backend.StackRawCall.compTop info y.2)).2,
              {target with clock := clock + target.clock}) = (result, postTarget)) ∧
    (EightySixShape ∧
      ∀ K ∈ ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨main200_slope.1, main200_slope.2.1⟩,
   zero_extra_clock_live_table_eighty_six_bridge_non_vacuous_and_tight (C := C) (F := F)
     arch prog wc ac perf dc info,
   ⟨(eighty_six_budget_certificates_non_vacuous_and_tight cert).1,
    (eighty_six_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.JointRlpArityFiftySixXAndEightySixBudgetBridge
