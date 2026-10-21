import InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
import InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
import InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# ByteCoupledWitnessThirtySixXAndEightyFourBudgetBridge

Wave 5 bridge (W5_226). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightyFourBudgetBridge

open InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
open InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
open InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Hash references are bounded by the input, and the bound is tight. -/
theorem refs_bound_and_tight_bridge_non_vacuous_and_tight :
    (∀ h : Nat, 33 * h ≤ inputBytes → h ≤ 4067203) ∧
    (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) :=
  ⟨refs_bound, refs_tight⟩

/-- 2. The reference ratio and the probe row at 200M. -/
theorem ratio_and_probes_bridge_non_vacuous_and_tight :
    (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
    (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248) :=
  ⟨ratio, probe_vals.1, probe_vals.2.1⟩

/-- 3. Coupling the probes to the bytes read saves 8_523_258_320 ticks. -/
theorem gain_bridge_non_vacuous_and_tight :
    8589933568 - probes 200000000 = 8523258320 :=
  gain

/-- 4. Byte-coupled main totals: 24_381_873_932 passes 36x and 32_488_958_762 passes 27x. -/
theorem main_slopes_bridge_non_vacuous_and_tight :
    (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
    (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) :=
  ⟨main200_slope, main380_slope⟩

/-- 5. Margins at both ceilings, and the decode row dominates. -/
theorem margins_and_decode_bridge_non_vacuous_and_tight :
    (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
    100 * 10938743528 > 44 * main200 :=
  ⟨margins, decode_dominates⟩

/-- 6. Every section other than label 6 is clean, and the live table has no entry at label 6. -/
theorem clean_sections_and_dead_stub_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config)
    (l : List (Nat × Flapjack.Compiler.Backend.StackLang.HolProg width)) :
    (∀ e ∈ stackAllocSections arch prog wc ac perf dc,
      e.1 = Flapjack.storeConstsStubLocation ∨
      InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts.Clean e.2 = true) ∧
    Flapjack.sptLookup Flapjack.storeConstsStubLocation
      (Flapjack.sptFromAList (liveSections l)) = none :=
  ⟨stackAllocSections_clean arch prog wc ac perf dc, liveTable_lookup_six l⟩

/-- 7. The full table really contains label 6, so filtering it out is not a no-op. -/
theorem fullTable_has_label6_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config) :
    (∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = Flapjack.storeConstsStubLocation) ∧
    Flapjack.sptLookup Flapjack.storeConstsStubLocation
      (Flapjack.sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none :=
  fullTable_has_label6 arch prog wc ac perf dc

/-- 8. The 84-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem eighty_four_portfolio_under_yukon_non_vacuous_and_tight :
    EightyFourShape ∧ yukon = 900719925474 ∧
    SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.portfolio.length = 84 ∧
    (∀ K ∈ SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.portfolio, K < yukon) :=
  ⟨eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 9. Every one of the 84 budgets carries a finite certificate, from one base certificate. -/
theorem eighty_four_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    EightyFourShape ∧
    (∀ K ∈ SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(eighty_four_budget_certificates_non_vacuous_and_tight cert).1,
   (eighty_four_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 10. Grand bridge: the 36x byte-coupled total, zero extra clock on every user body from the
live table, and the 84-budget portfolio with finite certificates. -/
theorem byte_coupled_witness_thirty_six_x_and_eighty_four_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config)
    (info : Flapjack.Spt Nat)
    (cert : CertificateAt 1212035192) :
    (main200 = 24381873932 ∧ 36 * main200 < yukon) ∧
    (∀ y ∈ (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
        (Flapjack.Compiler.Backend.WordToWord.compile wc ac
          (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = Flapjack.storeConstsStubLocation ∨
      ∀ (source : Flapjack.StackSemStateFiniteExact width C F)
        (result : Option (Flapjack.StackSemResult width))
        (postSource target : Flapjack.StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = Flapjack.sptFromAList
          (liveSections (stackAllocSections arch prog wc ac perf dc)) →
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
    (EightyFourShape ∧
      ∀ K ∈ SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨main200_slope.1, main200_slope.2.1⟩,
   panToStackRemove_body_zeroExtraClock_liveTable (C := C) (F := F) arch prog wc ac perf dc info,
   ⟨(eighty_four_budget_certificates_non_vacuous_and_tight cert).1,
    (eighty_four_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightyFourBudgetBridge
