import InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit
import InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock
import InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# SaltedNodedbTwentySevenXAndEightyTwoBudgetBridge

Wave 5 bridge (W5_221). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyTwoBudgetBridge

open InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit
open InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock
open InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. The salted nodedb row dissects, and the probe row is exactly two passes of eight steps
over the node table. -/
theorem dissect_and_probes_bridge_non_vacuous_and_tight :
    (decodeMemo + probesR8 + (20036870848 - 619060000) = 38946487944) ∧
    probesR8 = 2 * 8 * (16 * 33554428) :=
  ⟨dissect.1, probes_salted⟩

/-- 2. One salted visit costs 30 + 633 = 663 ticks, strictly under the 1000-tick unit. -/
theorem visit_cost_bridge_non_vacuous_and_tight :
    30 + 633 = 663 ∧ 663 < 1000 :=
  visit_cost

/-- 3. Witness plus MPT at 200M, and the salted post-EVM row. -/
theorem witness_mpt_and_post_bridge_non_vacuous_and_tight :
    witnessMptSalted 200000000 = 26801608212 ∧ postEvmSalted = 681400462 :=
  ⟨wm_vals.1, post_val⟩

/-- 4. Salted main totals: 32_905_132_252 passes 27x and 41_010_777_082 passes 21x. -/
theorem main_slopes_bridge_non_vacuous_and_tight :
    (main200 = 32905132252 ∧ 27 * main200 < yukon ∧ yukon < 28 * main200) ∧
    (main380 = 41010777082 ∧ 21 * main380 < yukon ∧ yukon < 22 * main380) :=
  ⟨main200_slope, main380_slope⟩

/-- 5. The decode and probe rows dominate, and dropping one probe pass is the lever. -/
theorem dominant_and_lever_bridge_non_vacuous_and_tight :
    100 * (decodeMemo + probesR8) > 59 * main200 ∧
    main200 - probesR8 + 2 * 1 * 536870848 = 25388940380 :=
  ⟨dominant, r1_lever.1⟩

/-- 6. The three initialization sections are storeConsts-free, and initCode preserves the clock. -/
theorem init_stubs_and_clock_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maximumHeap pointer start : Nat)
    (s t : Flapjack.StackSemStateFiniteExact width C F)
    (r : Option (Flapjack.StackSemResult width))
    (run : Flapjack.StackSemEvaluate.evaluate
      (Flapjack.Compiler.Backend.StackRemove.initCode generateGc maximumHeap pointer, s) = (r, t)) :
    (∀ e ∈ Flapjack.Compiler.Backend.StackRemove.initStubs (width := width) generateGc maximumHeap pointer start,
      InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true) ∧
    t.clock = s.clock :=
  ⟨noSt_initStubs generateGc maximumHeap pointer start,
   initCode_clock_preserved generateGc maximumHeap pointer s t r run⟩

/-- 7. Every section of the stack-side compile except label 6 is storeConsts-free. -/
theorem stackRemoveCompile_sections_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config)
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) :
    ∀ e ∈ Flapjack.Compiler.Backend.StackRemove.compileHOL jump bounds generateGc maximumHeap
        pointer start
        (Flapjack.Compiler.Backend.StackAlloc.compile dc
          (Flapjack.Compiler.Backend.StackRawCall.compile
            (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
              (Flapjack.Compiler.Backend.WordToWord.compile wc ac
                (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2)),
      e.1 = Flapjack.storeConstsStubLocation ∨
      InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true :=
  stackRemoveCompile_sections_noSt arch prog wc ac perf dc jump bounds generateGc maximumHeap
    pointer start

/-- 8. The 82-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem eighty_two_portfolio_under_yukon_non_vacuous_and_tight :
    EightyTwoShape ∧ yukon = 900719925474 ∧
    OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.portfolio.length = 82 ∧
    (∀ K ∈ OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.portfolio, K < yukon) :=
  ⟨eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 9. Every one of the 82 budgets carries a finite certificate, from one base certificate. -/
theorem eighty_two_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    EightyTwoShape ∧
    (∀ K ∈ OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(eighty_two_budget_certificates_non_vacuous_and_tight cert).1,
   (eighty_two_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 10. Grand bridge: the 27x salted total, zero extra clock on every user body, and the
82-budget portfolio with finite certificates. -/
theorem salted_nodedb_twenty_seven_x_and_eighty_two_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (perf : Bool) (dc : Flapjack.Compiler.Backend.DataToWord.Config)
    (info : Flapjack.Spt Nat) (jump : Bool) (bounds : BitVec width × BitVec width)
    (generateGc : Bool) (maximumHeap pointer start : Nat)
    (cert : CertificateAt 1212035192) :
    (main200 = 32905132252 ∧ 27 * main200 < yukon) ∧
    (∀ y ∈ (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac perf
        (Flapjack.Compiler.Backend.WordToWord.compile wc ac
          (Flapjack.panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = Flapjack.storeConstsStubLocation ∨
      ∀ (source : Flapjack.StackSemStateFiniteExact width C F)
        (result : Option (Flapjack.StackSemResult width))
        (postSource target : Flapjack.StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CodeNoSt source →
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
    (EightyTwoShape ∧
      ∀ K ∈ OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨main200_slope.1, main200_slope.2.1⟩,
   (pancake_stackRemove_compileProg_zeroExtraBodyClock (C := C) (F := F) arch prog wc ac perf dc
      info jump bounds generateGc maximumHeap pointer start).2.2.2,
   ⟨(eighty_two_budget_certificates_non_vacuous_and_tight cert).1,
    (eighty_two_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyTwoBudgetBridge
