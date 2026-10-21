import InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster
import InitECandidate.Solver.SelfContainedJointRlpArityFiftySixXAndEightySixBudgetMaster
import InitECandidate.Solver.JointRlpArityFiftySixXAndEightyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_238: exact arithmetic for the imported shared build/decode node model,
full self-contained compiler simulations, live-table contracts and 88
conditional finite certificates. Shared byte conservation assumes disjoint
entries, DAG memoization and the stated minimum entry sizes. Arithmetic cost
estimates are not semantic runtime certificates; finite certificates remain
conditional on the base semantic certificate. ClockOk retains its final-halt
allowance; exceptional StackAlloc may require one additional tick. -/
namespace InitECandidate.Solver.SelfContainedSharedWitnessSixtyXAndEightyEightBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev portfolio := JointRlpArityFiftySixXAndEightyEightBudgetMaster.portfolio
abbrev EightyEightShape := JointRlpArityFiftySixXAndEightyEightBudgetMaster.EightyEightShape

/-- Shared-entry byte bound and its attained all-two-item endpoint. -/
theorem joint_bound_joint_tight_non_vacuous_and_tight :
    (∀ m n2 n17 h : Nat, 4 * m + 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes →
      jointCost m n2 n17 h ≤ 138 * (inputBytes / 4)) ∧
    (4 * 33554428 ≤ inputBytes ∧ jointCost 0 33554428 0 0 = 4630511064 ∧
     inputBytes / 4 = 33554428) :=
  ⟨joint_bound, joint_tight⟩

/-- Imported node-count comparison and exact joint row, Keccak blocks and gain. -/
theorem branch_not_worst_joint_val_non_vacuous_and_tight :
    (jointCost 0 7456539 0 0 < jointCost 0 33554428 0 0) ∧
    (keccakBlocks = 18750986 ∧ jointNew = 4649262050 ∧
     separateOld - jointNew = 820219351) :=
  ⟨branch_not_worst, joint_val⟩

/-- Both complete main totals, adjacent multiplier thresholds and exact margins. -/
theorem main200_main380_slopes_margins_non_vacuous_and_tight :
    (main200 = 14988667700 ∧ 60 * main200 < yukon ∧ yukon < 61 * main200) ∧
    (main380 = 23095752530 ∧ 38 * main380 < yukon ∧ yukon < 39 * main380) ∧
    (yukon - 60 * main200 = 1399863474 ∧ yukon - 38 * main380 = 23081329334) :=
  ⟨main200_slope, main380_slope, margins⟩

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedJointRlpArityFiftySixXAndEightySixBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

theorem base_cases_zero_clock_non_vacuous_and_tight :
    ((∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.skip : HolProg width) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .skip,
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.tick, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.tick : HolProg width) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .tick,
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (instruction : HolInst width)
    (_hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.inst instruction) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.inst instruction),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackLoad register count : HolProg width) pointer),
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoad register count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.stackStore register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackStore register count : HolProg width) pointer),
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStore register count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget))) :=
  SelfContainedJointRlpArityFiftySixXAndEightySixBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

theorem stack_space_clock_non_vacuous_and_tight :
    ((∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackFree count) : HolProg width) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackAlloc count) : HolProg width) pointer),
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F), clock ≤ 1 ∧ (result = none → clock = 0) ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget))) :=
  SelfContainedJointRlpArityFiftySixXAndEightySixBudgetMaster.stack_space_clock_non_vacuous_and_tight

theorem pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) :
    (∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
    (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
      t.clock = s.clock) ∧
    (∀ e ∈ StackRemove.compileHOL jump bounds generateGc maximumHeap pointer start
        (StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)),
      e.1 = storeConstsStubLocation ∨ StackNoSt e.2 = true) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        CodeNoSt source →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget)) :=
  SelfContainedJointRlpArityFiftySixXAndEightySixBudgetMaster.pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight arch prog wc ac perf dc info jump bounds generateGc maximumHeap pointer start

theorem stackAllocSections_clean_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config) :
    ∀ e ∈ stackAllocSections arch prog wc ac perf dc,
      e.1 = storeConstsStubLocation ∨ Clean e.2 = true :=
  JointRlpArityFiftySixXAndEightyEightBudgetMaster.stackAllocSections_clean_non_vacuous_and_tight arch prog wc ac perf dc

theorem panToStackRemove_body_zeroExtraClock_liveTable_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1, StackNoSt e.2 = true) →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget) :=
  JointRlpArityFiftySixXAndEightyEightBudgetMaster.panToStackRemove_body_zeroExtraClock_liveTable_non_vacuous_and_tight arch prog wc ac perf dc info

theorem fullTable_has_label6_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config) :
    (∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
    sptLookup storeConstsStubLocation
      (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none :=
  JointRlpArityFiftySixXAndEightyEightBudgetMaster.fullTable_has_label6_non_vacuous_and_tight arch prog wc ac perf dc

theorem eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    EightyEightShape :=
  JointRlpArityFiftySixXAndEightyEightBudgetMaster.eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

theorem eighty_eight_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyEightShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  JointRlpArityFiftySixXAndEightyEightBudgetMaster.eighty_eight_budget_certificates_non_vacuous_and_tight cert

#print axioms joint_bound_joint_tight_non_vacuous_and_tight
#print axioms branch_not_worst_joint_val_non_vacuous_and_tight
#print axioms main200_main380_slopes_margins_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight
#print axioms stackAllocSections_clean_non_vacuous_and_tight
#print axioms panToStackRemove_body_zeroExtraClock_liveTable_non_vacuous_and_tight
#print axioms fullTable_has_label6_non_vacuous_and_tight
#print axioms eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms eighty_eight_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedSharedWitnessSixtyXAndEightyEightBudgetMaster
