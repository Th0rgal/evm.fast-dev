import InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
import InitECandidate.Solver.SelfContainedPatriciaSplitAndNinetyTwoBudgetMaster
import InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_255: exact StackAlloc identity outside stub six, unconditional absence
of direct GC calls, full compiler simulations and 94 conditional finite
certificates. NoGcCall does not constrain indirect targets. ClockOk retains
the final-halt allowance and exceptional StackAlloc may add one tick.
Patricia estimates retain their single-trie/multi-trie distinction and are not
semantic runtime certificates. Finite certificates remain conditional on the
base semantic certificate. -/
namespace InitECandidate.Solver.SelfContainedStackAllocIdentityAndNinetyFourBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
open _root_.InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural (NoGcCall)
open Flapjack.Pancake.PanLang
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native


open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural (NoTailHandler)

abbrev portfolio := PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.portfolio
abbrev NinetyFourShape := PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.NinetyFourShape

/-- All raw-call sections have no direct GC calls or tail handlers; StackAlloc
preserves absence of allocation and direct GC calls without a NoGcCall premise. -/
theorem unconditional_noGcCall_noAlloc_noTailHandler_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    (∀ y ∈ rawCallSections arch prog wc ac perf, NoGcCall y.2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, NoTailHandler y.2 = true) :=
  ⟨PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackRawCall_noGcCall_unconditional arch prog wc ac perf,
   PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackAlloc_noAlloc_noGcCall_unconditional arch prog wc ac perf,
   PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackRawCall_noTailHandler arch prog wc ac perf⟩

theorem panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (DeclHOL width)) (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y :=
  PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight arch prog wc ac perf

theorem stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight {width : Nat} [NeZero width] (n m : Nat) :
    StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m) :=
  PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight n m

theorem pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) :
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc y.2 = true ∧
      NoGcCall y.2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = sptFromAList
          (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.liveSections
            (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
              arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1,
          InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true) →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget,
          InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget)) :=
  PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight arch prog wc ac perf dc info

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedPatriciaSplitAndNinetyTwoBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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
  SelfContainedPatriciaSplitAndNinetyTwoBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  SelfContainedPatriciaSplitAndNinetyTwoBudgetMaster.stack_space_clock_non_vacuous_and_tight

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
  SelfContainedPatriciaSplitAndNinetyTwoBudgetMaster.pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight arch prog wc ac perf dc info jump bounds generateGc maximumHeap pointer start

theorem fullTable_has_label6_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config) :
    (∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
    sptLookup storeConstsStubLocation
      (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none :=
  SelfContainedPatriciaSplitAndNinetyTwoBudgetMaster.fullTable_has_label6_non_vacuous_and_tight arch prog wc ac perf dc

/-- Complete imported Patricia arithmetic, retaining both trie regimes. -/
theorem patricia_arithmetic_non_vacuous_and_tight :
    ((3 * keys 200000000 = 285714 ∧ 65 * keys 200000000 = 6190470) ∧
    (dirtyLevels 95238 = 5784185 ∧ dirtyLevels 180952 = 10927025 ∧
     dirtyLevels 95238 < 65 * 95238) ∧
    (rootLevel 200000000 = 3847103205 ∧ rootLevel 380000000 = 7269663225 ∧
     rootOld 200000000 - rootLevel 200000000 = 257178405)) ∧
    ((main200Single = 13120876751 ∧ 68 * main200Single < yukon ∧
     yukon < 69 * main200Single) ∧
    (main380Single = 20956676771 ∧ 42 * main380Single < yukon ∧
     yukon < 43 * main380Single)) ∧
    (((List.range 65).foldl (fun s _ => s + 95238) 0 = 65 * 95238 ∧
     67 * 13378055156 < yukon ∧ yukon < 68 * 13378055156) ∧
    (13378055156 - rootOld 200000000 = 9273773546 ∧
     9273773546 < 10000000000 ∧ 10000000000 < 13120876751)) :=
  ⟨SelfContainedPatriciaSplitAndNinetyTwoBudgetMaster.alloc_vs_path_level_sums_root_vals_non_vacuous_and_tight,
   SelfContainedPatriciaSplitAndNinetyTwoBudgetMaster.main200_main380_single_non_vacuous_and_tight,
   SelfContainedPatriciaSplitAndNinetyTwoBudgetMaster.multi_trie_no_sub_ten_non_vacuous_and_tight⟩

theorem ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    NinetyFourShape :=
  PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

theorem ninety_four_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetyFourShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.ninety_four_budget_certificates_non_vacuous_and_tight cert

#print axioms unconditional_noGcCall_noAlloc_noTailHandler_non_vacuous_and_tight
#print axioms panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight
#print axioms stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight
#print axioms fullTable_has_label6_non_vacuous_and_tight
#print axioms patricia_arithmetic_non_vacuous_and_tight
#print axioms ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms ninety_four_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedStackAllocIdentityAndNinetyFourBudgetMaster
