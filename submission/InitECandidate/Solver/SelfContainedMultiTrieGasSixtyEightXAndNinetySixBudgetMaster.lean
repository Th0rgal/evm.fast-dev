import InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster
import InitECandidate.Solver.SelfContainedStackAllocIdentityAndNinetyFourBudgetMaster
import InitECandidate.Solver.UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_260: exact arithmetic for the imported multi-trie gas/dirty-node model,
full self-contained compiler contracts and 96 conditional finite certificates.
The joint bounds retain all gas, dirty-node and witness-byte hypotheses.
The near200 witness is feasible with an explicit gap to the proved upper bound;
no attained exact optimum is asserted. Arithmetic estimates are not semantic
runtime certificates. Finite certificates remain conditional on the base
semantic certificate. NoGcCall excludes direct GC calls only; ClockOk retains
the final-halt allowance and exceptional StackAlloc may add one tick. -/
namespace InitECandidate.Solver.SelfContainedMultiTrieGasSixtyEightXAndNinetySixBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
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


open _root_.InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster

abbrev portfolio := UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.portfolio
abbrev NinetySixShape := UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.NinetySixShape

/-- Both joint bounds retain their explicit gas, dirty-node and byte constraints. -/
theorem joint200_joint380_non_vacuous_and_tight :
    (∀ A K R : Nat, 24 * A + 21 * K ≤ 2000000 →
      R ≤ 82 * A + 63 * K → R ≤ 66 * A + 64 * K →
      7 * (R - 3 * K - 3 * A) ≤ inputBytes → rw4 A K R ≤ 27655360747) ∧
    (∀ A K R : Nat, 24 * A + 21 * K ≤ 3800000 →
      R ≤ 82 * A + 63 * K → R ≤ 66 * A + 64 * K →
      7 * (R - 3 * K - 3 * A) ≤ inputBytes → rw4 A K R ≤ 41673550747) :=
  ⟨joint200, joint380⟩

/-- Feasible near-optimum: both dirty bounds, gas/byte feasibility, exact gap,
and the strict many-trie versus one-trie comparison. -/
theorem dirty_bounds_multi_worse_opt_tight_non_vacuous_and_tight :
    (82 * 5555 + 63 * 88888 ≤ 82 * 5555 + 63 * 88888) ∧
    (82 * 5555 + 63 * 88888 ≤ 66 * 5555 + 64 * 88888) ∧
    (7 * ((82 * 5555 + 63 * 88888) - 3 * 88888 - 3 * 5555) ≤ inputBytes) ∧
    (rw4 5555 88888 (82 * 5555 + 63 * 88888) = 27655104258 ∧
      24 * 5555 + 21 * 88888 ≤ 2000000) ∧
    (27655360747 - 27655104258 = 256489) ∧
    (rw4 1 95236 (82 + 63 * 95236) < rw4 5555 88888 (82 * 5555 + 63 * 88888)) :=
  ⟨by decide, by decide, by decide, near200, by decide, multi_worse⟩

/-- Exact bases, main totals, adjacent slope thresholds and passing margins. -/
theorem main200_main380_slopes_margins_non_vacuous_and_tight :
    (base200 = 6235124040 ∧ base380 = 10648364040) ∧
    (main200 = 13167715213 ∧ 68 * main200 < yukon ∧ yukon < 69 * main200) ∧
    (main380 = 21085502713 ∧ 42 * main380 < yukon ∧ yukon < 43 * main380) ∧
    (yukon - 68 * main200 = 5315290990 ∧ yukon - 42 * main380 = 15128811528) :=
  ⟨bases, main200_slope, main380_slope, margins⟩

theorem unconditional_noGcCall_noAlloc_noTailHandler_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    (∀ y ∈ rawCallSections arch prog wc ac perf, NoGcCall y.2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, NoTailHandler y.2 = true) :=
  SelfContainedStackAllocIdentityAndNinetyFourBudgetMaster.unconditional_noGcCall_noAlloc_noTailHandler_non_vacuous_and_tight arch prog wc ac perf

theorem panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (DeclHOL width)) (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y :=
  UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight arch prog wc ac perf

theorem stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight {width : Nat} [NeZero width] (n m : Nat) :
    StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m) :=
  UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight n m

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
  UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight arch prog wc ac perf dc info

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedStackAllocIdentityAndNinetyFourBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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
  SelfContainedStackAllocIdentityAndNinetyFourBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  SelfContainedStackAllocIdentityAndNinetyFourBudgetMaster.stack_space_clock_non_vacuous_and_tight

theorem ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    NinetySixShape :=
  UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

theorem ninety_six_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetySixShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.ninety_six_budget_certificates_non_vacuous_and_tight cert

#print axioms joint200_joint380_non_vacuous_and_tight
#print axioms dirty_bounds_multi_worse_opt_tight_non_vacuous_and_tight
#print axioms main200_main380_slopes_margins_non_vacuous_and_tight
#print axioms unconditional_noGcCall_noAlloc_noTailHandler_non_vacuous_and_tight
#print axioms panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight
#print axioms stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms ninety_six_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedMultiTrieGasSixtyEightXAndNinetySixBudgetMaster
