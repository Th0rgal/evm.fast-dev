import InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
import InitECandidate.Solver.SelfContainedSaltedNodedbTwentySevenXAndEightyTwoBudgetMaster
import InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_228: exact arithmetic in the imported byte-coupled witness model,
full compiler contracts including initialization and compiled sections, and
84 conditional finite certificates. Byte coupling assumes DAG memoization and
disjoint node bodies; bounded probe runs are an additional model assumption.
Arithmetic cost estimates are not semantic runtime certificates. The finite
certificates remain conditional on the base semantic certificate. ClockOk
retains its final-halt allowance, and exceptional StackAlloc may add one tick. -/
namespace InitECandidate.Solver.SelfContainedByteCoupledWitnessThirtySixXAndEightyFourBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev portfolio := SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.portfolio
abbrev EightyFourShape := SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.EightyFourShape

/-- Byte-bound implication, attained endpoint, first rejection and old/new ratio. -/
theorem refs_bound_refs_tight_ratio_non_vacuous_and_tight :
    (∀ h : Nat, 33 * h ≤ inputBytes → h ≤ 4067203) ∧
    (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
    (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) :=
  ⟨refs_bound, refs_tight, ratio⟩

/-- Exact probe rows at both gas budgets and the 200M saving. -/
theorem probe_vals_gain_non_vacuous_and_tight :
    (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
     probes 380000000 = 68115248) ∧
    8589933568 - probes 200000000 = 8523258320 :=
  ⟨probe_vals, gain⟩

/-- Both main totals, adjacent multiplier thresholds and exact passing margins. -/
theorem main200_main380_slope_margins_non_vacuous_and_tight :
    (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
    (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
    (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) :=
  ⟨main200_slope, main380_slope, margins⟩

/-- Decode dominance and the separate uncoupled tree-decode comparison. -/
theorem decode_dominates_tree_no_coupling_non_vacuous_and_tight :
    (100 * 10938743528 > 44 * main200) ∧
    (2 * 8 * hashRefs < 2 * 8 * 1110441952) :=
  ⟨decode_dominates, tree_no_coupling⟩

theorem panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 = true :=
  SelfContainedSaltedNodedbTwentySevenXAndEightyTwoBudgetMaster.panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight arch prog wc ac perf info

theorem panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
        CodeNoSt source →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 pointer →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp jump bounds pointer
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget) :=
  SelfContainedSaltedNodedbTwentySevenXAndEightyTwoBudgetMaster.panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight arch prog wc ac perf info

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedSaltedNodedbTwentySevenXAndEightyTwoBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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
  SelfContainedSaltedNodedbTwentySevenXAndEightyTwoBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  SelfContainedSaltedNodedbTwentySevenXAndEightyTwoBudgetMaster.stack_space_clock_non_vacuous_and_tight

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
  SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight arch prog wc ac perf dc info jump bounds generateGc maximumHeap pointer start

theorem eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    EightyFourShape :=
  SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

theorem eighty_four_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyFourShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.eighty_four_budget_certificates_non_vacuous_and_tight cert

#print axioms refs_bound_refs_tight_ratio_non_vacuous_and_tight
#print axioms probe_vals_gain_non_vacuous_and_tight
#print axioms main200_main380_slope_margins_non_vacuous_and_tight
#print axioms decode_dominates_tree_no_coupling_non_vacuous_and_tight
#print axioms panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight
#print axioms panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight
#print axioms eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms eighty_four_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedByteCoupledWitnessThirtySixXAndEightyFourBudgetMaster
