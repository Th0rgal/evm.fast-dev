import InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster
import InitECandidate.Solver.SelfContainedExactMergeBalSeventyThreeXAndOneHundredBudgetMaster
import InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_274: exact imported EVM dispatch/table arithmetic, full self-contained compiler
contracts and 102 conditional finite certificates. Hand cost estimates retain
the model assumptions of bounded salted probes, DAG memoization and gas/byte
constraints; they do not establish semantic runtime certificates. Finite
certificates remain conditional on the base semantic certificate. NoGcCall
excludes direct GC calls only. ClockOk retains its final-halt allowance and
exceptional StackAlloc may add one tick. -/
namespace InitECandidate.Solver.SelfContainedEvmStepDispatchSeventyEightXAndOneHundredTwoBudgetMaster

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







abbrev oneHundredExplicitFiniteKBugdetTable := TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster.oneHundredExplicitFiniteKBugdetTable

open _root_.InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster

abbrev oneHundredTwoExplicitFiniteKBugdetTable := ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster.oneHundredTwoExplicitFiniteKBugdetTable
abbrev portfolio := oneHundredTwoExplicitFiniteKBugdetTable
abbrev OneHundredTwoShape := ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster.OneHundredTwoShape

theorem ratios_non_vacuous_and_tight : jumpdestTicks = 5 ∧ addTicks = 9 ∧ addTicks ≤ 18 * 3 ∧ jumpdestTicks ≤ 18 * 1 ∧
    push31Ticks = 18 * 3 :=
  GuestEvmStepDispatchAndNinetyXMaster.ratios

theorem sload_inside_non_vacuous_and_tight :
    (sloadWarmTicks = 226 ∧ sloadWarmTicks ≤ 18 * 100) ∧
    (∀ a b : Nat, sloadWarmTicks * a + 18 * b ≤ 18 * (100 * a + b)) :=
  ⟨GuestEvmStepDispatchAndNinetyXMaster.sload_inside, GuestEvmStepDispatchAndNinetyXMaster.joint⟩

theorem removed_non_vacuous_and_tight : 336 * 2000000 = 672000000 ∧ 450000000 + 336 * 3800000 = 1726800000 :=
  GuestEvmStepDispatchAndNinetyXMaster.removed

theorem main200_slope_non_vacuous_and_tight : main200 = 11546768760 ∧ 78 * main200 < yukon ∧ yukon < 79 * main200 :=
  GuestEvmStepDispatchAndNinetyXMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight : main380 = 17251948659 ∧ 52 * main380 < yukon ∧ yukon < 53 * main380 :=
  GuestEvmStepDispatchAndNinetyXMaster.main380_slope

theorem margins_non_vacuous_and_tight : yukon - 78 * main200 = 71962194 ∧ yukon - 52 * main380 = 3618595206 :=
  GuestEvmStepDispatchAndNinetyXMaster.margins

theorem no_90_non_vacuous_and_tight : yukon / 90 = 10007999171 ∧ yukon < 90 * main200 :=
  GuestEvmStepDispatchAndNinetyXMaster.no_90

/-- Strict improvement over the previous 73x row, with its threshold pinned. -/
theorem strict_improvement_over_seventy_three_non_vacuous_and_tight :
    main200 < 12218768760 ∧ 73 * 12218768760 < yukon ∧
    yukon < 74 * 12218768760 ∧ 12218768760 - main200 = 672000000 := by decide

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
  SelfContainedExactMergeBalSeventyThreeXAndOneHundredBudgetMaster.pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight arch prog wc ac perf dc info

theorem user_sections_base_cases_stack_space_non_vacuous_and_tight :
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (((∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget)))) ∧
    (((∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget)))) :=
  SelfContainedExactMergeBalSeventyThreeXAndOneHundredBudgetMaster.user_sections_base_cases_stack_space_non_vacuous_and_tight

/-- Exactly 102 strictly increasing finite budgets below Yukon, with last entry. -/
theorem one_hundred_two_budget_table_non_vacuous_and_tight :
    OneHundredTwoShape ∧ oneHundredTwoExplicitFiniteKBugdetTable.length = 102 ∧
    oneHundredTwoExplicitFiniteKBugdetTable.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwoExplicitFiniteKBugdetTable, K < 900719925474) ∧
    oneHundredTwoExplicitFiniteKBugdetTable.getLast? = some 889500000000 := by
  refine ⟨ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster.one_hundred_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  decide

theorem one_hundred_two_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwoShape ∧
    (∀ K ∈ oneHundredTwoExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster.one_hundred_two_budget_certificates_non_vacuous_and_tight cert

#print axioms ratios_non_vacuous_and_tight
#print axioms sload_inside_non_vacuous_and_tight
#print axioms removed_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms no_90_non_vacuous_and_tight
#print axioms strict_improvement_over_seventy_three_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight
#print axioms user_sections_base_cases_stack_space_non_vacuous_and_tight
#print axioms one_hundred_two_budget_table_non_vacuous_and_tight
#print axioms one_hundred_two_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedEvmStepDispatchSeventyEightXAndOneHundredTwoBudgetMaster
