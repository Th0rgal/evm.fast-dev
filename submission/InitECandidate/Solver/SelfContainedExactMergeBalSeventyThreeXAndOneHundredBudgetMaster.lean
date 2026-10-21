import InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster
import InitECandidate.Solver.SelfContainedTwoItemNodeRehashSeventyXAndNinetyEightBudgetMaster
import InitECandidate.Solver.TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_270: exact imported merge/BAL arithmetic, full self-contained compiler
contracts and 100 conditional finite certificates. Hand cost estimates retain
the model assumptions of bounded salted probes, DAG memoization and gas/byte
constraints; they do not establish semantic runtime certificates. Finite
certificates remain conditional on the base semantic certificate. NoGcCall
excludes direct GC calls only. ClockOk retains its final-halt allowance and
exceptional StackAlloc may add one tick. -/
namespace InitECandidate.Solver.SelfContainedExactMergeBalSeventyThreeXAndOneHundredBudgetMaster

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






open _root_.InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster

abbrev oneHundredExplicitFiniteKBugdetTable := TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster.oneHundredExplicitFiniteKBugdetTable
abbrev portfolio := oneHundredExplicitFiniteKBugdetTable
abbrev OneHundredShape := TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster.OneHundredShape

theorem merge_vals_non_vacuous_and_tight : mergeTicks 200000000 = 65422992 ∧ mergeTicks 380000000 = 101802000 ∧
    mergeTicks 380000000 < 500000000 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.merge_vals

theorem bal_vals_non_vacuous_and_tight : balTicks 200000000 = 144000000 ∧ balTicks 380000000 = 273600000 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.bal_vals

theorem entry_charge_non_vacuous_and_tight : 12 + 2 * 8 ≤ 60 ∧ 2100 / 100 = 21 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.entry_charge

theorem main200_slope_non_vacuous_and_tight : main200 = 12218768760 ∧ 73 * main200 < yukon ∧ yukon < 74 * main200 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight : main380 = 18978748659 ∧ 47 * main380 < yukon ∧ yukon < 48 * main380 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380_slope

theorem margins_non_vacuous_and_tight : yukon - 73 * main200 = 8749805994 ∧ yukon - 47 * main380 = 8718738501 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.margins

theorem no_75_non_vacuous_and_tight : yukon / 75 = 12009599006 ∧ yukon < 75 * main200 :=
  GuestExactMergeBalPrologueAndSeventyFiveXMaster.no_75

/-- Strict improvement over the previous 70x row, with its threshold pinned. -/
theorem strict_improvement_over_seventy_non_vacuous_and_tight :
    main200 < 12809345768 ∧ 70 * 12809345768 < yukon ∧
    yukon < 71 * 12809345768 ∧ 12809345768 - main200 = 590577008 := by decide

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
  SelfContainedTwoItemNodeRehashSeventyXAndNinetyEightBudgetMaster.pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight arch prog wc ac perf dc info

/-- Full target/user safety and StackRemove base/space simulations. -/
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
  ⟨SelfContainedTwoItemNodeRehashSeventyXAndNinetyEightBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight,
   SelfContainedTwoItemNodeRehashSeventyXAndNinetyEightBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight,
   SelfContainedTwoItemNodeRehashSeventyXAndNinetyEightBudgetMaster.stack_space_clock_non_vacuous_and_tight⟩

/-- Exactly 100 strictly increasing finite budgets below Yukon, with last entry. -/
theorem one_hundred_budget_table_non_vacuous_and_tight :
    OneHundredShape ∧ oneHundredExplicitFiniteKBugdetTable.length = 100 ∧
    oneHundredExplicitFiniteKBugdetTable.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredExplicitFiniteKBugdetTable, K < 900719925474) ∧
    oneHundredExplicitFiniteKBugdetTable.getLast? = some 886500180428 := by
  refine ⟨TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster.one_hundred_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  decide

theorem one_hundred_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredShape ∧
    (∀ K ∈ oneHundredExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster.one_hundred_budget_certificates_non_vacuous_and_tight cert

#print axioms merge_vals_non_vacuous_and_tight
#print axioms bal_vals_non_vacuous_and_tight
#print axioms entry_charge_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms no_75_non_vacuous_and_tight
#print axioms strict_improvement_over_seventy_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight
#print axioms user_sections_base_cases_stack_space_non_vacuous_and_tight
#print axioms one_hundred_budget_table_non_vacuous_and_tight
#print axioms one_hundred_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedExactMergeBalSeventyThreeXAndOneHundredBudgetMaster
