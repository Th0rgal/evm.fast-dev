import InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster
import InitECandidate.Solver.SelfContainedEvmStepDispatchSeventyEightXAndOneHundredTwoBudgetMaster
import InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_277: exact imported global-gas LP arithmetic, full compiler contracts
and 104 conditional finite certificates. Joint bounds retain every gas,
dirty-node and witness-byte hypothesis. Hand per-opcode charges are cost-model
assumptions, not execution-derived semantic runtime certificates. Finite
certificates remain conditional on the base semantic certificate. NoGcCall
excludes direct GC calls only; ClockOk retains the final-halt allowance and
exceptional StackAlloc may add one tick. -/
namespace InitECandidate.Solver.SelfContainedGlobalGasCoupledOneHundredEightXAndOneHundredFourBudgetMaster

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



open _root_.InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster

abbrev oneHundredFourExplicitFiniteKBugdetTable := EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster.oneHundredFourExplicitFiniteKBugdetTable
abbrev portfolio := oneHundredFourExplicitFiniteKBugdetTable
abbrev OneHundredFourShape := EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster.OneHundredFourShape

theorem fixed_vals_non_vacuous_and_tight : fixed200 = 1391298018 ∧ fixed380 = 1675717026 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.fixed_vals

theorem joint200_non_vacuous_and_tight (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    3 * cost A K B E n2 n17 m P ≤ 20720445560 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.joint200 A K B E n2 n17 m P hg h1 h2 hb he hw

theorem joint380_non_vacuous_and_tight (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    65 * cost A K B E n2 n17 m P ≤ 661898475728 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.joint380 A K B E n2 n17 m P hg h1 h2 hb he hw

theorem all_push_non_vacuous_and_tight : 3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.all_push

theorem sensitivity_non_vacuous_and_tight : 98 * 9131446538 < yukon ∧ yukon < 99 * 9131446538 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.sensitivity

theorem main200_slope_non_vacuous_and_tight : main200 = 8298113205 ∧ 108 * main200 < yukon ∧ yukon < 109 * main200 ∧
    main200 < 9000000000 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight : main380 = 11858770499 ∧ 75 * main380 < yukon ∧ yukon < 76 * main380 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main380_slope

theorem margins_non_vacuous_and_tight : yukon - 108 * main200 = 4523699334 ∧ yukon - 75 * main380 = 11312138049 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.margins

/-- Strict improvement over the previous 78x total with its thresholds pinned. -/
theorem strict_improvement_over_seventy_eight_non_vacuous_and_tight :
    main200 < 11546768760 ∧ 78 * 11546768760 < yukon ∧
    yukon < 79 * 11546768760 ∧ 11546768760 - main200 = 3248655555 := by decide

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
  SelfContainedEvmStepDispatchSeventyEightXAndOneHundredTwoBudgetMaster.user_sections_base_cases_stack_space_non_vacuous_and_tight

/-- Exactly 104 increasing finite budgets below Yukon, with pinned last entry. -/
theorem one_hundred_four_budget_table_non_vacuous_and_tight :
    OneHundredFourShape ∧ oneHundredFourExplicitFiniteKBugdetTable.length = 104 ∧
    oneHundredFourExplicitFiniteKBugdetTable.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredFourExplicitFiniteKBugdetTable, K < 900719925474) ∧
    oneHundredFourExplicitFiniteKBugdetTable.getLast? = some 892500000000 := by
  refine ⟨EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster.one_hundred_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  decide

theorem one_hundred_four_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredFourShape ∧
    (∀ K ∈ oneHundredFourExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster.one_hundred_four_budget_certificates_non_vacuous_and_tight cert

#print axioms fixed_vals_non_vacuous_and_tight
#print axioms joint200_non_vacuous_and_tight
#print axioms joint380_non_vacuous_and_tight
#print axioms all_push_non_vacuous_and_tight
#print axioms sensitivity_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms strict_improvement_over_seventy_eight_non_vacuous_and_tight
#print axioms user_sections_base_cases_stack_space_non_vacuous_and_tight
#print axioms one_hundred_four_budget_table_non_vacuous_and_tight
#print axioms one_hundred_four_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedGlobalGasCoupledOneHundredEightXAndOneHundredFourBudgetMaster
