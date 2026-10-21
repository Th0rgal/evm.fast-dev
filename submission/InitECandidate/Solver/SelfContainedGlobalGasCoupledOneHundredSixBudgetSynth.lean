import InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster
import InitECandidate.Solver.SelfContainedGlobalGasCoupledOneHundredEightXAndOneHundredFourBudgetMaster
import InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_284: self-contained global-gas LP arithmetic, full compiler contracts
and 106 conditional finite certificates. Joint bounds retain every gas,
dirty-node and witness-byte hypothesis. Hand per-opcode charges are cost-model
assumptions, not execution-derived semantic runtime certificates. Finite
certificates remain conditional on the base semantic certificate. NoGcCall
excludes direct GC calls only; ClockOk retains the final-halt allowance and
exceptional StackAlloc may add one tick. -/
namespace InitECandidate.Solver.SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth

open InitECandidate.Solver
open _root_.InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural (NoGcCall NoTailHandler)
open Flapjack.Pancake.PanLang
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev oneHundredFourExplicitFiniteKBugdetTable :=
  EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster.oneHundredFourExplicitFiniteKBugdetTable

abbrev oneHundredSixExplicitFiniteKBugdetTable :=
  GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster.oneHundredSixExplicitFiniteKBugdetTable

abbrev portfolio := oneHundredSixExplicitFiniteKBugdetTable

abbrev OneHundredSixShape :=
  GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster.OneHundredSixShape

/-- 1. Fixed rows and all-PUSH31 extreme bound. -/
theorem fixed_vals_and_all_push_non_vacuous_and_tight :
    (fixed200 = 1391298018 ∧ fixed380 = 1675717026) ∧
    3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560 :=
  ⟨GuestGlobalGasCoupledEvmAndSubNineBillionMaster.fixed_vals,
   GuestGlobalGasCoupledEvmAndSubNineBillionMaster.all_push⟩

/-- 2. Global joint bound at 200M gas. -/
theorem joint200_non_vacuous_and_tight (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    3 * cost A K B E n2 n17 m P ≤ 20720445560 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.joint200 A K B E n2 n17 m P hg h1 h2 hb he hw

/-- 3. Global joint bound at 380M gas. -/
theorem joint380_non_vacuous_and_tight (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    65 * cost A K B E n2 n17 m P ≤ 661898475728 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.joint380 A K B E n2 n17 m P hg h1 h2 hb he hw

/-- 4. Sensitivity and strict improvement over the previous 78x/52x totals. -/
theorem sensitivity_and_strict_improvement_over_seventy_eight_non_vacuous_and_tight :
    (98 * 9131446538 < yukon ∧ yukon < 99 * 9131446538) ∧
    (main200 < 11546768760 ∧ 78 * 11546768760 < yukon ∧
      yukon < 79 * 11546768760 ∧ 11546768760 - main200 = 3248655555) ∧
    (main380 < 17251948659 ∧ 52 * 17251948659 < yukon ∧
      yukon < 53 * 17251948659 ∧ 17251948659 - main380 = 5393178160) := by
  decide

/-- 5. 200M main slope (108x passes, 109x fails, sub-9B). -/
theorem main200_slope_non_vacuous_and_tight :
    main200 = 8298113205 ∧ 108 * main200 < yukon ∧ yukon < 109 * main200 ∧
    main200 < 9000000000 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200_slope

/-- 6. 380M main slope (75x passes, 76x fails). -/
theorem main380_slope_non_vacuous_and_tight :
    main380 = 11858770499 ∧ 75 * main380 < yukon ∧ yukon < 76 * main380 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main380_slope

/-- 7. Exact margins below Yukon at 108x (200M) and 75x (380M). -/
theorem margins_non_vacuous_and_tight :
    yukon - 108 * main200 = 4523699334 ∧ yukon - 75 * main380 = 11312138049 :=
  GuestGlobalGasCoupledEvmAndSubNineBillionMaster.margins

/-- 8. User sections, base cases and stack-space simulation contracts. -/
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
  SelfContainedGlobalGasCoupledOneHundredEightXAndOneHundredFourBudgetMaster.user_sections_base_cases_stack_space_non_vacuous_and_tight

/-- 9. Exactly 106 increasing finite budgets below Yukon, with pinned last entry and margin. -/
theorem one_hundred_six_budget_table_non_vacuous_and_tight :
    OneHundredSixShape ∧ oneHundredSixExplicitFiniteKBugdetTable.length = 106 ∧
    oneHundredSixExplicitFiniteKBugdetTable.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable, K < 900719925474) ∧
    oneHundredFourExplicitFiniteKBugdetTable.getLast? = some 892500000000 ∧
    oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 ∧
    yukon - 894500000000 = 6219925474 := by
  refine ⟨GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster.one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  decide

/-- 10. Conditional finite certificates across all 106 budgets. -/
theorem one_hundred_six_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredSixShape ∧
    (∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster.one_hundred_six_budget_certificates_non_vacuous_and_tight cert

#print axioms fixed_vals_and_all_push_non_vacuous_and_tight
#print axioms joint200_non_vacuous_and_tight
#print axioms joint380_non_vacuous_and_tight
#print axioms sensitivity_and_strict_improvement_over_seventy_eight_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms user_sections_base_cases_stack_space_non_vacuous_and_tight
#print axioms one_hundred_six_budget_table_non_vacuous_and_tight
#print axioms one_hundred_six_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth
