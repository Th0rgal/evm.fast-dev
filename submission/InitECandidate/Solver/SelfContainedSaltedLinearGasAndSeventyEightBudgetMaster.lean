import InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster
import InitECandidate.Solver.SelfContainedCompleteMainAllSubsystemsAndSeventySixBudgetMaster
import InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_213: exact arithmetic for the imported linear salted-table cost model,
full self-contained compiler simulation contracts and 78 conditional finite
certificates. The linear cost model assumes probe runs bounded by eight;
salting alone does not establish that worst-case bound. These arithmetic
estimates do not establish semantic runtime certificates. The finite
certificates remain conditional on the base semantic certificate. Clock means
additional clock; exceptional StackAlloc retains its one-tick allowance. -/
namespace InitECandidate.Solver.SelfContainedSaltedLinearGasAndSeventyEightBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster
open _root_.InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

abbrev portfolio := CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.portfolio
abbrev SeventyEightShape := CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.SeventyEightShape

/-- Per-unit coverage, quadratic-to-linear substitution and both gas envelopes. -/
theorem per_unit_quad_vs_lin_salted_env_non_vacuous_and_tight :
    (60 * 8 * 2 ≤ 1000) ∧
    (2000000 * 2000000 / 40 = 100000000000 ∧ saltedTable 2000000 = 2000000000 ∧
     3800000 * 3800000 / 40 = 361000000000 ∧ saltedTable 3800000 = 3800000000) ∧
    (156088992805 - 100000000000 + 2000000000 = 58088992805 ∧
     467569086329 - 361000000000 + 3800000000 = 110369086329) :=
  ⟨per_unit, quad_vs_lin, salted_env⟩

/-- Exact totals after the linear replacement at both gas budgets. -/
theorem salted200_salted380_val_non_vacuous_and_tight :
    salted200 = 102485906743 ∧ salted380 = 154766000267 :=
  ⟨salted200_val, salted380_val⟩

/-- Last passing and first failing integer multipliers, with exact margins. -/
theorem slope200_slope380_non_vacuous_and_tight :
    (8 * salted200 < yukon ∧ yukon - 8 * salted200 = 80832671530 ∧
      yukon < 9 * salted200) ∧
    (5 * salted380 < yukon ∧ yukon - 5 * salted380 = 126889924139 ∧
      yukon < 6 * salted380) := by
  rw [salted200_val, salted380_val]
  exact ⟨slope200, slope380⟩

/-- Exact savings and the adjacent accepted/rejected per-unit charge thresholds. -/
theorem salt_gain_per_unit_slack_non_vacuous_and_tight :
    (100000000000 - 2000000000 = 98000000000 ∧
     361000000000 - 3800000000 = 357200000000) ∧
    (8 * (200485906743 - 100000000000 + 6052 * 2000000) < yukon ∧
     yukon < 8 * (200485906743 - 100000000000 + 6053 * 2000000) ∧
     5 * (511966000267 - 361000000000 + 7678 * 3800000) < yukon ∧
     yukon < 5 * (511966000267 - 361000000000 + 7679 * 3800000)) :=
  ⟨salt_gain, per_unit_slack⟩

theorem main_subsystem_table_non_vacuous_and_tight :
    gasEnv200 = 156088992805 ∧ witnessMpt = 38946487944 ∧
    postEvm = 4859866650 ∧ prologue = 268435424 ∧
    withdrawals16 = 2113920 ∧ balRlp = 300000000 ∧ requests = 20000000 ∧
    output = 10000 ∧ restTerms = 5450425994 ∧
    main200 = gasEnv200 + witnessMpt + postEvm + prologue + withdrawals16 +
      balRlp + requests + output :=
  CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.main_subsystem_table_non_vacuous_and_tight

theorem system_gas_non_vacuous_and_tight :
    2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000 :=
  CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.system_gas_non_vacuous_and_tight

theorem bal_bound_non_vacuous_and_tight (k : Nat) (h : 2000 * k ≤ 380000000) :
    k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp ∧ balRlp = 300000000 :=
  CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.bal_bound_non_vacuous_and_tight k h

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedCompleteMainAllSubsystemsAndSeventySixBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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
  SelfContainedCompleteMainAllSubsystemsAndSeventySixBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  SelfContainedCompleteMainAllSubsystemsAndSeventySixBudgetMaster.stack_space_clock_non_vacuous_and_tight

theorem seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SeventyEightShape :=
  CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

theorem seventy_eight_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventyEightShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.seventy_eight_budget_certificates_non_vacuous_and_tight cert

#print axioms per_unit_quad_vs_lin_salted_env_non_vacuous_and_tight
#print axioms salted200_salted380_val_non_vacuous_and_tight
#print axioms slope200_slope380_non_vacuous_and_tight
#print axioms salt_gain_per_unit_slack_non_vacuous_and_tight
#print axioms main_subsystem_table_non_vacuous_and_tight
#print axioms system_gas_non_vacuous_and_tight
#print axioms bal_bound_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms seventy_eight_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedSaltedLinearGasAndSeventyEightBudgetMaster
