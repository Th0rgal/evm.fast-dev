import InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
import InitECandidate.Solver.SelfContainedWithdrawalsSszLimitAndSeventyFourBudgetMaster
import InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_209: exact arithmetic for the imported conditional guest cost model,
full compiler safety and StackRemove simulations, and 76 conditional finite
certificates. The cost table assumes salted hashing, memoized witness decoding
and the withdrawal cap; it is not an execution-derived runtime certificate.
Zero clock denotes additional clock, with the exceptional allocation allowance
retained in the full simulation contract. -/
namespace InitECandidate.Solver.SelfContainedCompleteMainAllSubsystemsAndSeventySixBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

abbrev portfolio := WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.portfolio
abbrev SeventySixShape := WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.SeventySixShape

/-- Two unchecked and four checked system calls have separate 30M allowances. -/
theorem system_gas_non_vacuous_and_tight :
    2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000 := system_gas

/-- Every row of the 200M main table, including the sixteen-withdrawal cost. -/
theorem subsystem_table_non_vacuous_and_tight :
    gasEnv200 = 156088992805 ∧ witnessMpt = 38946487944 ∧
    postEvm = 4859866650 ∧ prologue = 268435424 ∧
    withdrawals16 = 2113920 ∧ balRlp = 300000000 ∧
    requests = 20000000 ∧ output = 10000 ∧
    132000 * 16 + 8 * (16 * 15) = withdrawals16 ∧
    restTerms = 5450425994 := by decide

/-- The full standard-contract total and its dominant gas-envelope row. -/
theorem main200_non_vacuous_and_tight :
    main200 = 200485906743 ∧ 100 * gasEnv200 ≥ 77 * main200 :=
  ⟨main_val, env_dominates⟩

/-- Exact 1x and 4x margins, and the first rejected integer multiplier. -/
theorem main200_slopes_non_vacuous_and_tight :
    yukon - main200 = 700234018731 ∧ 4 * main200 < yukon ∧
    yukon / 4 - main200 = 24694074625 ∧ yukon < 5 * main200 ∧
    main200 + 700234018731 = yukon ∧
    main200 + 24694074625 = yukon / 4 := by decide

/-- The rescaled gas envelope and complete total including adversarial system code. -/
theorem main380_non_vacuous_and_tight :
    gasEnv380 = 467569086329 ∧ main380 = 511966000267 :=
  ⟨env380_val, main380_val⟩

/-- Exact remaining 1x budget and rejection at 2x. -/
theorem main380_slopes_non_vacuous_and_tight :
    yukon - main380 = 388753925207 ∧ yukon < 2 * main380 ∧
    main380 + 388753925207 = yukon := by decide

/-- The cold-key endpoint is attained; its sorting/encoding cost fits the BAL row. -/
theorem bal_bound_non_vacuous_and_tight (k : Nat) (h : 2000 * k ≤ 380000000) :
    k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp ∧
    balRlp = 300000000 ∧ 2000 * 190000 = 380000000 ∧
    380000000 < 2000 * 190001 :=
  ⟨(bal_bound k h).1, (bal_bound k h).2, rfl, by decide, by decide⟩

/-- Full user-section safety after LabToTarget. -/
theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedWithdrawalsSszLimitAndSeventyFourBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Imported full StackRemove simulation contracts, including post-state relations. -/
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
  SelfContainedWithdrawalsSszLimitAndSeventyFourBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

/-- Imported full StackRemove simulation contracts, including post-state relations. -/
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
  SelfContainedWithdrawalsSszLimitAndSeventyFourBudgetMaster.stack_space_clock_non_vacuous_and_tight

/-- Exactly 76 strictly increasing budgets below 900719925474. -/
theorem seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SeventySixShape :=
  WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

/-- Complete main arithmetic, full user safety and the conditional finite portfolio. -/
theorem complete_main_all_subsystems_and_seventy_six_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    main200 = 200485906743 ∧ main380 = 511966000267 ∧
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
      NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    SeventySixShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨main200_non_vacuous_and_tight.1, main380_non_vacuous_and_tight.2,
   panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight,
   WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.seventy_six_budget_certificates_non_vacuous_and_tight cert⟩

#print axioms system_gas_non_vacuous_and_tight
#print axioms subsystem_table_non_vacuous_and_tight
#print axioms main200_non_vacuous_and_tight
#print axioms main200_slopes_non_vacuous_and_tight
#print axioms main380_non_vacuous_and_tight
#print axioms main380_slopes_non_vacuous_and_tight
#print axioms bal_bound_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms complete_main_all_subsystems_and_seventy_six_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedCompleteMainAllSubsystemsAndSeventySixBudgetMaster
