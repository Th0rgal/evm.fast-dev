import InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
import InitECandidate.Solver.SelfContainedSszHtrHeadersAndSeventyFourBudgetBridge
import InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact synthesis of the imported conservative guest cost model, conditional on
salted hashing, memoized witness decoding and the withdrawal spec cap. Arithmetic
cost estimates do not themselves establish a semantic runtime certificate.
Finite certificates are conditional on the base certificate. Zero clock means
zero additional clock; exceptional StackAlloc can require one tick. -/
namespace InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

abbrev Previous := WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318287, 880629318288]
def SeventyEightShape : Prop :=
  portfolio.length = 78 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 76 = Previous ∧
  portfolio.drop 76 = [880629318287, 880629318288] ∧
  portfolio.getLast? = some 880629318288 ∧ yukon = 900719925474

/-- All subsystem rows, and their exact aggregate. -/
theorem main_subsystem_table_non_vacuous_and_tight :
    gasEnv200 = 156088992805 ∧ witnessMpt = 38946487944 ∧
    postEvm = 4859866650 ∧ prologue = 268435424 ∧
    withdrawals16 = 2113920 ∧ balRlp = 300000000 ∧ requests = 20000000 ∧
    output = 10000 ∧ restTerms = 5450425994 ∧
    main200 = gasEnv200 + witnessMpt + postEvm + prologue + withdrawals16 +
      balRlp + requests + output := by decide

/-- Six system calls add 180M gas outside the 200M user budget. -/
theorem system_gas_non_vacuous_and_tight :
    2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000 := system_gas

 theorem main200_non_vacuous_and_tight :
    main200 = 200485906743 := main_val

 theorem main200_margins_non_vacuous_and_tight :
    yukon - main200 = 700234018731 ∧ 4 * main200 < yukon ∧
    yukon / 4 - main200 = 24694074625 ∧ yukon < 5 * main200 := main_slopes

 theorem main380_non_vacuous_and_tight :
    gasEnv380 = 467569086329 ∧ main380 = 511966000267 ∧
    main380 = gasEnv380 + witnessMpt + restTerms :=
  ⟨env380_val, main380_val, rfl⟩

 theorem main380_margins_non_vacuous_and_tight :
    main380 < yukon ∧ yukon - main380 = 388753925207 ∧ yukon < 2 * main380 := by
  exact ⟨by decide, main380_slopes⟩

/-- Cold keys and the conservative BAL sorting/encoding allowance. -/
theorem bal_bound_non_vacuous_and_tight (k : Nat) (h : 2000 * k ≤ 380000000) :
    k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp ∧ balRlp = 300000000 :=
  ⟨(bal_bound k h).1, (bal_bound k h).2, rfl⟩

 theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedSszHtrHeadersAndSeventyFourBudgetBridge.panToTarget_user_sections_seventy_four_bridge_non_vacuous_and_tight

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
  WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.stack_space_clock_non_vacuous_and_tight

/-- Exactly 78 increasing budgets, with both extension endpoints pinned. -/
theorem seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SeventyEightShape := by
  unfold SeventyEightShape
  decide

/-- Every budget yields a finite certificate conditional on the base certificate. -/
theorem seventy_eight_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventyEightShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms main_subsystem_table_non_vacuous_and_tight
#print axioms system_gas_non_vacuous_and_tight
#print axioms main200_non_vacuous_and_tight
#print axioms main200_margins_non_vacuous_and_tight
#print axioms main380_non_vacuous_and_tight
#print axioms main380_margins_non_vacuous_and_tight
#print axioms bal_bound_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms seventy_eight_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster
