import InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit
import InitECandidate.Solver.WithdrawalsSszLimitAndSeventyTwoBudgetBridge
import InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact closure arithmetic for the imported guest cost model. Semantic finite
certificates remain conditional on the base certificate. Zero clock denotes
additional clock; exceptional StackAlloc may require one tick. -/
namespace InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit
open _root_.InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound (nwdMax r1 r4)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

abbrev Previous := SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318285, 880629318286]
def SeventySixShape : Prop :=
  portfolio.length = 76 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 74 = Previous ∧
  portfolio.drop 74 = [880629318285, 880629318286] ∧
  portfolio.getLast? = some 880629318286 ∧ yukon = 900719925474

theorem ssz_no_cap_non_vacuous_and_tight :
    nwdMax ≤ 9223372036854775807 ∧ 16 < nwdMax := ssz_no_cap

theorem linear_val_non_vacuous_and_tight :
    132000 * nwdMax = 44291808000 := linear_val

theorem close_1x_salted_non_vacuous_and_tight :
    wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707 := close_1x_salted

theorem unsalted_thresholds_non_vacuous_and_tight :
    (wdTicks 6 323652 ≤ r1 ∧ r1 < wdTicks 6 323653) ∧
    (wdTicks 8 281528 ≤ r1 ∧ r1 < wdTicks 8 281529) := ⟨nmax_f6, nmax_f8⟩

theorem nmax_4x_non_vacuous_and_tight :
    wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517 := nmax_4x

theorem spec_cap_closes_non_vacuous_and_tight (n : Nat) (h : n ≤ 16) :
    wdTicks 8 n ≤ wdTicks 8 16 ∧ wdTicks 8 16 ≤ r4 ∧
    r4 - wdTicks 8 16 = 25014084625 := spec_cap_closes n h

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  WithdrawalsSszLimitAndSeventyTwoBudgetBridge.panToTarget_user_sections_seventy_two_bridge_non_vacuous_and_tight

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
  SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.stack_space_clock_non_vacuous_and_tight

/-- The previous 74 budgets followed by two larger admissible budgets. -/
theorem seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SeventySixShape := by
  unfold SeventySixShape
  decide

/-- Finite semantic certificates, conditional on the base semantic certificate. -/
theorem seventy_six_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventySixShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

/-- Combined SSZ diagnostic, closure, user-section safety and conditional portfolio. -/
theorem withdrawals_ssz_limit_main_closure_and_seventy_six_budget_master_non_vacuous_and_tight
    (n : Nat) (hn : n ≤ 16) (cert : CertificateAt 1212035192) :
    (nwdMax ≤ 9223372036854775807 ∧ 16 < nwdMax) ∧
    (132000 * nwdMax = 44291808000) ∧
    (wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707) ∧
    ((wdTicks 6 323652 ≤ r1 ∧ r1 < wdTicks 6 323653) ∧
      (wdTicks 8 281528 ≤ r1 ∧ r1 < wdTicks 8 281529)) ∧
    (wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517) ∧
    (wdTicks 8 n ≤ wdTicks 8 16 ∧ wdTicks 8 16 ≤ r4 ∧
      r4 - wdTicks 8 16 = 25014084625) ∧
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
      NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (SeventySixShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨ssz_no_cap_non_vacuous_and_tight, linear_val_non_vacuous_and_tight,
   close_1x_salted_non_vacuous_and_tight, unsalted_thresholds_non_vacuous_and_tight,
   nmax_4x_non_vacuous_and_tight, spec_cap_closes_non_vacuous_and_tight n hn,
   panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight,
   seventy_six_budget_certificates_non_vacuous_and_tight cert⟩

#print axioms ssz_no_cap_non_vacuous_and_tight
#print axioms linear_val_non_vacuous_and_tight
#print axioms close_1x_salted_non_vacuous_and_tight
#print axioms unsalted_thresholds_non_vacuous_and_tight
#print axioms nmax_4x_non_vacuous_and_tight
#print axioms spec_cap_closes_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms seventy_six_budget_certificates_non_vacuous_and_tight
#print axioms withdrawals_ssz_limit_main_closure_and_seventy_six_budget_master_non_vacuous_and_tight

end InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster
