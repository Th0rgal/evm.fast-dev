import InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit
import InitECandidate.Solver.SelfContainedSszHtrHeadersAndSeventyBudgetMaster
import InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_203: withdrawal SSZ diagnostics and exact arithmetic under the imported
conservative cost estimates, full compiler safety and StackRemove simulations,
and 74 conditional finite certificates. The arithmetic envelopes are not
execution-derived runtime certificates. Zero clock means zero additional clock;
exceptional allocation retains its one-tick allowance. -/
namespace InitECandidate.Solver.SelfContainedWithdrawalsSszLimitAndSeventyFourBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev nwdMax := GuestSszHtrHeadersAndCompleteMainBound.nwdMax
abbrev r1 := GuestSszHtrHeadersAndCompleteMainBound.r1
abbrev r4 := GuestSszHtrHeadersAndCompleteMainBound.r4
abbrev sszLim := GuestWithdrawalsSszLimitAndMainClosureAudit.sszLim
abbrev wdTicks := GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks
abbrev portfolio := SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.portfolio
abbrev SeventyFourShape := SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.SeventyFourShape

/-- The SSZ decoder limit admits the RLP withdrawal maximum, well above sixteen. -/
theorem ssz_no_cap_non_vacuous_and_tight :
    nwdMax = 335544 ∧ sszLim = 9223372036854775807 ∧
    nwdMax ≤ sszLim ∧ 16 < nwdMax :=
  ⟨rfl, rfl, GuestWithdrawalsSszLimitAndMainClosureAudit.ssz_no_cap⟩

/-- Exact linear cost at the maximal withdrawal count. -/
theorem linear_val_non_vacuous_and_tight :
    132000 * nwdMax = 44291808000 :=
  GuestWithdrawalsSszLimitAndMainClosureAudit.linear_val

/-- Salted closure, with the exact residual accounted for without subtraction. -/
theorem close_1x_salted_non_vacuous_and_tight :
    wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707 ∧
    wdTicks 0 nwdMax + 626933565707 = r1 := by decide

/-- Six unsalted finds: the last accepted count and its first rejected successor. -/
theorem nmax_f6_non_vacuous_and_tight :
    wdTicks 6 323652 ≤ r1 ∧ r1 < wdTicks 6 323653 ∧
    r1 < wdTicks 6 nwdMax :=
  ⟨GuestWithdrawalsSszLimitAndMainClosureAudit.nmax_f6.1,
   GuestWithdrawalsSszLimitAndMainClosureAudit.nmax_f6.2,
   GuestWithdrawalsSszLimitAndMainClosureAudit.fail_1x_unsalted⟩

/-- Eight unsalted finds: the last accepted count and first rejected successor. -/
theorem nmax_f8_non_vacuous_and_tight :
    wdTicks 8 281528 ≤ r1 ∧ r1 < wdTicks 8 281529 :=
  GuestWithdrawalsSszLimitAndMainClosureAudit.nmax_f8

/-- The exact salted linear interval at 4x and failure at the RLP maximum. -/
theorem nmax_4x_non_vacuous_and_tight :
    (∀ n : Nat, wdTicks 0 n ≤ r4 ↔ n ≤ 189516) ∧
    wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517 ∧
    r4 < wdTicks 0 nwdMax := by
  refine ⟨?_, GuestWithdrawalsSszLimitAndMainClosureAudit.nmax_4x.1,
    GuestWithdrawalsSszLimitAndMainClosureAudit.nmax_4x.2,
    GuestWithdrawalsSszLimitAndMainClosureAudit.fail_4x⟩
  intro n
  change 2 * 134217712 + 132000 * n + 0 * (n * (n - 1)) ≤ 25284633969 ↔ n ≤ 189516
  omega

/-- Every spec-capped count closes even with eight unsalted finds; exact margin. -/
theorem spec_cap_closes_non_vacuous_and_tight (n : Nat) (h : n ≤ 16) :
    wdTicks 8 n ≤ wdTicks 8 16 ∧ wdTicks 8 16 ≤ r4 ∧
    r4 - wdTicks 8 16 = 25014084625 ∧
    wdTicks 8 16 + 25014084625 = r4 :=
  ⟨(GuestWithdrawalsSszLimitAndMainClosureAudit.spec_cap_closes n h).1,
   (GuestWithdrawalsSszLimitAndMainClosureAudit.spec_cap_closes n h).2.1,
   (GuestWithdrawalsSszLimitAndMainClosureAudit.spec_cap_closes n h).2.2, by decide⟩

/-- Full user-section safety after LabToTarget. -/
theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedSszHtrHeadersAndSeventyBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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
  SelfContainedSszHtrHeadersAndSeventyBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  SelfContainedSszHtrHeadersAndSeventyBudgetMaster.stack_space_clock_non_vacuous_and_tight

/-- Exactly 74 strictly increasing budgets below the finite Yukon ceiling. -/
theorem seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SeventyFourShape :=
  SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

/-- Full user safety and all finite certificates, conditional on the semantic base. -/
theorem seventy_four_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧ SeventyFourShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight.2,
   SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.seventy_four_budget_certificates_non_vacuous_and_tight cert⟩

#print axioms ssz_no_cap_non_vacuous_and_tight
#print axioms linear_val_non_vacuous_and_tight
#print axioms close_1x_salted_non_vacuous_and_tight
#print axioms nmax_f6_non_vacuous_and_tight
#print axioms nmax_f8_non_vacuous_and_tight
#print axioms nmax_4x_non_vacuous_and_tight
#print axioms spec_cap_closes_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms seventy_four_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedWithdrawalsSszLimitAndSeventyFourBudgetMaster
