import InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit
import InitECandidate.Solver.PrologueSecp256k1AndSeventyBudgetCampaignBridge
import InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.WithdrawalsSszLimitAndSeventyFourBudgetCampaignBridge

open InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit
open InitECandidate.Solver.PrologueSecp256k1AndSeventyBudgetCampaignBridge
open InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem withdrawals_ssz_no_cap_and_linear_val_non_vacuous_and_tight :
    (nwdMax ≤ sszLim ∧ 16 < nwdMax) ∧
    (2 ^ 4 = 16 ∧ 335544 / 16 = 20971) ∧
    (132000 * nwdMax = 44291808000 ∧ nwdMax = 335544) ∧
    ((16 * 44 : Nat) = 704 ∧ 704 < 8388608) :=
  ⟨ssz_no_cap, spec_vs_guest, ⟨linear_val, rfl⟩, fix_shape⟩

theorem withdrawals_close_1x_salted_and_unsalted_failure_non_vacuous_and_tight :
    (wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707) ∧
    r1 < wdTicks 6 nwdMax ∧
    r4 < wdTicks 0 nwdMax :=
  ⟨close_1x_salted, fail_1x_unsalted, fail_4x⟩

theorem withdrawals_unsalted_1x_thresholds_f6_and_f8_non_vacuous_and_tight :
    (wdTicks 6 323652 ≤ r1 ∧ r1 < wdTicks 6 323653) ∧
    (wdTicks 8 281528 ≤ r1 ∧ r1 < wdTicks 8 281529) :=
  ⟨nmax_f6, nmax_f8⟩

theorem withdrawals_salted_4x_threshold_and_spec_cap_closure_non_vacuous_and_tight :
    (wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517) ∧
    (∀ n : Nat, n ≤ 16 →
      wdTicks 8 n ≤ wdTicks 8 16 ∧
      wdTicks 8 16 ≤ r4 ∧
      r4 - wdTicks 8 16 = 25014084625) :=
  ⟨nmax_4x, spec_cap_closes⟩

theorem stack_remove_skip_and_tick_zero_clock_wd_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool) :
    (∀ (_hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.skip : HolProg width) pointer),
      ∃ postTarget : StackSemStateFiniteExact width C F,
        StackSemEvaluate.evaluate (comp jump bounds pointer .skip, target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ (_hypothesis : StackSemEvaluate.evaluate (.tick, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.tick : HolProg width) pointer),
      ∃ postTarget : StackSemStateFiniteExact width C F,
        StackSemEvaluate.evaluate (comp jump bounds pointer .tick, target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  stack_remove_skip_and_tick_zero_clock_campaign_non_vacuous_and_tight source result postSource
    target pointer bounds jump

theorem stack_remove_inst_zero_clock_wd_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (instruction : HolInst width)
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.inst instruction) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.inst instruction),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) :=
  stack_remove_inst_zero_clock_campaign_non_vacuous_and_tight source result postSource target
    pointer bounds jump instruction hypothesis

theorem stack_remove_load_and_store_zero_clock_wd_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool) :
    (∀ (_hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.stackLoad register count : HolProg width) pointer),
      ∃ postTarget,
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoad register count),
          target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ (_hypothesis : StackSemEvaluate.evaluate (.stackStore register count, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.stackStore register count : HolProg width) pointer),
      ∃ postTarget,
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStore register count),
          target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  stack_remove_load_and_store_zero_clock_campaign_non_vacuous_and_tight source result postSource
    target register count pointer bounds jump

theorem stack_remove_free_and_alloc_zero_clock_wd_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool) :
    (∀ (_hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound ((.stackFree count) : HolProg width) pointer),
      ∃ (postTarget : StackSemStateFiniteExact width C F),
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count),
          target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ (_hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound ((.stackAlloc count) : HolProg width) pointer),
      ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
        clock ≤ 1 ∧ (result = none → clock = 0) ∧
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
          {target with clock := clock + target.clock}) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  stack_remove_free_and_alloc_zero_clock_campaign_non_vacuous_and_tight source result postSource
    target count pointer bounds jump

theorem seventy_four_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventyFourShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(seventy_four_budget_certificates_non_vacuous_and_tight cert).1,
   rfl,
   (seventy_four_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem withdrawals_ssz_limit_and_seventy_four_budget_campaign_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (nwdMax ≤ sszLim ∧ 16 < nwdMax ∧ 132000 * nwdMax = 44291808000 ∧
      wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707) ∧
    (wdTicks 6 323652 ≤ r1 ∧ r1 < wdTicks 6 323653 ∧
      wdTicks 8 281528 ≤ r1 ∧ r1 < wdTicks 8 281529 ∧
      wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517) ∧
    (∀ n : Nat, n ≤ 16 →
      wdTicks 8 n ≤ wdTicks 8 16 ∧ wdTicks 8 16 ≤ r4 ∧ r4 - wdTicks 8 16 = 25014084625) ∧
    (SeventyFourShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨ssz_no_cap.1,
    ssz_no_cap.2,
    linear_val,
    close_1x_salted.1,
    close_1x_salted.2⟩,
   ⟨nmax_f6.1,
    nmax_f6.2,
    nmax_f8.1,
    nmax_f8.2,
    nmax_4x.1,
    nmax_4x.2⟩,
   spec_cap_closes,
   ⟨(seventy_four_budget_certificates_non_vacuous_and_tight cert).1,
    rfl⟩,
   (seventy_four_budget_certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.WithdrawalsSszLimitAndSeventyFourBudgetCampaignBridge
