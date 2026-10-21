import InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
import InitECandidate.Solver.WithdrawalsSszLimitAndSeventyFourBudgetCampaignBridge
import InitECandidate.Solver.SelfContainedCompleteMainAllSubsystemsAndSeventySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.StackRemoveNoStoreConstsAndSeventySixBudgetCampaignBridge

open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake
open InitECandidate.Solver.WithdrawalsSszLimitAndSeventyFourBudgetCampaignBridge
open InitECandidate.Solver.SelfContainedCompleteMainAllSubsystemsAndSeventySixBudgetMaster
open _root_.InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
open _root_.InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound (nwdMax r1 r4)
open _root_.InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit (sszLim wdTicks)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open Flapjack
open Flapjack.Compiler
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

theorem stackNoSt_and_clockOk_witnesses_non_vacuous_and_tight
    {width : Nat} [NeZero width] (a b : Nat) (c : Option Nat) (w : WordLocW width) :
    StackNoSt (.storeConsts a b c : HolProg width) = false ∧
    StackNoSt (.seq .skip .skip : HolProg width) = true ∧
    ClockOk 1 (some (.halt w)) ∧
    ¬ ClockOk (width := width) 1 none ∧
    ¬ ClockOk 2 (some (.halt w)) :=
  ⟨stackNoSt_rejects_storeConsts a b c,
   stackNoSt_accepts_skip,
   clockOk_halt_one w,
   clockOk_rejects_one_none,
   clockOk_rejects_two_halt w⟩

theorem panToStackAlloc_bodies_StackNoSt_and_rejects_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat)
    (a b : Nat) (c : Option Nat) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 = true) ∧
    StackNoSt (.storeConsts a b c : HolProg width) = false ∧
    StackNoSt (.seq .skip .skip : HolProg width) = true :=
  ⟨panToStackAlloc_bodies_StackNoSt arch prog wc ac perf info,
   stackNoSt_rejects_storeConsts a b c,
   stackNoSt_accepts_skip⟩

theorem panToStackRemove_body_zeroExtraClock_and_clockOk_tight_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat)
    (w : WordLocW width) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
        CodeNoSt source →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 pointer →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp jump bounds pointer
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget)) ∧
    ¬ ClockOk (width := width) 1 none ∧
    ¬ ClockOk 2 (some (.halt w)) :=
  ⟨panToStackRemove_body_zeroExtraClock arch prog wc ac perf info,
   clockOk_rejects_one_none,
   clockOk_rejects_two_halt w⟩

theorem withdrawals_ssz_and_salted_unsalted_thresholds_campaign_non_vacuous_and_tight :
    ((nwdMax ≤ sszLim ∧ 16 < nwdMax) ∧
      (2 ^ 4 = 16 ∧ 335544 / 16 = 20971) ∧
      (132000 * nwdMax = 44291808000 ∧ nwdMax = 335544) ∧
      ((16 * 44 : Nat) = 704 ∧ 704 < 8388608)) ∧
    ((wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707) ∧
      r1 < wdTicks 6 nwdMax ∧
      r4 < wdTicks 0 nwdMax) ∧
    ((wdTicks 6 323652 ≤ r1 ∧ r1 < wdTicks 6 323653) ∧
      (wdTicks 8 281528 ≤ r1 ∧ r1 < wdTicks 8 281529)) :=
  ⟨withdrawals_ssz_no_cap_and_linear_val_non_vacuous_and_tight,
   withdrawals_close_1x_salted_and_unsalted_failure_non_vacuous_and_tight,
   withdrawals_unsalted_1x_thresholds_f6_and_f8_non_vacuous_and_tight⟩

theorem withdrawals_4x_threshold_and_spec_cap_campaign_non_vacuous_and_tight :
    (wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517) ∧
    (∀ n : Nat, n ≤ 16 →
      wdTicks 8 n ≤ wdTicks 8 16 ∧
      wdTicks 8 16 ≤ r4 ∧
      r4 - wdTicks 8 16 = 25014084625) :=
  withdrawals_salted_4x_threshold_and_spec_cap_closure_non_vacuous_and_tight

theorem complete_main_subsystems_and_200m_bounds_non_vacuous_and_tight :
    (2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000) ∧
    (gasEnv200 = 156088992805 ∧ witnessMpt = 38946487944 ∧
      postEvm = 4859866650 ∧ prologue = 268435424 ∧
      withdrawals16 = 2113920 ∧ balRlp = 300000000 ∧
      requests = 20000000 ∧ output = 10000 ∧
      132000 * 16 + 8 * (16 * 15) = withdrawals16 ∧
      restTerms = 5450425994) ∧
    (main200 = 200485906743 ∧ 100 * gasEnv200 ≥ 77 * main200) ∧
    (yukon - main200 = 700234018731 ∧ 4 * main200 < yukon ∧
      yukon / 4 - main200 = 24694074625 ∧ yukon < 5 * main200 ∧
      main200 + 700234018731 = yukon ∧
      main200 + 24694074625 = yukon / 4) :=
  ⟨system_gas_non_vacuous_and_tight,
   subsystem_table_non_vacuous_and_tight,
   main200_non_vacuous_and_tight,
   main200_slopes_non_vacuous_and_tight⟩

theorem complete_main_380m_and_bal_bound_non_vacuous_and_tight :
    (gasEnv380 = 467569086329 ∧ main380 = 511966000267) ∧
    (yukon - main380 = 388753925207 ∧ yukon < 2 * main380 ∧
      main380 + 388753925207 = yukon) ∧
    (∀ k : Nat, 2000 * k ≤ 380000000 →
      k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp ∧
      balRlp = 300000000 ∧ 2000 * 190000 = 380000000 ∧
      380000000 < 2000 * 190001) :=
  ⟨main380_non_vacuous_and_tight,
   main380_slopes_non_vacuous_and_tight,
   bal_bound_non_vacuous_and_tight⟩

theorem stack_remove_base_and_space_clock_campaign_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool) :
    ((∀ (_hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
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
         | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ (_hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
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
         | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ (_hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
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
         | _ => stateRelHOL jump bounds pointer postSource postTarget))) :=
  ⟨stack_remove_skip_and_tick_zero_clock_wd_bridge_non_vacuous_and_tight source result postSource
     target pointer bounds jump,
   stack_remove_load_and_store_zero_clock_wd_bridge_non_vacuous_and_tight source result postSource
     target register count pointer bounds jump,
   stack_remove_free_and_alloc_zero_clock_wd_bridge_non_vacuous_and_tight source result postSource
     target count pointer bounds jump⟩

theorem seventy_six_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventySixShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ SelfContainedCompleteMainAllSubsystemsAndSeventySixBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   rfl,
   (complete_main_all_subsystems_and_seventy_six_budget_certificates_non_vacuous_and_tight cert).2.2.2.2⟩

theorem stack_remove_no_store_consts_and_seventy_six_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (StackNoSt (.storeConsts a b c : HolProg width) = false ∧
      ¬ ClockOk (width := width) 1 none ∧
      ¬ ClockOk 2 (some (.halt w))) ∧
    (nwdMax ≤ sszLim ∧ 16 < nwdMax ∧ 132000 * nwdMax = 44291808000 ∧
      wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707 ∧
      wdTicks 8 16 ≤ r4 ∧ r4 - wdTicks 8 16 = 25014084625) ∧
    (main200 = 200485906743 ∧ main380 = 511966000267 ∧
      4 * main200 < yukon ∧ yukon < 5 * main200 ∧
      yukon - main380 = 388753925207 ∧ yukon < 2 * main380) ∧
    (SeventySixShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ SelfContainedCompleteMainAllSubsystemsAndSeventySixBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(withdrawals_ssz_limit_and_seventy_four_budget_campaign_bridge_non_vacuous_and_tight cert).1.1,
    (withdrawals_ssz_limit_and_seventy_four_budget_campaign_bridge_non_vacuous_and_tight cert).1.2.1,
    (withdrawals_ssz_limit_and_seventy_four_budget_campaign_bridge_non_vacuous_and_tight cert).1.2.2.1,
    (withdrawals_ssz_limit_and_seventy_four_budget_campaign_bridge_non_vacuous_and_tight cert).1.2.2.2.1,
    (withdrawals_ssz_limit_and_seventy_four_budget_campaign_bridge_non_vacuous_and_tight cert).1.2.2.2.2,
    ((withdrawals_ssz_limit_and_seventy_four_budget_campaign_bridge_non_vacuous_and_tight cert).2.2.1 16 (Nat.le_refl 16)).2.1,
    ((withdrawals_ssz_limit_and_seventy_four_budget_campaign_bridge_non_vacuous_and_tight cert).2.2.1 16 (Nat.le_refl 16)).2.2⟩,
   ⟨main200_non_vacuous_and_tight.1,
    main380_non_vacuous_and_tight.2,
    main200_slopes_non_vacuous_and_tight.2.1,
    main200_slopes_non_vacuous_and_tight.2.2.2.1,
    main380_slopes_non_vacuous_and_tight.1,
    main380_slopes_non_vacuous_and_tight.2.1⟩,
   ⟨seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
    rfl⟩,
   (complete_main_all_subsystems_and_seventy_six_budget_certificates_non_vacuous_and_tight cert).2.2.2.2⟩

end InitECandidate.Solver.StackRemoveNoStoreConstsAndSeventySixBudgetCampaignBridge
