import InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster
import InitECandidate.Solver.StackRemoveNoStoreConstsAndSeventySixBudgetCampaignBridge
import InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyBudgetCampaignBridge

open InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster
open InitECandidate.Solver.StackRemoveNoStoreConstsAndSeventySixBudgetCampaignBridge
open InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake
open _root_.InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
open _root_.InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster (salted200 salted380)
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

theorem opcode_table_finds_unit_and_env_vals_non_vacuous_and_tight :
    (1 + 2 + 2 + 2 = 7 ∧ 1 ≤ 7 ∧ 3 ≤ 7 ∧ 1 + 5 ≤ 7) ∧
    (opTicks 8 = 28 ∧ unitTicks = 336) ∧
    (3659564234 + 500000000 + 151929428571 = 156088992805 ∧
      151929428571 = 100000000000 + 51929428571) ∧
    (env200 = 4831564234 ∧ env380 = 9126364234 ∧ restMain = 44396913938) :=
  ⟨finds_max,
   unit_val,
   env_split,
   ⟨env_vals.1, env_vals.2, rest_val⟩⟩

theorem all_salted_main200_and_main380_slopes_non_vacuous_and_tight :
    (main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
      yukon < 19 * main200AllSalted) ∧
    (main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
      yukon < 17 * main380AllSalted) :=
  ⟨main200_slope, main380_slope⟩

theorem all_salted_unit_slack_and_run_slack_non_vacuous_and_tight :
    (18 * (3659564234 + 500000000 + 741 * 2000000 + restMain) < yukon ∧
      yukon ≤ 18 * (3659564234 + 500000000 + 742 * 2000000 + restMain) ∧
      16 * (59564234 + 18 * 380000000 + 950000000 + 1065 * 3800000 + restMain) < yukon ∧
      yukon ≤ 16 * (59564234 + 18 * 380000000 + 950000000 + 1066 * 3800000 + restMain)) ∧
    (12 * opTicks 24 ≤ 741 ∧ 741 < 12 * opTicks 25) :=
  ⟨unit_slack, run_slack⟩

theorem all_salted_gain_and_rest_dominance_non_vacuous_and_tight :
    (102485906743 - 49228478172 = 53257428571 ∧
      154766000267 - 53523278172 = 101242722095) ∧
    10 * restMain > 9 * main200AllSalted :=
  ⟨gain, rest_dominates⟩

theorem panToStackAlloc_bodies_StackNoSt_campaign_non_vacuous_and_tight
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
  panToStackAlloc_bodies_StackNoSt_and_rejects_non_vacuous_and_tight arch prog wc ac perf info a b c

theorem panToStackRemove_body_zeroExtraClock_campaign_non_vacuous_and_tight
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
  panToStackRemove_body_zeroExtraClock_and_clockOk_tight_non_vacuous_and_tight arch prog wc ac perf info w

theorem salted_linear_gas_and_main_subsystems_campaign_non_vacuous_and_tight :
    ((156088992805 - 100000000000 + 2000000000 = 58088992805 ∧
      467569086329 - 361000000000 + 3800000000 = 110369086329) ∧
      salted200 = 102485906743 ∧
      salted380 = 154766000267) ∧
    ((8 * 102485906743 < yukon ∧ yukon - 8 * 102485906743 = 80832671530 ∧
      yukon < 9 * 102485906743) ∧
     (5 * 154766000267 < yukon ∧ yukon - 5 * 154766000267 = 126889924139 ∧
      yukon < 6 * 154766000267)) ∧
    (main200 = 200485906743 ∧ main380 = 511966000267) :=
  ⟨salted_envelopes_and_main_values_non_vacuous_and_tight,
   salted_main_slopes_non_vacuous_and_tight,
   ⟨(complete_main_subsystems_and_200m_bounds_non_vacuous_and_tight).2.2.1.1,
    (complete_main_380m_and_bal_bound_non_vacuous_and_tight).1.2⟩⟩

theorem stack_remove_base_and_space_clock_all_salted_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_campaign_non_vacuous_and_tight source result postSource target
    register count pointer bounds jump

theorem eighty_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(eighty_budget_certificates_non_vacuous_and_tight cert).1,
   rfl,
   (eighty_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem opcode_table_count_all_salted_and_eighty_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (opTicks 8 = 28 ∧ unitTicks = 336 ∧ env200 = 4831564234 ∧
      env380 = 9126364234 ∧ restMain = 44396913938) ∧
    (main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
      yukon < 19 * main200AllSalted ∧
      main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
      yukon < 17 * main380AllSalted ∧
      12 * opTicks 24 ≤ 741 ∧ 741 < 12 * opTicks 25 ∧
      10 * restMain > 9 * main200AllSalted) ∧
    (StackNoSt (.storeConsts a b c : HolProg width) = false ∧
      ¬ ClockOk (width := width) 1 none ∧
      ¬ ClockOk 2 (some (.halt w))) ∧
    (EightyShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨unit_val.1, unit_val.2, env_vals.1, env_vals.2, rest_val⟩,
   ⟨main200_slope.1,
    main200_slope.2.1,
    main200_slope.2.2,
    main380_slope.1,
    main380_slope.2.1,
    main380_slope.2.2,
    run_slack.1,
    run_slack.2,
    rest_dominates⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(eighty_budget_certificates_non_vacuous_and_tight cert).1,
    rfl⟩,
   (eighty_budget_certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyBudgetCampaignBridge
