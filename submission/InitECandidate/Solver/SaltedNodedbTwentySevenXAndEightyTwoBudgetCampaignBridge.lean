import InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit
import InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyBudgetCampaignBridge
import InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyTwoBudgetCampaignBridge

open InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit
open InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyBudgetCampaignBridge
open InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster
open _root_.InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster
  (opTicks unitTicks restMain env200 env380 main200AllSalted main380AllSalted)
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake
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

theorem nodedb_dissect_probes_and_visit_cost_non_vacuous_and_tight :
    (decodeMemo + probesR8 + (20036870848 - 619060000) = 38946487944 ∧
      probesR8 = 8589933568) ∧
    (probesR8 = 2 * 8 * (16 * 33554428)) ∧
    (30 + 633 = 663 ∧ 663 < 1000) :=
  ⟨dissect, probes_salted, visit_cost⟩

theorem salted_nodedb_rows_wm_and_post_vals_non_vacuous_and_tight :
    (buildNodedb = 3038649506 ∧ walks 200000000 = 130000000 ∧
      rootTicks 200000000 = 4104281610) ∧
    (witnessMptSalted 200000000 = 26801608212 ∧
      witnessMptSalted 380000000 = 30612453042) ∧
    postEvmSalted = 681400462 :=
  ⟨rows_200, wm_vals, post_val⟩

theorem salted_nodedb_twenty_seven_x_and_twenty_one_x_slopes_non_vacuous_and_tight :
    (main200 = 32905132252 ∧ 27 * main200 < yukon ∧ yukon < 28 * main200) ∧
    (main380 = 41010777082 ∧ 21 * main380 < yukon ∧ yukon < 22 * main380) ∧
    (yukon / 30 = 30023997515 ∧ yukon < 30 * main200) :=
  ⟨GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200_slope,
   GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380_slope,
   no_thirty⟩

theorem salted_nodedb_dominant_and_r1_lever_non_vacuous_and_tight :
    100 * (decodeMemo + probesR8) > 59 * main200 ∧
    (main200 - probesR8 + 2 * 1 * 536870848 = 25388940380 ∧
      35 * 25388940380 < yukon ∧ yukon < 36 * 25388940380) :=
  ⟨dominant, r1_lever⟩

theorem opcode_table_all_salted_eighteen_x_and_sixteen_x_campaign_non_vacuous_and_tight :
    ((1 + 2 + 2 + 2 = 7 ∧ 1 ≤ 7 ∧ 3 ≤ 7 ∧ 1 + 5 ≤ 7) ∧
      (opTicks 8 = 28 ∧ unitTicks = 336) ∧
      (3659564234 + 500000000 + 151929428571 = 156088992805 ∧
        151929428571 = 100000000000 + 51929428571) ∧
      (env200 = 4831564234 ∧ env380 = 9126364234 ∧ restMain = 44396913938)) ∧
    ((main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
      yukon < 19 * main200AllSalted) ∧
     (main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
      yukon < 17 * main380AllSalted)) ∧
    ((102485906743 - 49228478172 = 53257428571 ∧
      154766000267 - 53523278172 = 101242722095) ∧
      10 * restMain > 9 * main200AllSalted) :=
  ⟨opcode_table_finds_unit_and_env_vals_non_vacuous_and_tight,
   all_salted_main200_and_main380_slopes_non_vacuous_and_tight,
   all_salted_gain_and_rest_dominance_non_vacuous_and_tight⟩

theorem panToStackAlloc_bodies_StackNoSt_nodedb_bridge_non_vacuous_and_tight
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
  panToStackAlloc_bodies_StackNoSt_campaign_non_vacuous_and_tight arch prog wc ac perf info a b c

theorem panToStackRemove_body_zeroExtraClock_nodedb_bridge_non_vacuous_and_tight
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
  panToStackRemove_body_zeroExtraClock_campaign_non_vacuous_and_tight arch prog wc ac perf info w

theorem stack_remove_base_and_space_clock_nodedb_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_all_salted_bridge_non_vacuous_and_tight source result postSource
    target register count pointer bounds jump

theorem eighty_two_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyTwoShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(eighty_two_budget_certificates_non_vacuous_and_tight cert).1,
   rfl,
   (eighty_two_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem salted_nodedb_twenty_seven_x_and_eighty_two_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (probesR8 = 8589933568 ∧ 30 + 633 = 663 ∧ 663 < 1000 ∧
      buildNodedb = 3038649506 ∧ witnessMptSalted 200000000 = 26801608212 ∧
      witnessMptSalted 380000000 = 30612453042 ∧ postEvmSalted = 681400462) ∧
    (main200 = 32905132252 ∧ 27 * main200 < yukon ∧ yukon < 28 * main200 ∧
      main380 = 41010777082 ∧ 21 * main380 < yukon ∧ yukon < 22 * main380 ∧
      100 * (decodeMemo + probesR8) > 59 * main200 ∧
      main200 - probesR8 + 2 * 1 * 536870848 = 25388940380 ∧
      35 * 25388940380 < yukon ∧ yukon < 36 * 25388940380) ∧
    (StackNoSt (.storeConsts a b c : HolProg width) = false ∧
      ¬ ClockOk (width := width) 1 none ∧
      ¬ ClockOk 2 (some (.halt w))) ∧
    (EightyTwoShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨dissect.2,
    visit_cost.1,
    visit_cost.2,
    rows_200.1,
    wm_vals.1,
    wm_vals.2,
    post_val⟩,
   ⟨GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200_slope.1,
    GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200_slope.2.1,
    GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200_slope.2.2,
    GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380_slope.1,
    GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380_slope.2.1,
    GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380_slope.2.2,
    dominant,
    r1_lever.1,
    r1_lever.2.1,
    r1_lever.2.2⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(eighty_two_budget_certificates_non_vacuous_and_tight cert).1,
    rfl⟩,
   (eighty_two_budget_certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyTwoBudgetCampaignBridge
