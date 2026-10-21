import InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
import InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyTwoBudgetCampaignBridge
import InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightyFourBudgetCampaignBridge

open InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
open InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyTwoBudgetCampaignBridge
open InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster
open _root_.InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit
  (decodeMemo probesR8 buildNodedb walks rootTicks witnessMptSalted postEvmSalted)
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

theorem byte_coupled_refs_bound_tight_and_ratio_non_vacuous_and_tight :
    (∀ h : Nat, 33 * h ≤ inputBytes → h ≤ 4067203) ∧
    (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
    (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) :=
  ⟨refs_bound, refs_tight, ratio⟩

theorem byte_coupled_probe_vals_and_gain_non_vacuous_and_tight :
    (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
      probes 380000000 = 68115248) ∧
    (8589933568 - probes 200000000 = 8523258320) ∧
    (2 * 8 * hashRefs < 2 * 8 * 1110441952) :=
  ⟨probe_vals, gain, tree_no_coupling⟩

theorem byte_coupled_thirty_six_x_and_twenty_seven_x_slopes_non_vacuous_and_tight :
    (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
    (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) :=
  ⟨GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200_slope,
   GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380_slope⟩

theorem byte_coupled_margins_and_decode_dominates_non_vacuous_and_tight :
    (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
    (100 * 10938743528 > 44 * main200) :=
  ⟨margins, decode_dominates⟩

theorem salted_nodedb_twenty_seven_x_and_rows_campaign_non_vacuous_and_tight :
    ((decodeMemo + probesR8 + (20036870848 - 619060000) = 38946487944 ∧
      probesR8 = 8589933568) ∧
     (probesR8 = 2 * 8 * (16 * 33554428)) ∧
     (30 + 633 = 663 ∧ 663 < 1000)) ∧
    ((buildNodedb = 3038649506 ∧ walks 200000000 = 130000000 ∧
      rootTicks 200000000 = 4104281610) ∧
     (witnessMptSalted 200000000 = 26801608212 ∧
      witnessMptSalted 380000000 = 30612453042) ∧
     postEvmSalted = 681400462) ∧
    (100 * (decodeMemo + probesR8) > 59 *
      GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200 ∧
     (GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200 - probesR8 +
        2 * 1 * 536870848 = 25388940380 ∧
      35 * 25388940380 < yukon ∧ yukon < 36 * 25388940380)) :=
  ⟨nodedb_dissect_probes_and_visit_cost_non_vacuous_and_tight,
   salted_nodedb_rows_wm_and_post_vals_non_vacuous_and_tight,
   salted_nodedb_dominant_and_r1_lever_non_vacuous_and_tight⟩

theorem pancake_stackRemove_compileProg_zeroExtraBodyClock_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) :
    (∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
    (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
      t.clock = s.clock) ∧
    (∀ e ∈ StackRemove.compileHOL jump bounds generateGc maximumHeap pointer start
        (StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)),
      e.1 = storeConstsStubLocation ∨ StackNoSt e.2 = true) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        CodeNoSt source →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget)) :=
  pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight arch prog wc ac perf dc
    info jump bounds generateGc maximumHeap pointer start

theorem panToStackRemove_body_zeroExtraClock_byte_coupled_bridge_non_vacuous_and_tight
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
  panToStackRemove_body_zeroExtraClock_nodedb_bridge_non_vacuous_and_tight arch prog wc ac perf
    info w

theorem stack_remove_base_and_space_clock_byte_coupled_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_nodedb_bridge_non_vacuous_and_tight source result postSource
    target register count pointer bounds jump

theorem eighty_four_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyFourShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(eighty_four_budget_certificates_non_vacuous_and_tight cert).1,
   rfl,
   (eighty_four_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem byte_coupled_witness_thirty_six_x_and_eighty_four_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    ((∀ h : Nat, 33 * h ≤ inputBytes → h ≤ 4067203) ∧
      33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204 ∧
      132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs ∧
      2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
      probes 380000000 = 68115248 ∧
      8589933568 - probes 200000000 = 8523258320) ∧
    (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200 ∧
      main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380 ∧
      yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900 ∧
      100 * 10938743528 > 44 * main200) ∧
    (StackNoSt (.storeConsts a b c : HolProg width) = false ∧
      ¬ ClockOk (width := width) 1 none ∧
      ¬ ClockOk 2 (some (.halt w))) ∧
    (EightyFourShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨refs_bound,
    refs_tight.1,
    refs_tight.2,
    ratio.1,
    ratio.2,
    probe_vals.1,
    probe_vals.2.1,
    probe_vals.2.2,
    gain⟩,
   ⟨GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200_slope.1,
    GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200_slope.2.1,
    GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200_slope.2.2,
    GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380_slope.1,
    GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380_slope.2.1,
    GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380_slope.2.2,
    margins.1,
    margins.2,
    decode_dominates⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(eighty_four_budget_certificates_non_vacuous_and_tight cert).1,
    rfl⟩,
   (eighty_four_budget_certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightyFourBudgetCampaignBridge
