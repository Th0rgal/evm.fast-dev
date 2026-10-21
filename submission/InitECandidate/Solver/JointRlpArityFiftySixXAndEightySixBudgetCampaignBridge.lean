import InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster
import InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightyFourBudgetCampaignBridge
import InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.JointRlpArityFiftySixXAndEightySixBudgetCampaignBridge

open InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster
open InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightyFourBudgetCampaignBridge
open InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster
open _root_.InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
  (hashRefs probes)
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
  (stackAllocSections liveSections)
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

theorem joint_rlp_arity_bound_and_tight_non_vacuous_and_tight :
    (∀ n2 n17 h : Nat, 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes →
      jointCost n2 n17 h ≤ 2430831895) ∧
    (4 * 2 + 18 * 7456539 + 32 * 0 ≤ inputBytes ∧
      jointCost 2 7456539 0 = 2430831810 ∧
      2430831895 - 2430831810 = 85 ∧
      inputBytes < 18 * 7456540) :=
  ⟨joint_bound, joint_tight⟩

theorem joint_rlp_branch_count_and_gain_non_vacuous_and_tight :
    (inputBytes / 18 = 7456539 ∧ 9 * 7456539 ≤ 2 * 33554428) ∧
    (decodeProbesOld - decodeProbesNew = 8572986881) :=
  ⟨branch_count, gain⟩

theorem joint_rlp_fifty_six_x_and_thirty_seven_x_slopes_non_vacuous_and_tight :
    (main200 = 15808887051 ∧ 56 * main200 < yukon ∧
      yukon < 57 * main200 ∧ 50 * main200 < yukon) ∧
    (main380 = 23915971881 ∧ 37 * main380 < yukon ∧ yukon < 38 * main380) :=
  ⟨GuestJointRlpArityByteConservationAndFiftyXMaster.main200_slope,
   GuestJointRlpArityByteConservationAndFiftyXMaster.main380_slope⟩

theorem joint_rlp_margins_and_build_dominates_non_vacuous_and_tight :
    (yukon - 56 * main200 = 15422250618 ∧ yukon - 37 * main380 = 15828965877) ∧
    (100 * 3038649506 > 19 * main200 ∧ 3038649506 > decodeProbesNew) :=
  ⟨GuestJointRlpArityByteConservationAndFiftyXMaster.margins, build_dominates⟩

theorem byte_coupled_thirty_six_x_and_probe_vals_campaign_non_vacuous_and_tight :
    ((∀ h : Nat, 33 * h ≤ inputBytes → h ≤ 4067203) ∧
     (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
     (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs)) ∧
    ((2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
      probes 380000000 = 68115248) ∧
     (8589933568 - probes 200000000 = 8523258320) ∧
     (2 * 8 * hashRefs < 2 * 8 * 1110441952)) ∧
    ((GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 = 24381873932 ∧
      36 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200 < yukon ∧
      yukon < 37 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200) ∧
     (GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 = 32488958762 ∧
      27 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380 < yukon ∧
      yukon < 28 * GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380)) :=
  ⟨byte_coupled_refs_bound_tight_and_ratio_non_vacuous_and_tight,
   byte_coupled_probe_vals_and_gain_non_vacuous_and_tight,
   byte_coupled_thirty_six_x_and_twenty_seven_x_slopes_non_vacuous_and_tight⟩

theorem stackRemove_liveTable_and_deadStub6_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (l : List (Nat × HolProg width)) :
    (∀ e ∈ stackAllocSections arch prog wc ac perf dc,
      e.1 = storeConstsStubLocation ∨ Clean e.2 = true) ∧
    sptLookup storeConstsStubLocation (sptFromAList (liveSections l)) = none ∧
    ((∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
      sptLookup storeConstsStubLocation
        (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none) :=
  ⟨stackAllocSections_clean_non_vacuous_and_tight arch prog wc ac perf dc,
   liveTable_lookup_six_non_vacuous_and_tight l,
   fullTable_has_label6_non_vacuous_and_tight arch prog wc ac perf dc⟩

theorem panToStackRemove_body_zeroExtraClock_liveTable_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (w : WordLocW width) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1, StackNoSt e.2 = true) →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget)) ∧
    ¬ ClockOk (width := width) 1 none ∧
    ¬ ClockOk 2 (some (.halt w)) :=
  ⟨panToStackRemove_body_zeroExtraClock_liveTable_non_vacuous_and_tight arch prog wc ac perf dc info,
   clockOk_rejects_one_none,
   clockOk_rejects_two_halt w⟩

theorem stack_remove_base_and_space_clock_joint_rlp_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_byte_coupled_bridge_non_vacuous_and_tight source result
    postSource target register count pointer bounds jump

theorem eighty_six_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightySixShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(eighty_six_budget_certificates_non_vacuous_and_tight cert).1,
   rfl,
   (eighty_six_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem joint_rlp_arity_fifty_six_x_and_eighty_six_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    ((∀ n2 n17 h : Nat, 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes →
        jointCost n2 n17 h ≤ 2430831895) ∧
      jointCost 2 7456539 0 = 2430831810 ∧
      2430831895 - 2430831810 = 85 ∧
      inputBytes / 18 = 7456539 ∧
      decodeProbesOld - decodeProbesNew = 8572986881) ∧
    (main200 = 15808887051 ∧ 56 * main200 < yukon ∧
      yukon < 57 * main200 ∧ 50 * main200 < yukon ∧
      main380 = 23915971881 ∧ 37 * main380 < yukon ∧ yukon < 38 * main380 ∧
      yukon - 56 * main200 = 15422250618 ∧ yukon - 37 * main380 = 15828965877 ∧
      100 * 3038649506 > 19 * main200 ∧ 3038649506 > decodeProbesNew) ∧
    (StackNoSt (.storeConsts a b c : HolProg width) = false ∧
      ¬ ClockOk (width := width) 1 none ∧
      ¬ ClockOk 2 (some (.halt w))) ∧
    (EightySixShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨joint_bound,
    joint_tight.2.1,
    joint_tight.2.2.1,
    branch_count.1,
    gain⟩,
   ⟨GuestJointRlpArityByteConservationAndFiftyXMaster.main200_slope.1,
    GuestJointRlpArityByteConservationAndFiftyXMaster.main200_slope.2.1,
    GuestJointRlpArityByteConservationAndFiftyXMaster.main200_slope.2.2.1,
    GuestJointRlpArityByteConservationAndFiftyXMaster.main200_slope.2.2.2,
    GuestJointRlpArityByteConservationAndFiftyXMaster.main380_slope.1,
    GuestJointRlpArityByteConservationAndFiftyXMaster.main380_slope.2.1,
    GuestJointRlpArityByteConservationAndFiftyXMaster.main380_slope.2.2,
    GuestJointRlpArityByteConservationAndFiftyXMaster.margins.1,
    GuestJointRlpArityByteConservationAndFiftyXMaster.margins.2,
    build_dominates.1,
    build_dominates.2⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(eighty_six_budget_certificates_non_vacuous_and_tight cert).1,
    rfl⟩,
   (eighty_six_budget_certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.JointRlpArityFiftySixXAndEightySixBudgetCampaignBridge
