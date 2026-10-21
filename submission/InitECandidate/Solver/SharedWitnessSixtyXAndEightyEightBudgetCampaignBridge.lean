import InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster
import InitECandidate.Solver.JointRlpArityFiftySixXAndEightySixBudgetCampaignBridge
import InitECandidate.Solver.JointRlpArityFiftySixXAndEightyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.SharedWitnessSixtyXAndEightyEightBudgetCampaignBridge

open InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster
open InitECandidate.Solver.JointRlpArityFiftySixXAndEightySixBudgetCampaignBridge
open InitECandidate.Solver.JointRlpArityFiftySixXAndEightyEightBudgetMaster
open _root_.InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster
  (decodeProbesOld decodeProbesNew)
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

theorem shared_witness_joint_bound_and_tight_non_vacuous_and_tight :
    (∀ m n2 n17 h : Nat, 4 * m + 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes →
      jointCost m n2 n17 h ≤ 138 * (inputBytes / 4)) ∧
    (4 * 33554428 ≤ inputBytes ∧ jointCost 0 33554428 0 0 = 4630511064 ∧
      inputBytes / 4 = 33554428) :=
  ⟨joint_bound, joint_tight⟩

theorem shared_witness_branch_not_worst_and_joint_val_non_vacuous_and_tight :
    (jointCost 0 7456539 0 0 < jointCost 0 33554428 0 0) ∧
    (keccakBlocks = 18750986 ∧ jointNew = 4649262050 ∧
      separateOld - jointNew = 820219351) :=
  ⟨branch_not_worst, joint_val⟩

theorem shared_witness_sixty_x_and_thirty_eight_x_slopes_non_vacuous_and_tight :
    (main200 = 14988667700 ∧ 60 * main200 < yukon ∧ yukon < 61 * main200) ∧
    (main380 = 23095752530 ∧ 38 * main380 < yukon ∧ yukon < 39 * main380) :=
  ⟨GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200_slope,
   GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380_slope⟩

theorem shared_witness_margins_and_joint_rlp_fifty_six_x_non_vacuous_and_tight :
    (yukon - 60 * main200 = 1399863474 ∧ yukon - 38 * main380 = 23081329334) ∧
    ((GuestJointRlpArityByteConservationAndFiftyXMaster.main200 = 15808887051 ∧
      56 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 < yukon ∧
      yukon < 57 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 ∧
      50 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 < yukon) ∧
     (GuestJointRlpArityByteConservationAndFiftyXMaster.main380 = 23915971881 ∧
      37 * GuestJointRlpArityByteConservationAndFiftyXMaster.main380 < yukon ∧
      yukon < 38 * GuestJointRlpArityByteConservationAndFiftyXMaster.main380)) :=
  ⟨margins, joint_rlp_fifty_six_x_and_thirty_seven_x_slopes_non_vacuous_and_tight⟩

theorem joint_rlp_arity_and_build_dominates_campaign_non_vacuous_and_tight :
    ((∀ n2 n17 h : Nat, 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes →
        GuestJointRlpArityByteConservationAndFiftyXMaster.jointCost n2 n17 h ≤ 2430831895) ∧
      (4 * 2 + 18 * 7456539 + 32 * 0 ≤ inputBytes ∧
        GuestJointRlpArityByteConservationAndFiftyXMaster.jointCost 2 7456539 0 = 2430831810 ∧
        2430831895 - 2430831810 = 85 ∧
        inputBytes < 18 * 7456540)) ∧
    ((inputBytes / 18 = 7456539 ∧ 9 * 7456539 ≤ 2 * 33554428) ∧
      decodeProbesOld - decodeProbesNew = 8572986881) ∧
    ((yukon - 56 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 = 15422250618 ∧
      yukon - 37 * GuestJointRlpArityByteConservationAndFiftyXMaster.main380 = 15828965877) ∧
     (100 * 3038649506 > 19 * GuestJointRlpArityByteConservationAndFiftyXMaster.main200 ∧
      3038649506 > decodeProbesNew)) :=
  ⟨joint_rlp_arity_bound_and_tight_non_vacuous_and_tight,
   joint_rlp_branch_count_and_gain_non_vacuous_and_tight,
   joint_rlp_margins_and_build_dominates_non_vacuous_and_tight⟩

theorem stackRemove_liveTable_and_deadStub6_shared_bridge_non_vacuous_and_tight
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
  stackRemove_liveTable_and_deadStub6_bridge_non_vacuous_and_tight arch prog wc ac perf dc l

theorem panToStackRemove_body_zeroExtraClock_liveTable_shared_bridge_non_vacuous_and_tight
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
  panToStackRemove_body_zeroExtraClock_liveTable_bridge_non_vacuous_and_tight arch prog wc ac perf
    dc info w

theorem stack_remove_base_and_space_clock_shared_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_joint_rlp_bridge_non_vacuous_and_tight source result postSource
    target register count pointer bounds jump

theorem eighty_eight_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyEightShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ JointRlpArityFiftySixXAndEightyEightBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(eighty_eight_budget_certificates_non_vacuous_and_tight cert).1,
   rfl,
   (eighty_eight_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem shared_witness_sixty_x_and_eighty_eight_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    ((∀ m n2 n17 h : Nat, 4 * m + 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes →
        jointCost m n2 n17 h ≤ 138 * (inputBytes / 4)) ∧
      4 * 33554428 ≤ inputBytes ∧ jointCost 0 33554428 0 0 = 4630511064 ∧
      inputBytes / 4 = 33554428 ∧
      jointCost 0 7456539 0 0 < jointCost 0 33554428 0 0 ∧
      keccakBlocks = 18750986 ∧ jointNew = 4649262050 ∧
      separateOld - jointNew = 820219351) ∧
    (main200 = 14988667700 ∧ 60 * main200 < yukon ∧ yukon < 61 * main200 ∧
      main380 = 23095752530 ∧ 38 * main380 < yukon ∧ yukon < 39 * main380 ∧
      yukon - 60 * main200 = 1399863474 ∧ yukon - 38 * main380 = 23081329334) ∧
    (StackNoSt (.storeConsts a b c : HolProg width) = false ∧
      ¬ ClockOk (width := width) 1 none ∧
      ¬ ClockOk 2 (some (.halt w))) ∧
    (EightyEightShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ JointRlpArityFiftySixXAndEightyEightBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨joint_bound,
    joint_tight.1,
    joint_tight.2.1,
    joint_tight.2.2,
    branch_not_worst,
    joint_val.1,
    joint_val.2.1,
    joint_val.2.2⟩,
   ⟨GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200_slope.1,
    GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200_slope.2.1,
    GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200_slope.2.2,
    GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380_slope.1,
    GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380_slope.2.1,
    GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380_slope.2.2,
    margins.1,
    margins.2⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(eighty_eight_budget_certificates_non_vacuous_and_tight cert).1,
    rfl⟩,
   (eighty_eight_budget_certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.SharedWitnessSixtyXAndEightyEightBudgetCampaignBridge
