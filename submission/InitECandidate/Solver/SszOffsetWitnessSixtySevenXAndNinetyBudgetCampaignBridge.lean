import InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster
import InitECandidate.Solver.SharedWitnessSixtyXAndEightyEightBudgetCampaignBridge
import InitECandidate.Solver.SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyBudgetCampaignBridge

open InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster
open InitECandidate.Solver.SharedWitnessSixtyXAndEightyEightBudgetCampaignBridge
open InitECandidate.Solver.SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster
open _root_.InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster
  (separateOld jointNew)
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural
  (NoGcCall NoTailHandler)
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc
  (StackNoAlloc)
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

theorem ssz_offset_witness_joint_bound_and_tight_non_vacuous_and_tight :
    (∀ m n2 n17 h : Nat, 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes →
      jointCost m n2 n17 h ≤ 90 * (inputBytes / 4)) ∧
    (4 * 33554428 ≤ inputBytes ∧ jointCost 33554428 0 0 0 = 3019898520 ∧
      138 * 4 < 90 * 7) :=
  ⟨joint_bound, joint_tight⟩

theorem ssz_offset_witness_joint_val_and_sixty_eight_gap_non_vacuous_and_tight :
    (jointSsz = 3038649506 ∧ jointPrev - jointSsz = 1610612544) ∧
    (yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900) :=
  ⟨joint_val, sixty_eight_gap⟩

theorem ssz_offset_witness_sixty_seven_x_and_forty_one_x_slopes_non_vacuous_and_tight :
    (main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200) ∧
    (main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380) :=
  ⟨GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main200_slope,
   GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main380_slope⟩

theorem ssz_offset_witness_margins_and_shared_sixty_x_non_vacuous_and_tight :
    (yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048) ∧
    ((GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200 = 14988667700 ∧
      60 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200 < yukon ∧
      yukon < 61 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200) ∧
     (GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380 = 23095752530 ∧
      38 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380 < yukon ∧
      yukon < 39 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380)) :=
  ⟨margins, shared_witness_sixty_x_and_thirty_eight_x_slopes_non_vacuous_and_tight⟩

theorem shared_witness_joint_and_margins_campaign_non_vacuous_and_tight :
    ((∀ m n2 n17 h : Nat, 4 * m + 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes →
        jointCost m n2 n17 h ≤ 138 * (inputBytes / 4)) ∧
      (4 * 33554428 ≤ inputBytes ∧ jointCost 0 33554428 0 0 = 4630511064 ∧
        inputBytes / 4 = 33554428)) ∧
    ((jointCost 0 7456539 0 0 < jointCost 0 33554428 0 0) ∧
      (keccakBlocks = 18750986 ∧ jointNew = 4649262050 ∧
        separateOld - jointNew = 820219351)) ∧
    (yukon - 60 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200 = 1399863474 ∧
      yukon - 38 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380 = 23081329334) :=
  ⟨shared_witness_joint_bound_and_tight_non_vacuous_and_tight,
   shared_witness_branch_not_worst_and_joint_val_non_vacuous_and_tight,
   margins_non_vacuous_and_tight⟩

theorem stackAlloc_noAlloc_noGcCall_and_id_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      NoGcCall y.2 = true →
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    (∀ (n m : Nat) (p : HolProg width),
      StackNoAlloc p = true → StackNoSt p = true →
      NoTailHandler p = true → StackAlloc.comp n m p = (p, m)) :=
  ⟨panToStackRawCall_noAlloc_unconditional_non_vacuous_and_tight arch prog wc ac perf,
   panToStackAlloc_noAlloc_noGcCall_non_vacuous_and_tight arch prog wc ac perf,
   stackAllocComp_id_non_vacuous_and_tight⟩

theorem panToStackRemove_noAlloc_noGc_zeroExtraClock_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (w : WordLocW width) :
    ((∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
     (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      NoGcCall y.2 = true →
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
     (∀ e ∈ InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
        arch prog wc ac perf dc, e.1 ≠ storeConstsStubLocation →
      InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true ∧
      InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts.Clean e.2 = true) ∧
     (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = sptFromAList
          (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.liveSections
            (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
              arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1,
          InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true) →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget,
          InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget))) ∧
    ¬ ClockOk (width := width) 1 none ∧
    ¬ ClockOk 2 (some (.halt w)) :=
  ⟨panToStackRemove_noAlloc_noGc_zeroExtraClock_non_vacuous_and_tight arch prog wc ac perf dc info,
   clockOk_rejects_one_none,
   clockOk_rejects_two_halt w⟩

theorem stack_remove_base_and_space_clock_ssz_offset_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_shared_bridge_non_vacuous_and_tight source result postSource
    target register count pointer bounds jump

theorem ninety_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetyShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(ninety_budget_certificates_non_vacuous_and_tight cert).1,
   rfl,
   (ninety_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem ssz_offset_witness_sixty_seven_x_and_ninety_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    ((∀ m n2 n17 h : Nat, 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes →
        jointCost m n2 n17 h ≤ 90 * (inputBytes / 4)) ∧
      4 * 33554428 ≤ inputBytes ∧ jointCost 33554428 0 0 0 = 3019898520 ∧
      138 * 4 < 90 * 7 ∧
      jointSsz = 3038649506 ∧ jointPrev - jointSsz = 1610612544 ∧
      yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900) ∧
    (main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200 ∧
      main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380 ∧
      yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048) ∧
    (StackNoSt (.storeConsts a b c : HolProg width) = false ∧
      ¬ ClockOk (width := width) 1 none ∧
      ¬ ClockOk 2 (some (.halt w))) ∧
    (NinetyShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨joint_bound,
    joint_tight.1,
    joint_tight.2.1,
    joint_tight.2.2,
    joint_val.1,
    joint_val.2,
    sixty_eight_gap.1,
    sixty_eight_gap.2⟩,
   ⟨GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main200_slope.1,
    GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main200_slope.2.1,
    GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main200_slope.2.2,
    GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main380_slope.1,
    GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main380_slope.2.1,
    GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main380_slope.2.2,
    margins.1,
    margins.2⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(ninety_budget_certificates_non_vacuous_and_tight cert).1,
    rfl⟩,
   (ninety_budget_certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyBudgetCampaignBridge
