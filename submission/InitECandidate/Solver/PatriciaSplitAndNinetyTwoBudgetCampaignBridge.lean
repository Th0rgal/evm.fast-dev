import InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster
import InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyBudgetCampaignBridge
import InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.PatriciaSplitAndNinetyTwoBudgetCampaignBridge

open InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster
open InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyBudgetCampaignBridge
open InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster
open _root_.InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster
  (inputBytes jointCost jointPrev jointSsz main200 main380)
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

theorem patricia_split_alloc_path_and_level_sums_non_vacuous_and_tight :
    (3 * keys 200000000 = 285714 ∧ 65 * keys 200000000 = 6190470) ∧
    (dirtyLevels 95238 = 5784185 ∧ dirtyLevels 180952 = 10927025 ∧
      dirtyLevels 95238 < 65 * 95238) :=
  ⟨alloc_vs_path, level_sums⟩

theorem patricia_split_root_vals_and_single_slopes_non_vacuous_and_tight :
    (rootLevel 200000000 = 3847103205 ∧ rootLevel 380000000 = 7269663225 ∧
      rootOld 200000000 - rootLevel 200000000 = 257178405) ∧
    (main200Single = 13120876751 ∧ 68 * main200Single < yukon ∧
      yukon < 69 * main200Single) ∧
    (main380Single = 20956676771 ∧ 42 * main380Single < yukon ∧
      yukon < 43 * main380Single) :=
  ⟨root_vals, main200_single, main380_single⟩

theorem patricia_split_multi_trie_and_no_sub_ten_non_vacuous_and_tight :
    ((List.range 65).foldl (fun s _ => s + 95238) 0 = 65 * 95238 ∧
      67 * 13378055156 < yukon ∧ yukon < 68 * 13378055156) ∧
    (13378055156 - rootOld 200000000 = 9273773546 ∧
      9273773546 < 10000000000 ∧ 10000000000 < 13120876751) :=
  ⟨multi_trie, no_sub_ten⟩

theorem ssz_offset_witness_sixty_seven_x_and_forty_one_x_campaign_non_vacuous_and_tight :
    ((∀ m n2 n17 h : Nat, 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes →
        jointCost m n2 n17 h ≤ 90 * (inputBytes / 4)) ∧
      (4 * 33554428 ≤ inputBytes ∧ jointCost 33554428 0 0 0 = 3019898520 ∧
        138 * 4 < 90 * 7)) ∧
    ((jointSsz = 3038649506 ∧ jointPrev - jointSsz = 1610612544) ∧
      (yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900)) ∧
    ((main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200) ∧
     (main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380)) :=
  ⟨ssz_offset_witness_joint_bound_and_tight_non_vacuous_and_tight,
   ssz_offset_witness_joint_val_and_sixty_eight_gap_non_vacuous_and_tight,
   ssz_offset_witness_sixty_seven_x_and_forty_one_x_slopes_non_vacuous_and_tight⟩

theorem ssz_offset_witness_margins_and_sixty_eight_gap_campaign_non_vacuous_and_tight :
    ((yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048) ∧
     ((GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200 = 14988667700 ∧
       60 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200 < yukon ∧
       yukon < 61 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200) ∧
      (GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380 = 23095752530 ∧
       38 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380 < yukon ∧
       yukon < 39 * GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380))) ∧
    ((yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048) ∧
     (yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900)) :=
  ⟨ssz_offset_witness_margins_and_shared_sixty_x_non_vacuous_and_tight,
   margins_and_sixty_eight_gap_non_vacuous_and_tight⟩

theorem stackAlloc_noAlloc_noGcCall_and_id_patricia_bridge_non_vacuous_and_tight
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
  stackAlloc_noAlloc_noGcCall_and_id_bridge_non_vacuous_and_tight arch prog wc ac perf

theorem panToStackRemove_noAlloc_noGc_zeroExtraClock_patricia_bridge_non_vacuous_and_tight
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
  panToStackRemove_noAlloc_noGc_zeroExtraClock_bridge_non_vacuous_and_tight arch prog wc ac perf dc
    info w

theorem stack_remove_base_and_space_clock_patricia_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_ssz_offset_bridge_non_vacuous_and_tight source result
    postSource target register count pointer bounds jump

theorem ninety_two_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetyTwoShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(ninety_two_budget_certificates_non_vacuous_and_tight cert).1,
   rfl,
   (ninety_two_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem patricia_split_and_ninety_two_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (3 * keys 200000000 = 285714 ∧ 65 * keys 200000000 = 6190470 ∧
      dirtyLevels 95238 = 5784185 ∧ dirtyLevels 180952 = 10927025 ∧
      dirtyLevels 95238 < 65 * 95238 ∧
      rootLevel 200000000 = 3847103205 ∧ rootLevel 380000000 = 7269663225 ∧
      rootOld 200000000 - rootLevel 200000000 = 257178405) ∧
    (main200Single = 13120876751 ∧ 68 * main200Single < yukon ∧ yukon < 69 * main200Single ∧
      main380Single = 20956676771 ∧ 42 * main380Single < yukon ∧ yukon < 43 * main380Single ∧
      (List.range 65).foldl (fun s _ => s + 95238) 0 = 65 * 95238 ∧
      67 * 13378055156 < yukon ∧ yukon < 68 * 13378055156 ∧
      13378055156 - rootOld 200000000 = 9273773546 ∧
      9273773546 < 10000000000 ∧ 10000000000 < 13120876751) ∧
    (StackNoSt (.storeConsts a b c : HolProg width) = false ∧
      ¬ ClockOk (width := width) 1 none ∧
      ¬ ClockOk 2 (some (.halt w))) ∧
    (NinetyTwoShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨alloc_vs_path.1,
    alloc_vs_path.2,
    level_sums.1,
    level_sums.2.1,
    level_sums.2.2,
    root_vals.1,
    root_vals.2.1,
    root_vals.2.2⟩,
   ⟨main200_single.1,
    main200_single.2.1,
    main200_single.2.2,
    main380_single.1,
    main380_single.2.1,
    main380_single.2.2,
    multi_trie.1,
    multi_trie.2.1,
    multi_trie.2.2,
    no_sub_ten.1,
    no_sub_ten.2.1,
    no_sub_ten.2.2⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(ninety_two_budget_certificates_non_vacuous_and_tight cert).1,
    rfl⟩,
   (ninety_two_budget_certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.PatriciaSplitAndNinetyTwoBudgetCampaignBridge
