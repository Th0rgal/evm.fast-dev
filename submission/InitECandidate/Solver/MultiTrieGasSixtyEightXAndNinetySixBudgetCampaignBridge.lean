import InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster
import InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetCampaignBridge
import InitECandidate.Solver.UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.MultiTrieGasSixtyEightXAndNinetySixBudgetCampaignBridge

open InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster
open InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetCampaignBridge
open InitECandidate.Solver.UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster
open _root_.InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster
  (keys dirtyLevels rootOld rootLevel main200Single main380Single)
open _root_.InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
  (rawCallSections)
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

theorem multi_trie_gas_bases_and_joint_bounds_non_vacuous_and_tight :
    (base200 = 6235124040 ∧ base380 = 10648364040) ∧
    (∀ A K R : Nat, 24 * A + 21 * K ≤ 2000000 →
      R ≤ 82 * A + 63 * K → R ≤ 66 * A + 64 * K →
      7 * (R - 3 * K - 3 * A) ≤ inputBytes →
      rw4 A K R ≤ 27655360747) ∧
    (∀ A K R : Nat, 24 * A + 21 * K ≤ 3800000 →
      R ≤ 82 * A + 63 * K → R ≤ 66 * A + 64 * K →
      7 * (R - 3 * K - 3 * A) ≤ inputBytes →
      rw4 A K R ≤ 41673550747) :=
  ⟨bases, joint200, joint380⟩

theorem multi_trie_gas_opt_tight_and_multi_worse_non_vacuous_and_tight :
    (rw4 5555 88888 (82 * 5555 + 63 * 88888) = 27655104258 ∧
      24 * 5555 + 21 * 88888 ≤ 2000000) ∧
    (rw4 1 95236 (82 + 63 * 95236) < rw4 5555 88888 (82 * 5555 + 63 * 88888)) :=
  ⟨near200, multi_worse⟩

theorem multi_trie_gas_sixty_eight_x_and_forty_two_x_slopes_non_vacuous_and_tight :
    (main200 = 13167715213 ∧ 68 * main200 < yukon ∧ yukon < 69 * main200) ∧
    (main380 = 21085502713 ∧ 42 * main380 < yukon ∧ yukon < 43 * main380) :=
  ⟨GuestMultiTrieGasAndLeafBranchRehashMaster.main200_slope,
   GuestMultiTrieGasAndLeafBranchRehashMaster.main380_slope⟩

theorem multi_trie_gas_margins_and_single_slopes_non_vacuous_and_tight :
    (yukon - 68 * main200 = 5315290990 ∧ yukon - 42 * main380 = 15128811528) ∧
    ((3 * keys 200000000 = 285714 ∧ 65 * keys 200000000 = 6190470) ∧
     (dirtyLevels 95238 = 5784185 ∧ dirtyLevels 180952 = 10927025 ∧
      dirtyLevels 95238 < 65 * 95238)) ∧
    ((rootLevel 200000000 = 3847103205 ∧ rootLevel 380000000 = 7269663225 ∧
      rootOld 200000000 - rootLevel 200000000 = 257178405) ∧
     (main200Single = 13120876751 ∧ 68 * main200Single < yukon ∧
      yukon < 69 * main200Single) ∧
     (main380Single = 20956676771 ∧ 42 * main380Single < yukon ∧
      yukon < 43 * main380Single)) :=
  ⟨margins, patricia_split_dirty_node_and_single_slopes_campaign_non_vacuous_and_tight⟩

theorem patricia_split_multi_trie_no_sub_ten_and_ssz_sixty_seven_x_non_vacuous_and_tight :
    (((List.range 65).foldl (fun s _ => s + 95238) 0 = 65 * 95238 ∧
      67 * 13378055156 < yukon ∧ yukon < 68 * 13378055156) ∧
     (13378055156 - rootOld 200000000 = 9273773546 ∧
      9273773546 < 10000000000 ∧ 10000000000 < 13120876751)) ∧
    (((∀ m n2 n17 h : Nat, 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤
         GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.inputBytes →
         GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.jointCost m n2 n17 h ≤
           90 * (GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.inputBytes / 4)) ∧
       (4 * 33554428 ≤ GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.inputBytes ∧
         GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.jointCost 33554428 0 0 0 = 3019898520 ∧
         138 * 4 < 90 * 7)) ∧
      ((GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.jointSsz = 3038649506 ∧
        GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.jointPrev -
          GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.jointSsz = 1610612544) ∧
        (yukon / 68 = 13245881256 ∧
          GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main200 - yukon / 68 = 132173900)) ∧
      ((GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main200 = 13378055156 ∧
        67 * GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main200 < yukon ∧
        yukon < 68 * GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main200) ∧
       (GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main380 = 21485139986 ∧
        41 * GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main380 < yukon ∧
        yukon < 42 * GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main380))) :=
  patricia_split_multi_trie_no_sub_ten_and_ssz_offset_campaign_non_vacuous_and_tight

theorem panToStackAlloc_unconditional_noGcCall_and_id_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (n m : Nat) :
    ((∀ y ∈ rawCallSections arch prog wc ac perf, NoGcCall y.2 = true) ∧
     (∀ y ∈ rawCallSections arch prog wc ac perf,
        StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true)) ∧
    ((∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
        StackAlloc.progComp y = y) ∧
     (StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
        ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m))) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, NoTailHandler y.2 = true) :=
  ⟨panToStackRawCall_and_stackAlloc_noGcCall_unconditional_non_vacuous_and_tight arch prog wc ac perf,
   panToStackAlloc_id_of_ne_six_and_not_id_on_tagged_storeConsts_non_vacuous_and_tight arch prog wc
     ac perf n m,
   panToStackRawCall_noTailHandler_non_vacuous_and_tight arch prog wc ac perf⟩

theorem pancake_stackAllocIdentity_noGc_zeroExtraClock_multi_trie_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (n m : Nat) (w : WordLocW width) :
    ((∀ y ∈ rawCallSections arch prog wc ac perf,
        StackNoAlloc y.2 = true ∧ NoGcCall y.2 = true) ∧
     (∀ y ∈ rawCallSections arch prog wc ac perf,
        StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
     (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
        StackAlloc.progComp y = y) ∧
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
    (StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m)) ∧
    ¬ ClockOk (width := width) 1 none ∧
    ¬ ClockOk 2 (some (.halt w)) :=
  pancake_stackAllocIdentity_noGc_zeroExtraClock_campaign_non_vacuous_and_tight arch prog wc ac perf
    dc info n m w

theorem stack_remove_base_and_space_clock_ninety_six_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_ninety_four_bridge_non_vacuous_and_tight source result
    postSource target register count pointer bounds jump

theorem ninety_six_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetySixShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(ninety_six_budget_certificates_non_vacuous_and_tight cert).1,
   rfl,
   (ninety_six_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem multi_trie_gas_sixty_eight_x_and_ninety_six_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (base200 = 6235124040 ∧ base380 = 10648364040 ∧
      (∀ A K R : Nat, 24 * A + 21 * K ≤ 2000000 →
        R ≤ 82 * A + 63 * K → R ≤ 66 * A + 64 * K →
        7 * (R - 3 * K - 3 * A) ≤ inputBytes →
        rw4 A K R ≤ 27655360747) ∧
      (∀ A K R : Nat, 24 * A + 21 * K ≤ 3800000 →
        R ≤ 82 * A + 63 * K → R ≤ 66 * A + 64 * K →
        7 * (R - 3 * K - 3 * A) ≤ inputBytes →
        rw4 A K R ≤ 41673550747) ∧
      rw4 5555 88888 (82 * 5555 + 63 * 88888) = 27655104258 ∧
      24 * 5555 + 21 * 88888 ≤ 2000000 ∧
      rw4 1 95236 (82 + 63 * 95236) < rw4 5555 88888 (82 * 5555 + 63 * 88888)) ∧
    (main200 = 13167715213 ∧ 68 * main200 < yukon ∧ yukon < 69 * main200 ∧
      main380 = 21085502713 ∧ 42 * main380 < yukon ∧ yukon < 43 * main380 ∧
      yukon - 68 * main200 = 5315290990 ∧ yukon - 42 * main380 = 15128811528) ∧
    ((∀ y ∈ rawCallSections arch prog wc ac perf, NoGcCall y.2 = true) ∧
     (∀ y ∈ rawCallSections arch prog wc ac perf,
        StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
     (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
        StackAlloc.progComp y = y) ∧
     (StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
        ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m))) ∧
    (StackNoSt (.storeConsts a b c : HolProg width) = false ∧
      ¬ ClockOk (width := width) 1 none ∧
      ¬ ClockOk 2 (some (.halt w))) ∧
    (NinetySixShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨bases.1,
    bases.2,
    joint200,
    joint380,
    near200.1,
    near200.2,
    multi_worse⟩,
   ⟨GuestMultiTrieGasAndLeafBranchRehashMaster.main200_slope.1,
    GuestMultiTrieGasAndLeafBranchRehashMaster.main200_slope.2.1,
    GuestMultiTrieGasAndLeafBranchRehashMaster.main200_slope.2.2,
    GuestMultiTrieGasAndLeafBranchRehashMaster.main380_slope.1,
    GuestMultiTrieGasAndLeafBranchRehashMaster.main380_slope.2.1,
    GuestMultiTrieGasAndLeafBranchRehashMaster.main380_slope.2.2,
    margins.1,
    margins.2⟩,
   ⟨panToStackRawCall_noGcCall_unconditional_non_vacuous_and_tight arch prog wc ac perf,
    panToStackAlloc_noAlloc_noGcCall_unconditional_non_vacuous_and_tight arch prog wc ac perf,
    UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight
      arch prog wc ac perf,
    UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight
      n m⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(ninety_six_budget_certificates_non_vacuous_and_tight cert).1,
    rfl⟩,
   (ninety_six_budget_certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.MultiTrieGasSixtyEightXAndNinetySixBudgetCampaignBridge
