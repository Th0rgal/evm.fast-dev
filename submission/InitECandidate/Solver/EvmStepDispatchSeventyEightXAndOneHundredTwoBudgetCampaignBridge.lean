import InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster
import InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredBudgetCampaignBridge
import InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredTwoBudgetCampaignBridge

open InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster
open InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredBudgetCampaignBridge
open InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredTwoBudgetMaster
open _root_.InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster
  (mergeTicks balTicks)
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

theorem evm_step_dispatch_ratios_sload_joint_and_removed_non_vacuous_and_tight :
    (jumpdestTicks = 5 ∧ addTicks = 9 ∧ addTicks ≤ 18 * 3 ∧ jumpdestTicks ≤ 18 * 1 ∧
      push31Ticks = 18 * 3) ∧
    (sloadWarmTicks = 226 ∧ sloadWarmTicks ≤ 18 * 100) ∧
    (∀ a b : Nat, sloadWarmTicks * a + 18 * b ≤ 18 * (100 * a + b)) ∧
    (336 * 2000000 = 672000000 ∧ 450000000 + 336 * 3800000 = 1726800000) :=
  ⟨ratios, sload_inside, joint, removed⟩

theorem evm_step_dispatch_seventy_eight_x_and_fifty_two_x_slopes_non_vacuous_and_tight :
    (main200 = 11546768760 ∧ 78 * main200 < yukon ∧ yukon < 79 * main200) ∧
    (main380 = 17251948659 ∧ 52 * main380 < yukon ∧ yukon < 53 * main380) ∧
    (yukon / 90 = 10007999171 ∧ yukon < 90 * main200) ∧
    (yukon - 78 * main200 = 71962194 ∧ yukon - 52 * main380 = 3618595206) :=
  ⟨GuestEvmStepDispatchAndNinetyXMaster.main200_slope,
   GuestEvmStepDispatchAndNinetyXMaster.main380_slope,
   no_90,
   GuestEvmStepDispatchAndNinetyXMaster.margins⟩

theorem evm_step_dispatch_strictly_improves_exact_merge_bal_seventy_three_x_non_vacuous_and_tight :
    (main200 = 11546768760 ∧
      GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 = 12218768760 ∧
      main200 < GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 ∧
      GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 - main200 = 672000000 ∧
      78 * main200 < yukon ∧
      73 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 < yukon ∧
      yukon < 74 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200) ∧
    (main380 = 17251948659 ∧
      GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 = 18978748659 ∧
      main380 < GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 ∧
      GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 - main380 = 1726800000 ∧
      52 * main380 < yukon ∧
      47 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 < yukon ∧
      yukon < 48 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380) := by
  decide

theorem exact_merge_bal_vals_and_seventy_three_x_campaign_non_vacuous_and_tight :
    ((mergeTicks 200000000 = 65422992 ∧ mergeTicks 380000000 = 101802000 ∧
      mergeTicks 380000000 < 500000000) ∧
     (balTicks 200000000 = 144000000 ∧ balTicks 380000000 = 273600000) ∧
     (12 + 2 * 8 ≤ 60 ∧ 2100 / 100 = 21)) ∧
    ((GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 = 12218768760 ∧
      73 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 < yukon ∧
      yukon < 74 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200) ∧
     (GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 = 18978748659 ∧
      47 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 < yukon ∧
      yukon < 48 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380) ∧
     (yukon / 75 = 12009599006 ∧
      yukon < 75 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200) ∧
     (yukon - 73 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 = 8749805994 ∧
      yukon - 47 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 = 8718738501)) :=
  ⟨exact_merge_bal_vals_and_entry_charge_non_vacuous_and_tight,
   exact_merge_bal_seventy_three_x_and_forty_seven_x_slopes_non_vacuous_and_tight⟩

theorem exact_merge_bal_vs_two_item_seventy_x_campaign_non_vacuous_and_tight :
    (GuestTwoItemNodeRehashAndSeventyXMaster.main200 = 12809345768 ∧
      GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 <
        GuestTwoItemNodeRehashAndSeventyXMaster.main200 ∧
      70 * GuestTwoItemNodeRehashAndSeventyXMaster.main200 < yukon ∧
      yukon < 71 * GuestTwoItemNodeRehashAndSeventyXMaster.main200 ∧
      GuestTwoItemNodeRehashAndSeventyXMaster.main200 -
        GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 = 590577008) ∧
    (GuestTwoItemNodeRehashAndSeventyXMaster.main380 = 19403346659 ∧
      GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 <
        GuestTwoItemNodeRehashAndSeventyXMaster.main380 ∧
      46 * GuestTwoItemNodeRehashAndSeventyXMaster.main380 < yukon ∧
      yukon < 47 * GuestTwoItemNodeRehashAndSeventyXMaster.main380 ∧
      GuestTwoItemNodeRehashAndSeventyXMaster.main380 -
        GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 = 424598000) :=
  ⟨improvement200_non_vacuous_and_tight, improvement380_non_vacuous_and_tight⟩

theorem panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_two_bridge_non_vacuous_and_tight
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
  panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_bridge_non_vacuous_and_tight arch prog
    wc ac perf n m

theorem pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_two_bridge_non_vacuous_and_tight
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
  pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_bridge_non_vacuous_and_tight arch prog
    wc ac perf dc info n m w

theorem stack_remove_base_and_space_clock_one_hundred_two_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_one_hundred_bridge_non_vacuous_and_tight source result
    postSource target register count pointer bounds jump

theorem one_hundred_two_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwoShape ∧
      oneHundredTwoExplicitFiniteKBugdetTable.length = 102 ∧
      oneHundredTwoExplicitFiniteKBugdetTable.getLast? = some 889500000000 ∧
      900719925474 - 889500000000 = 11219925474 ∧
      yukon - 889500000000 = 11219925474 ∧
      (∀ K ∈ oneHundredTwoExplicitFiniteKBugdetTable,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(one_hundred_two_budget_certificates_non_vacuous_and_tight cert).1,
   one_hundred_two_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_two_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_two_budget_last_margin_non_vacuous_and_tight.2.2.1,
   one_hundred_two_budget_last_margin_non_vacuous_and_tight.2.2.2,
   (one_hundred_two_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem evm_step_dispatch_seventy_eight_x_and_one_hundred_two_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (jumpdestTicks = 5 ∧ addTicks = 9 ∧ addTicks ≤ 18 * 3 ∧ jumpdestTicks ≤ 18 * 1 ∧
      push31Ticks = 18 * 3 ∧ sloadWarmTicks = 226 ∧ sloadWarmTicks ≤ 18 * 100 ∧
      (∀ x y : Nat, sloadWarmTicks * x + 18 * y ≤ 18 * (100 * x + y)) ∧
      336 * 2000000 = 672000000 ∧ 450000000 + 336 * 3800000 = 1726800000) ∧
    (main200 = 11546768760 ∧ 78 * main200 < yukon ∧ yukon < 79 * main200 ∧
      main380 = 17251948659 ∧ 52 * main380 < yukon ∧ yukon < 53 * main380 ∧
      yukon / 90 = 10007999171 ∧ yukon < 90 * main200 ∧
      yukon - 78 * main200 = 71962194 ∧ yukon - 52 * main380 = 3618595206 ∧
      main200 < GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 ∧
      GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 - main200 = 672000000 ∧
      main380 < GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 ∧
      GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 - main380 = 1726800000) ∧
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
    (OneHundredTwoShape ∧
      oneHundredTwoExplicitFiniteKBugdetTable.length = 102 ∧
      oneHundredTwoExplicitFiniteKBugdetTable.getLast? = some 889500000000 ∧
      yukon - 889500000000 = 11219925474 ∧
      yukon = 900719925474) ∧
    (∀ K ∈ oneHundredTwoExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨ratios.1,
    ratios.2.1,
    ratios.2.2.1,
    ratios.2.2.2.1,
    ratios.2.2.2.2,
    sload_inside.1,
    sload_inside.2,
    joint,
    removed.1,
    removed.2⟩,
   ⟨GuestEvmStepDispatchAndNinetyXMaster.main200_slope.1,
    GuestEvmStepDispatchAndNinetyXMaster.main200_slope.2.1,
    GuestEvmStepDispatchAndNinetyXMaster.main200_slope.2.2,
    GuestEvmStepDispatchAndNinetyXMaster.main380_slope.1,
    GuestEvmStepDispatchAndNinetyXMaster.main380_slope.2.1,
    GuestEvmStepDispatchAndNinetyXMaster.main380_slope.2.2,
    no_90.1,
    no_90.2,
    GuestEvmStepDispatchAndNinetyXMaster.margins.1,
    GuestEvmStepDispatchAndNinetyXMaster.margins.2,
    evm_step_dispatch_strictly_improves_exact_merge_bal_seventy_three_x_non_vacuous_and_tight.1.2.2.1,
    evm_step_dispatch_strictly_improves_exact_merge_bal_seventy_three_x_non_vacuous_and_tight.1.2.2.2.1,
    evm_step_dispatch_strictly_improves_exact_merge_bal_seventy_three_x_non_vacuous_and_tight.2.2.2.1,
    evm_step_dispatch_strictly_improves_exact_merge_bal_seventy_three_x_non_vacuous_and_tight.2.2.2.2.1⟩,
   ⟨panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_two_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.1.1,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_two_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.1.2,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_two_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.2.1.1,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_two_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.2.1.2⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(one_hundred_two_budget_certificates_non_vacuous_and_tight cert).1,
    one_hundred_two_budget_last_margin_non_vacuous_and_tight.1,
    one_hundred_two_budget_last_margin_non_vacuous_and_tight.2.1,
    one_hundred_two_budget_last_margin_non_vacuous_and_tight.2.2.2,
    rfl⟩,
   (one_hundred_two_budget_certificates_non_vacuous_and_tight cert).2⟩

#print axioms evm_step_dispatch_ratios_sload_joint_and_removed_non_vacuous_and_tight
#print axioms evm_step_dispatch_seventy_eight_x_and_fifty_two_x_slopes_non_vacuous_and_tight
#print axioms evm_step_dispatch_strictly_improves_exact_merge_bal_seventy_three_x_non_vacuous_and_tight
#print axioms exact_merge_bal_vals_and_seventy_three_x_campaign_non_vacuous_and_tight
#print axioms exact_merge_bal_vs_two_item_seventy_x_campaign_non_vacuous_and_tight
#print axioms panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_two_bridge_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_two_bridge_non_vacuous_and_tight
#print axioms stack_remove_base_and_space_clock_one_hundred_two_bridge_non_vacuous_and_tight
#print axioms one_hundred_two_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
#print axioms evm_step_dispatch_seventy_eight_x_and_one_hundred_two_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredTwoBudgetCampaignBridge
