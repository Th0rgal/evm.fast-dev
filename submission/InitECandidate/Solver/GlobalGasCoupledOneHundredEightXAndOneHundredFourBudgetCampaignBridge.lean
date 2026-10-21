import InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster
import InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredTwoBudgetCampaignBridge
import InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredFourBudgetCampaignBridge

open InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster
open InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredTwoBudgetCampaignBridge
open InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster
open _root_.InitECandidate.Solver.GuestEvmStepDispatchAndNinetyXMaster
  (jumpdestTicks addTicks push31Ticks sloadWarmTicks)
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

theorem global_gas_coupled_fixed_vals_all_push_and_sensitivity_non_vacuous_and_tight :
    (fixed200 = 1391298018 ∧ fixed380 = 1675717026) ∧
    (3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560) ∧
    (98 * 9131446538 < yukon ∧ yukon < 99 * 9131446538) :=
  ⟨fixed_vals, all_push, sensitivity⟩

theorem global_gas_coupled_joint200_and_joint380_non_vacuous_and_tight :
    (∀ A K B E n2 n17 m P : Nat, 24 * A + 21 * K + P ≤ 2000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * m ≤ inputBytes →
      3 * cost A K B E n2 n17 m P ≤ 20720445560) ∧
    (∀ A K B E n2 n17 m P : Nat, 24 * A + 21 * K + P ≤ 3800000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * m ≤ inputBytes →
      65 * cost A K B E n2 n17 m P ≤ 661898475728) ∧
    (3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560) :=
  ⟨joint200, joint380, all_push⟩

theorem global_gas_coupled_one_hundred_eight_x_and_seventy_five_x_slopes_non_vacuous_and_tight :
    (main200 = 8298113205 ∧ 108 * main200 < yukon ∧ yukon < 109 * main200 ∧
      main200 < 9000000000) ∧
    (main380 = 11858770499 ∧ 75 * main380 < yukon ∧ yukon < 76 * main380) ∧
    (yukon - 108 * main200 = 4523699334 ∧ yukon - 75 * main380 = 11312138049) :=
  ⟨GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200_slope,
   GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main380_slope,
   GuestGlobalGasCoupledEvmAndSubNineBillionMaster.margins⟩

theorem global_gas_coupled_strictly_improves_evm_step_dispatch_seventy_eight_x_non_vacuous_and_tight :
    (main200 = 8298113205 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main200 = 11546768760 ∧
      main200 < GuestEvmStepDispatchAndNinetyXMaster.main200 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main200 - main200 = 3248655555 ∧
      108 * main200 < yukon ∧
      main200 < 9000000000 ∧
      78 * GuestEvmStepDispatchAndNinetyXMaster.main200 < yukon ∧
      yukon < 79 * GuestEvmStepDispatchAndNinetyXMaster.main200) ∧
    (main380 = 11858770499 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main380 = 17251948659 ∧
      main380 < GuestEvmStepDispatchAndNinetyXMaster.main380 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main380 - main380 = 5393178160 ∧
      75 * main380 < yukon ∧
      52 * GuestEvmStepDispatchAndNinetyXMaster.main380 < yukon ∧
      yukon < 53 * GuestEvmStepDispatchAndNinetyXMaster.main380) := by
  decide

theorem evm_step_dispatch_ratios_and_seventy_eight_x_campaign_non_vacuous_and_tight :
    ((jumpdestTicks = 5 ∧ addTicks = 9 ∧ addTicks ≤ 18 * 3 ∧ jumpdestTicks ≤ 18 * 1 ∧
      push31Ticks = 18 * 3) ∧
     (sloadWarmTicks = 226 ∧ sloadWarmTicks ≤ 18 * 100) ∧
     (∀ a b : Nat, sloadWarmTicks * a + 18 * b ≤ 18 * (100 * a + b)) ∧
     (336 * 2000000 = 672000000 ∧ 450000000 + 336 * 3800000 = 1726800000)) ∧
    ((GuestEvmStepDispatchAndNinetyXMaster.main200 = 11546768760 ∧
      78 * GuestEvmStepDispatchAndNinetyXMaster.main200 < yukon ∧
      yukon < 79 * GuestEvmStepDispatchAndNinetyXMaster.main200) ∧
     (GuestEvmStepDispatchAndNinetyXMaster.main380 = 17251948659 ∧
      52 * GuestEvmStepDispatchAndNinetyXMaster.main380 < yukon ∧
      yukon < 53 * GuestEvmStepDispatchAndNinetyXMaster.main380) ∧
     (yukon / 90 = 10007999171 ∧
      yukon < 90 * GuestEvmStepDispatchAndNinetyXMaster.main200) ∧
     (yukon - 78 * GuestEvmStepDispatchAndNinetyXMaster.main200 = 71962194 ∧
      yukon - 52 * GuestEvmStepDispatchAndNinetyXMaster.main380 = 3618595206)) ∧
    ((GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 = 12218768760 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main200 <
        GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 ∧
      73 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 < yukon ∧
      yukon < 74 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 ∧
      GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200 -
        GuestEvmStepDispatchAndNinetyXMaster.main200 = 672000000) ∧
     (GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 = 18978748659 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main380 <
        GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 ∧
      47 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 < yukon ∧
      yukon < 48 * GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 ∧
      GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380 -
        GuestEvmStepDispatchAndNinetyXMaster.main380 = 1726800000)) :=
  ⟨evm_step_dispatch_ratios_sload_joint_and_removed_non_vacuous_and_tight,
   evm_step_dispatch_seventy_eight_x_and_fifty_two_x_slopes_non_vacuous_and_tight,
   ⟨improvement200_non_vacuous_and_tight, improvement380_non_vacuous_and_tight⟩⟩

theorem panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_four_bridge_non_vacuous_and_tight
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
  panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_two_bridge_non_vacuous_and_tight arch
    prog wc ac perf n m

theorem pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_four_bridge_non_vacuous_and_tight
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
  pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_two_bridge_non_vacuous_and_tight arch
    prog wc ac perf dc info n m w

theorem stack_remove_base_and_space_clock_one_hundred_four_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_one_hundred_two_bridge_non_vacuous_and_tight source result
    postSource target register count pointer bounds jump

theorem one_hundred_four_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredFourShape ∧
      oneHundredFourExplicitFiniteKBugdetTable.length = 104 ∧
      oneHundredFourExplicitFiniteKBugdetTable.getLast? = some 892500000000 ∧
      900719925474 - 892500000000 = 8219925474 ∧
      yukon - 892500000000 = 8219925474 ∧
      (∀ K ∈ oneHundredFourExplicitFiniteKBugdetTable,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(one_hundred_four_budget_certificates_non_vacuous_and_tight cert).1,
   one_hundred_four_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_four_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_four_budget_last_margin_non_vacuous_and_tight.2.2.1,
   one_hundred_four_budget_last_margin_non_vacuous_and_tight.2.2.2,
   (one_hundred_four_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem global_gas_coupled_one_hundred_eight_x_and_one_hundred_four_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (fixed200 = 1391298018 ∧ fixed380 = 1675717026 ∧
      (∀ A K B E n2 n17 m P : Nat, 24 * A + 21 * K + P ≤ 2000000 →
        B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
        B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
        7 * n2 + 22 * n17 + 4 * m ≤ inputBytes →
        3 * cost A K B E n2 n17 m P ≤ 20720445560) ∧
      (∀ A K B E n2 n17 m P : Nat, 24 * A + 21 * K + P ≤ 3800000 →
        B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
        B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
        7 * n2 + 22 * n17 + 4 * m ≤ inputBytes →
        65 * cost A K B E n2 n17 m P ≤ 661898475728) ∧
      3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560 ∧
      98 * 9131446538 < yukon ∧ yukon < 99 * 9131446538) ∧
    (main200 = 8298113205 ∧ 108 * main200 < yukon ∧ yukon < 109 * main200 ∧
      main200 < 9000000000 ∧
      main380 = 11858770499 ∧ 75 * main380 < yukon ∧ yukon < 76 * main380 ∧
      yukon - 108 * main200 = 4523699334 ∧ yukon - 75 * main380 = 11312138049 ∧
      main200 < GuestEvmStepDispatchAndNinetyXMaster.main200 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main200 - main200 = 3248655555 ∧
      main380 < GuestEvmStepDispatchAndNinetyXMaster.main380 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main380 - main380 = 5393178160) ∧
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
    (OneHundredFourShape ∧
      oneHundredFourExplicitFiniteKBugdetTable.length = 104 ∧
      oneHundredFourExplicitFiniteKBugdetTable.getLast? = some 892500000000 ∧
      yukon - 892500000000 = 8219925474 ∧
      yukon = 900719925474) ∧
    (∀ K ∈ oneHundredFourExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨fixed_vals.1,
    fixed_vals.2,
    joint200,
    joint380,
    all_push,
    sensitivity.1,
    sensitivity.2⟩,
   ⟨GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200_slope.1,
    GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200_slope.2.1,
    GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200_slope.2.2.1,
    GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200_slope.2.2.2,
    GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main380_slope.1,
    GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main380_slope.2.1,
    GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main380_slope.2.2,
    GuestGlobalGasCoupledEvmAndSubNineBillionMaster.margins.1,
    GuestGlobalGasCoupledEvmAndSubNineBillionMaster.margins.2,
    global_gas_coupled_strictly_improves_evm_step_dispatch_seventy_eight_x_non_vacuous_and_tight.1.2.2.1,
    global_gas_coupled_strictly_improves_evm_step_dispatch_seventy_eight_x_non_vacuous_and_tight.1.2.2.2.1,
    global_gas_coupled_strictly_improves_evm_step_dispatch_seventy_eight_x_non_vacuous_and_tight.2.2.2.1,
    global_gas_coupled_strictly_improves_evm_step_dispatch_seventy_eight_x_non_vacuous_and_tight.2.2.2.2.1⟩,
   ⟨panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_four_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.1.1,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_four_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.1.2,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_four_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.2.1.1,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_four_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.2.1.2⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(one_hundred_four_budget_certificates_non_vacuous_and_tight cert).1,
    one_hundred_four_budget_last_margin_non_vacuous_and_tight.1,
    one_hundred_four_budget_last_margin_non_vacuous_and_tight.2.1,
    one_hundred_four_budget_last_margin_non_vacuous_and_tight.2.2.2,
    rfl⟩,
   (one_hundred_four_budget_certificates_non_vacuous_and_tight cert).2⟩

#print axioms global_gas_coupled_fixed_vals_all_push_and_sensitivity_non_vacuous_and_tight
#print axioms global_gas_coupled_joint200_and_joint380_non_vacuous_and_tight
#print axioms global_gas_coupled_one_hundred_eight_x_and_seventy_five_x_slopes_non_vacuous_and_tight
#print axioms global_gas_coupled_strictly_improves_evm_step_dispatch_seventy_eight_x_non_vacuous_and_tight
#print axioms evm_step_dispatch_ratios_and_seventy_eight_x_campaign_non_vacuous_and_tight
#print axioms panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_four_bridge_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_four_bridge_non_vacuous_and_tight
#print axioms stack_remove_base_and_space_clock_one_hundred_four_bridge_non_vacuous_and_tight
#print axioms one_hundred_four_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
#print axioms global_gas_coupled_one_hundred_eight_x_and_one_hundred_four_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredFourBudgetCampaignBridge
