import InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster
import InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster
import InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredFourBudgetCampaignBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixBudgetCampaignBridge

open InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster
open InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster
open InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredFourBudgetCampaignBridge
open _root_.InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster
  (inputBytes cost fixed200 fixed380 main200 main380)
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

theorem exact_sstore_sload_call_base_ticks_and_tx_count_non_vacuous_and_tight :
    (sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349 ∧
      maxCode = 65536 ∧ callGas = 126) ∧
    (sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
      sloadBaseTicks + 7 * 28 ≤ 18 * 100) ∧
    (200000000 / 12000 = 16666 ∧ 200000000 / 21000 = 9523) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, charges_ok, tx_count⟩

theorem compute_jumpdests_uncached_attack_eight_x_and_four_x_non_vacuous_and_tight :
    (18 * callGas < maxCode ∧ 28 * (18 * callGas) < maxCode) ∧
    (jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon ∧
      yukon < 9 * jumpdestTicks 200000000) ∧
    (jumpdestTicks 380000000 = 197648252928 ∧ 4 * jumpdestTicks 380000000 < yukon ∧
      yukon < 5 * jumpdestTicks 380000000) ∧
    (12 * 8298113205 < jumpdestTicks 200000000) :=
  ⟨scan_ratio, attack200, attack380, previous_broken⟩

theorem compute_jumpdests_cached_vs_uncached_duality_non_vacuous_and_tight :
    (8298113205 + 134217712 = 8432330917 ∧ 106 * 8432330917 < yukon ∧
      yukon < 107 * 8432330917 ∧ 11858770499 + 134217712 = 11992988211 ∧
      75 * 11992988211 < yukon ∧ yukon < 76 * 11992988211) ∧
    (8 * jumpdestTicks 200000000 < yukon ∧ yukon < 9 * jumpdestTicks 200000000 ∧
      4 * jumpdestTicks 380000000 < yukon ∧ yukon < 5 * jumpdestTicks 380000000) :=
  ⟨cached,
   ⟨attack200.2.1, attack200.2.2, attack380.2.1, attack380.2.2⟩⟩

theorem global_gas_coupled_one_hundred_eight_x_and_joint_lp_campaign_non_vacuous_and_tight :
    ((fixed200 = 1391298018 ∧ fixed380 = 1675717026) ∧
     (3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560) ∧
     (98 * 9131446538 < yukon ∧ yukon < 99 * 9131446538)) ∧
    ((∀ A K B E n2 n17 m P : Nat, 24 * A + 21 * K + P ≤ 2000000 →
        B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
        B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
        7 * n2 + 22 * n17 + 4 * m ≤ inputBytes →
        3 * cost A K B E n2 n17 m P ≤ 20720445560) ∧
     (∀ A K B E n2 n17 m P : Nat, 24 * A + 21 * K + P ≤ 3800000 →
        B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
        B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
        7 * n2 + 22 * n17 + 4 * m ≤ inputBytes →
        65 * cost A K B E n2 n17 m P ≤ 661898475728) ∧
     (3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560)) ∧
    ((main200 = 8298113205 ∧ 108 * main200 < yukon ∧ yukon < 109 * main200 ∧
      main200 < 9000000000) ∧
     (main380 = 11858770499 ∧ 75 * main380 < yukon ∧ yukon < 76 * main380) ∧
     (yukon - 108 * main200 = 4523699334 ∧ yukon - 75 * main380 = 11312138049)) :=
  ⟨global_gas_coupled_fixed_vals_all_push_and_sensitivity_non_vacuous_and_tight,
   global_gas_coupled_joint200_and_joint380_non_vacuous_and_tight,
   global_gas_coupled_one_hundred_eight_x_and_seventy_five_x_slopes_non_vacuous_and_tight⟩

theorem global_gas_coupled_vs_evm_step_dispatch_seventy_eight_x_campaign_non_vacuous_and_tight :
    (GuestEvmStepDispatchAndNinetyXMaster.main200 = 11546768760 ∧
      main200 < GuestEvmStepDispatchAndNinetyXMaster.main200 ∧
      78 * GuestEvmStepDispatchAndNinetyXMaster.main200 < yukon ∧
      yukon < 79 * GuestEvmStepDispatchAndNinetyXMaster.main200 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main200 - main200 = 3248655555) ∧
    (GuestEvmStepDispatchAndNinetyXMaster.main380 = 17251948659 ∧
      main380 < GuestEvmStepDispatchAndNinetyXMaster.main380 ∧
      52 * GuestEvmStepDispatchAndNinetyXMaster.main380 < yukon ∧
      yukon < 53 * GuestEvmStepDispatchAndNinetyXMaster.main380 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main380 - main380 = 5393178160) :=
  ⟨improvement200_non_vacuous_and_tight, improvement380_non_vacuous_and_tight⟩

theorem panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_six_bridge_non_vacuous_and_tight
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
  panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_four_bridge_non_vacuous_and_tight arch
    prog wc ac perf n m

theorem pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_six_bridge_non_vacuous_and_tight
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
  pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_four_bridge_non_vacuous_and_tight arch
    prog wc ac perf dc info n m w

theorem stack_remove_base_and_space_clock_one_hundred_six_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_one_hundred_four_bridge_non_vacuous_and_tight source result
    postSource target register count pointer bounds jump

theorem one_hundred_six_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredSixShape ∧
      oneHundredSixExplicitFiniteKBugdetTable.length = 106 ∧
      oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 ∧
      900719925474 - 894500000000 = 6219925474 ∧
      yukon - 894500000000 = 6219925474 ∧
      (∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(one_hundred_six_budget_certificates_non_vacuous_and_tight cert).1,
   one_hundred_six_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_six_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_six_budget_last_margin_non_vacuous_and_tight.2.2.1,
   one_hundred_six_budget_last_margin_non_vacuous_and_tight.2.2.2,
   (one_hundred_six_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem exact_sstore_call_jumpdest_one_hundred_six_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349 ∧
      sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
      sloadBaseTicks + 7 * 28 ≤ 18 * 100 ∧
      18 * callGas < maxCode ∧ 28 * (18 * callGas) < maxCode ∧
      200000000 / 12000 = 16666 ∧ 200000000 / 21000 = 9523) ∧
    (jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon ∧
      yukon < 9 * jumpdestTicks 200000000 ∧
      jumpdestTicks 380000000 = 197648252928 ∧ 4 * jumpdestTicks 380000000 < yukon ∧
      yukon < 5 * jumpdestTicks 380000000 ∧
      12 * 8298113205 < jumpdestTicks 200000000 ∧
      8298113205 + 134217712 = 8432330917 ∧ 106 * 8432330917 < yukon ∧
      yukon < 107 * 8432330917 ∧ 11858770499 + 134217712 = 11992988211 ∧
      75 * 11992988211 < yukon ∧ yukon < 76 * 11992988211) ∧
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
    (OneHundredSixShape ∧
      oneHundredSixExplicitFiniteKBugdetTable.length = 106 ∧
      oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 ∧
      yukon - 894500000000 = 6219925474 ∧
      yukon = 900719925474) ∧
    (∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨rfl,
    rfl,
    rfl,
    charges_ok.1,
    charges_ok.2.1,
    charges_ok.2.2,
    scan_ratio.1,
    scan_ratio.2,
    tx_count.1,
    tx_count.2⟩,
   ⟨attack200.1,
    attack200.2.1,
    attack200.2.2,
    attack380.1,
    attack380.2.1,
    attack380.2.2,
    previous_broken,
    cached.1,
    cached.2.1,
    cached.2.2.1,
    cached.2.2.2.1,
    cached.2.2.2.2.1,
    cached.2.2.2.2.2⟩,
   ⟨panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_six_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.1.1,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_six_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.1.2,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_six_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.2.1.1,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_six_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.2.1.2⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(one_hundred_six_budget_certificates_non_vacuous_and_tight cert).1,
    one_hundred_six_budget_last_margin_non_vacuous_and_tight.1,
    one_hundred_six_budget_last_margin_non_vacuous_and_tight.2.1,
    one_hundred_six_budget_last_margin_non_vacuous_and_tight.2.2.2,
    rfl⟩,
   (one_hundred_six_budget_certificates_non_vacuous_and_tight cert).2⟩

#print axioms exact_sstore_sload_call_base_ticks_and_tx_count_non_vacuous_and_tight
#print axioms compute_jumpdests_uncached_attack_eight_x_and_four_x_non_vacuous_and_tight
#print axioms compute_jumpdests_cached_vs_uncached_duality_non_vacuous_and_tight
#print axioms global_gas_coupled_one_hundred_eight_x_and_joint_lp_campaign_non_vacuous_and_tight
#print axioms global_gas_coupled_vs_evm_step_dispatch_seventy_eight_x_campaign_non_vacuous_and_tight
#print axioms panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_six_bridge_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_six_bridge_non_vacuous_and_tight
#print axioms stack_remove_base_and_space_clock_one_hundred_six_bridge_non_vacuous_and_tight
#print axioms one_hundred_six_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
#print axioms exact_sstore_call_jumpdest_one_hundred_six_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixBudgetCampaignBridge
