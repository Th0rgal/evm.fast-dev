import InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
import InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster
import InitECandidate.Solver.JumpdestDualLPOneHundredTwelveBudgetCampaignBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.WitnessEmptyItemPushOneHundredFourteenBudgetCampaignBridge

open InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
open InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster
open InitECandidate.Solver.JumpdestDualLPOneHundredTwelveBudgetCampaignBridge
open _root_.InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster
  (sstoreBaseTicks sloadBaseTicks accountAccessBaseTicks maxCode callGas jumpdestTicks)
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

theorem witness_empty_item_push_leaf_counts_and_cached_lp_non_vacuous_and_tight :
    (keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3) ∧
    (∀ A K B E n2 n17 md ms P : Nat,
      2400 * A + 2100 * K + P ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      33 * costC A K B E n2 n17 md ms P ≤ 214138410040) ∧
    (∀ A K B E n2 n17 md ms P : Nat,
      2400 * A + 2100 * K + P ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      11803 * costC A K B E n2 n17 md ms P ≤ 114947567578464) :=
  ⟨leaf_counts, cached200, cached380⟩

theorem witness_empty_item_push_uncached_full_lp_non_vacuous_and_tight :
    (∀ A K B E n2 n17 md ms P C T : Nat,
      2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 200000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280) ∧
    (∀ A K B E n2 n17 md ms P C T : Nat,
      2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 380000000 →
      B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
      B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
      7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes →
      231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280) ∧
    (yukon / 135 = 6671999447 ∧ yukon < 135 * mainCached200) :=
  ⟨uncached200, uncached380, no_135⟩

theorem witness_empty_item_push_cached_one_hundred_twelve_x_and_uncached_slopes_non_vacuous_and_tight :
    (mainCached200 = 8014558459 ∧ 112 * mainCached200 < yukon ∧
      yukon < 113 * mainCached200 ∧ mainCached380 = 11548778048 ∧
      77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380) ∧
    (mainUncached200 = 111614505033 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 208876066898 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) ∧
    (mainCached200 < GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 ∧
      mainCached380 < GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 - mainCached200 = 130855791 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 - mainCached380 = 121055210) := by
  refine ⟨cached_slopes, uncached_slopes, ?_⟩
  decide

theorem jumpdest_dual_lp_one_hundred_fourteen_bridge_non_vacuous_and_tight :
    (GuestExactSstoreCallLPAndJumpdestDualBoundMaster.callTicks = 67884 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached200 = 112163577490 ∧
      8 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached200 < yukon ∧
      yukon < 9 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached200 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached380 = 209425139355 ∧
      4 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached380 < yukon ∧
      yukon < 5 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached380) ∧
    (GuestExactSstoreCallLPAndJumpdestDualBoundMaster.costC 0 0 0 0 0 0 (inputBytes / 4) 2000000 = 6619898520 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.costC 0 0 0 0 0 0 (inputBytes / 4) 3800000 = 9859898520) ∧
    (GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 = 8145414250 ∧
      110 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 < yukon ∧
      yukon < 111 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 = 11669833258 ∧
      77 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 < yukon ∧
      yukon < 78 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380) :=
  ⟨⟨call_val_non_vacuous_and_tight, uncached_slopes_non_vacuous_and_tight⟩,
   cached_tight_non_vacuous_and_tight,
   cached_slopes_non_vacuous_and_tight⟩

theorem exact_sstore_sload_call_and_jumpdest_duality_one_hundred_fourteen_bridge_non_vacuous_and_tight :
    ((sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349 ∧
      maxCode = 65536 ∧ callGas = 126) ∧
     (sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
      sloadBaseTicks + 7 * 28 ≤ 18 * 100) ∧
     (200000000 / 12000 = 16666 ∧ 200000000 / 21000 = 9523)) ∧
    ((18 * callGas < maxCode ∧ 28 * (18 * callGas) < maxCode) ∧
     (jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon ∧
      yukon < 9 * jumpdestTicks 200000000) ∧
     (jumpdestTicks 380000000 = 197648252928 ∧ 4 * jumpdestTicks 380000000 < yukon ∧
      yukon < 5 * jumpdestTicks 380000000) ∧
     (12 * 8298113205 < jumpdestTicks 200000000)) ∧
    ((8298113205 + 134217712 = 8432330917 ∧ 106 * 8432330917 < yukon ∧
      yukon < 107 * 8432330917 ∧ 11858770499 + 134217712 = 11992988211 ∧
      75 * 11992988211 < yukon ∧ yukon < 76 * 11992988211) ∧
     (yukon - 106 * 8432330917 = 6892848272 ∧
      yukon - 75 * 11992988211 = 1245809649)) :=
  exact_sstore_sload_call_and_jumpdest_duality_one_hundred_twelve_bridge_non_vacuous_and_tight

theorem panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_fourteen_bridge_non_vacuous_and_tight
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
  panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_twelve_bridge_non_vacuous_and_tight arch
    prog wc ac perf n m

theorem pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_fourteen_bridge_non_vacuous_and_tight
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
  pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_twelve_bridge_non_vacuous_and_tight arch
    prog wc ac perf dc info n m w

theorem stack_remove_base_and_space_clock_one_hundred_fourteen_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_one_hundred_twelve_bridge_non_vacuous_and_tight source result
    postSource target register count pointer bounds jump

theorem one_hundred_fourteen_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredFourteenShape ∧
      oneHundredFourteenExplicitBudgets.length = 114 ∧
      oneHundredFourteenExplicitBudgets.getLast? = some 900715000000 ∧
      yukon - 900715000000 = 4925474 ∧
      (oneHundredFourteenExplicitBudgets.Pairwise (· < ·) ∧
        (∀ K ∈ oneHundredFourteenExplicitBudgets, K < 900719925474)) ∧
      (∀ K ∈ oneHundredFourteenExplicitBudgets,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(one_hundred_fourteen_budget_certificates_non_vacuous_and_tight cert).1,
   one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight.2.2,
   one_hundred_fourteen_budgets_under_yukon_non_vacuous_and_tight,
   (one_hundred_fourteen_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem witness_empty_item_push_one_hundred_fourteen_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3 ∧
      mainCached200 = 8014558459 ∧ 112 * mainCached200 < yukon ∧
      yukon < 113 * mainCached200 ∧ mainCached380 = 11548778048 ∧
      77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380) ∧
    (mainUncached200 = 111614505033 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 208876066898 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380 ∧
      yukon / 135 = 6671999447 ∧ yukon < 135 * mainCached200) ∧
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
    (OneHundredFourteenShape ∧
      oneHundredFourteenExplicitBudgets.length = 114 ∧
      oneHundredFourteenExplicitBudgets.getLast? = some 900715000000 ∧
      yukon - 900715000000 = 4925474 ∧
      yukon = 900719925474) ∧
    (∀ K ∈ oneHundredFourteenExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨leaf_counts.1, leaf_counts.2.1, leaf_counts.2.2, cached_slopes⟩,
   ⟨uncached_slopes.1,
    uncached_slopes.2.1,
    uncached_slopes.2.2.1,
    uncached_slopes.2.2.2.1,
    uncached_slopes.2.2.2.2.1,
    uncached_slopes.2.2.2.2.2,
    no_135.1,
    no_135.2⟩,
   ⟨panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_fourteen_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.1.1,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_fourteen_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.1.2,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_fourteen_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.2.1.1,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_fourteen_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.2.1.2⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(one_hundred_fourteen_budget_certificates_non_vacuous_and_tight cert).1,
    one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight.1,
    one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight.2.1,
    one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight.2.2,
    rfl⟩,
   (one_hundred_fourteen_budget_certificates_non_vacuous_and_tight cert).2⟩

#print axioms witness_empty_item_push_leaf_counts_and_cached_lp_non_vacuous_and_tight
#print axioms witness_empty_item_push_uncached_full_lp_non_vacuous_and_tight
#print axioms witness_empty_item_push_cached_one_hundred_twelve_x_and_uncached_slopes_non_vacuous_and_tight
#print axioms jumpdest_dual_lp_one_hundred_fourteen_bridge_non_vacuous_and_tight
#print axioms exact_sstore_sload_call_and_jumpdest_duality_one_hundred_fourteen_bridge_non_vacuous_and_tight
#print axioms panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_fourteen_bridge_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_fourteen_bridge_non_vacuous_and_tight
#print axioms stack_remove_base_and_space_clock_one_hundred_fourteen_bridge_non_vacuous_and_tight
#print axioms one_hundred_fourteen_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
#print axioms witness_empty_item_push_one_hundred_fourteen_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.WitnessEmptyItemPushOneHundredFourteenBudgetCampaignBridge
