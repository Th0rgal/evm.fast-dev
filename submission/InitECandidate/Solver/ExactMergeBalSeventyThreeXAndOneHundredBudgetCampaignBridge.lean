import InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster
import InitECandidate.Solver.TwoItemNodeRehashSeventyXAndNinetyEightBudgetCampaignBridge
import InitECandidate.Solver.TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredBudgetCampaignBridge

open InitECandidate.Solver.GuestExactMergeBalPrologueAndSeventyFiveXMaster
open InitECandidate.Solver.TwoItemNodeRehashSeventyXAndNinetyEightBudgetCampaignBridge
open InitECandidate.Solver.TwoItemNodeRehashSeventyXAndOneHundredBudgetMaster
open _root_.InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster
  (beginTicks finish2Ticks keccakTicks532 node2Ticks inputBytes cost near200)
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

theorem exact_merge_bal_vals_and_entry_charge_non_vacuous_and_tight :
    (mergeTicks 200000000 = 65422992 ∧ mergeTicks 380000000 = 101802000 ∧
      mergeTicks 380000000 < 500000000) ∧
    (balTicks 200000000 = 144000000 ∧ balTicks 380000000 = 273600000) ∧
    (12 + 2 * 8 ≤ 60 ∧ 2100 / 100 = 21) :=
  ⟨merge_vals, bal_vals, entry_charge⟩

theorem exact_merge_bal_seventy_three_x_and_forty_seven_x_slopes_non_vacuous_and_tight :
    (main200 = 12218768760 ∧ 73 * main200 < yukon ∧ yukon < 74 * main200) ∧
    (main380 = 18978748659 ∧ 47 * main380 < yukon ∧ yukon < 48 * main380) ∧
    (yukon / 75 = 12009599006 ∧ yukon < 75 * main200) ∧
    (yukon - 73 * main200 = 8749805994 ∧ yukon - 47 * main380 = 8718738501) :=
  ⟨GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200_slope,
   GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380_slope,
   no_75,
   GuestExactMergeBalPrologueAndSeventyFiveXMaster.margins⟩

theorem exact_merge_bal_strictly_improves_two_item_seventy_x_non_vacuous_and_tight :
    (main200 = 12218768760 ∧
      GuestTwoItemNodeRehashAndSeventyXMaster.main200 = 12809345768 ∧
      main200 < GuestTwoItemNodeRehashAndSeventyXMaster.main200 ∧
      GuestTwoItemNodeRehashAndSeventyXMaster.main200 - main200 = 590577008 ∧
      73 * main200 < yukon ∧
      70 * GuestTwoItemNodeRehashAndSeventyXMaster.main200 < yukon ∧
      yukon < 71 * GuestTwoItemNodeRehashAndSeventyXMaster.main200) ∧
    (main380 = 18978748659 ∧
      GuestTwoItemNodeRehashAndSeventyXMaster.main380 = 19403346659 ∧
      main380 < GuestTwoItemNodeRehashAndSeventyXMaster.main380 ∧
      GuestTwoItemNodeRehashAndSeventyXMaster.main380 - main380 = 424598000 ∧
      47 * main380 < yukon ∧
      46 * GuestTwoItemNodeRehashAndSeventyXMaster.main380 < yukon ∧
      yukon < 47 * GuestTwoItemNodeRehashAndSeventyXMaster.main380) := by
  decide

theorem two_item_node_rehash_seventy_x_and_lp_campaign_non_vacuous_and_tight :
    ((beginTicks = 58 ∧ finish2Ticks = 227 ∧ keccakTicks532 = 146 ∧ node2Ticks = 439) ∧
     (24 * 5556 + 21 * 88888 ≤ 2000000 ∧
       7 * 0 + 22 * 5961084 + 4 * ((inputBytes - 22 * 5961084) / 4) ≤ inputBytes ∧
       6555470742 - cost 88888 (5961084 + 88888 + 5556) 0 0 5961084 ((inputBytes - 22 * 5961084) / 4)
         ≤ 20000)) ∧
    ((∀ A K B E n2 n17 m : Nat, 24 * A + 21 * K ≤ 2000000 →
       B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
       B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
       7 * n2 + 22 * n17 + 4 * m ≤ inputBytes →
       9 * cost K B E n2 n17 m ≤ 58999236680) ∧
     (∀ A K B E n2 n17 m : Nat, 24 * A + 21 * K ≤ 3800000 →
       B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
       B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
       7 * n2 + 22 * n17 + 4 * m ≤ inputBytes →
       135 * cost K B E n2 n17 m ≤ 1179391270576) ∧
     (24 * 5556 + 21 * 88888 ≤ 2000000 ∧
       7 * 0 + 22 * 5961084 + 4 * ((inputBytes - 22 * 5961084) / 4) ≤ inputBytes ∧
       6555470742 - cost 88888 (5961084 + 88888 + 5556) 0 0 5961084 ((inputBytes - 22 * 5961084) / 4)
         ≤ 20000)) :=
  ⟨two_item_node_rehash_ticks_and_near200_non_vacuous_and_tight,
   two_item_node_rehash_joint200_and_joint380_non_vacuous_and_tight⟩

theorem two_item_seventy_x_vs_multi_trie_sixty_eight_x_campaign_non_vacuous_and_tight :
    ((GuestMultiTrieGasAndLeafBranchRehashMaster.main200 = 13167715213 ∧
      GuestTwoItemNodeRehashAndSeventyXMaster.main200 <
        GuestMultiTrieGasAndLeafBranchRehashMaster.main200 ∧
      68 * GuestMultiTrieGasAndLeafBranchRehashMaster.main200 < yukon ∧
      yukon < 69 * GuestMultiTrieGasAndLeafBranchRehashMaster.main200 ∧
      GuestMultiTrieGasAndLeafBranchRehashMaster.main200 -
        GuestTwoItemNodeRehashAndSeventyXMaster.main200 = 358369445) ∧
     (GuestMultiTrieGasAndLeafBranchRehashMaster.main380 = 21085502713 ∧
      GuestTwoItemNodeRehashAndSeventyXMaster.main380 <
        GuestMultiTrieGasAndLeafBranchRehashMaster.main380 ∧
      42 * GuestMultiTrieGasAndLeafBranchRehashMaster.main380 < yukon ∧
      yukon < 43 * GuestMultiTrieGasAndLeafBranchRehashMaster.main380 ∧
      GuestMultiTrieGasAndLeafBranchRehashMaster.main380 -
        GuestTwoItemNodeRehashAndSeventyXMaster.main380 = 1682156054)) ∧
    (yukon - 70 * GuestTwoItemNodeRehashAndSeventyXMaster.main200 = 4065721714 ∧
      yukon - 46 * GuestTwoItemNodeRehashAndSeventyXMaster.main380 = 8165979160) :=
  ⟨⟨improvement200_non_vacuous_and_tight, improvement380_non_vacuous_and_tight⟩,
   margins_non_vacuous_and_tight⟩

theorem panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_bridge_non_vacuous_and_tight
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
  panToStackAlloc_unconditional_noGcCall_and_id_ninety_eight_bridge_non_vacuous_and_tight arch prog
    wc ac perf n m

theorem pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_bridge_non_vacuous_and_tight
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
  pancake_stackAllocIdentity_noGc_zeroExtraClock_two_item_bridge_non_vacuous_and_tight arch prog wc
    ac perf dc info n m w

theorem stack_remove_base_and_space_clock_one_hundred_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_ninety_eight_bridge_non_vacuous_and_tight source result
    postSource target register count pointer bounds jump

theorem one_hundred_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredShape ∧
      oneHundredExplicitFiniteKBugdetTable.length = 100 ∧
      oneHundredExplicitFiniteKBugdetTable.getLast? = some 886500180428 ∧
      900719925474 - 886500180428 = 14219745046 ∧
      yukon - 886500180428 = 14219745046 ∧
      (∀ K ∈ oneHundredExplicitFiniteKBugdetTable,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(one_hundred_budget_certificates_non_vacuous_and_tight cert).1,
   one_hundred_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_budget_last_margin_non_vacuous_and_tight.2.2.1,
   one_hundred_budget_last_margin_non_vacuous_and_tight.2.2.2,
   (one_hundred_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem exact_merge_bal_seventy_three_x_and_one_hundred_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (mergeTicks 200000000 = 65422992 ∧ mergeTicks 380000000 = 101802000 ∧
      mergeTicks 380000000 < 500000000 ∧
      balTicks 200000000 = 144000000 ∧ balTicks 380000000 = 273600000 ∧
      12 + 2 * 8 ≤ 60 ∧ 2100 / 100 = 21) ∧
    (main200 = 12218768760 ∧ 73 * main200 < yukon ∧ yukon < 74 * main200 ∧
      main380 = 18978748659 ∧ 47 * main380 < yukon ∧ yukon < 48 * main380 ∧
      yukon / 75 = 12009599006 ∧ yukon < 75 * main200 ∧
      yukon - 73 * main200 = 8749805994 ∧ yukon - 47 * main380 = 8718738501 ∧
      main200 < GuestTwoItemNodeRehashAndSeventyXMaster.main200 ∧
      GuestTwoItemNodeRehashAndSeventyXMaster.main200 - main200 = 590577008 ∧
      main380 < GuestTwoItemNodeRehashAndSeventyXMaster.main380 ∧
      GuestTwoItemNodeRehashAndSeventyXMaster.main380 - main380 = 424598000) ∧
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
    (OneHundredShape ∧
      oneHundredExplicitFiniteKBugdetTable.length = 100 ∧
      oneHundredExplicitFiniteKBugdetTable.getLast? = some 886500180428 ∧
      yukon - 886500180428 = 14219745046 ∧
      yukon = 900719925474) ∧
    (∀ K ∈ oneHundredExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨merge_vals.1,
    merge_vals.2.1,
    merge_vals.2.2,
    bal_vals.1,
    bal_vals.2,
    entry_charge.1,
    entry_charge.2⟩,
   ⟨GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200_slope.1,
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200_slope.2.1,
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.main200_slope.2.2,
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380_slope.1,
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380_slope.2.1,
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.main380_slope.2.2,
    no_75.1,
    no_75.2,
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.margins.1,
    GuestExactMergeBalPrologueAndSeventyFiveXMaster.margins.2,
    exact_merge_bal_strictly_improves_two_item_seventy_x_non_vacuous_and_tight.1.2.2.1,
    exact_merge_bal_strictly_improves_two_item_seventy_x_non_vacuous_and_tight.1.2.2.2.1,
    exact_merge_bal_strictly_improves_two_item_seventy_x_non_vacuous_and_tight.2.2.2.1,
    exact_merge_bal_strictly_improves_two_item_seventy_x_non_vacuous_and_tight.2.2.2.2.1⟩,
   ⟨panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.1.1,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.1.2,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.2.1.1,
    panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_bridge_non_vacuous_and_tight
      arch prog wc ac perf n m |>.2.1.2⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(one_hundred_budget_certificates_non_vacuous_and_tight cert).1,
    one_hundred_budget_last_margin_non_vacuous_and_tight.1,
    one_hundred_budget_last_margin_non_vacuous_and_tight.2.1,
    one_hundred_budget_last_margin_non_vacuous_and_tight.2.2.2,
    rfl⟩,
   (one_hundred_budget_certificates_non_vacuous_and_tight cert).2⟩

#print axioms exact_merge_bal_vals_and_entry_charge_non_vacuous_and_tight
#print axioms exact_merge_bal_seventy_three_x_and_forty_seven_x_slopes_non_vacuous_and_tight
#print axioms exact_merge_bal_strictly_improves_two_item_seventy_x_non_vacuous_and_tight
#print axioms two_item_node_rehash_seventy_x_and_lp_campaign_non_vacuous_and_tight
#print axioms two_item_seventy_x_vs_multi_trie_sixty_eight_x_campaign_non_vacuous_and_tight
#print axioms panToStackAlloc_unconditional_noGcCall_and_id_one_hundred_bridge_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_bridge_non_vacuous_and_tight
#print axioms stack_remove_base_and_space_clock_one_hundred_bridge_non_vacuous_and_tight
#print axioms one_hundred_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
#print axioms exact_merge_bal_seventy_three_x_and_one_hundred_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.ExactMergeBalSeventyThreeXAndOneHundredBudgetCampaignBridge
