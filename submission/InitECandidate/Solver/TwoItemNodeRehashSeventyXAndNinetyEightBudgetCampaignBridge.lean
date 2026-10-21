import InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster
import InitECandidate.Solver.MultiTrieGasSixtyEightXAndNinetySixBudgetCampaignBridge
import InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.TwoItemNodeRehashSeventyXAndNinetyEightBudgetCampaignBridge

open InitECandidate.Solver.GuestTwoItemNodeRehashAndSeventyXMaster
open InitECandidate.Solver.MultiTrieGasSixtyEightXAndNinetySixBudgetCampaignBridge
open InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster
open _root_.InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster
  (base200 base380 rw4)
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

abbrev ninetyEightExplicitFiniteKBugdetTable : List Nat :=
  MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster.portfolio

theorem two_item_node_rehash_ticks_and_near200_non_vacuous_and_tight :
    (beginTicks = 58 ∧ finish2Ticks = 227 ∧ keccakTicks532 = 146 ∧ node2Ticks = 439) ∧
    (24 * 5556 + 21 * 88888 ≤ 2000000 ∧
      7 * 0 + 22 * 5961084 + 4 * ((inputBytes - 22 * 5961084) / 4) ≤ inputBytes ∧
      6555470742 - cost 88888 (5961084 + 88888 + 5556) 0 0 5961084 ((inputBytes - 22 * 5961084) / 4)
        ≤ 20000) :=
  ⟨node2_val, near200⟩

theorem two_item_node_rehash_joint200_and_joint380_non_vacuous_and_tight :
    (∀ A K B E n2 n17 m : Nat, 24 * A + 21 * K ≤ 2000000 →
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
        ≤ 20000) :=
  ⟨GuestTwoItemNodeRehashAndSeventyXMaster.joint200,
   GuestTwoItemNodeRehashAndSeventyXMaster.joint380,
   near200⟩

theorem two_item_node_rehash_seventy_x_and_forty_six_x_slopes_non_vacuous_and_tight :
    (main200 = 12809345768 ∧ 70 * main200 < yukon ∧ yukon < 71 * main200) ∧
    (main380 = 19403346659 ∧ 46 * main380 < yukon ∧ yukon < 47 * main380) ∧
    (yukon - 70 * main200 = 4065721714 ∧ yukon - 46 * main380 = 8165979160) :=
  ⟨GuestTwoItemNodeRehashAndSeventyXMaster.main200_slope,
   GuestTwoItemNodeRehashAndSeventyXMaster.main380_slope,
   GuestTwoItemNodeRehashAndSeventyXMaster.margins⟩

theorem two_item_node_rehash_strictly_improves_multi_trie_sixty_eight_x_non_vacuous_and_tight :
    (main200 = 12809345768 ∧
      GuestMultiTrieGasAndLeafBranchRehashMaster.main200 = 13167715213 ∧
      main200 < GuestMultiTrieGasAndLeafBranchRehashMaster.main200 ∧
      GuestMultiTrieGasAndLeafBranchRehashMaster.main200 - main200 = 358369445 ∧
      70 * main200 < yukon ∧
      68 * GuestMultiTrieGasAndLeafBranchRehashMaster.main200 < yukon ∧
      yukon < 69 * GuestMultiTrieGasAndLeafBranchRehashMaster.main200) ∧
    (main380 = 19403346659 ∧
      GuestMultiTrieGasAndLeafBranchRehashMaster.main380 = 21085502713 ∧
      main380 < GuestMultiTrieGasAndLeafBranchRehashMaster.main380 ∧
      GuestMultiTrieGasAndLeafBranchRehashMaster.main380 - main380 = 1682156054 ∧
      46 * main380 < yukon ∧
      42 * GuestMultiTrieGasAndLeafBranchRehashMaster.main380 < yukon ∧
      yukon < 43 * GuestMultiTrieGasAndLeafBranchRehashMaster.main380) := by
  decide

theorem multi_trie_gas_unconditional_sixty_eight_x_campaign_non_vacuous_and_tight :
    ((base200 = 6235124040 ∧ base380 = 10648364040) ∧
     (∀ A K R : Nat, 24 * A + 21 * K ≤ 2000000 →
       R ≤ 82 * A + 63 * K → R ≤ 66 * A + 64 * K →
       7 * (R - 3 * K - 3 * A) ≤ GuestMultiTrieGasAndLeafBranchRehashMaster.inputBytes →
       rw4 A K R ≤ 27655360747) ∧
     (∀ A K R : Nat, 24 * A + 21 * K ≤ 3800000 →
       R ≤ 82 * A + 63 * K → R ≤ 66 * A + 64 * K →
       7 * (R - 3 * K - 3 * A) ≤ GuestMultiTrieGasAndLeafBranchRehashMaster.inputBytes →
       rw4 A K R ≤ 41673550747)) ∧
    (rw4 5555 88888 (82 * 5555 + 63 * 88888) = 27655104258 ∧
      24 * 5555 + 21 * 88888 ≤ 2000000 ∧
      82 * 5555 + 63 * 88888 ≤ 66 * 5555 + 64 * 88888 ∧
      7 * ((82 * 5555 + 63 * 88888) - 3 * 88888 - 3 * 5555) ≤
        GuestMultiTrieGasAndLeafBranchRehashMaster.inputBytes ∧
      27655360747 - rw4 5555 88888 (82 * 5555 + 63 * 88888) = 256489 ∧
      yukon - 68 * GuestMultiTrieGasAndLeafBranchRehashMaster.main200 = 5315290990 ∧
      yukon - 42 * GuestMultiTrieGasAndLeafBranchRehashMaster.main380 = 15128811528) :=
  ⟨multi_trie_gas_bases_and_joint_bounds_non_vacuous_and_tight,
   opt_tight_and_margins_non_vacuous_and_tight⟩

theorem panToStackAlloc_unconditional_noGcCall_and_id_ninety_eight_bridge_non_vacuous_and_tight
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
  panToStackAlloc_unconditional_noGcCall_and_id_bridge_non_vacuous_and_tight arch prog wc ac perf n m

theorem pancake_stackAllocIdentity_noGc_zeroExtraClock_two_item_bridge_non_vacuous_and_tight
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
  pancake_stackAllocIdentity_noGc_zeroExtraClock_multi_trie_bridge_non_vacuous_and_tight arch prog
    wc ac perf dc info n m w

theorem stack_remove_base_and_space_clock_ninety_eight_bridge_non_vacuous_and_tight
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
  stack_remove_base_and_space_clock_ninety_six_bridge_non_vacuous_and_tight source result postSource
    target register count pointer bounds jump

theorem ninety_eight_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetyEightShape ∧
      ninetyEightExplicitFiniteKBugdetTable.length = 98 ∧
      ninetyEightExplicitFiniteKBugdetTable.getLast? = some 880629318308 ∧
      yukon = 900719925474 ∧
      (∀ K ∈ ninetyEightExplicitFiniteKBugdetTable,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(ninety_eight_budget_certificates_non_vacuous_and_tight cert).1,
   (ninety_eight_budget_certificates_non_vacuous_and_tight cert).1.1,
   (ninety_eight_budget_certificates_non_vacuous_and_tight cert).1.2.2.2.2.2.1,
   rfl,
   (ninety_eight_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem two_item_node_rehash_seventy_x_and_ninety_eight_budget_campaign_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (n m a b : Nat) (c : Option Nat) (w : WordLocW width)
    (cert : CertificateAt 1212035192) :
    (beginTicks = 58 ∧ finish2Ticks = 227 ∧ keccakTicks532 = 146 ∧ node2Ticks = 439 ∧
      (∀ A K B E n2 n17 m : Nat, 24 * A + 21 * K ≤ 2000000 →
        B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
        B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
        7 * n2 + 22 * n17 + 4 * m ≤ inputBytes →
        9 * cost K B E n2 n17 m ≤ 58999236680) ∧
      (∀ A K B E n2 n17 m : Nat, 24 * A + 21 * K ≤ 3800000 →
        B + E ≤ 82 * A + 63 * K → B + E ≤ 66 * A + 64 * K →
        B ≤ n17 + K + A → E ≤ n2 + 2 * (K + A) →
        7 * n2 + 22 * n17 + 4 * m ≤ inputBytes →
        135 * cost K B E n2 n17 m ≤ 1179391270576) ∧
      24 * 5556 + 21 * 88888 ≤ 2000000 ∧
      7 * 0 + 22 * 5961084 + 4 * ((inputBytes - 22 * 5961084) / 4) ≤ inputBytes ∧
      6555470742 - cost 88888 (5961084 + 88888 + 5556) 0 0 5961084 ((inputBytes - 22 * 5961084) / 4)
        ≤ 20000) ∧
    (main200 = 12809345768 ∧ 70 * main200 < yukon ∧ yukon < 71 * main200 ∧
      main380 = 19403346659 ∧ 46 * main380 < yukon ∧ yukon < 47 * main380 ∧
      yukon - 70 * main200 = 4065721714 ∧ yukon - 46 * main380 = 8165979160 ∧
      main200 < GuestMultiTrieGasAndLeafBranchRehashMaster.main200 ∧
      main380 < GuestMultiTrieGasAndLeafBranchRehashMaster.main380) ∧
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
    (NinetyEightShape ∧
      ninetyEightExplicitFiniteKBugdetTable.length = 98 ∧
      ninetyEightExplicitFiniteKBugdetTable.getLast? = some 880629318308 ∧
      yukon = 900719925474) ∧
    (∀ K ∈ ninetyEightExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨node2_val.1,
    node2_val.2.1,
    node2_val.2.2.1,
    node2_val.2.2.2,
    GuestTwoItemNodeRehashAndSeventyXMaster.joint200,
    GuestTwoItemNodeRehashAndSeventyXMaster.joint380,
    near200.1,
    near200.2.1,
    near200.2.2⟩,
   ⟨GuestTwoItemNodeRehashAndSeventyXMaster.main200_slope.1,
    GuestTwoItemNodeRehashAndSeventyXMaster.main200_slope.2.1,
    GuestTwoItemNodeRehashAndSeventyXMaster.main200_slope.2.2,
    GuestTwoItemNodeRehashAndSeventyXMaster.main380_slope.1,
    GuestTwoItemNodeRehashAndSeventyXMaster.main380_slope.2.1,
    GuestTwoItemNodeRehashAndSeventyXMaster.main380_slope.2.2,
    GuestTwoItemNodeRehashAndSeventyXMaster.margins.1,
    GuestTwoItemNodeRehashAndSeventyXMaster.margins.2,
    two_item_node_rehash_strictly_improves_multi_trie_sixty_eight_x_non_vacuous_and_tight.1.2.2.1,
    two_item_node_rehash_strictly_improves_multi_trie_sixty_eight_x_non_vacuous_and_tight.2.2.2.1⟩,
   ⟨MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster.panToStackRawCall_noGcCall_unconditional_non_vacuous_and_tight
      arch prog wc ac perf,
    MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster.panToStackAlloc_noAlloc_noGcCall_unconditional_non_vacuous_and_tight
      arch prog wc ac perf,
    MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster.panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight
      arch prog wc ac perf,
    UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight
      n m⟩,
   ⟨stackNoSt_rejects_storeConsts a b c,
    clockOk_rejects_one_none,
    clockOk_rejects_two_halt w⟩,
   ⟨(ninety_eight_budget_certificates_non_vacuous_and_tight cert).1,
    (ninety_eight_budget_certificates_non_vacuous_and_tight cert).1.1,
    (ninety_eight_budget_certificates_non_vacuous_and_tight cert).1.2.2.2.2.2.1,
    rfl⟩,
   (ninety_eight_budget_certificates_non_vacuous_and_tight cert).2⟩

#print axioms two_item_node_rehash_ticks_and_near200_non_vacuous_and_tight
#print axioms two_item_node_rehash_joint200_and_joint380_non_vacuous_and_tight
#print axioms two_item_node_rehash_seventy_x_and_forty_six_x_slopes_non_vacuous_and_tight
#print axioms two_item_node_rehash_strictly_improves_multi_trie_sixty_eight_x_non_vacuous_and_tight
#print axioms multi_trie_gas_unconditional_sixty_eight_x_campaign_non_vacuous_and_tight
#print axioms panToStackAlloc_unconditional_noGcCall_and_id_ninety_eight_bridge_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_two_item_bridge_non_vacuous_and_tight
#print axioms stack_remove_base_and_space_clock_ninety_eight_bridge_non_vacuous_and_tight
#print axioms ninety_eight_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
#print axioms two_item_node_rehash_seventy_x_and_ninety_eight_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.TwoItemNodeRehashSeventyXAndNinetyEightBudgetCampaignBridge
