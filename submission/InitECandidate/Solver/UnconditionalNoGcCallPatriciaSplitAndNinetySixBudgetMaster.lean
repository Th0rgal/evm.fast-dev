import InitECandidate.Solver.PatriciaSplitSixtyEightXAndNinetyTwoBudgetBridge
import InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
import InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact synthesis of the imported hand cost estimates, conditional on bounded
salted probe runs and memoized witness decoding. These arithmetic estimates are
not semantic runtime certificates; finite certificates remain conditional on
the base certificate. NoGcCall excludes direct GC calls; it does not constrain indirect targets.
StackRemove adds zero clock except at most one tick on a
final halt. Byte coupling assumes disjoint node bodies decoded once with DAG memoization. -/
namespace InitECandidate.Solver.UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural (NoGcCall NoTailHandler)
open Flapjack.Pancake.PanLang
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev Previous := PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318305, 880629318306]
def NinetySixShape : Prop :=
  portfolio.length = 96 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 94 = Previous ∧
  portfolio.drop 94 = [880629318305, 880629318306] ∧
  portfolio.getLast? = some 880629318306 ∧ yukon = 900719925474

theorem alloc_vs_path_bridge_non_vacuous_and_tight :
    3 * keys 200000000 = 285714 ∧ 65 * keys 200000000 = 6190470 :=
  PatriciaSplitSixtyEightXAndNinetyTwoBudgetBridge.alloc_vs_path_bridge_non_vacuous_and_tight

theorem level_sums_and_root_vals_bridge_non_vacuous_and_tight :
    (dirtyLevels 95238 = 5784185 ∧ dirtyLevels 180952 = 10927025) ∧
    (rootLevel 200000000 = 3847103205 ∧ rootLevel 380000000 = 7269663225) :=
  PatriciaSplitSixtyEightXAndNinetyTwoBudgetBridge.level_sums_and_root_vals_bridge_non_vacuous_and_tight

theorem single_trie_slopes_bridge_non_vacuous_and_tight :
    (main200Single = 13120876751 ∧ 68 * main200Single < yukon ∧ yukon < 69 * main200Single) ∧
    (main380Single = 20956676771 ∧ 42 * main380Single < yukon ∧ yukon < 43 * main380Single) :=
  PatriciaSplitSixtyEightXAndNinetyTwoBudgetBridge.single_trie_slopes_bridge_non_vacuous_and_tight

theorem multi_trie_and_floor_bridge_non_vacuous_and_tight :
    ((List.range 65).foldl (fun s _ => s + 95238) 0 = 65 * 95238) ∧
    13378055156 - rootOld 200000000 = 9273773546 :=
  PatriciaSplitSixtyEightXAndNinetyTwoBudgetBridge.multi_trie_and_floor_bridge_non_vacuous_and_tight

theorem panToStackRawCall_noGcCall_unconditional_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, NoGcCall y.2 = true :=
  PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackRawCall_noGcCall_unconditional arch prog wc ac perf

theorem panToStackAlloc_noAlloc_noGcCall_unconditional_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (DeclHOL width)) (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true :=
  PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackAlloc_noAlloc_noGcCall_unconditional arch prog wc ac perf

theorem panToStackRawCall_noTailHandler_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, NoTailHandler y.2 = true :=
  PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackRawCall_noTailHandler arch prog wc ac perf

theorem panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (DeclHOL width)) (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y :=
  PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf

theorem stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight {width : Nat} [NeZero width] (n m : Nat) :
    StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m) :=
  PanToStackAllocIdentityAndUnconditionalNoGcCall.stackAlloc_not_id_on_tagged_storeConsts n m

theorem pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) :
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc y.2 = true ∧
      NoGcCall y.2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
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
            {target with clock := clock + target.clock}) = (result, postTarget)) :=
  PanToStackAllocIdentityAndUnconditionalNoGcCall.pancake_stackAllocIdentity_noGc_zeroExtraClock arch prog wc ac perf dc info

theorem ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    NinetySixShape := by
  unfold NinetySixShape
  decide

theorem ninety_six_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetySixShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms alloc_vs_path_bridge_non_vacuous_and_tight
#print axioms level_sums_and_root_vals_bridge_non_vacuous_and_tight
#print axioms single_trie_slopes_bridge_non_vacuous_and_tight
#print axioms multi_trie_and_floor_bridge_non_vacuous_and_tight
#print axioms panToStackRawCall_noGcCall_unconditional_non_vacuous_and_tight
#print axioms panToStackAlloc_noAlloc_noGcCall_unconditional_non_vacuous_and_tight
#print axioms panToStackRawCall_noTailHandler_non_vacuous_and_tight
#print axioms panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight
#print axioms stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight
#print axioms ninety_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms ninety_six_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster
