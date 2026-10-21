import InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster
import InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
import InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact synthesis of the imported hand cost estimates, conditional on bounded
salted probe runs and memoized witness decoding. These arithmetic estimates are
not semantic runtime certificates; finite certificates remain conditional on
the base certificate. NoGcCall excludes direct GC calls; it does not constrain indirect targets.
StackRemove adds zero clock except at most one tick on a
final halt. Byte coupling assumes disjoint node bodies decoded once with DAG memoization. -/
namespace InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural (NoGcCall)
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

abbrev Previous := SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318303, 880629318304]
def NinetyFourShape : Prop :=
  portfolio.length = 94 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 92 = Previous ∧
  portfolio.drop 92 = [880629318303, 880629318304] ∧
  portfolio.getLast? = some 880629318304 ∧ yukon = 900719925474

theorem alloc_vs_path_non_vacuous_and_tight : 3 * keys 200000000 = 285714 ∧ 65 * keys 200000000 = 6190470 :=
  GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.alloc_vs_path

theorem level_sums_non_vacuous_and_tight : dirtyLevels 95238 = 5784185 ∧ dirtyLevels 180952 = 10927025 ∧
    dirtyLevels 95238 < 65 * 95238 :=
  GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.level_sums

theorem root_vals_non_vacuous_and_tight : rootLevel 200000000 = 3847103205 ∧ rootLevel 380000000 = 7269663225 ∧
    rootOld 200000000 - rootLevel 200000000 = 257178405 :=
  GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.root_vals

theorem main200_single_non_vacuous_and_tight : main200Single = 13120876751 ∧ 68 * main200Single < yukon ∧
    yukon < 69 * main200Single :=
  GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main200_single

theorem main380_single_non_vacuous_and_tight : main380Single = 20956676771 ∧ 42 * main380Single < yukon ∧
    yukon < 43 * main380Single :=
  GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.main380_single

theorem multi_trie_non_vacuous_and_tight : (List.range 65).foldl (fun s _ => s + 95238) 0 = 65 * 95238 ∧
    67 * 13378055156 < yukon ∧ yukon < 68 * 13378055156 :=
  GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.multi_trie

theorem no_sub_ten_non_vacuous_and_tight : 13378055156 - rootOld 200000000 = 9273773546 ∧
    9273773546 < 10000000000 ∧ 10000000000 < 13120876751 :=
  GuestPatriciaSplitDirtyNodeCountAndSubTenBillionMaster.no_sub_ten

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

theorem ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    NinetyFourShape := by
  unfold NinetyFourShape
  decide

theorem ninety_four_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetyFourShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms alloc_vs_path_non_vacuous_and_tight
#print axioms level_sums_non_vacuous_and_tight
#print axioms root_vals_non_vacuous_and_tight
#print axioms main200_single_non_vacuous_and_tight
#print axioms main380_single_non_vacuous_and_tight
#print axioms multi_trie_non_vacuous_and_tight
#print axioms no_sub_ten_non_vacuous_and_tight
#print axioms panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight
#print axioms stackAlloc_not_id_on_tagged_storeConsts_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight
#print axioms ninety_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms ninety_four_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.PatriciaSplitStackAllocIdentityAndNinetyFourBudgetMaster
