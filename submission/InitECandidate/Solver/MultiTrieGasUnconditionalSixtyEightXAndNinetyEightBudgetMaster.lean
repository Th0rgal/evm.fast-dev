import InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster
import InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
import InitECandidate.Solver.UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact synthesis of the imported hand cost estimates, conditional on bounded
salted probe runs and memoized witness decoding. These arithmetic estimates are
not semantic runtime certificates; finite certificates remain conditional on
the base certificate. NoGcCall excludes direct GC calls; it does not constrain indirect targets.
StackRemove adds zero clock except at most one tick on a
final halt. Byte coupling assumes disjoint node bodies decoded once with DAG memoization. -/
namespace InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestMultiTrieGasAndLeafBranchRehashMaster
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

abbrev Previous := UnconditionalNoGcCallPatriciaSplitAndNinetySixBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318307, 880629318308]
def NinetyEightShape : Prop :=
  portfolio.length = 98 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 96 = Previous ∧
  portfolio.drop 96 = [880629318307, 880629318308] ∧
  portfolio.getLast? = some 880629318308 ∧ yukon = 900719925474

/-- The two imported dirty-node constraints combined, plus a many-trie witness. -/
theorem dirty_bounds_and_multi_worse_non_vacuous_and_tight (A K R : Nat)
    (h1 : R ≤ 82 * A + 63 * K) (h2 : R ≤ 66 * A + 64 * K) :
    R ≤ min (82 * A + 63 * K) (66 * A + 64 * K) ∧
    rw4 1 95236 (82 + 63 * 95236) < rw4 5555 88888 (82 * 5555 + 63 * 88888) :=
  ⟨Nat.le_min.mpr ⟨h1, h2⟩, GuestMultiTrieGasAndLeafBranchRehashMaster.multi_worse⟩

/-- Feasible near-optimum and its exact gap to the general upper bound;
this does not assert that the integer optimum equals the upper bound. -/
theorem opt_tight_and_margins_non_vacuous_and_tight :
    rw4 5555 88888 (82 * 5555 + 63 * 88888) = 27655104258 ∧
    24 * 5555 + 21 * 88888 ≤ 2000000 ∧
    82 * 5555 + 63 * 88888 ≤ 66 * 5555 + 64 * 88888 ∧
    7 * ((82 * 5555 + 63 * 88888) - 3 * 88888 - 3 * 5555) ≤ inputBytes ∧
    27655360747 - rw4 5555 88888 (82 * 5555 + 63 * 88888) = 256489 ∧
    yukon - 68 * main200 = 5315290990 ∧ yukon - 42 * main380 = 15128811528 := by
  decide

theorem joint200_non_vacuous_and_tight (A K R : Nat) (hg : 24 * A + 21 * K ≤ 2000000)
    (h1 : R ≤ 82 * A + 63 * K) (h2 : R ≤ 66 * A + 64 * K) (hw : 7 * (R - 3 * K - 3 * A) ≤ inputBytes) :
    rw4 A K R ≤ 27655360747 :=
  GuestMultiTrieGasAndLeafBranchRehashMaster.joint200 A K R hg h1 h2 hw

theorem joint380_non_vacuous_and_tight (A K R : Nat) (hg : 24 * A + 21 * K ≤ 3800000)
    (h1 : R ≤ 82 * A + 63 * K) (h2 : R ≤ 66 * A + 64 * K) (hw : 7 * (R - 3 * K - 3 * A) ≤ inputBytes) :
    rw4 A K R ≤ 41673550747 :=
  GuestMultiTrieGasAndLeafBranchRehashMaster.joint380 A K R hg h1 h2 hw

theorem main200_slope_non_vacuous_and_tight : main200 = 13167715213 ∧ 68 * main200 < yukon ∧ yukon < 69 * main200 :=
  GuestMultiTrieGasAndLeafBranchRehashMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight : main380 = 21085502713 ∧ 42 * main380 < yukon ∧ yukon < 43 * main380 :=
  GuestMultiTrieGasAndLeafBranchRehashMaster.main380_slope

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

theorem panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (DeclHOL width)) (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y :=
  PanToStackAllocIdentityAndUnconditionalNoGcCall.panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf

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

theorem ninety_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    NinetyEightShape := by
  unfold NinetyEightShape
  decide

theorem ninety_eight_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetyEightShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨ninety_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (ninety_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms dirty_bounds_and_multi_worse_non_vacuous_and_tight
#print axioms opt_tight_and_margins_non_vacuous_and_tight
#print axioms joint200_non_vacuous_and_tight
#print axioms joint380_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms panToStackRawCall_noGcCall_unconditional_non_vacuous_and_tight
#print axioms panToStackAlloc_noAlloc_noGcCall_unconditional_non_vacuous_and_tight
#print axioms panToStackAlloc_progComp_eq_id_of_ne_six_non_vacuous_and_tight
#print axioms pancake_stackAllocIdentity_noGc_zeroExtraClock_non_vacuous_and_tight
#print axioms ninety_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms ninety_eight_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.MultiTrieGasUnconditionalSixtyEightXAndNinetyEightBudgetMaster
