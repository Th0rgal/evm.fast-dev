import InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster
import InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural
import InitECandidate.Solver.JointRlpArityFiftySixXAndEightyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact synthesis of the imported hand cost estimates, conditional on bounded
salted probe runs and memoized witness decoding. These arithmetic estimates are
not semantic runtime certificates; finite certificates remain conditional on
the base certificate. NoGcCall excludes direct GC calls; it does not constrain indirect targets.
StackRemove adds zero clock except at most one tick on a
final halt. Byte coupling assumes disjoint node bodies decoded once with DAG memoization. -/
namespace InitECandidate.Solver.SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc (StackNoAlloc)
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev Previous := JointRlpArityFiftySixXAndEightyEightBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318299, 880629318300]
def NinetyShape : Prop :=
  portfolio.length = 90 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 88 = Previous ∧
  portfolio.drop 88 = [880629318299, 880629318300] ∧
  portfolio.getLast? = some 880629318300 ∧ yukon = 900719925474

theorem joint_tight_and_branch_not_worst_non_vacuous_and_tight :
    (4 * 33554428 ≤ inputBytes ∧ jointCost 0 33554428 0 0 = 4630511064 ∧
    inputBytes / 4 = 33554428) ∧
    (jointCost 0 7456539 0 0 < jointCost 0 33554428 0 0) :=
  ⟨GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.joint_tight, GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.branch_not_worst⟩

theorem joint_val_non_vacuous_and_tight :
    (keccakBlocks = 18750986 ∧ jointNew = 4649262050 ∧
    separateOld - jointNew = 820219351) :=
  GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.joint_val

theorem main200_slope_non_vacuous_and_tight :
    (main200 = 14988667700 ∧ 60 * main200 < yukon ∧ yukon < 61 * main200) :=
  GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight :
    (main380 = 23095752530 ∧ 38 * main380 < yukon ∧ yukon < 39 * main380) :=
  GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.main380_slope

theorem margins_non_vacuous_and_tight :
    (yukon - 60 * main200 = 1399863474 ∧ yukon - 38 * main380 = 23081329334) :=
  GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.margins

theorem joint_bound_non_vacuous_and_tight (m n2 n17 h : Nat) (hb : 4 * m + 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes) :
    jointCost m n2 n17 h ≤ 138 * (inputBytes / 4) :=
  GuestSharedWitnessNodesBuildDecodeAndSixtyXMaster.joint_bound m n2 n17 h hb

theorem panToStackRawCall_noAlloc_unconditional_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true :=
  PanToStackRawCallNoAllocAndStackAllocStructural.panToStackRawCall_noAlloc_unconditional arch prog wc ac perf

theorem panToStackAlloc_noAlloc_noGcCall_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      NoGcCall y.2 = true →
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true :=
  PanToStackRawCallNoAllocAndStackAllocStructural.panToStackAlloc_noAlloc_noGcCall arch prog wc ac perf

theorem panToStackRemove_noAlloc_noGc_zeroExtraClock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) :
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      NoGcCall y.2 = true →
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    (∀ e ∈ InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
        arch prog wc ac perf dc, e.1 ≠ storeConstsStubLocation →
      InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true ∧
      InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts.Clean e.2 = true) ∧
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
  PanToStackRawCallNoAllocAndStackAllocStructural.panToStackRemove_noAlloc_noGc_zeroExtraClock arch prog wc ac perf dc info

theorem stackAllocComp_id_non_vacuous_and_tight {width : Nat} [NeZero width] :
    ∀ (n m : Nat) (p : HolProg width),
    StackNoAlloc p = true → InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt p = true →
    NoTailHandler p = true → StackAlloc.comp n m p = (p, m) :=
  PanToStackRawCallNoAllocAndStackAllocStructural.stackAllocComp_id

theorem ninety_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    NinetyShape := by
  unfold NinetyShape
  decide

theorem ninety_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetyShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨ninety_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (ninety_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms joint_tight_and_branch_not_worst_non_vacuous_and_tight
#print axioms joint_val_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms joint_bound_non_vacuous_and_tight
#print axioms panToStackRawCall_noAlloc_unconditional_non_vacuous_and_tight
#print axioms panToStackAlloc_noAlloc_noGcCall_non_vacuous_and_tight
#print axioms panToStackRemove_noAlloc_noGc_zeroExtraClock_non_vacuous_and_tight
#print axioms stackAllocComp_id_non_vacuous_and_tight
#print axioms ninety_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms ninety_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster
