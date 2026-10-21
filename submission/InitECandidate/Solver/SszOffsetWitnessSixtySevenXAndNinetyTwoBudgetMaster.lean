import InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster
import InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural
import InitECandidate.Solver.SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact synthesis of the imported hand cost estimates, conditional on bounded
salted probe runs and memoized witness decoding. These arithmetic estimates are
not semantic runtime certificates; finite certificates remain conditional on
the base certificate. NoGcCall excludes direct GC calls; it does not constrain indirect targets.
StackRemove adds zero clock except at most one tick on a
final halt. Byte coupling assumes disjoint node bodies decoded once with DAG memoization. -/
namespace InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster
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

abbrev Previous := SharedWitnessSixtyXStackAllocNoGcAndNinetyBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318301, 880629318302]
def NinetyTwoShape : Prop :=
  portfolio.length = 92 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 90 = Previous ∧
  portfolio.drop 90 = [880629318301, 880629318302] ∧
  portfolio.getLast? = some 880629318302 ∧ yukon = 900719925474

theorem joint_tight_non_vacuous_and_tight :
    (4 * 33554428 ≤ inputBytes ∧ jointCost 33554428 0 0 0 = 3019898520 ∧
    138 * 4 < 90 * 7) :=
  GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.joint_tight

theorem joint_val_non_vacuous_and_tight :
    (jointSsz = 3038649506 ∧ jointPrev - jointSsz = 1610612544) :=
  GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.joint_val

theorem main200_slope_non_vacuous_and_tight :
    (main200 = 13378055156 ∧ 67 * main200 < yukon ∧ yukon < 68 * main200) :=
  GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight :
    (main380 = 21485139986 ∧ 41 * main380 < yukon ∧ yukon < 42 * main380) :=
  GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.main380_slope

theorem margins_and_sixty_eight_gap_non_vacuous_and_tight :
    (yukon - 67 * main200 = 4390230022 ∧ yukon - 41 * main380 = 19829186048) ∧
    (yukon / 68 = 13245881256 ∧ main200 - yukon / 68 = 132173900) :=
  ⟨GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.margins, GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.sixty_eight_gap⟩

theorem joint_bound_non_vacuous_and_tight (m n2 n17 h : Nat) (hb : 4 * m + 7 * n2 + 22 * n17 + 32 * h ≤ inputBytes) :
    jointCost m n2 n17 h ≤ 90 * (inputBytes / 4) :=
  GuestSszOffsetWitnessNodeMinBytesAndSixtyEightXMaster.joint_bound m n2 n17 h hb

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

theorem ninety_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    NinetyTwoShape := by
  unfold NinetyTwoShape
  decide

theorem ninety_two_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NinetyTwoShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨ninety_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (ninety_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms joint_tight_non_vacuous_and_tight
#print axioms joint_val_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_and_sixty_eight_gap_non_vacuous_and_tight
#print axioms joint_bound_non_vacuous_and_tight
#print axioms panToStackRawCall_noAlloc_unconditional_non_vacuous_and_tight
#print axioms panToStackAlloc_noAlloc_noGcCall_non_vacuous_and_tight
#print axioms panToStackRemove_noAlloc_noGc_zeroExtraClock_non_vacuous_and_tight
#print axioms stackAllocComp_id_non_vacuous_and_tight
#print axioms ninety_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms ninety_two_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SszOffsetWitnessSixtySevenXAndNinetyTwoBudgetMaster
