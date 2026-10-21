import InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster
import InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
import InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact synthesis of the imported hand cost estimates, conditional on bounded
salted probe runs and memoized witness decoding. These arithmetic estimates are
not semantic runtime certificates; finite certificates remain conditional on
the base certificate. StackRemove adds zero clock except at most one tick on a
final halt. Byte coupling assumes disjoint node bodies decoded once with DAG memoization. -/
namespace InitECandidate.Solver.JointRlpArityFiftySixXAndEightyEightBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestJointRlpArityByteConservationAndFiftyXMaster
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev Previous := ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318297, 880629318298]
def EightyEightShape : Prop :=
  portfolio.length = 88 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 86 = Previous ∧
  portfolio.drop 86 = [880629318297, 880629318298] ∧
  portfolio.getLast? = some 880629318298 ∧ yukon = 900719925474

theorem joint_tight_and_branch_count_non_vacuous_and_tight :
    (4 * 2 + 18 * 7456539 + 32 * 0 ≤ inputBytes ∧
    jointCost 2 7456539 0 = 2430831810 ∧ 2430831895 - 2430831810 = 85 ∧ inputBytes < 18 * 7456540) ∧
    (inputBytes / 18 = 7456539 ∧ 9 * 7456539 ≤ 2 * 33554428) :=
  ⟨GuestJointRlpArityByteConservationAndFiftyXMaster.joint_tight, GuestJointRlpArityByteConservationAndFiftyXMaster.branch_count⟩

theorem gain_non_vacuous_and_tight :
    (decodeProbesOld - decodeProbesNew = 8572986881) :=
  GuestJointRlpArityByteConservationAndFiftyXMaster.gain

theorem main200_slope_non_vacuous_and_tight :
    (main200 = 15808887051 ∧ 56 * main200 < yukon ∧
    yukon < 57 * main200 ∧ 50 * main200 < yukon) :=
  GuestJointRlpArityByteConservationAndFiftyXMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight :
    (main380 = 23915971881 ∧ 37 * main380 < yukon ∧ yukon < 38 * main380) :=
  GuestJointRlpArityByteConservationAndFiftyXMaster.main380_slope

theorem margins_and_build_dominates_non_vacuous_and_tight :
    (yukon - 56 * main200 = 15422250618 ∧ yukon - 37 * main380 = 15828965877) ∧
    (100 * 3038649506 > 19 * main200 ∧ 3038649506 > decodeProbesNew) :=
  ⟨GuestJointRlpArityByteConservationAndFiftyXMaster.margins, GuestJointRlpArityByteConservationAndFiftyXMaster.build_dominates⟩

theorem joint_bound_non_vacuous_and_tight (n2 n17 h : Nat) (hb : 4 * n2 + 18 * n17 + 32 * h ≤ inputBytes) :
    jointCost n2 n17 h ≤ 2430831895 :=
  GuestJointRlpArityByteConservationAndFiftyXMaster.joint_bound n2 n17 h hb

theorem stackAllocSections_clean_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config) :
    ∀ e ∈ stackAllocSections arch prog wc ac perf dc,
      e.1 = storeConstsStubLocation ∨ Clean e.2 = true :=
  StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections_clean arch prog wc ac perf dc

theorem liveTable_lookup_six_non_vacuous_and_tight {width : Nat} [NeZero width] (l : List (Nat × HolProg width)) :
    sptLookup storeConstsStubLocation (sptFromAList (liveSections l)) = none :=
  StackRemoveDeadStub6AndUnconditionalCodeNoSt.liveTable_lookup_six l

theorem panToStackRemove_body_zeroExtraClock_liveTable_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1, StackNoSt e.2 = true) →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget) :=
  StackRemoveDeadStub6AndUnconditionalCodeNoSt.panToStackRemove_body_zeroExtraClock_liveTable arch prog wc ac perf dc info

theorem fullTable_has_label6_non_vacuous_and_tight {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config) :
    (∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
    sptLookup storeConstsStubLocation
      (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none :=
  StackRemoveDeadStub6AndUnconditionalCodeNoSt.fullTable_has_label6 arch prog wc ac perf dc

theorem eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    EightyEightShape := by
  unfold EightyEightShape
  decide

theorem eighty_eight_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyEightShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms joint_tight_and_branch_count_non_vacuous_and_tight
#print axioms gain_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms margins_and_build_dominates_non_vacuous_and_tight
#print axioms joint_bound_non_vacuous_and_tight
#print axioms stackAllocSections_clean_non_vacuous_and_tight
#print axioms liveTable_lookup_six_non_vacuous_and_tight
#print axioms panToStackRemove_body_zeroExtraClock_liveTable_non_vacuous_and_tight
#print axioms fullTable_has_label6_non_vacuous_and_tight
#print axioms eighty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms eighty_eight_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.JointRlpArityFiftySixXAndEightyEightBudgetMaster
