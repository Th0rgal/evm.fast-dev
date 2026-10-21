import InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
import InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
import InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact synthesis of the imported hand cost estimates, conditional on bounded
salted probe runs and memoized witness decoding. These arithmetic estimates are
not semantic runtime certificates; finite certificates remain conditional on
the base certificate. StackRemove adds zero clock except at most one tick on a
final halt. Byte coupling assumes disjoint node bodies decoded once with DAG memoization. -/
namespace InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
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

abbrev Previous := SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318295, 880629318296]
def EightySixShape : Prop :=
  portfolio.length = 86 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 84 = Previous ∧
  portfolio.drop 84 = [880629318295, 880629318296] ∧
  portfolio.getLast? = some 880629318296 ∧ yukon = 900719925474

theorem refs_tight_and_ratio_non_vacuous_and_tight :
    (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
    (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) :=
  ⟨GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.refs_tight, GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.ratio⟩

theorem probe_vals_and_gain_non_vacuous_and_tight :
    (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
    probes 380000000 = 68115248) ∧
    (8589933568 - probes 200000000 = 8523258320) :=
  ⟨GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.probe_vals, GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.gain⟩

theorem main200_slope_non_vacuous_and_tight :
    (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) :=
  GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main200_slope

theorem main380_slope_and_margins_non_vacuous_and_tight :
    (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
    (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) :=
  ⟨GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.main380_slope, GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.margins⟩

theorem decode_dominates_and_tree_no_coupling_non_vacuous_and_tight :
    (100 * 10938743528 > 44 * main200) ∧
    (2 * 8 * hashRefs < 2 * 8 * 1110441952) :=
  ⟨GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.decode_dominates, GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.tree_no_coupling⟩

theorem refs_bound_non_vacuous_and_tight (h : Nat) (hb : 33 * h ≤ inputBytes) : h ≤ 4067203 :=
  GuestByteCoupledWitnessResolveAndThirtyFiveXMaster.refs_bound h hb

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

theorem eighty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    EightySixShape := by
  unfold EightySixShape
  decide

theorem eighty_six_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightySixShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨eighty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (eighty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms refs_tight_and_ratio_non_vacuous_and_tight
#print axioms probe_vals_and_gain_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_and_margins_non_vacuous_and_tight
#print axioms decode_dominates_and_tree_no_coupling_non_vacuous_and_tight
#print axioms refs_bound_non_vacuous_and_tight
#print axioms stackAllocSections_clean_non_vacuous_and_tight
#print axioms liveTable_lookup_six_non_vacuous_and_tight
#print axioms panToStackRemove_body_zeroExtraClock_liveTable_non_vacuous_and_tight
#print axioms fullTable_has_label6_non_vacuous_and_tight
#print axioms eighty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms eighty_six_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.ByteCoupledWitnessThirtySixXAndEightySixBudgetMaster
