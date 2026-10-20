import InitECandidate.Solver.PanToStackAndJointTransitionMaster
import InitECandidate.Solver.CleanToDirtyCoupledSixPassMaster
import InitECandidate.Solver.SelfContainedCleanToDirtyAndFullWordSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.ThirtyTwoBudgetJointAbsorptionMaster
open InitECandidate.Solver
open Flapjack InitE
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang Flapjack.Pancake.PanLang
open PanToStackNoStoreConsts WordPassesPreserveNoStoreConsts
open SelfContainedBoundedCertificate UnrolledTwelveCandidatePortfolio
open _root_.InitECandidate.Solver.GuestCoupledTxBlockStorageBound (kPanCoupled)
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S)
open _root_.InitECandidate.Solver.GuestJointTransitionInsertionBound (kIns)
open _root_.InitECandidate.Solver.GuestSstoreCleanToDirtyTransition (kPanTransition)

/-! Clock absorption is arithmetic. Every semantic certificate below retains
its explicit CertificateAt premise; a larger transition certificate alone does
not justify decreasing its execution bound. -/

variable {width : Nat} [NeZero width]
theorem pan_word_non_vacuous_and_tight (a : AsmArchitecture) (p : List (DeclHOL width)) :
    ∀ x ∈ panToWordCompileProgHOL a p, NoSt x.2.2 = true :=
  PanToStackAndJointTransitionMaster.pan_word_non_vacuous_and_tight a p

theorem stack_alloc_non_vacuous_and_tight (a : AsmArchitecture) (p : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ (WordToStack.Native.compileNative ac perf
      (WordToWord.compile wc ac (panToWordCompileProgHOL a p)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
        StackNoSt (StackAlloc.progComp y).2 = true :=
  PanToStackAndJointTransitionMaster.stack_alloc_non_vacuous_and_tight a p wc ac perf

theorem absorption_non_vacuous_and_tight (D W R : Nat) (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + kIns * R) ≤ S * S :=
  PanToStackAndJointTransitionMaster.absorption_non_vacuous_and_tight D W R h

theorem portfolio_non_vacuous_and_tight :
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧ CleanToDirtyCoupledSixPassMaster.unified.Pairwise (· < ·) :=
  ⟨CleanToDirtyCoupledSixPassMaster.unified_count_non_vacuous_and_tight, CleanToDirtyCoupledSixPassMaster.unified_order_non_vacuous_and_tight⟩

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified, InitE.Certificate (baselineWithFiniteK k) (.finite k) :=
  CleanToDirtyCoupledSixPassMaster.unified_certificates_non_vacuous_and_tight hc

def transitionTiers : List Nat :=
  [SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope3UnrolledK, SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope3K,
   SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope6UnrolledK, SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope6K]

def jointTiers : List Nat :=
  [PanToStackAndJointTransitionMaster.jointSlope3UnrolledK, PanToStackAndJointTransitionMaster.jointSlope3K, PanToStackAndJointTransitionMaster.jointSlope6UnrolledK, PanToStackAndJointTransitionMaster.jointSlope6K]

theorem projection_3_unrolled_non_vacuous_and_tight :
    SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope3UnrolledK ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy ∧
    PanToStackAndJointTransitionMaster.jointSlope3UnrolledK = SelfContainedWordSimpAndCoupledSynth.coupledSlope3UnrolledK ∧
    PanToStackAndJointTransitionMaster.jointSlope3UnrolledK ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy ∧
    PanToStackAndJointTransitionMaster.jointSlope3UnrolledK < SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope3UnrolledK ∧
    PanToStackAndJointTransitionMaster.jointSlope3UnrolledK + 12582900000 = SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope3UnrolledK := by decide

theorem certificate_3_unrolled_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK PanToStackAndJointTransitionMaster.jointSlope3UnrolledK) (.finite PanToStackAndJointTransitionMaster.jointSlope3UnrolledK) :=
  PanToStackAndJointTransitionMaster.jointSlope3UnrolledK_certificate_non_vacuous_and_tight hc

theorem projection_3_baseline_non_vacuous_and_tight :
    SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope3K ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy ∧
    PanToStackAndJointTransitionMaster.jointSlope3K = SelfContainedWordSimpAndCoupledSynth.coupledSlope3K ∧
    PanToStackAndJointTransitionMaster.jointSlope3K ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy ∧
    PanToStackAndJointTransitionMaster.jointSlope3K < SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope3K ∧
    PanToStackAndJointTransitionMaster.jointSlope3K + 12582900000 = SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope3K := by decide

theorem certificate_3_baseline_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK PanToStackAndJointTransitionMaster.jointSlope3K) (.finite PanToStackAndJointTransitionMaster.jointSlope3K) :=
  PanToStackAndJointTransitionMaster.jointSlope3K_certificate_non_vacuous_and_tight hc

theorem projection_6_unrolled_non_vacuous_and_tight :
    SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope6UnrolledK ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy ∧
    PanToStackAndJointTransitionMaster.jointSlope6UnrolledK = SelfContainedWordSimpAndCoupledSynth.coupledSlope6UnrolledK ∧
    PanToStackAndJointTransitionMaster.jointSlope6UnrolledK ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy ∧
    PanToStackAndJointTransitionMaster.jointSlope6UnrolledK < SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope6UnrolledK ∧
    PanToStackAndJointTransitionMaster.jointSlope6UnrolledK + 25165800000 = SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope6UnrolledK := by decide

theorem certificate_6_unrolled_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK PanToStackAndJointTransitionMaster.jointSlope6UnrolledK) (.finite PanToStackAndJointTransitionMaster.jointSlope6UnrolledK) :=
  PanToStackAndJointTransitionMaster.jointSlope6UnrolledK_certificate_non_vacuous_and_tight hc

theorem projection_6_baseline_non_vacuous_and_tight :
    SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope6K ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy ∧
    PanToStackAndJointTransitionMaster.jointSlope6K = SelfContainedWordSimpAndCoupledSynth.coupledSlope6K ∧
    PanToStackAndJointTransitionMaster.jointSlope6K ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy ∧
    PanToStackAndJointTransitionMaster.jointSlope6K < SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope6K ∧
    PanToStackAndJointTransitionMaster.jointSlope6K + 25165800000 = SelfContainedCleanToDirtyAndFullWordSynth.transitionSlope6K := by decide

theorem certificate_6_baseline_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK PanToStackAndJointTransitionMaster.jointSlope6K) (.finite PanToStackAndJointTransitionMaster.jointSlope6K) :=
  PanToStackAndJointTransitionMaster.jointSlope6K_certificate_non_vacuous_and_tight hc

theorem hierarchy_non_vacuous_and_tight :
    SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy.length = 22 ∧
    SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy.Pairwise (· < ·) := by
  have h := SelfContainedCleanToDirtyAndFullWordSynth.twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  exact ⟨h.1, h.2.1⟩

def absorbBudget (K : Nat) : Nat :=
  if K = CleanToDirtyCoupledSixPassMaster.transition3K then 23132 + 3 * kPanCoupled
  else if K = CleanToDirtyCoupledSixPassMaster.transition4K then 23132 + 4 * kPanCoupled
  else if K = CleanToDirtyCoupledSixPassMaster.transition5K then 23132 + 5 * kPanCoupled
  else if K = CleanToDirtyCoupledSixPassMaster.transition6K then 23132 + 6 * kPanCoupled
  else K

def absorbedPortfolio : List Nat := CleanToDirtyCoupledSixPassMaster.unified.map absorbBudget

theorem absorbed_count_non_vacuous_and_tight : absorbedPortfolio.length = 32 := by decide

theorem absorbed_bounds_non_vacuous_and_tight :
    ∀ K ∈ CleanToDirtyCoupledSixPassMaster.unified, 1212035192 ≤ absorbBudget K ∧ absorbBudget K ≤ K := by decide

theorem portfolio_transition_projection_non_vacuous_and_tight :
    ∀ n ∈ [3, 4, 5, 6],
      23132 + n * kPanTransition ∈ CleanToDirtyCoupledSixPassMaster.unified ∧
      absorbBudget (23132 + n * kPanTransition) = 23132 + n * kPanCoupled ∧
      absorbBudget (23132 + n * kPanTransition) < 23132 + n * kPanTransition ∧
      absorbBudget (23132 + n * kPanTransition) + n * 4194300000 =
        23132 + n * kPanTransition := by decide

theorem absorbed_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ K ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (absorbBudget K)) (.finite (absorbBudget K)) := by
  intro K hK
  exact certificate_lift_non_vacuous_and_tight _ _
    (absorbed_bounds_non_vacuous_and_tight K hK).1 hc

theorem hierarchy_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ K ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy,
      InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
  intro K hK
  apply certificate_lift_non_vacuous_and_tight 1212035192 K _ hc
  have hb : ∀ K ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy, 1212035192 ≤ K := by decide
  exact hb K hK

theorem joint_tiers_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ K ∈ jointTiers, InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
  intro K hK
  apply hierarchy_certificates_non_vacuous_and_tight hc K
  have hm : ∀ K ∈ jointTiers, K ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy := by decide
  exact hm K hK

theorem master_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy.length = 22 ∧
    (∀ K ∈ CleanToDirtyCoupledSixPassMaster.unified, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (∀ K ∈ CleanToDirtyCoupledSixPassMaster.unified, InitE.Certificate (baselineWithFiniteK (absorbBudget K))
      (.finite (absorbBudget K))) ∧
    (∀ K ∈ SelfContainedCleanToDirtyAndFullWordSynth.twentyTwoTierHierarchy,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨portfolio_non_vacuous_and_tight.1, hierarchy_non_vacuous_and_tight.1,
   portfolio_certificates_non_vacuous_and_tight hc,
   absorbed_certificates_non_vacuous_and_tight hc,
   hierarchy_certificates_non_vacuous_and_tight hc⟩

#print axioms pan_word_non_vacuous_and_tight
#print axioms stack_alloc_non_vacuous_and_tight
#print axioms absorption_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms portfolio_certificates_non_vacuous_and_tight
#print axioms projection_3_unrolled_non_vacuous_and_tight
#print axioms certificate_3_unrolled_non_vacuous_and_tight
#print axioms projection_3_baseline_non_vacuous_and_tight
#print axioms certificate_3_baseline_non_vacuous_and_tight
#print axioms projection_6_unrolled_non_vacuous_and_tight
#print axioms certificate_6_unrolled_non_vacuous_and_tight
#print axioms projection_6_baseline_non_vacuous_and_tight
#print axioms certificate_6_baseline_non_vacuous_and_tight
#print axioms hierarchy_non_vacuous_and_tight
#print axioms absorbed_count_non_vacuous_and_tight
#print axioms absorbed_bounds_non_vacuous_and_tight
#print axioms portfolio_transition_projection_non_vacuous_and_tight
#print axioms absorbed_certificates_non_vacuous_and_tight
#print axioms hierarchy_certificates_non_vacuous_and_tight
#print axioms joint_tiers_certificates_non_vacuous_and_tight
#print axioms master_non_vacuous_and_tight

end InitECandidate.Solver.ThirtyTwoBudgetJointAbsorptionMaster
