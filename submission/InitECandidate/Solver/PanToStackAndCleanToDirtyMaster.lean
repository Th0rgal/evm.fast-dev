import InitECandidate.Solver.PanToStackNoStoreConsts
import InitECandidate.Solver.GuestJointTransitionInsertionBound
import InitECandidate.Solver.CleanToDirtyCoupledSixPassMaster

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.PanToStackAndCleanToDirtyMaster
open InitE Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Pancake.PanLang
open InitECandidate.Solver
open PanToStackNoStoreConsts GuestCoupledTxBlockStorageBound
open GuestBs32BlockStorageEnvelope GuestJointBlockGasHtabBound
open GuestSstoreCleanToDirtyTransition
open UnrolledTwelveCandidatePortfolio SelfContainedBoundedCertificate

/-! Syntax excludes storeConsts in all non-stub compiled bodies. Arithmetic
absorption supplies an envelope, not a semantic execution proof. Certificate
lifting explicitly retains the baseline semantic certificate premise. -/
abbrev portfolio := CleanToDirtyCoupledSixPassMaster.unified
def absorbed6K : Nat := 23132 + 6 * kPanCoupled
def unrolled6K : Nat := 9332 + 6 * kPanCoupled
def oldUnrolled6K : Nat := 9332 + 6 * kPanTransition

variable {width : Nat} [NeZero width]

theorem chain_non_vacuous_and_tight (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
      (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoSt (StackAlloc.progComp y).2 = true :=
  panToStackAlloc_NoSt arch prog wc ac perf

theorem stub_exception_non_vacuous_and_tight (k : Nat) :
    StackNoSt (storeConstsStubNative (width := width) k) = false :=
  storeConstsStub_not_StackNoSt k

theorem joint_absorption_non_vacuous_and_tight (D W R : Nat)
    (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤ S * S :=
  GuestJointTransitionInsertionBound.joint_transition_absorbed D W R h

theorem joint_witness_non_vacuous_and_tight :
    21 * 47619 + 1000001 + 20 * 0 = S ∧
    47619 * (2 * 1000001 + 4 * 0) + GuestJointTransitionInsertionBound.kIns * 0 = 95238095238 :=
  GuestJointTransitionInsertionBound.joint_tight

theorem source_absorption_non_vacuous_and_tight (D W R Tloc : Nat)
    (h : 21 * D + W + 20 * R ≤ S) (hloc : Tloc ≤ 8 * 3994571428) :
    linear + Tloc + (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤ kPanCoupled :=
  GuestJointTransitionInsertionBound.kPan_with_transitions D W R h Tloc hloc

theorem source_improvement_non_vacuous_and_tight :
    kPanCoupled < kPanTransition ∧ kPanTransition - kPanCoupled = 4194300000 :=
  GuestJointTransitionInsertionBound.improves_transition

theorem source_margin_non_vacuous_and_tight :
    6 * kPanCoupled < yukon ∧ yukon - 6 * kPanCoupled = 115594540098 :=
  GuestJointTransitionInsertionBound.margin6

theorem standard_values_non_vacuous_and_tight :
    CleanToDirtyCoupledSixPassMaster.transition6K = 810291208508 ∧
    absorbed6K = 785125408508 ∧ absorbed6K < 900719925474 := by decide

theorem unrolled_values_non_vacuous_and_tight :
    oldUnrolled6K = 810291194708 ∧ unrolled6K = 785125394708 ∧
    unrolled6K < 900719925474 := by decide

theorem savings_non_vacuous_and_tight :
    CleanToDirtyCoupledSixPassMaster.transition6K - absorbed6K = 25165800000 ∧
    oldUnrolled6K - unrolled6K = 25165800000 ∧
    absorbed6K - unrolled6K = 13800 := by decide

theorem target_margin_non_vacuous_and_tight :
    900719925474 - absorbed6K = 115594516966 ∧
    900719925474 - unrolled6K = 115594530766 := by decide

theorem target_bound_non_vacuous_and_tight (D W R Tloc post : Nat)
    (h : 21 * D + W + 20 * R ≤ S) (hloc : Tloc ≤ 8 * 3994571428)
    (hexpand : post ≤ 6 * (linear + Tloc +
      (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R))) :
    23132 + post ≤ absorbed6K ∧ 9332 + post ≤ unrolled6K := by
  have hb := Nat.mul_le_mul_left 6 (source_absorption_non_vacuous_and_tight D W R Tloc h hloc)
  unfold absorbed6K unrolled6K
  constructor <;> omega

theorem saturated_non_vacuous_and_tight :
    ¬ 23132 + 6 * kPanCoupled ≤ absorbed6K - 1 ∧
    ¬ 9332 + 6 * kPanCoupled ≤ unrolled6K - 1 := by decide

theorem threshold_non_vacuous_and_tight (slope : Nat) :
    23132 + slope * kPanCoupled < 900719925474 ↔ slope ≤ 6 := by
  change 23132 + slope * 130854230896 < 900719925474 ↔ slope ≤ 6
  omega

theorem portfolio_count_non_vacuous_and_tight : portfolio.length = 32 :=
  CleanToDirtyCoupledSixPassMaster.unified_count_non_vacuous_and_tight

theorem portfolio_order_non_vacuous_and_tight : portfolio.Pairwise (· < ·) :=
  CleanToDirtyCoupledSixPassMaster.unified_order_non_vacuous_and_tight

theorem portfolio_bounds_non_vacuous_and_tight :
    ∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < 900719925474 :=
  CleanToDirtyCoupledSixPassMaster.unified_bounds_non_vacuous_and_tight

theorem portfolio_absorbed_member_non_vacuous_and_tight : absorbed6K ∈ portfolio := by decide

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) :=
  CleanToDirtyCoupledSixPassMaster.unified_certificates_non_vacuous_and_tight hc

theorem absorbed_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK absorbed6K) (.finite absorbed6K) :=
  portfolio_certificates_non_vacuous_and_tight hc _ portfolio_absorbed_member_non_vacuous_and_tight

theorem unrolled_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK unrolled6K) (.finite unrolled6K) :=
  certificate_lift_non_vacuous_and_tight _ _ (by decide) hc

theorem master_non_vacuous_and_tight (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (D W R Tloc : Nat) (h : 21 * D + W + 20 * R ≤ S)
    (hloc : Tloc ≤ 8 * 3994571428) (hc : CertificateAt 1212035192) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
      (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoSt (StackAlloc.progComp y).2 = true) ∧
    linear + Tloc + (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤ kPanCoupled ∧
    portfolio.length = 32 ∧
    (∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    InitE.Certificate (baselineWithFiniteK absorbed6K) (.finite absorbed6K) ∧
    InitE.Certificate (baselineWithFiniteK unrolled6K) (.finite unrolled6K) :=
  ⟨chain_non_vacuous_and_tight arch prog wc ac perf,
   source_absorption_non_vacuous_and_tight D W R Tloc h hloc,
   portfolio_count_non_vacuous_and_tight, portfolio_certificates_non_vacuous_and_tight hc,
   absorbed_certificate_non_vacuous_and_tight hc, unrolled_certificate_non_vacuous_and_tight hc⟩

#print axioms chain_non_vacuous_and_tight
#print axioms stub_exception_non_vacuous_and_tight
#print axioms joint_absorption_non_vacuous_and_tight
#print axioms joint_witness_non_vacuous_and_tight
#print axioms source_absorption_non_vacuous_and_tight
#print axioms source_improvement_non_vacuous_and_tight
#print axioms source_margin_non_vacuous_and_tight
#print axioms standard_values_non_vacuous_and_tight
#print axioms unrolled_values_non_vacuous_and_tight
#print axioms savings_non_vacuous_and_tight
#print axioms target_margin_non_vacuous_and_tight
#print axioms target_bound_non_vacuous_and_tight
#print axioms saturated_non_vacuous_and_tight
#print axioms threshold_non_vacuous_and_tight
#print axioms portfolio_count_non_vacuous_and_tight
#print axioms portfolio_order_non_vacuous_and_tight
#print axioms portfolio_bounds_non_vacuous_and_tight
#print axioms portfolio_absorbed_member_non_vacuous_and_tight
#print axioms portfolio_certificates_non_vacuous_and_tight
#print axioms absorbed_certificate_non_vacuous_and_tight
#print axioms unrolled_certificate_non_vacuous_and_tight
#print axioms master_non_vacuous_and_tight
end InitECandidate.Solver.PanToStackAndCleanToDirtyMaster
