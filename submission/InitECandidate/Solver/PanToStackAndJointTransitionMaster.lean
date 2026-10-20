import InitECandidate.Solver.PanToStackNoStoreConsts
import InitECandidate.Solver.GuestJointTransitionInsertionBound
import InitECandidate.Solver.FullWordToWordAndTransitionMaster

set_option autoImplicit false

/-! Pancake body closure and jointly absorbed transition budgets.
The fixed storeConsts stub is excluded explicitly. Clock equations use the existing
allowance model; semantic target certificates retain their certificate premise. -/
namespace InitECandidate.Solver.PanToStackAndJointTransitionMaster
open Flapjack InitE
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang Flapjack.Pancake.PanLang
open InitECandidate.Solver
open PanToStackNoStoreConsts WordPassesPreserveNoStoreConsts
open _root_.InitECandidate.Solver.GuestCoupledTxBlockStorageBound (kPanCoupled)
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open _root_.InitECandidate.Solver.GuestJointTransitionInsertionBound (kIns)
open _root_.InitECandidate.Solver.Bs32EnvelopeTwelveCandidateBridge (yukonCeiling)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

section Bodies
variable {width : Nat} [NeZero width]

theorem pan_word_non_vacuous_and_tight (a : AsmArchitecture) (p : List (DeclHOL width)) :
    ∀ x ∈ panToWordCompileProgHOL a p, NoSt x.2.2 = true := panToWord_NoSt a p

theorem pan_wordword_non_vacuous_and_tight (a : AsmArchitecture) (p : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) :
    ∀ x ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL a p)).2,
      NoSt x.2.2 = true := panToWordToWord_NoSt a p wc ac

theorem comp_native_non_vacuous_and_tight (ac : AsmConfigExact width) (perf : Bool)
    (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) (h : NoSt p = true) :
    StackNoSt (WordToStack.Native.compNative ac perf p bs kf).1 = true :=
  s_compNative ac perf p bs kf h

theorem stack_bodies_non_vacuous_and_tight (a : AsmArchitecture) (p : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ (WordToStack.Native.compileNative ac perf
      (WordToWord.compile wc ac (panToWordCompileProgHOL a p)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoSt y.2 = true :=
  s_compileNative_bodies ac perf _ (panToWordToWord_NoSt a p wc ac)

theorem stack_alloc_non_vacuous_and_tight (a : AsmArchitecture) (p : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ (WordToStack.Native.compileNative ac perf
      (WordToWord.compile wc ac (panToWordCompileProgHOL a p)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
        StackNoSt (StackAlloc.progComp y).2 = true := panToStackAlloc_NoSt a p wc ac perf

/-- Actual input function bodies, before the fixed stubs are prepended. -/
theorem every_function_non_vacuous_and_tight (a : AsmArchitecture) (p : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (rc : Nat)
    (bs : AppList (BitVec width) × Nat) :
    ∀ y ∈ (WordToStack.Native.compileWordToStackNative ac perf rc
      (WordToWord.compile wc ac (panToWordCompileProgHOL a p)).2 bs).1,
      StackNoSt (StackAlloc.progComp y).2 = true := by
  intro y hy
  exact s_progComp y (s_compileWordToStack ac perf rc _ bs
    (panToWordToWord_NoSt a p wc ac) y hy)

theorem stub_exception_non_vacuous_and_tight (k : Nat) :
    StackNoSt (WordToStack.Native.storeConstsStubNative (width := width) k) = false :=
  storeConstsStub_not_StackNoSt k

theorem word_allowance_non_vacuous_and_tight (a : AsmArchitecture) (p : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width)
    (x : Nat × Nat × WordLangProgHOL (BitVec width))
    (hx : x ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL a p)).2) :
    StackRemoveStoreConstsZeroBridge.storeConstsAllowance x.2.2 = 0 :=
  WordToWordTailNoStoreConstsBridge.noSt_allowance_zero _ (panToWordToWord_NoSt a p wc ac x hx)

theorem stack_clock_non_vacuous_and_tight (a : AsmArchitecture) (p : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width)
    (x : Nat × Nat × WordLangProgHOL (BitVec width))
    (hx : x ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL a p)).2) (k_sn : Nat) :
    SelfContainedMidPassesAndSloadSynth.stackRemoveClockWithAllowance k_sn x.2.2 = k_sn + 1 ∧
    SelfContainedQuadraticEnvelopeCert.C_sr_probe = 1 := by
  constructor
  · unfold SelfContainedMidPassesAndSloadSynth.stackRemoveClockWithAllowance
    rw [word_allowance_non_vacuous_and_tight a p wc ac x hx, Nat.add_zero]
  · rfl
end Bodies

theorem absorption_non_vacuous_and_tight (D W R : Nat) (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + kIns * R) ≤ S * S :=
  GuestJointTransitionInsertionBound.joint_transition_absorbed D W R h

theorem envelope_non_vacuous_and_tight (D W R : Nat) (h : 21 * D + W + 20 * R ≤ S)
    (T : Nat) (ht : T ≤ 8 * 3994571428) :
    linear + T + (D * (2 * W + 4 * R) + kIns * R) ≤ kPanCoupled :=
  GuestJointTransitionInsertionBound.kPan_with_transitions D W R h T ht

theorem absorption_witness_non_vacuous_and_tight :
    21 * 47619 + 1000001 + 20 * 0 = S ∧
    47619 * (2 * 1000001 + 4 * 0) + kIns * 0 = 95238095238 :=
  GuestJointTransitionInsertionBound.joint_tight

theorem source_saving_non_vacuous_and_tight :
    kPanCoupled < GuestSstoreCleanToDirtyTransition.kPanTransition ∧
    GuestSstoreCleanToDirtyTransition.kPanTransition - kPanCoupled = 4194300000 :=
  GuestJointTransitionInsertionBound.improves_transition

theorem margin6_non_vacuous_and_tight :
    6 * kPanCoupled < yukonCeiling ∧ yukonCeiling - 6 * kPanCoupled = 115594540098 :=
  GuestJointTransitionInsertionBound.margin6

theorem threshold_non_vacuous_and_tight (k : Nat) :
    k * kPanCoupled < yukonCeiling ↔ k ≤ 6 :=
  GuestJointTransitionInsertionBound.slope_threshold k

def jointSlope3K : Nat := 23132 + 3 * kPanCoupled
def jointSlope6K : Nat := 23132 + 6 * kPanCoupled
def jointSlope3UnrolledK : Nat := 9332 + 3 * kPanCoupled
def jointSlope6UnrolledK : Nat := 9332 + 6 * kPanCoupled

theorem values_non_vacuous_and_tight :
    kPanCoupled = 130854230896 ∧ jointSlope3K = 392562715820 ∧
    jointSlope6K = 785125408508 ∧ jointSlope3UnrolledK = 392562702020 ∧
    jointSlope6UnrolledK = 785125394708 := by decide

theorem reduction6_non_vacuous_and_tight :
    FullWordToWordAndTransitionMaster.transitionSlope6K = 810291208508 ∧
    FullWordToWordAndTransitionMaster.transitionSlope6K - jointSlope6K = 25165800000 ∧
    jointSlope6K + 25165800000 = FullWordToWordAndTransitionMaster.transitionSlope6K := by decide

theorem reduction3_non_vacuous_and_tight :
    FullWordToWordAndTransitionMaster.transitionSlope3K - jointSlope3K = 12582900000 ∧
    jointSlope3K + 12582900000 = FullWordToWordAndTransitionMaster.transitionSlope3K := by decide

theorem target_margin_non_vacuous_and_tight :
    jointSlope6K < yukonCeiling ∧ yukonCeiling = 900719925474 ∧
    yukonCeiling - jointSlope6K = 115594516966 := by decide

theorem unrolling_non_vacuous_and_tight :
    jointSlope3K - jointSlope3UnrolledK = 13800 ∧
    jointSlope6K - jointSlope6UnrolledK = 13800 := by decide

/-- Unified arithmetic conclusion; the function-body theorem above applies to
arbitrary Pancake programs independently of the gas-allocation parameters. -/
theorem joint_target_non_vacuous_and_tight (D W R T : Nat)
    (h : 21 * D + W + 20 * R ≤ S) (ht : T ≤ 8 * 3994571428) :
    23132 + 6 * (linear + T + (D * (2 * W + 4 * R) + kIns * R)) ≤ jointSlope6K ∧
    jointSlope6K < yukonCeiling := by
  have he := envelope_non_vacuous_and_tight D W R h T ht
  constructor
  · unfold jointSlope6K; omega
  · exact target_margin_non_vacuous_and_tight.1

theorem jointSlope3K_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK jointSlope3K) (.finite jointSlope3K) :=
  UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight _ jointSlope3K
    (by decide) hc

theorem jointSlope6K_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK jointSlope6K) (.finite jointSlope6K) :=
  UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight _ jointSlope6K
    (by decide) hc

theorem jointSlope3UnrolledK_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK jointSlope3UnrolledK) (.finite jointSlope3UnrolledK) :=
  UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight _ jointSlope3UnrolledK
    (by decide) hc

theorem jointSlope6UnrolledK_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK jointSlope6UnrolledK) (.finite jointSlope6UnrolledK) :=
  UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight _ jointSlope6UnrolledK
    (by decide) hc

#print axioms pan_word_non_vacuous_and_tight
#print axioms pan_wordword_non_vacuous_and_tight
#print axioms comp_native_non_vacuous_and_tight
#print axioms stack_bodies_non_vacuous_and_tight
#print axioms stack_alloc_non_vacuous_and_tight
#print axioms every_function_non_vacuous_and_tight
#print axioms stub_exception_non_vacuous_and_tight
#print axioms word_allowance_non_vacuous_and_tight
#print axioms stack_clock_non_vacuous_and_tight
#print axioms absorption_non_vacuous_and_tight
#print axioms envelope_non_vacuous_and_tight
#print axioms absorption_witness_non_vacuous_and_tight
#print axioms source_saving_non_vacuous_and_tight
#print axioms margin6_non_vacuous_and_tight
#print axioms threshold_non_vacuous_and_tight
#print axioms values_non_vacuous_and_tight
#print axioms reduction6_non_vacuous_and_tight
#print axioms reduction3_non_vacuous_and_tight
#print axioms target_margin_non_vacuous_and_tight
#print axioms unrolling_non_vacuous_and_tight
#print axioms joint_target_non_vacuous_and_tight
#print axioms jointSlope3K_certificate_non_vacuous_and_tight
#print axioms jointSlope6K_certificate_non_vacuous_and_tight
#print axioms jointSlope3UnrolledK_certificate_non_vacuous_and_tight
#print axioms jointSlope6UnrolledK_certificate_non_vacuous_and_tight

end InitECandidate.Solver.PanToStackAndJointTransitionMaster
