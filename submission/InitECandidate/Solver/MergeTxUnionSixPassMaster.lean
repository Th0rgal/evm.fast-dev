import InitECandidate.Solver.GuestMergeTxUnionEnvelope
import InitECandidate.Solver.PanToStackAndCleanToDirtyMaster
import InitECandidate.Solver.PanToStackAndJointTransitionMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.MergeTxUnionSixPassMaster
open InitE Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.PanLang Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Solver
open GuestMergeTxUnionEnvelope
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open UnrolledTwelveCandidatePortfolio SelfContainedBoundedCertificate

/-! Merge arithmetic is integrated with the two syntax/transition masters.
The finite certificates explicitly retain the baseline semantic certificate premise;
the arithmetic source envelope alone does not establish guest execution termination. -/

def mergeSlope3UnrolledK : Nat := 9332 + 3 * kPanMerge
def mergeSlope3K : Nat := 23132 + 3 * kPanMerge
def mergeSlope6UnrolledK : Nat := 9332 + 6 * kPanMerge
def mergeSlope6K : Nat := 23132 + 6 * kPanMerge

def portfolio : List Nat :=
  (PanToStackAndCleanToDirtyMaster.portfolio ++
    [mergeSlope3UnrolledK, mergeSlope3K, mergeSlope6UnrolledK, mergeSlope6K]).insertionSort (· ≤ ·)

theorem union_linear_non_vacuous_and_tight (n : Nat) (h : 21 * n ≤ S) :
    2 * n + n ≤ mergeLin ∧ 3 * 95238 ≤ mergeLin := union_linear n h

theorem merge_block_square_non_vacuous_and_tight (D W : Nat)
    (h : 20 * D + (W + D) ≤ S) : 80 * (D * (W + D)) ≤ S * S :=
  merge_block_square D W h

theorem merge_block_le_non_vacuous_and_tight (D W : Nat)
    (h : 20 * D + (W + D) ≤ S) : 2 * (D * (W + D)) ≤ blockMerge :=
  merge_block_le D W h

theorem block_witness_non_vacuous_and_tight :
    20 * 50000 + (950000 + 50000) = S ∧
    2 * (50000 * (950000 + 50000)) = blockMerge := merge_block_tight

theorem kPanMerge_val_non_vacuous_and_tight : kPanMerge = 136116135658 := kPanMerge_val

theorem source_master_non_vacuous_and_tight (D W Tloc Tlin : Nat)
    (h : 20 * D + (W + D) ≤ S) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + 2 * (D * (W + D)) + Tlin ≤ kPanMerge :=
  kPanMerge_master D W Tloc Tlin h hloc hlin

theorem slopes_ok_non_vacuous_and_tight :
    3 * kPanMerge < yukon ∧ 4 * kPanMerge < yukon ∧
    5 * kPanMerge < yukon ∧ 6 * kPanMerge < yukon := slopes_ok

theorem slope_threshold_non_vacuous_and_tight (k : Nat) :
    k * kPanMerge < yukon ↔ k ≤ 6 := slope_threshold k

theorem margin6_non_vacuous_and_tight : yukon - 6 * kPanMerge = 84023111526 := margin6

theorem values_non_vacuous_and_tight :
    mergeSlope3UnrolledK = 408348416306 ∧ mergeSlope3K = 408348430106 ∧
    mergeSlope6UnrolledK = 816696823280 ∧ mergeSlope6K = 816696837080 ∧
    mergeSlope6K < 900719925474 := by decide

theorem target_margins_non_vacuous_and_tight :
    yukon - mergeSlope6K = 84023088394 ∧
    yukon - mergeSlope6UnrolledK = 84023102194 := by decide

theorem unrolling_non_vacuous_and_tight :
    mergeSlope3K - mergeSlope3UnrolledK = 13800 ∧
    mergeSlope6K - mergeSlope6UnrolledK = 13800 := by decide

theorem target_threshold_non_vacuous_and_tight (k : Nat) :
    23132 + k * kPanMerge < yukon ↔ k ≤ 6 := by
  change 23132 + k * 136116135658 < 900719925474 ↔ k ≤ 6
  omega

theorem saturated_non_vacuous_and_tight :
    ¬ 9332 + 3 * kPanMerge ≤ mergeSlope3UnrolledK - 1 ∧
    ¬ 23132 + 3 * kPanMerge ≤ mergeSlope3K - 1 ∧
    ¬ 9332 + 6 * kPanMerge ≤ mergeSlope6UnrolledK - 1 ∧
    ¬ 23132 + 6 * kPanMerge ≤ mergeSlope6K - 1 := by decide

theorem target_bound_non_vacuous_and_tight (D W Tloc Tlin post : Nat)
    (h : 20 * D + (W + D) ≤ S) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hexpand : post ≤ 6 * (linear + Tloc + 2 * (D * (W + D)) + Tlin)) :
    23132 + post ≤ mergeSlope6K ∧ 9332 + post ≤ mergeSlope6UnrolledK := by
  have hb := Nat.mul_le_mul_left 6 (source_master_non_vacuous_and_tight D W Tloc Tlin h hloc hlin)
  unfold mergeSlope6K mergeSlope6UnrolledK
  constructor <;> omega

theorem clean_joint_agreement_non_vacuous_and_tight :
    PanToStackAndCleanToDirtyMaster.absorbed6K = PanToStackAndJointTransitionMaster.jointSlope6K ∧
    PanToStackAndCleanToDirtyMaster.unrolled6K = PanToStackAndJointTransitionMaster.jointSlope6UnrolledK ∧
    PanToStackAndJointTransitionMaster.jointSlope6K < mergeSlope6K := by decide

theorem clean_absorption_non_vacuous_and_tight (D W R : Nat)
    (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤ S * S :=
  PanToStackAndCleanToDirtyMaster.joint_absorption_non_vacuous_and_tight D W R h

theorem joint_envelope_non_vacuous_and_tight (D W R T : Nat)
    (h : 21 * D + W + 20 * R ≤ S) (ht : T ≤ 8 * 3994571428) :
    linear + T + (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤
      GuestCoupledTxBlockStorageBound.kPanCoupled :=
  PanToStackAndJointTransitionMaster.envelope_non_vacuous_and_tight D W R h T ht

variable {width : Nat} [NeZero width]

theorem chain_non_vacuous_and_tight (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
      (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      PanToStackNoStoreConsts.StackNoSt (StackAlloc.progComp y).2 = true :=
  PanToStackAndCleanToDirtyMaster.chain_non_vacuous_and_tight arch prog wc ac perf

theorem joint_word_non_vacuous_and_tight (arch : AsmArchitecture) (prog : List (DeclHOL width)) :
    ∀ x ∈ panToWordCompileProgHOL arch prog,
      WordPassesPreserveNoStoreConsts.NoSt x.2.2 = true :=
  PanToStackAndJointTransitionMaster.pan_word_non_vacuous_and_tight arch prog

theorem portfolio_count_non_vacuous_and_tight : portfolio.length = 36 := by decide

theorem portfolio_order_non_vacuous_and_tight : portfolio.Pairwise (· < ·) := by decide

theorem portfolio_bounds_non_vacuous_and_tight :
    ∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon := by decide

theorem portfolio_coverage_non_vacuous_and_tight :
    (∀ k ∈ PanToStackAndCleanToDirtyMaster.portfolio, k ∈ portfolio) ∧
    (∀ k ∈ [mergeSlope3UnrolledK, mergeSlope3K, mergeSlope6UnrolledK, mergeSlope6K],
      k ∈ portfolio) := by decide

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  intro k hk
  exact certificate_lift_non_vacuous_and_tight _ _
    (portfolio_bounds_non_vacuous_and_tight k hk).1 hc

theorem mergeSlope3UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3UnrolledK) (.finite mergeSlope3UnrolledK) :=
  portfolio_certificates_non_vacuous_and_tight hc _ (by decide)

theorem mergeSlope3K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3K) (.finite mergeSlope3K) :=
  portfolio_certificates_non_vacuous_and_tight hc _ (by decide)

theorem mergeSlope6UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK) (.finite mergeSlope6UnrolledK) :=
  portfolio_certificates_non_vacuous_and_tight hc _ (by decide)

theorem mergeSlope6K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6K) (.finite mergeSlope6K) :=
  portfolio_certificates_non_vacuous_and_tight hc _ (by decide)

theorem master_non_vacuous_and_tight (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (D W Tloc Tlin : Nat) (h : 20 * D + (W + D) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) (hc : CertificateAt 1212035192) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
      (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      PanToStackNoStoreConsts.StackNoSt (StackAlloc.progComp y).2 = true) ∧
    linear + Tloc + 2 * (D * (W + D)) + Tlin ≤ kPanMerge ∧
    portfolio.length = 36 ∧ portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ portfolio, k < yukon) ∧
    (∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) :=
  ⟨chain_non_vacuous_and_tight arch prog wc ac perf,
   source_master_non_vacuous_and_tight D W Tloc Tlin h hloc hlin,
   portfolio_count_non_vacuous_and_tight, portfolio_order_non_vacuous_and_tight,
   fun k hk => (portfolio_bounds_non_vacuous_and_tight k hk).2,
   portfolio_certificates_non_vacuous_and_tight hc⟩

#print axioms union_linear_non_vacuous_and_tight
#print axioms merge_block_square_non_vacuous_and_tight
#print axioms merge_block_le_non_vacuous_and_tight
#print axioms block_witness_non_vacuous_and_tight
#print axioms kPanMerge_val_non_vacuous_and_tight
#print axioms source_master_non_vacuous_and_tight
#print axioms slopes_ok_non_vacuous_and_tight
#print axioms slope_threshold_non_vacuous_and_tight
#print axioms margin6_non_vacuous_and_tight
#print axioms values_non_vacuous_and_tight
#print axioms target_margins_non_vacuous_and_tight
#print axioms unrolling_non_vacuous_and_tight
#print axioms target_threshold_non_vacuous_and_tight
#print axioms saturated_non_vacuous_and_tight
#print axioms target_bound_non_vacuous_and_tight
#print axioms clean_joint_agreement_non_vacuous_and_tight
#print axioms clean_absorption_non_vacuous_and_tight
#print axioms joint_envelope_non_vacuous_and_tight
#print axioms chain_non_vacuous_and_tight
#print axioms joint_word_non_vacuous_and_tight
#print axioms portfolio_count_non_vacuous_and_tight
#print axioms portfolio_order_non_vacuous_and_tight
#print axioms portfolio_bounds_non_vacuous_and_tight
#print axioms portfolio_coverage_non_vacuous_and_tight
#print axioms portfolio_certificates_non_vacuous_and_tight
#print axioms mergeSlope3UnrolledK_certificate_non_vacuous_and_tight
#print axioms mergeSlope3K_certificate_non_vacuous_and_tight
#print axioms mergeSlope6UnrolledK_certificate_non_vacuous_and_tight
#print axioms mergeSlope6K_certificate_non_vacuous_and_tight
#print axioms master_non_vacuous_and_tight
end InitECandidate.Solver.MergeTxUnionSixPassMaster
