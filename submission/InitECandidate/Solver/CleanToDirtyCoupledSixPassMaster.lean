import InitECandidate.Solver.FullWordToWordCoupledMaster
import InitECandidate.Solver.GuestSstoreCleanToDirtyTransition
import InitECandidate.Solver.SelfContainedWordSimpAndCoupledSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.CleanToDirtyCoupledSixPassMaster
open InitE
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver
open WordPassesPreserveNoStoreConsts StackRemoveStoreConstsZeroBridge
open SelfContainedBoundedCertificate UnrolledTwelveCandidatePortfolio
open Flapjack.Pancake.Proofs.PanToTarget
open GuestSstoreCleanToDirtyTransition
open SelfContainedMidPassesAndSloadSynth

/-! Arithmetic envelopes are tight as arithmetic bounds. Certificates retain the
semantic premise CertificateAt 1212035192; syntax alone proves no execution bound. -/

def transition3K : Nat := 23132 + 3 * kPanTransition
def transition4K : Nat := 23132 + 4 * kPanTransition
def transition5K : Nat := 23132 + 5 * kPanTransition
def transition6K : Nat := 23132 + 6 * kPanTransition

def unified : List Nat :=
  (FullWordToWordCoupledMaster.unified ++
    [transition3K, transition4K, transition5K, transition6K]).insertionSort (· ≤ ·)

variable {width : Nat} [NeZero width]

theorem loop_full_pass_non_vacuous_and_tight (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac : Nat)
    (co : Option (Spt Nat)) :
    NoSt (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true :=
  FullWordToWordCoupledMaster.loop_full_pass_non_vacuous_and_tight ctx q l b rc alg c nm ac co

theorem loop_full_clock_non_vacuous_and_tight (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac k_sn : Nat)
    (co : Option (Spt Nat)) :
    stackRemoveClockWithAllowance k_sn (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = k_sn + 1 :=
  FullWordToWordCoupledMaster.loop_full_clock_non_vacuous_and_tight ctx q l b rc alg c nm ac k_sn co

theorem transition_non_vacuous_and_tight (d : Bool) :
    afterSet d = true ∧ InitECandidate.Solver.GuestSstoreWarmCoeffAudit.cnt .blockStor (InitECandidate.Solver.GuestSstoreWarmCoeffAudit.sstoreWarm (afterSet d)) = 1 ∧
      InitECandidate.Solver.GuestSstoreWarmCoeffAudit.cnt .blockStor (InitECandidate.Solver.GuestSstoreWarmCoeffAudit.sstoreWarm false) = 2 :=
  GuestSstoreCleanToDirtyTransition.transition d

theorem seqBlock_eq_non_vacuous_and_tight (n : Nat) : seqBlock false (n + 1) = n + 2 ∧ seqBlock true n = n :=
  GuestSstoreCleanToDirtyTransition.seqBlock_eq n

theorem clean_cost_non_vacuous_and_tight : cleanUnits = 20 ∧ 4 ≤ 2 * cleanUnits :=
  GuestSstoreCleanToDirtyTransition.clean_cost 

theorem block_with_clean_non_vacuous_and_tight (D W R : Nat) (h : 21 * D + W + 20 * R ≤ InitECandidate.Solver.GuestBs32BlockStorageEnvelope.S) :
    42 * (D * (2 * W + 4 * R)) ≤ InitECandidate.Solver.GuestBs32BlockStorageEnvelope.S * InitECandidate.Solver.GuestBs32BlockStorageEnvelope.S :=
  GuestSstoreCleanToDirtyTransition.block_with_clean D W R h

theorem block_unchanged_non_vacuous_and_tight (D W R : Nat) (h : 21 * D + W + 20 * R ≤ InitECandidate.Solver.GuestBs32BlockStorageEnvelope.S) :
    D * (2 * W + 4 * R) ≤ 95238095238 ∧ 47619 * (2 * 1000001 + 4 * 0) = 95238095238 :=
  GuestSstoreCleanToDirtyTransition.block_unchanged D W R h

theorem insert_le_non_vacuous_and_tight (rs : List Nat) (h : ∀ r ∈ rs, 20 * r ≤ InitECandidate.Solver.GuestCoupledTxBlockStorageBound.M) (hS : 20 * rs.sum ≤ InitECandidate.Solver.GuestBs32BlockStorageEnvelope.S) :
    (rs.map (fun r => 5 * (r * (r - 1)))).sum ≤ 4194300000 :=
  GuestSstoreCleanToDirtyTransition.insert_le rs h hS

theorem kPanTransition_val_non_vacuous_and_tight :
    kPanTransition = 135048530896 ∧ kPanTransition - InitECandidate.Solver.GuestCoupledTxBlockStorageBound.kPanCoupled = 4194300000 :=
  GuestSstoreCleanToDirtyTransition.kPanTransition_val 

theorem slopes_ok_non_vacuous_and_tight :
    3 * kPanTransition < InitECandidate.Solver.GuestJointBlockGasHtabBound.yukon ∧ 4 * kPanTransition < InitECandidate.Solver.GuestJointBlockGasHtabBound.yukon ∧
      5 * kPanTransition < InitECandidate.Solver.GuestJointBlockGasHtabBound.yukon ∧ 6 * kPanTransition < InitECandidate.Solver.GuestJointBlockGasHtabBound.yukon :=
  GuestSstoreCleanToDirtyTransition.slopes_ok 

theorem slope_threshold_non_vacuous_and_tight (k : Nat) : k * kPanTransition < InitECandidate.Solver.GuestJointBlockGasHtabBound.yukon ↔ k ≤ 6 :=
  GuestSstoreCleanToDirtyTransition.slope_threshold k

theorem source_gap_non_vacuous_and_tight :
    kPanTransition = 135048530896 ∧
    GuestCoupledTxBlockStorageBound.kPanCoupled = 130854230896 ∧
    kPanTransition - GuestCoupledTxBlockStorageBound.kPanCoupled = 4194300000 ∧
    GuestBs32BlockStorageEnvelope.kPanBs32Joint - kPanTransition = 18032958243 := by decide

theorem target_gaps_non_vacuous_and_tight :
    transition3K - CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope3K = 12582900000 ∧
    transition6K - CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope6K = 25165800000 := by decide

theorem transition_values_non_vacuous_and_tight :
    transition3K = 405145615820 ∧ transition4K = 540194146716 ∧
    transition5K = 675242677612 ∧ transition6K = 810291208508 := by decide

theorem synth_agreement_non_vacuous_and_tight :
    SelfContainedWordSimpAndCoupledSynth.coupledSlope3K =
      CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope3K ∧
    SelfContainedWordSimpAndCoupledSynth.coupledSlope6K =
      CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope6K := by decide

theorem unified_count_non_vacuous_and_tight : unified.length = 32 := by decide

theorem unified_order_non_vacuous_and_tight : unified.Pairwise (· < ·) := by decide

theorem unified_bounds_non_vacuous_and_tight :
    ∀ k ∈ unified, 1212035192 ≤ k ∧ k < 900719925474 := by decide

theorem unified_coverage_non_vacuous_and_tight :
    (∀ k ∈ FullWordToWordCoupledMaster.unified, k ∈ unified) ∧
    (∀ k ∈ [transition3K, transition4K, transition5K, transition6K], k ∈ unified) := by decide

theorem unified_one_tick_non_vacuous_and_tight (k : Nat) (hk : k ∈ unified) :
    ¬ k ≤ k - 1 := by
  have h := (unified_bounds_non_vacuous_and_tight k hk).1
  omega

theorem unified_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ unified, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  intro k hk
  exact certificate_lift_non_vacuous_and_tight _ _
    (unified_bounds_non_vacuous_and_tight k hk).1 hc

theorem target_threshold_non_vacuous_and_tight (slope : Nat) :
    23132 + slope * kPanTransition < 900719925474 ↔ slope ≤ 6 := by
  change 23132 + slope * 135048530896 < 900719925474 ↔ slope ≤ 6
  omega

theorem master_non_vacuous_and_tight
    (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat) (b : Bool)
    (rc alg : Nat) (c : AsmConfigExact width) (nm ac k_sn : Nat) (co : Option (Spt Nat))
    (d : Bool) (n : Nat) (hc : CertificateAt 1212035192) :
    NoSt (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true ∧
    stackRemoveClockWithAllowance k_sn (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = k_sn + 1 ∧
    afterSet d = true ∧ seqBlock false (n + 1) = n + 2 ∧
    kPanTransition - GuestCoupledTxBlockStorageBound.kPanCoupled = 4194300000 ∧
    unified.length = 32 ∧ unified.Pairwise (· < ·) ∧
    (∀ k ∈ unified, InitE.Certificate (baselineWithFiniteK k) (.finite k)) :=
  ⟨loop_full_pass_non_vacuous_and_tight ctx q l b rc alg c nm ac co,
   loop_full_clock_non_vacuous_and_tight ctx q l b rc alg c nm ac k_sn co,
   (transition_non_vacuous_and_tight d).1, (seqBlock_eq_non_vacuous_and_tight n).1,
   kPanTransition_val_non_vacuous_and_tight.2,
   unified_count_non_vacuous_and_tight, unified_order_non_vacuous_and_tight,
   unified_certificates_non_vacuous_and_tight hc⟩

#print axioms loop_full_pass_non_vacuous_and_tight
#print axioms loop_full_clock_non_vacuous_and_tight
#print axioms transition_non_vacuous_and_tight
#print axioms seqBlock_eq_non_vacuous_and_tight
#print axioms clean_cost_non_vacuous_and_tight
#print axioms block_with_clean_non_vacuous_and_tight
#print axioms block_unchanged_non_vacuous_and_tight
#print axioms insert_le_non_vacuous_and_tight
#print axioms kPanTransition_val_non_vacuous_and_tight
#print axioms slopes_ok_non_vacuous_and_tight
#print axioms slope_threshold_non_vacuous_and_tight
#print axioms source_gap_non_vacuous_and_tight
#print axioms target_gaps_non_vacuous_and_tight
#print axioms transition_values_non_vacuous_and_tight
#print axioms synth_agreement_non_vacuous_and_tight
#print axioms unified_count_non_vacuous_and_tight
#print axioms unified_order_non_vacuous_and_tight
#print axioms unified_bounds_non_vacuous_and_tight
#print axioms unified_coverage_non_vacuous_and_tight
#print axioms unified_one_tick_non_vacuous_and_tight
#print axioms unified_certificates_non_vacuous_and_tight
#print axioms target_threshold_non_vacuous_and_tight
#print axioms master_non_vacuous_and_tight
end InitECandidate.Solver.CleanToDirtyCoupledSixPassMaster
