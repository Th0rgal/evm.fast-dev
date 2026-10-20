import InitECandidate.Solver.GuestMergeTxUnionEnvelope
import InitECandidate.Solver.ThirtyTwoBudgetJointAbsorptionMaster
import InitECandidate.Solver.SelfContainedFullWordToWordAndSstoreSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.MergeTxAndJointAbsorptionMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestMergeTxUnionEnvelope (kPanMerge locCoup mergeLin blockMerge)
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear kPanBs32Joint)
open _root_.InitECandidate.Solver.GuestCoupledTxBlockStorageBound (kPanCoupled)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon maxGuestSourceClock)
open SelfContainedBoundedCertificate UnrolledTwelveCandidatePortfolio

/-! Merge-aware arithmetic and semantic certificates. Certificates retain an explicit
semantic premise; no execution bound follows from arithmetic alone. -/

theorem union_linear_non_vacuous_and_tight (n : Nat) (h : 21 * n ≤ S) :
    2 * n + n ≤ mergeLin ∧ 3 * 95238 ≤ mergeLin :=
  GuestMergeTxUnionEnvelope.union_linear n h

theorem merge_block_square_non_vacuous_and_tight (D W : Nat)
    (h : 20 * D + (W + D) ≤ S) : 80 * (D * (W + D)) ≤ S * S :=
  GuestMergeTxUnionEnvelope.merge_block_square D W h

theorem merge_block_le_non_vacuous_and_tight (D W : Nat)
    (h : 20 * D + (W + D) ≤ S) : 2 * (D * (W + D)) ≤ blockMerge :=
  GuestMergeTxUnionEnvelope.merge_block_le D W h

theorem merge_block_tight_non_vacuous_and_tight :
    20 * 50000 + (950000 + 50000) = S ∧
    2 * (50000 * (950000 + 50000)) = blockMerge :=
  GuestMergeTxUnionEnvelope.merge_block_tight

theorem kPanMerge_val_non_vacuous_and_tight : kPanMerge = 136116135658 :=
  GuestMergeTxUnionEnvelope.kPanMerge_val

theorem kPanMerge_master_non_vacuous_and_tight (D W Tloc Tlin : Nat)
    (h : 20 * D + (W + D) ≤ S) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + 2 * (D * (W + D)) + Tlin ≤ kPanMerge :=
  GuestMergeTxUnionEnvelope.kPanMerge_master D W Tloc Tlin h hloc hlin

theorem slopes_ok_non_vacuous_and_tight :
    3 * kPanMerge < yukon ∧ 4 * kPanMerge < yukon ∧
    5 * kPanMerge < yukon ∧ 6 * kPanMerge < yukon :=
  GuestMergeTxUnionEnvelope.slopes_ok

theorem slope_threshold_non_vacuous_and_tight (k : Nat) :
    k * kPanMerge < yukon ↔ k ≤ 6 := GuestMergeTxUnionEnvelope.slope_threshold k

theorem margin6_non_vacuous_and_tight : yukon - 6 * kPanMerge = 84023111526 :=
  GuestMergeTxUnionEnvelope.margin6

/-- Total overhead includes both block insertion excess and the linear union scan. -/
theorem merge_overhead :
    kPanMerge - kPanCoupled = 5261904762 ∧
    3 * (kPanMerge - kPanCoupled) = 15785714286 ∧
    6 * (kPanMerge - kPanCoupled) = 31571428572 ∧
    maxGuestSourceClock < kPanMerge ∧ blockMerge - 95238095238 = 4761904762 := by
  exact ⟨by decide, by decide, by decide, GuestMergeTxUnionEnvelope.merge_overhead⟩

theorem merge_savings_non_vacuous_and_tight :
    kPanBs32Joint = 153081489139 ∧ kPanMerge < kPanBs32Joint ∧
    kPanBs32Joint - kPanMerge = 16965353481 ∧
    6 * (kPanBs32Joint - kPanMerge) = 101792120886 := by decide

/-- Exact additive identities avoid any ambiguity from natural subtraction. -/
theorem overhead_and_savings_non_vacuous_and_tight :
    kPanCoupled + 5261904762 = kPanMerge ∧
    kPanMerge + 16965353481 = kPanBs32Joint ∧
    5261904762 + 16965353481 = 22227258243 := by decide

def mergeTarget (slope : Nat) : Nat := 23132 + slope * kPanMerge

theorem merge_targets_non_vacuous_and_tight :
    mergeTarget 3 = 408348430106 ∧ mergeTarget 6 = 816696837080 ∧
    mergeTarget 6 < yukon ∧ yukon - mergeTarget 6 = 84023088394 := by decide

theorem merge_target_threshold_non_vacuous_and_tight (k : Nat) :
    mergeTarget k < yukon ↔ k ≤ 6 := by
  unfold mergeTarget GuestMergeTxUnionEnvelope.kPanMerge
    GuestMergeTxUnionEnvelope.locCoup GuestMergeTxUnionEnvelope.blockMerge
    GuestMergeTxUnionEnvelope.mergeLin GuestBs32BlockStorageEnvelope.linear
    GuestJointBlockGasHtabBound.yukon
  omega

theorem joint_absorption_non_vacuous_and_tight (D W R : Nat)
    (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤ S * S :=
  ThirtyTwoBudgetJointAbsorptionMaster.absorption_non_vacuous_and_tight D W R h

theorem absorbed_portfolio_non_vacuous_and_tight :
    ThirtyTwoBudgetJointAbsorptionMaster.absorbedPortfolio.length = 32 :=
  ThirtyTwoBudgetJointAbsorptionMaster.absorbed_count_non_vacuous_and_tight

theorem merge_certificate_3_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK (mergeTarget 3)) (.finite (mergeTarget 3)) :=
  certificate_lift_non_vacuous_and_tight _ _ (by decide) hc

theorem merge_certificate_6_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK (mergeTarget 6)) (.finite (mergeTarget 6)) :=
  certificate_lift_non_vacuous_and_tight _ _ (by decide) hc

theorem merge_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ n ∈ [3, 4, 5, 6],
      InitE.Certificate (baselineWithFiniteK (mergeTarget n)) (.finite (mergeTarget n)) := by
  intro n hn
  have hb : ∀ n ∈ [3, 4, 5, 6], 1212035192 ≤ mergeTarget n := by decide
  exact certificate_lift_non_vacuous_and_tight _ _ (hb n hn) hc

theorem absorbed_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ K ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (ThirtyTwoBudgetJointAbsorptionMaster.absorbBudget K))
        (.finite (ThirtyTwoBudgetJointAbsorptionMaster.absorbBudget K)) :=
  ThirtyTwoBudgetJointAbsorptionMaster.absorbed_certificates_non_vacuous_and_tight hc

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open WordPassesPreserveNoStoreConsts WordToWordFullCompileNoStoreConsts

theorem full_word_merge_zero_allowance_non_vacuous_and_tight
    {width : Nat} [NeZero width] (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (nm ac : Nat) (co : Option (Spt Nat)) :
    NoSt (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordToWord.fullCompileSingle b rc alg c
        ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 :=
  ⟨loopToWord_fullCompileSingle_NoSt ctx q l b rc alg c nm ac co,
   loopToWord_fullCompileSingle_allowance_zero ctx q l b rc alg c nm ac co⟩

theorem full_word_sstore_bridge_non_vacuous_and_tight :
    SelfContainedFullWordToWordAndSstoreSynth.coupledTxBlockSlope6K = 785125408508 ∧
    SelfContainedFullWordToWordAndSstoreSynth.coupledTxBlockSlope6K + 31571428572 =
      mergeTarget 6 := by decide

theorem master_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    kPanMerge = 136116135658 ∧ 6 * kPanMerge < yukon ∧
    kPanBs32Joint - kPanMerge = 16965353481 ∧
    ThirtyTwoBudgetJointAbsorptionMaster.absorbedPortfolio.length = 32 ∧
    (∀ n ∈ [3, 4, 5, 6], InitE.Certificate
      (baselineWithFiniteK (mergeTarget n)) (.finite (mergeTarget n))) ∧
    (∀ K ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (ThirtyTwoBudgetJointAbsorptionMaster.absorbBudget K))
        (.finite (ThirtyTwoBudgetJointAbsorptionMaster.absorbBudget K))) :=
  ⟨kPanMerge_val_non_vacuous_and_tight, slopes_ok_non_vacuous_and_tight.2.2.2,
   merge_savings_non_vacuous_and_tight.2.2.1, absorbed_portfolio_non_vacuous_and_tight,
   merge_certificates_non_vacuous_and_tight hc, absorbed_certificates_non_vacuous_and_tight hc⟩

#print axioms union_linear_non_vacuous_and_tight
#print axioms merge_block_square_non_vacuous_and_tight
#print axioms merge_block_le_non_vacuous_and_tight
#print axioms merge_block_tight_non_vacuous_and_tight
#print axioms kPanMerge_val_non_vacuous_and_tight
#print axioms kPanMerge_master_non_vacuous_and_tight
#print axioms slopes_ok_non_vacuous_and_tight
#print axioms slope_threshold_non_vacuous_and_tight
#print axioms margin6_non_vacuous_and_tight
#print axioms merge_overhead
#print axioms merge_savings_non_vacuous_and_tight
#print axioms overhead_and_savings_non_vacuous_and_tight
#print axioms merge_targets_non_vacuous_and_tight
#print axioms merge_target_threshold_non_vacuous_and_tight
#print axioms joint_absorption_non_vacuous_and_tight
#print axioms absorbed_portfolio_non_vacuous_and_tight
#print axioms merge_certificate_3_non_vacuous_and_tight
#print axioms merge_certificate_6_non_vacuous_and_tight
#print axioms merge_certificates_non_vacuous_and_tight
#print axioms absorbed_certificates_non_vacuous_and_tight
#print axioms full_word_merge_zero_allowance_non_vacuous_and_tight
#print axioms full_word_sstore_bridge_non_vacuous_and_tight
#print axioms master_non_vacuous_and_tight

end InitECandidate.Solver.MergeTxAndJointAbsorptionMaster
