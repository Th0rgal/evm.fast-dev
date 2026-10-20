import InitECandidate.Solver.GuestMultiAddressMergeDominance
import InitECandidate.Solver.MergeTxUnionSixPassMaster
import InitECandidate.Solver.ThirtyTwoBudgetJointAbsorptionMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.MultiAddressMergeThirtySixBudgetMaster
open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestMergeTxUnionEnvelope (kPanMerge mergeLin blockMerge locCoup)
open _root_.InitECandidate.Solver.GuestMultiAddressMergeDominance (kPanMultiAddrMerge)
open SelfContainedBoundedCertificate UnrolledTwelveCandidatePortfolio

/-! Multi-address arithmetic preserves the existing 36 budgets. Semantic
certificates remain conditional on the explicit baseline certificate. -/

abbrev portfolio := MergeTxUnionSixPassMaster.portfolio
abbrev mergeSlope3UnrolledK := MergeTxUnionSixPassMaster.mergeSlope3UnrolledK
abbrev mergeSlope3K := MergeTxUnionSixPassMaster.mergeSlope3K
abbrev mergeSlope6UnrolledK := MergeTxUnionSixPassMaster.mergeSlope6UnrolledK
abbrev mergeSlope6K := MergeTxUnionSixPassMaster.mergeSlope6K

theorem per_address_split_non_vacuous_and_tight (l : List (Nat × Nat)) :
    (l.map (fun p => p.1 * (p.2 + p.1))).sum ≤
      (l.map Prod.fst).sum * ((l.map Prod.snd).sum + (l.map Prod.fst).sum) :=
  GuestMultiAddressMergeDominance.per_address_split l

theorem per_address_tight_non_vacuous_and_tight (d w : Nat) :
    ([(d, w)].map (fun p => p.1 * (p.2 + p.1))).sum =
      ([(d, w)].map Prod.fst).sum * (([(d, w)].map Prod.snd).sum + ([(d, w)].map Prod.fst).sum) :=
  GuestMultiAddressMergeDominance.per_address_tight d w

theorem addr_square_non_vacuous_and_tight (A W t : Nat) (h : 26 * A + W ≤ t) : 104 * (A * W) ≤ t * t :=
  GuestMultiAddressMergeDominance.addr_square A W t h

theorem addr_dominated_non_vacuous_and_tight : S * S / 52 < S * S / 42 :=
  GuestMultiAddressMergeDominance.addr_dominated 

theorem joint_multi_non_vacuous_and_tight (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    80 * ((D + A) * (W + (D + A))) ≤ S * S :=
  GuestMultiAddressMergeDominance.joint_multi D A W h

theorem joint_multi_le_non_vacuous_and_tight (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    2 * ((D + A) * (W + (D + A))) ≤ blockMerge :=
  GuestMultiAddressMergeDominance.joint_multi_le D A W h

theorem vertex_single_address_non_vacuous_and_tight :
    20 * 50000 + 26 * 0 + (950000 + 50000 + 0) = S ∧
      2 * ((50000 + 0) * (950000 + (50000 + 0))) = blockMerge :=
  GuestMultiAddressMergeDominance.vertex_single_address 

theorem addr_merge_linear_non_vacuous_and_tight (D A : Nat) (h : 21 * D + 26 * A ≤ S) : 3 * D + 18 * A ≤ mergeLin :=
  GuestMultiAddressMergeDominance.addr_merge_linear D A h

theorem kPanMultiAddrMerge_eq_non_vacuous_and_tight : kPanMultiAddrMerge = kPanMerge ∧ kPanMultiAddrMerge = 136116135658 :=
  GuestMultiAddressMergeDominance.kPanMultiAddrMerge_eq 

theorem master_non_vacuous_and_tight (D A W Tloc Tlin : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + 2 * ((D + A) * (W + (D + A))) + Tlin ≤ kPanMultiAddrMerge :=
  GuestMultiAddressMergeDominance.master D A W Tloc Tlin h hloc hlin

theorem slopes_ok_non_vacuous_and_tight :
    3 * kPanMultiAddrMerge < yukon ∧ 4 * kPanMultiAddrMerge < yukon ∧
      5 * kPanMultiAddrMerge < yukon ∧ 6 * kPanMultiAddrMerge < yukon :=
  GuestMultiAddressMergeDominance.slopes_ok 

theorem threshold_and_margin_non_vacuous_and_tight (k : Nat) :
    (k * kPanMultiAddrMerge < yukon ↔ k ≤ 6) ∧ yukon - 6 * kPanMultiAddrMerge = 84023111526 :=
  GuestMultiAddressMergeDominance.threshold_and_margin k

theorem tiers_preserved_non_vacuous_and_tight :
    9332 + 3 * kPanMultiAddrMerge = mergeSlope3UnrolledK ∧
    23132 + 3 * kPanMultiAddrMerge = mergeSlope3K ∧
    9332 + 6 * kPanMultiAddrMerge = mergeSlope6UnrolledK ∧
    23132 + 6 * kPanMultiAddrMerge = mergeSlope6K := by
  rw [kPanMultiAddrMerge_eq_non_vacuous_and_tight.1]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem values_non_vacuous_and_tight :
    mergeSlope3UnrolledK = 408348416306 ∧ mergeSlope3K = 408348430106 ∧
    mergeSlope6UnrolledK = 816696823280 ∧ mergeSlope6K = 816696837080 ∧
    mergeSlope6K < 900719925474 :=
  MergeTxUnionSixPassMaster.values_non_vacuous_and_tight

theorem multi_target_bound_non_vacuous_and_tight (D A W Tloc Tlin post : Nat)
    (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (he : post ≤ 6 * (linear + Tloc + 2 * ((D + A) * (W + (D + A))) + Tlin)) :
    23132 + post ≤ mergeSlope6K ∧ 9332 + post ≤ mergeSlope6UnrolledK := by
  have hb := Nat.mul_le_mul_left 6 (master_non_vacuous_and_tight D A W Tloc Tlin h hloc hlin)
  have ht := tiers_preserved_non_vacuous_and_tight
  omega

theorem multi_three_target_bound_non_vacuous_and_tight (D A W Tloc Tlin post : Nat)
    (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (he : post ≤ 3 * (linear + Tloc + 2 * ((D + A) * (W + (D + A))) + Tlin)) :
    23132 + post ≤ mergeSlope3K ∧ 9332 + post ≤ mergeSlope3UnrolledK := by
  have hb := Nat.mul_le_mul_left 3 (master_non_vacuous_and_tight D A W Tloc Tlin h hloc hlin)
  have ht := tiers_preserved_non_vacuous_and_tight
  omega

theorem portfolio_non_vacuous_and_tight :
    portfolio.length = 36 ∧ portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon) :=
  ⟨MergeTxUnionSixPassMaster.portfolio_count_non_vacuous_and_tight,
   MergeTxUnionSixPassMaster.portfolio_order_non_vacuous_and_tight,
   MergeTxUnionSixPassMaster.portfolio_bounds_non_vacuous_and_tight⟩

theorem thirty_two_coverage_non_vacuous_and_tight :
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified, k ∈ portfolio) ∧
    ThirtyTwoBudgetJointAbsorptionMaster.absorbedPortfolio.length = 32 := by
  exact ⟨ThirtyTwoBudgetJointAbsorptionMaster.portfolio_non_vacuous_and_tight.1,
    by decide, ThirtyTwoBudgetJointAbsorptionMaster.absorbed_count_non_vacuous_and_tight⟩

theorem joint_absorption_non_vacuous_and_tight (D W R : Nat)
    (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤ S * S :=
  ThirtyTwoBudgetJointAbsorptionMaster.absorption_non_vacuous_and_tight D W R h

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) :=
  MergeTxUnionSixPassMaster.portfolio_certificates_non_vacuous_and_tight hc

theorem mergeSlope3UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3UnrolledK) (.finite mergeSlope3UnrolledK) :=
  MergeTxUnionSixPassMaster.mergeSlope3UnrolledK_certificate_non_vacuous_and_tight hc

theorem mergeSlope3K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3K) (.finite mergeSlope3K) :=
  MergeTxUnionSixPassMaster.mergeSlope3K_certificate_non_vacuous_and_tight hc

theorem mergeSlope6UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK) (.finite mergeSlope6UnrolledK) :=
  MergeTxUnionSixPassMaster.mergeSlope6UnrolledK_certificate_non_vacuous_and_tight hc

theorem mergeSlope6K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6K) (.finite mergeSlope6K) :=
  MergeTxUnionSixPassMaster.mergeSlope6K_certificate_non_vacuous_and_tight hc

theorem integrated_master_non_vacuous_and_tight (D A W Tloc Tlin : Nat)
    (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hc : CertificateAt 1212035192) :
    linear + Tloc + 2 * ((D + A) * (W + (D + A))) + Tlin ≤ kPanMerge ∧
    portfolio.length = 36 ∧ portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ portfolio, k < yukon) ∧
    (∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (ThirtyTwoBudgetJointAbsorptionMaster.absorbBudget k))
        (.finite (ThirtyTwoBudgetJointAbsorptionMaster.absorbBudget k))) := by
  have hb := master_non_vacuous_and_tight D A W Tloc Tlin h hloc hlin
  rw [kPanMultiAddrMerge_eq_non_vacuous_and_tight.1] at hb
  exact ⟨hb, portfolio_non_vacuous_and_tight.1, portfolio_non_vacuous_and_tight.2.1,
    fun k hk => (portfolio_non_vacuous_and_tight.2.2 k hk).2,
    portfolio_certificates_non_vacuous_and_tight hc,
    ThirtyTwoBudgetJointAbsorptionMaster.absorbed_certificates_non_vacuous_and_tight hc⟩

#print axioms per_address_split_non_vacuous_and_tight
#print axioms per_address_tight_non_vacuous_and_tight
#print axioms addr_square_non_vacuous_and_tight
#print axioms addr_dominated_non_vacuous_and_tight
#print axioms joint_multi_non_vacuous_and_tight
#print axioms joint_multi_le_non_vacuous_and_tight
#print axioms vertex_single_address_non_vacuous_and_tight
#print axioms addr_merge_linear_non_vacuous_and_tight
#print axioms kPanMultiAddrMerge_eq_non_vacuous_and_tight
#print axioms master_non_vacuous_and_tight
#print axioms slopes_ok_non_vacuous_and_tight
#print axioms threshold_and_margin_non_vacuous_and_tight
#print axioms tiers_preserved_non_vacuous_and_tight
#print axioms values_non_vacuous_and_tight
#print axioms multi_target_bound_non_vacuous_and_tight
#print axioms multi_three_target_bound_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms thirty_two_coverage_non_vacuous_and_tight
#print axioms joint_absorption_non_vacuous_and_tight
#print axioms portfolio_certificates_non_vacuous_and_tight
#print axioms mergeSlope3UnrolledK_certificate_non_vacuous_and_tight
#print axioms mergeSlope3K_certificate_non_vacuous_and_tight
#print axioms mergeSlope6UnrolledK_certificate_non_vacuous_and_tight
#print axioms mergeSlope6K_certificate_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight
end InitECandidate.Solver.MultiAddressMergeThirtySixBudgetMaster
