import InitECandidate.Solver.GuestFiveAddrTablesMergeBound
import InitECandidate.Solver.MultiAddressMergeThirtySixBudgetMaster
import InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.FiveAddrTablesThirtySixBudgetMaster
open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestMergeTxUnionEnvelope (kPanMerge mergeLin blockMerge locCoup)
open _root_.InitECandidate.Solver.GuestMultiAddressMergeDominance (kPanMultiAddrMerge)
open SelfContainedBoundedCertificate UnrolledTwelveCandidatePortfolio

/-! Arithmetic envelopes for the five address tables bs+8/16/24/40/48 and
storage bs+32. Semantic certificates retain their explicit baseline premise. -/

abbrev portfolio := MultiAddressMergeThirtySixBudgetMaster.portfolio
abbrev mergeSlope3UnrolledK := MultiAddressMergeThirtySixBudgetMaster.mergeSlope3UnrolledK
abbrev mergeSlope3K := MultiAddressMergeThirtySixBudgetMaster.mergeSlope3K
abbrev mergeSlope6UnrolledK := MultiAddressMergeThirtySixBudgetMaster.mergeSlope6UnrolledK
abbrev mergeSlope6K := MultiAddressMergeThirtySixBudgetMaster.mergeSlope6K

theorem identity5_non_vacuous_and_tight (D A W : Int) :
    2000000 ^ 2 - 40 * (2 * (D + A) * (W + D + A) + 5 * A ^ 2) =
      (2000000 - 40 * (D + A)) ^ 2 + 80 * (D + A) * (2000000 - 21 * D - 27 * A - W)
        + 480 * D * A + 280 * A ^ 2 :=
  GuestFiveAddrTablesMergeBound.identity5 (D := D) (A := A) (W := W)

theorem five_addr_tables_absorbed_non_vacuous_and_tight (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    40 * (2 * ((D + A) * (W + D + A)) + 5 * (A * A)) ≤ S * S :=
  GuestFiveAddrTablesMergeBound.five_addr_tables_absorbed (D := D) (A := A) (W := W) (h := h)

theorem five_le_non_vacuous_and_tight (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    2 * ((D + A) * (W + D + A)) + 5 * (A * A) ≤ 100000000000 :=
  GuestFiveAddrTablesMergeBound.five_le (D := D) (A := A) (W := W) (h := h)

theorem five_tight_non_vacuous_and_tight :
    20 * 50000 + 26 * 0 + (950000 + 50000 + 0) = S ∧
      2 * ((50000 + 0) * (950000 + 50000 + 0)) + 5 * (0 * 0) = 100000000000 :=
  GuestFiveAddrTablesMergeBound.five_tight

theorem identity12_non_vacuous_and_tight (D A W : Int) :
    2000000 ^ 2 - 40 * (2 * (D + A) * (W + D + A) + 12 * A ^ 2) =
      (2000000 - 40 * (D + A)) ^ 2 + 80 * (D + A) * (2000000 - 21 * D - 27 * A - W)
        + 480 * D * A :=
  GuestFiveAddrTablesMergeBound.identity12 (D := D) (A := A) (W := W)

theorem twelve_addr_tables_absorbed_non_vacuous_and_tight (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    40 * (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) ≤ S * S :=
  GuestFiveAddrTablesMergeBound.twelve_addr_tables_absorbed (D := D) (A := A) (W := W) (h := h)

theorem twelve_sharp_non_vacuous_and_tight :
    20 * 0 + 26 * 50000 + (650000 + 0 + 50000) = S ∧
      2 * ((0 + 50000) * (650000 + 0 + 50000)) + 12 * (50000 * 50000) = 100000000000 :=
  GuestFiveAddrTablesMergeBound.twelve_sharp

theorem coupled_absorbed_non_vacuous_and_tight (D A W : Nat) (h : 21 * D + 26 * A + W ≤ S) :
    42 * (2 * (D * W) + 12 * (A * A)) ≤ S * S :=
  GuestFiveAddrTablesMergeBound.coupled_absorbed (D := D) (A := A) (W := W) (h := h)

theorem coupled_le_non_vacuous_and_tight (D A W : Nat) (h : 21 * D + 26 * A + W ≤ S) :
    2 * (D * W) + 12 * (A * A) ≤ 95238095238 ∧
      2 * (47619 * 1000001) + 12 * (0 * 0) = 95238095238 :=
  GuestFiveAddrTablesMergeBound.coupled_le (D := D) (A := A) (W := W) (h := h)

theorem coupled_addr_corner_non_vacuous_and_tight :
    21 * 0 + 26 * 76923 + 0 ≤ S ∧ 2 * (0 * 0) + 12 * (76923 * 76923) = 71005775148 ∧
      71005775148 < 95238095238 :=
  GuestFiveAddrTablesMergeBound.coupled_addr_corner

theorem envelope_unchanged_non_vacuous_and_tight : 6 * kPanMultiAddrMerge < yukon ∧ kPanMultiAddrMerge = 136116135658 :=
  GuestFiveAddrTablesMergeBound.envelope_unchanged

theorem per_address_split_non_vacuous_and_tight (l : List (Nat × Nat)) :
    (l.map (fun p => p.1 * (p.2 + p.1))).sum ≤
      (l.map Prod.fst).sum * ((l.map Prod.snd).sum + (l.map Prod.fst).sum) :=
  MultiAddressMergeThirtySixBudgetMaster.per_address_split_non_vacuous_and_tight (l := l)

theorem per_address_tight_non_vacuous_and_tight (d w : Nat) :
    ([(d, w)].map (fun p => p.1 * (p.2 + p.1))).sum =
      ([(d, w)].map Prod.fst).sum * (([(d, w)].map Prod.snd).sum + ([(d, w)].map Prod.fst).sum) :=
  MultiAddressMergeThirtySixBudgetMaster.per_address_tight_non_vacuous_and_tight (d := d) (w := w)

theorem addr_square_non_vacuous_and_tight (A W t : Nat) (h : 26 * A + W ≤ t) : 104 * (A * W) ≤ t * t :=
  MultiAddressMergeThirtySixBudgetMaster.addr_square_non_vacuous_and_tight (A := A) (W := W) (t := t) (h := h)

theorem addr_dominated_non_vacuous_and_tight : S * S / 52 < S * S / 42 :=
  MultiAddressMergeThirtySixBudgetMaster.addr_dominated_non_vacuous_and_tight

theorem joint_multi_non_vacuous_and_tight (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    80 * ((D + A) * (W + (D + A))) ≤ S * S :=
  MultiAddressMergeThirtySixBudgetMaster.joint_multi_non_vacuous_and_tight (D := D) (A := A) (W := W) (h := h)

theorem joint_multi_le_non_vacuous_and_tight (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    2 * ((D + A) * (W + (D + A))) ≤ blockMerge :=
  MultiAddressMergeThirtySixBudgetMaster.joint_multi_le_non_vacuous_and_tight (D := D) (A := A) (W := W) (h := h)

theorem vertex_single_address_non_vacuous_and_tight :
    20 * 50000 + 26 * 0 + (950000 + 50000 + 0) = S ∧
      2 * ((50000 + 0) * (950000 + (50000 + 0))) = blockMerge :=
  MultiAddressMergeThirtySixBudgetMaster.vertex_single_address_non_vacuous_and_tight

theorem addr_merge_linear_non_vacuous_and_tight (D A : Nat) (h : 21 * D + 26 * A ≤ S) : 3 * D + 18 * A ≤ mergeLin :=
  MultiAddressMergeThirtySixBudgetMaster.addr_merge_linear_non_vacuous_and_tight (D := D) (A := A) (h := h)

theorem kPanMultiAddrMerge_eq_non_vacuous_and_tight : kPanMultiAddrMerge = kPanMerge ∧ kPanMultiAddrMerge = 136116135658 :=
  MultiAddressMergeThirtySixBudgetMaster.kPanMultiAddrMerge_eq_non_vacuous_and_tight

theorem master_non_vacuous_and_tight (D A W Tloc Tlin : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + 2 * ((D + A) * (W + (D + A))) + Tlin ≤ kPanMultiAddrMerge :=
  MultiAddressMergeThirtySixBudgetMaster.master_non_vacuous_and_tight (D := D) (A := A) (W := W) (Tloc := Tloc) (Tlin := Tlin) (h := h) (hloc := hloc) (hlin := hlin)

theorem slopes_ok_non_vacuous_and_tight :
    3 * kPanMultiAddrMerge < yukon ∧ 4 * kPanMultiAddrMerge < yukon ∧
      5 * kPanMultiAddrMerge < yukon ∧ 6 * kPanMultiAddrMerge < yukon :=
  MultiAddressMergeThirtySixBudgetMaster.slopes_ok_non_vacuous_and_tight

theorem threshold_and_margin_non_vacuous_and_tight (k : Nat) :
    (k * kPanMultiAddrMerge < yukon ↔ k ≤ 6) ∧ yukon - 6 * kPanMultiAddrMerge = 84023111526 :=
  MultiAddressMergeThirtySixBudgetMaster.threshold_and_margin_non_vacuous_and_tight (k := k)

theorem tiers_preserved_non_vacuous_and_tight :
    9332 + 3 * kPanMultiAddrMerge = mergeSlope3UnrolledK ∧
    23132 + 3 * kPanMultiAddrMerge = mergeSlope3K ∧
    9332 + 6 * kPanMultiAddrMerge = mergeSlope6UnrolledK ∧
    23132 + 6 * kPanMultiAddrMerge = mergeSlope6K :=
  MultiAddressMergeThirtySixBudgetMaster.tiers_preserved_non_vacuous_and_tight

theorem values_non_vacuous_and_tight :
    mergeSlope3UnrolledK = 408348416306 ∧ mergeSlope3K = 408348430106 ∧
    mergeSlope6UnrolledK = 816696823280 ∧ mergeSlope6K = 816696837080 ∧
    mergeSlope6K < 900719925474 :=
  MultiAddressMergeThirtySixBudgetMaster.values_non_vacuous_and_tight

theorem multi_target_bound_non_vacuous_and_tight (D A W Tloc Tlin post : Nat)
    (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (he : post ≤ 6 * (linear + Tloc + 2 * ((D + A) * (W + (D + A))) + Tlin)) :
    23132 + post ≤ mergeSlope6K ∧ 9332 + post ≤ mergeSlope6UnrolledK :=
  MultiAddressMergeThirtySixBudgetMaster.multi_target_bound_non_vacuous_and_tight (D := D) (A := A) (W := W) (Tloc := Tloc) (Tlin := Tlin) (post := post) (h := h) (hloc := hloc) (hlin := hlin) (he := he)

theorem multi_three_target_bound_non_vacuous_and_tight (D A W Tloc Tlin post : Nat)
    (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (he : post ≤ 3 * (linear + Tloc + 2 * ((D + A) * (W + (D + A))) + Tlin)) :
    23132 + post ≤ mergeSlope3K ∧ 9332 + post ≤ mergeSlope3UnrolledK :=
  MultiAddressMergeThirtySixBudgetMaster.multi_three_target_bound_non_vacuous_and_tight (D := D) (A := A) (W := W) (Tloc := Tloc) (Tlin := Tlin) (post := post) (h := h) (hloc := hloc) (hlin := hlin) (he := he)

theorem portfolio_non_vacuous_and_tight :
    portfolio.length = 36 ∧ portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon) :=
  MultiAddressMergeThirtySixBudgetMaster.portfolio_non_vacuous_and_tight

theorem thirty_two_coverage_non_vacuous_and_tight :
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified, k ∈ portfolio) ∧
    ThirtyTwoBudgetJointAbsorptionMaster.absorbedPortfolio.length = 32 :=
  MultiAddressMergeThirtySixBudgetMaster.thirty_two_coverage_non_vacuous_and_tight

theorem joint_absorption_non_vacuous_and_tight (D W R : Nat)
    (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤ S * S :=
  MultiAddressMergeThirtySixBudgetMaster.joint_absorption_non_vacuous_and_tight (D := D) (W := W) (R := R) (h := h)

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) :=
  MultiAddressMergeThirtySixBudgetMaster.portfolio_certificates_non_vacuous_and_tight (hc := hc)

theorem mergeSlope3UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3UnrolledK) (.finite mergeSlope3UnrolledK) :=
  MultiAddressMergeThirtySixBudgetMaster.mergeSlope3UnrolledK_certificate_non_vacuous_and_tight (hc := hc)

theorem mergeSlope3K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3K) (.finite mergeSlope3K) :=
  MultiAddressMergeThirtySixBudgetMaster.mergeSlope3K_certificate_non_vacuous_and_tight (hc := hc)

theorem mergeSlope6UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK) (.finite mergeSlope6UnrolledK) :=
  MultiAddressMergeThirtySixBudgetMaster.mergeSlope6UnrolledK_certificate_non_vacuous_and_tight (hc := hc)

theorem mergeSlope6K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6K) (.finite mergeSlope6K) :=
  MultiAddressMergeThirtySixBudgetMaster.mergeSlope6K_certificate_non_vacuous_and_tight (hc := hc)

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
        (.finite (ThirtyTwoBudgetJointAbsorptionMaster.absorbBudget k))) :=
  MultiAddressMergeThirtySixBudgetMaster.integrated_master_non_vacuous_and_tight (D := D) (A := A) (W := W) (Tloc := Tloc) (Tlin := Tlin) (h := h) (hloc := hloc) (hlin := hlin) (hc := hc)

/-- Both exact vertices of the twelve-table boundary. Coordinates are (D,W,A). -/
theorem twelve_double_vertex_non_vacuous_and_tight :
    (20 * 50000 + 26 * 0 + (950000 + 50000 + 0) = S ∧
     2 * ((50000 + 0) * (950000 + 50000 + 0)) + 12 * (0 * 0) = 100000000000) ∧
    (20 * 0 + 26 * 50000 + (650000 + 0 + 50000) = S ∧
     2 * ((0 + 50000) * (650000 + 0 + 50000)) + 12 * (50000 * 50000) = 100000000000) := by
  decide

/-- The offset list names exactly the five charged address tables. -/
theorem five_offsets_non_vacuous_and_tight (bs A : Nat) :
    ([bs+8, bs+16, bs+24, bs+40, bs+48].map (fun _ => A*A)).sum = 5*(A*A) := by
  simp; omega

/-- Storage and all five address-table costs fit the unchanged block envelope. -/
theorem complete_five_absorption_non_vacuous_and_tight (bs D A W : Nat)
    (h : 20*D + 26*A + (W+D+A) ≤ S) :
    2*((D+A)*(W+D+A)) +
      ([bs+8, bs+16, bs+24, bs+40, bs+48].map (fun _ => A*A)).sum ≤ blockMerge := by
  rw [five_offsets_non_vacuous_and_tight]
  exact GuestFiveAddrTablesMergeBound.five_le D A W h

/-- The stronger twelve-table bound preserves the complete source envelope. -/
theorem twelve_master_non_vacuous_and_tight (D A W Tloc Tlin : Nat)
    (h : 20*D + 26*A + (W+D+A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + (2*((D+A)*(W+D+A)) + 12*(A*A)) + Tlin ≤ kPanMultiAddrMerge := by
  have hb := GuestFiveAddrTablesMergeBound.twelve_addr_tables_absorbed D A W h
  unfold S at hb
  unfold GuestMultiAddressMergeDominance.kPanMultiAddrMerge
  change linear + Tloc + (2*((D+A)*(W+D+A)) + 12*(A*A)) + Tlin ≤
    linear + locCoup + 100000000000 + mergeLin
  omega

/-- All five address tables, with the storage term, preserve the source budget. -/
theorem five_master_non_vacuous_and_tight (bs D A W Tloc Tlin : Nat)
    (h : 20*D + 26*A + (W+D+A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + (2*((D+A)*(W+D+A)) +
      ([bs+8, bs+16, bs+24, bs+40, bs+48].map (fun _ => A*A)).sum) + Tlin ≤ kPanMultiAddrMerge := by
  have hb := complete_five_absorption_non_vacuous_and_tight bs D A W h
  unfold GuestMultiAddressMergeDominance.kPanMultiAddrMerge
  omega

/-- Both three-pass and six-pass target tiers absorb the five tables. -/
theorem five_four_tiers_non_vacuous_and_tight (bs D A W Tloc Tlin : Nat)
    (h : 20*D + 26*A + (W+D+A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    let cost := linear + Tloc + (2*((D+A)*(W+D+A)) +
      ([bs+8, bs+16, bs+24, bs+40, bs+48].map (fun _ => A*A)).sum) + Tlin
    9332+3*cost ≤ 408348416306 ∧ 23132+3*cost ≤ 408348430106 ∧
    9332+6*cost ≤ 816696823280 ∧ 23132+6*cost ≤ 816696837080 ∧
    816696837080 < 900719925474 := by
  have hb := five_master_non_vacuous_and_tight bs D A W Tloc Tlin h hloc hlin
  have he := GuestMultiAddressMergeDominance.kPanMultiAddrMerge_eq.2
  dsimp only
  omega

/-- The twelve-table boundary also preserves the same four target tiers. -/
theorem twelve_four_tiers_non_vacuous_and_tight (D A W Tloc Tlin : Nat)
    (h : 20*D + 26*A + (W+D+A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    let cost := linear + Tloc + (2*((D+A)*(W+D+A)) + 12*(A*A)) + Tlin
    9332+3*cost ≤ 408348416306 ∧ 23132+3*cost ≤ 408348430106 ∧
    9332+6*cost ≤ 816696823280 ∧ 23132+6*cost ≤ 816696837080 ∧
    816696837080 < 900719925474 := by
  have hb := twelve_master_non_vacuous_and_tight D A W Tloc Tlin h hloc hlin
  have he := GuestMultiAddressMergeDominance.kPanMultiAddrMerge_eq.2
  dsimp only
  omega

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open WordPassesPreserveNoStoreConsts PanToStackNoStoreConsts
variable {width : Nat} [NeZero width]

theorem panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true :=
  PanToStackToLabUnconditionalNoStoreConsts.panToStackNames_bodies_StackNoSt_unconditional arch prog wc ac perf info j bd ptr f

theorem flatten_storeConsts_empty_non_vacuous_and_tight (tail : Bool) (s b : Nat) (stub : Option Nat)
    (sid next : Nat) (cs bs : List Nat) :
    StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
      (.list [], false, next) :=
  PanToStackToLabUnconditionalNoStoreConsts.flatten_storeConsts_empty (tail := tail) (s := s) (b := b) (stub := stub) (sid := sid) (next := next) (cs := cs) (bs := bs)

theorem panToLabSection_unconditional_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (PanToStackToLabUnconditionalNoStoreConsts.FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1) :=
  PanToStackToLabUnconditionalNoStoreConsts.panToLabSection_unconditional (arch := arch) (prog := prog) (wc := wc) (ac := ac) (perf := perf) (info := info) (j := j) (bd := bd) (ptr := ptr) (f := f)

/-- Joint arithmetic and unconditional backend invariant; no baseline certificate needed. -/
theorem five_tables_backend_portfolio_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (bs D A W Tloc Tlin : Nat) (h : 20*D + 26*A + (W+D+A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    (linear + Tloc + (2*((D+A)*(W+D+A)) +
      ([bs+8, bs+16, bs+24, bs+40, bs+48].map (fun _ => A*A)).sum) + Tlin ≤ kPanMultiAddrMerge) ∧
    (portfolio.length = 36 ∧ ∀ k ∈ portfolio, k < yukon) ∧
    (∀ (tail : Bool) (s b : Nat) (stub : Option Nat) (sid next : Nat) (cs bs : List Nat),
      StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
        (.list [], false, next)) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) := by
  exact ⟨five_master_non_vacuous_and_tight bs D A W Tloc Tlin h hloc hlin,
    ⟨portfolio_non_vacuous_and_tight.1,
      fun k hk => (portfolio_non_vacuous_and_tight.2.2 k hk).2⟩,
    flatten_storeConsts_empty_non_vacuous_and_tight,
    panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight
      arch prog wc ac perf info j bd ptr f⟩

#print axioms identity5_non_vacuous_and_tight
#print axioms five_addr_tables_absorbed_non_vacuous_and_tight
#print axioms five_le_non_vacuous_and_tight
#print axioms five_tight_non_vacuous_and_tight
#print axioms identity12_non_vacuous_and_tight
#print axioms twelve_addr_tables_absorbed_non_vacuous_and_tight
#print axioms twelve_sharp_non_vacuous_and_tight
#print axioms coupled_absorbed_non_vacuous_and_tight
#print axioms coupled_le_non_vacuous_and_tight
#print axioms coupled_addr_corner_non_vacuous_and_tight
#print axioms envelope_unchanged_non_vacuous_and_tight
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
#print axioms twelve_double_vertex_non_vacuous_and_tight
#print axioms five_offsets_non_vacuous_and_tight
#print axioms complete_five_absorption_non_vacuous_and_tight
#print axioms twelve_master_non_vacuous_and_tight
#print axioms five_master_non_vacuous_and_tight
#print axioms five_four_tiers_non_vacuous_and_tight
#print axioms twelve_four_tiers_non_vacuous_and_tight
#print axioms panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight
#print axioms flatten_storeConsts_empty_non_vacuous_and_tight
#print axioms panToLabSection_unconditional_non_vacuous_and_tight
#print axioms five_tables_backend_portfolio_non_vacuous_and_tight

end InitECandidate.Solver.FiveAddrTablesThirtySixBudgetMaster
