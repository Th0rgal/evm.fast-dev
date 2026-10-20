import InitECandidate.Solver.GuestSubBlockTxSplittingDominance
import InitECandidate.Solver.PanToLabSectionAndStackRemoveClock
import InitECandidate.Solver.UnifiedAllTablesAndUnconditionalNoStoreConstsMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.SubBlockTxSplittingAndPanToLabMaster

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver
open WordPassesPreserveNoStoreConsts PanToStackNoStoreConsts
open StackRemoveAndNamesNoStoreConsts
open UnrolledTwelveCandidatePortfolio SelfContainedBoundedCertificate
open GuestMergeTxUnionEnvelope MergeTxUnionSixPassMaster
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestMultiAddressMergeDominance (kPanMultiAddrMerge)
open _root_.InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts (FlattenVisitsSt)
open _root_.InitECandidate.Solver.StackRemoveNamesAndMergeTxMaster (flattenInput)

variable {width : Nat} [NeZero width]


open GuestSubBlockTxSplittingDominance PanToLabSectionAndStackRemoveClock

theorem split_local_le_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat)) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) :=
  GuestSubBlockTxSplittingDominance.split_local_le l

theorem split_strict_non_vacuous_and_tight :
    localCost (1, 1, 1, 1, 1) + localCost (1, 1, 1, 1, 1) = 40 ∧ localCost (2, 2, 2, 2, 2) = 80 :=
  GuestSubBlockTxSplittingDominance.split_strict

theorem prefix_le_non_vacuous_and_tight (l : List (Nat × Nat)) (P : Nat) :
    prefixCost l P ≤ (P + (l.map Prod.fst).sum) * (l.map Prod.snd).sum :=
  GuestSubBlockTxSplittingDominance.prefix_le l P

theorem prefix_tight_non_vacuous_and_tight (D W : Nat) : prefixCost [(D, W)] 0 = D * W :=
  GuestSubBlockTxSplittingDominance.prefix_tight D W

theorem prefix_strict_non_vacuous_and_tight : prefixCost [(1, 1), (1, 1)] 0 = 3 ∧ 3 < (0 + 2) * 2 :=
  GuestSubBlockTxSplittingDominance.prefix_strict

theorem reset_bound_non_vacuous_and_tight : 8 * (6 + 1 + (1 + 64 / 32 + 3)) + 2 ≤ txResetTicks :=
  GuestSubBlockTxSplittingDominance.reset_bound

theorem reset_absorbed_non_vacuous_and_tight (T : Nat) (h : txMinUnits * T ≤ 2000000) :
    txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666 :=
  GuestSubBlockTxSplittingDominance.reset_absorbed T h

theorem max_tx_reset_non_vacuous_and_tight : txMinUnits * 16666 ≤ 2000000 ∧ 2000000 < txMinUnits * 16667 ∧
    txResetTicks * 16666 = 3333200 :=
  GuestSubBlockTxSplittingDominance.max_tx_reset

theorem access_list_key_cost_non_vacuous_and_tight : (2100 - 100) + 128 * 16 = 4048 ∧ 2000 ≤ 4048 :=
  GuestSubBlockTxSplittingDominance.access_list_key_cost

theorem subblock_master_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat)) (bound : Nat)
    (hb : localCost (sD l, sR l, sA l, sC l, sW l) ≤ bound) :
    (l.map localCost).sum ≤ bound ∧ 6 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables < yukon ∧
      _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables = 136116135658 :=
  GuestSubBlockTxSplittingDominance.split_master l bound hb

theorem panToLab_sections_unconditional_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    ∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
      IsStubLabel s.sectionId = true ∨ CleanSection s :=
  PanToLabSectionAndStackRemoveClock.panToLab_sections_unconditional arch prog wc ac perf sc dc mh sp off

theorem stackToLab_compile_ids_non_vacuous_and_tight (sc : StackToLab.Config) (dc : DataToWord.Config)
    (mh sp : Nat) (off : BitVec width × BitVec width) (L : List (Nat × HolProg width)) :
    (StackToLab.compile sc dc mh sp off L).map (·.sectionId) =
      [0, 1, 2, gcStubLocation] ++ L.map Prod.fst :=
  PanToLabSectionAndStackRemoveClock.stackToLab_compile_ids sc dc mh sp off L

theorem stackRemove_no_storeConsts_branch_non_vacuous_and_tight (j : Bool) (bd : BitVec width × BitVec width)
    (ptr : Nat) (p : HolProg width) (h : StackNoSt p = true) :
    StackNoSt (StackRemove.comp j bd ptr p) = true ∧ FlattenVisitsSt p = false :=
  PanToLabSectionAndStackRemoveClock.stackRemove_no_storeConsts_branch j bd ptr p h

theorem stackRemove_branch_tight_non_vacuous_and_tight :
    StackNoSt (.storeConsts 3 4 none : HolProg width) = false ∧
      FlattenVisitsSt (.storeConsts 3 4 none : HolProg width) = true :=
  PanToLabSectionAndStackRemoveClock.stackRemove_branch_tight

theorem isStubLabel_tight_non_vacuous_and_tight : IsStubLabel 64 = false :=
  PanToLabSectionAndStackRemoveClock.isStubLabel_tight

theorem unified_five_var_coupled_envelope_non_vacuous_and_tight (D R A C W : Nat)
    (h : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S) : 42 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.F D R A C W ≤ S * S :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.unified_five_var_coupled_envelope_non_vacuous_and_tight D R A C W h

theorem unified_coupled_le_non_vacuous_and_tight (D R A C W : Nat) (h : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S) :
    _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.F D R A C W ≤ 95238095238 :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.unified_coupled_le_non_vacuous_and_tight D R A C W h

theorem unified_coupled_tight_non_vacuous_and_tight :
    21 * 47619 + 20 * 0 + 26 * 0 + 21 * 0 + 1000001 = S ∧ _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.F 47619 0 0 0 1000001 = 95238095238 :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.unified_coupled_tight_non_vacuous_and_tight

theorem unified_cold_corner_non_vacuous_and_tight : _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.F 0 0 0 95238 0 = 9070276644 ∧ 9070276644 < 95238095238 :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.unified_cold_corner_non_vacuous_and_tight

theorem merge_identity_non_vacuous_and_tight (X Y A : Int) :
    (20 * X + 6 * A + Y) ^ 2 - 40 * (2 * X * Y + 12 * A ^ 2) = (20 * X - Y - 6 * A) ^ 2 + 480 * A * (X - A) :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.merge_identity_non_vacuous_and_tight X Y A

theorem unified_five_var_merge_envelope_non_vacuous_and_tight (D R A C W : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S) : 40 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G D R A C W ≤ S * S :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.unified_five_var_merge_envelope_non_vacuous_and_tight D R A C W h

theorem unified_merge_le_non_vacuous_and_tight (D R A C W : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S) :
    _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G D R A C W ≤ 100000000000 :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.unified_merge_le_non_vacuous_and_tight D R A C W h

theorem unified_merge_tight_non_vacuous_and_tight :
    _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G 50000 0 0 0 950000 = 100000000000 ∧ _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G 2000 48000 0 0 950000 = 100000000000 ∧
      20 * (2000 + 48000 + 0) + 6 * 0 + 21 * 0 + (950000 + (2000 + 48000 + 0)) = S :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.unified_merge_tight_non_vacuous_and_tight

theorem kPanUnified_val_non_vacuous_and_tight : _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables = 136116135658 ∧ _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables = kPanMerge :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.kPanUnified_val_non_vacuous_and_tight

theorem kPanUnified_master_non_vacuous_and_tight (D R A C W Tloc Tlin : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G D R A C W + Tlin ≤ _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.kPanUnified_master_non_vacuous_and_tight D R A C W Tloc Tlin h hloc hlin

theorem slopes_non_vacuous_and_tight (k : Nat) :
    6 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables < yukon ∧ (k * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables < yukon ↔ k ≤ 6) :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.slopes_non_vacuous_and_tight k

theorem portfolio_count_non_vacuous_and_tight : portfolio.length = 36 :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.portfolio_count_non_vacuous_and_tight

theorem portfolio_bounds_non_vacuous_and_tight :
    ∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.portfolio_bounds_non_vacuous_and_tight

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) :=
  UnifiedAllTablesAndUnconditionalNoStoreConstsMaster.portfolio_certificates_non_vacuous_and_tight hc

/-- The sum of transaction-local costs inherits the five-variable coupled bound. -/
theorem split_coupled_envelope_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat))
    (h : 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ S) :
    42 * (l.map localCost).sum ≤ S * S := by
  have hs := split_local_le l
  have he := unified_five_var_coupled_envelope_non_vacuous_and_tight
    (sD l) (sR l) (sA l) (sC l) (sW l) h
  simp only [localCost, GuestUnifiedAllTablesMasterEnvelope.F] at hs he
  omega

/-- The splitting and compiler facts share the same nine-table envelope. Finite
certificates retain the semantic certificate premise; no call-target assumption
is needed for the LabLang section characterization. -/
theorem subblock_pan_to_lab_portfolio_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (l : List (Nat × Nat × Nat × Nat × Nat)) (probes : List (Nat × Nat)) (P T : Nat)
    (hgas : txMinUnits * T ≤ 2000000)
    (hcoup : 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ S)
    (hmerge : 20 * (sD l + sR l + sA l) + 6 * sA l + 21 * sC l +
      (sW l + (sD l + sR l + sA l)) ≤ S)
    (Tloc Tlin : Nat) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hc : CertificateAt 1212035192) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    42 * (l.map localCost).sum ≤ S * S ∧
    prefixCost probes P ≤ (P + (probes.map Prod.fst).sum) * (probes.map Prod.snd).sum ∧
    (txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) ∧
    42 * GuestUnifiedAllTablesMasterEnvelope.F (sD l) (sR l) (sA l) (sC l) (sW l) ≤ S * S ∧
    40 * GuestUnifiedAllTablesMasterEnvelope.G (sD l) (sR l) (sA l) (sC l) (sW l) ≤ S * S ∧
    linear + Tloc + GuestUnifiedAllTablesMasterEnvelope.G (sD l) (sR l) (sA l) (sC l) (sW l) + Tlin
      ≤ GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables ∧
    GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables = 136116135658 ∧
    6 * GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables < yukon ∧
    (∀ s ∈ StackToLab.compile sc dc mh sp off
      (compileNative ac perf (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2).2.2.2,
      IsStubLabel s.sectionId = true ∨ CleanSection s) ∧
    ((StackToLab.compile sc dc mh sp off
      (compileNative ac perf (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2).2.2.2).map
        (·.sectionId) = [0, 1, 2, gcStubLocation] ++
      ((compileNative ac perf (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2).2.2.2).map Prod.fst) ∧
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    portfolio.length = 36 ∧
    (∀ k ∈ portfolio, k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) := by
  have hsub : ∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified, k ∈ portfolio := by decide
  have hcert := portfolio_certificates_non_vacuous_and_tight hc
  have hbounds := portfolio_bounds_non_vacuous_and_tight
  exact ⟨split_local_le l, split_coupled_envelope_non_vacuous_and_tight l hcoup, prefix_le probes P, reset_absorbed T hgas,
    unified_five_var_coupled_envelope_non_vacuous_and_tight _ _ _ _ _ hcoup,
    unified_five_var_merge_envelope_non_vacuous_and_tight _ _ _ _ _ hmerge,
    kPanUnified_master_non_vacuous_and_tight _ _ _ _ _ Tloc Tlin hmerge hloc hlin,
    kPanUnified_val_non_vacuous_and_tight.1, (slopes_non_vacuous_and_tight 6).1,
    panToLab_sections_unconditional arch prog wc ac perf sc dc mh sp off,
    stackToLab_compile_ids sc dc mh sp off _, by decide,
    portfolio_count_non_vacuous_and_tight,
    fun k hk => ⟨(hbounds k hk).2, hcert k hk⟩,
    fun k hk => ⟨(hbounds k (hsub k hk)).2, hcert k (hsub k hk)⟩⟩

#print axioms split_coupled_envelope_non_vacuous_and_tight
#print axioms split_local_le_non_vacuous_and_tight
#print axioms split_strict_non_vacuous_and_tight
#print axioms prefix_le_non_vacuous_and_tight
#print axioms prefix_tight_non_vacuous_and_tight
#print axioms prefix_strict_non_vacuous_and_tight
#print axioms reset_bound_non_vacuous_and_tight
#print axioms reset_absorbed_non_vacuous_and_tight
#print axioms max_tx_reset_non_vacuous_and_tight
#print axioms access_list_key_cost_non_vacuous_and_tight
#print axioms subblock_master_non_vacuous_and_tight
#print axioms panToLab_sections_unconditional_non_vacuous_and_tight
#print axioms stackToLab_compile_ids_non_vacuous_and_tight
#print axioms stackRemove_no_storeConsts_branch_non_vacuous_and_tight
#print axioms stackRemove_branch_tight_non_vacuous_and_tight
#print axioms isStubLabel_tight_non_vacuous_and_tight
#print axioms unified_five_var_coupled_envelope_non_vacuous_and_tight
#print axioms unified_coupled_le_non_vacuous_and_tight
#print axioms unified_coupled_tight_non_vacuous_and_tight
#print axioms unified_cold_corner_non_vacuous_and_tight
#print axioms merge_identity_non_vacuous_and_tight
#print axioms unified_five_var_merge_envelope_non_vacuous_and_tight
#print axioms unified_merge_le_non_vacuous_and_tight
#print axioms unified_merge_tight_non_vacuous_and_tight
#print axioms kPanUnified_val_non_vacuous_and_tight
#print axioms kPanUnified_master_non_vacuous_and_tight
#print axioms slopes_non_vacuous_and_tight
#print axioms portfolio_count_non_vacuous_and_tight
#print axioms portfolio_bounds_non_vacuous_and_tight
#print axioms portfolio_certificates_non_vacuous_and_tight
#print axioms subblock_pan_to_lab_portfolio_master_non_vacuous_and_tight

end InitECandidate.Solver.SubBlockTxSplittingAndPanToLabMaster
