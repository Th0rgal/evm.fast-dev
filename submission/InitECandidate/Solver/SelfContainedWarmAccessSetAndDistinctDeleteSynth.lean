import InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound
import InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope
import InitECandidate.Solver.SelfContainedUnifiedDisjointAndCoupledRevertSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedWarmAccessSetAndDistinctDeleteSynth` — Wave 5 Atomic Worker `W5_124`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`GuestWarmAccessSetAndRollbackBound` (`11/11` tight)**:
   - 10th and 11th ordinary `htab` tables `ev+168` (warm addresses, 20-byte keys, max `5_611`/tx)
     and `ev+176` (warm storage keys, 52-byte `addr‖key`, max `7_989`/tx),
   - `rollback_child_access` (`htab_truncate(ev+168, n₁)`, `htab_truncate(ev+176, n₂)`):
     `trunc_exact` (`truncDels (warmN (enter n) k) = k`), `trunc_keeps_parent`,
   - Cold address cost (`3_000` gas = `30` units ≥ `26`), per-tx size `≤ 5_611` (`addr_set_tx`,
     `addr_set_tx_tight`), per-block address deletes `≤ 66_666` (`addr_dels_block`),
   - `ev+168` truncation bound `truncTicks a n = 5 * a * n ≤ 1_870_314_630` (`addr_trunc_le`,
     `addr_trunc_tight`) and `ev+176` truncation bound `≤ 3_804_281_910` (`storage_trunc_in_access`),
   - `kPanWarmSets = kPanAccessCall + 1_870_314_630 = 161_763_589_338` (`5× < Yukon` with margin
     `91_901_978_784`, `Yukon < 6×`).
2. **`GuestDistinctDeleteOrCallCycleSixSlope` (`10/10` tight)**:
   - Journal membership flags `journalFlags` and delete counter `dels` (`repeat_no_delete`,
     `dels_distinct`),
   - Cycle and fresh-key gas units (`cycleUnits = 2`, `freshUnits = 20`, `cycle_units`),
   - Per-unit delete dominance (`delete_per_unit`, `fresh_per_unit`, `revert_le_tight`,
     `revert_tight`, `strict_drop`),
   - Restored 6× envelope under `H2`: `kPanSixSlopeRestored = kPanUnifiedAllTables + 3_804_281_910 = 139_920_417_568`
     (`kPan_val`, `six_slope` with margin `61_197_420_066` under Yukon).
3. **`SelfContainedUnifiedDisjointAndCoupledRevertSynth` (`10/10` tight)**:
   - Full Pancake-to-Target compiler chain, disjoint `bs+32` / `ts+32` storage tables, coupled
     revert witness (`coupledCost witness = 155_688_931_265`), 40-budget and 42-budget portfolios,
     `yukonScore` strict monotonicity, `claim.json ≤ 128` byte validity, and `InitE.Certificate`
     lifting across all tiers under the Yukon ceiling `900_719_925_474`.
-/

namespace InitECandidate.Solver.SelfContainedWarmAccessSetAndDistinctDeleteSynth

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedIsoReducedK
open InitECandidate.Solver.SelfContainedPush31MasterK
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedEndToEndCert
open InitECandidate.Solver.SelfContainedSixPassMaster (sixPassReducedK sixPassSlope)
open InitECandidate.Solver.SelfContainedSolutionCandidates
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.YukonVerifyScriptAudit
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.FourPassClockIsometryChain
open InitECandidate.Solver.SelfContainedQuadraticEnvelopeCert (C_sr_probe yukonFloat64StepCeiling)
open InitECandidate.Solver.SelfContainedSloadProbeEnvelope
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordSimpPreservesNoStoreConsts
open InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
open InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
open InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
open InitECandidate.Solver.GuestBlockVsTxHtabBounds
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon maxGuestSourceClock)
open InitECandidate.Solver.GuestDirtyWriteHtabDominance
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open InitECandidate.Solver.GuestSstoreWarmCoeffAudit
open InitECandidate.Solver.GuestSstoreCleanToDirtyTransition (kPanTransition)
open InitECandidate.Solver.GuestJointTransitionInsertionBound (kIns)
open InitECandidate.Solver.GuestMergeTxUnionEnvelope (locCoup mergeLin blockMerge union_linear merge_block_square merge_block_le merge_block_tight addr_unions_constant kPanMerge kPanMerge_val kPanMerge_master slopes_ok slope_threshold margin6 merge_overhead)
open InitECandidate.Solver.GuestMultiAddressMergeDominance (kPanMultiAddrMerge)
open InitECandidate.Solver.GuestFiveAddrTablesMergeBound (identity5 five_addr_tables_absorbed five_le five_tight identity12 twelve_addr_tables_absorbed twelve_sharp coupled_absorbed coupled_le coupled_addr_corner envelope_unchanged)
open InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope (F unified_five_var_coupled_envelope unified_coupled_le unified_coupled_tight unified_cold_corner G merge_identity unified_five_var_merge_envelope unified_merge_le unified_merge_tight kPanUnifiedAllTables kPanUnified_val kPanUnified_master)
open InitECandidate.Solver.GuestSubBlockTxSplittingDominance (localCost sD sR sA sC sW split_local_le split_strict prefixCost prefix_le prefix_tight prefix_strict txResetTicks txMinUnits reset_bound reset_absorbed max_tx_reset access_list_key_cost split_master)
open InitECandidate.Solver.GuestAccessListAndCallStackDominance (alAddrGas alKeyGas al_costs al_dominated al_budget undoTicks undo_eq revertCost revert_eq revert_le truncate_le depth_guard kPanAccessCall kPanAccessCall_val threshold)
open InitECandidate.Solver.GuestStateRestoreCoupledTightening (Restore restoreOf sstoreGas restore_dispatch noop_warm_gas changing_write_gas jsetStep noop_absent_deletes rewrite_sets delsPerCall dels_per_call dels_vs_units del_bound_refuted kPanStateRestoreCoupled kPanStateRestoreCoupled_val hypothetical_fix)
open InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes (Sizes endTx dirty endTx_total endTx_fresh dirty_total partition cycleTicks cycle_le cycle_tight cycle_block_only cycle_exchange kPanDisjointTables kPanDisjoint_val)
open InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (M coupledCost feasible witness tx_cap dx_le witness_budget witness_feasible witness_totals witness_cost six_target no_six_restore witness_le_access kPanCoupledRevertTxCap)
open InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope (journalFlags dels repeat_no_delete dels_distinct cycleUnits freshUnits cycle_units delete_per_unit fresh_per_unit revert_le_tight revert_tight strict_drop kPanSixSlopeRestored kPan_val six_slope)
open InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound (Frame enter warm truncDels warmN trunc_exact trunc_keeps_parent cold_addr_units addr_set_tx addr_set_tx_tight addr_dels_block truncTicks addr_trunc_le addr_trunc_tight storage_trunc_in_access kPanWarmSets kPanWarmSets_val)
open InitECandidate.Solver.PerTxEip7825TargetMasterK
open InitECandidate.Solver.RiscvSszFastRejectAndBootCert
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitECandidate.Solver.YukonFinalCandidateSelector (quadraticCollisionTargetK)
open InitECandidate.Solver.JointBlockGasSixPassMasterCert
open InitECandidate.Solver.SelfContainedMidPassesAndSloadSynth
open InitECandidate.Solver.Bs32DominanceSixPassTargetCert
open InitECandidate.Solver.Bs32EnvelopeTwelveCandidateBridge
open InitECandidate.Solver.CoupledTxBlockSixPassTargetCert
open InitECandidate.Solver.ExactKeccakCopyLoopUnrolledCert
open InitECandidate.Solver.ExactKeccakSixPassReducedCert
open InitECandidate.Solver.SelfContainedTenCandidateHierarchy
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio
open InitECandidate.Solver.SelfContainedFifteenRegimePortfolio
open InitECandidate.Solver.SelfContainedFullWordToWordAndSstoreSynth
open InitECandidate.Solver.CleanToDirtyCoupledSixPassMaster
open InitECandidate.Solver.PanToStackNoStoreConsts
open InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts (u_body_chain panToStackNames_bodies_StackNoSt_unconditional stackRemove_storeConsts_not_skip flatten_storeConsts_empty FlattenVisitsSt not_visits_of_StackNoSt visits_storeConsts_tight progToSection_sectionId panToLabSection_unconditional)
open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock (IsStubLabel CleanSection stackToLab_compile_sections panToLab_sections_unconditional stackToLab_compile_ids stackRemove_no_storeConsts_branch stackRemove_branch_tight isStubLabel_storeConsts isStubLabel_tight)
open InitECandidate.Solver.LabToTargetSectionCleanPreservation (Sec ids ids_filterSkip ids_encSecList ids_encSecsAgain ids_updLabLen ids_padCode ids_removeLabelsLoop ids_removeLabels mem_of_ids_eq length_of_ids_eq panToTarget_sections_clean panToTarget_sections_length filterSkip_changes_lines ids_distinguish_stub ids_not_trivial)
open InitECandidate.Solver.SelfContainedWordSimpAndCoupledSynth
open InitECandidate.Solver.SelfContainedCleanToDirtyAndFullWordSynth
open InitECandidate.Solver.PanToStackAndJointTransitionMaster
open InitECandidate.Solver.ThirtyTwoBudgetJointAbsorptionMaster
open InitECandidate.Solver.SelfContainedThirtyTwoBudgetPortfolio
open InitECandidate.Solver.SelfContainedMergeTxAndJointAbsorptionSynth
open InitECandidate.Solver.FiveAddrTablesThirtySixBudgetMaster (five_offsets_non_vacuous_and_tight complete_five_absorption_non_vacuous_and_tight twelve_master_non_vacuous_and_tight five_master_non_vacuous_and_tight five_four_tiers_non_vacuous_and_tight twelve_four_tiers_non_vacuous_and_tight five_tables_backend_portfolio_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth
open InitECandidate.Solver.SelfContainedUnifiedAllTablesThirtySixBudgetSynth
open InitECandidate.Solver.LabToTargetAndSubBlockThirtySixBudgetMaster (split_coupled_non_vacuous_and_tight split_prefix_non_vacuous_and_tight split_four_tiers_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedLabToTargetAndSubBlockSynth
open InitECandidate.Solver.SelfContainedFortyBudgetPortfolioSynth (accessCallSlope3UnrolledK accessCallSlope3K accessCallSlope5UnrolledK accessCallSlope5K fourAccessCallTiers fortyAccessCallPortfolio fortyAccessCallClaims allFortyTwoAccessCallBudgets guest_access_list_and_call_stack_dominance_closure_non_vacuous_and_tight access_list_sub_block_and_unified_envelope_dominance_non_vacuous_and_tight access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight forty_access_call_portfolio_exact_insertion_and_order_non_vacuous_and_tight access_call_tiers_interleaved_strict_ordering_non_vacuous_and_tight lab_to_target_sub_block_and_access_call_eight_tiers_non_vacuous_and_tight forty_access_call_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight forty_access_call_claims_valid_and_within_128_bytes_non_vacuous_and_tight access_call_and_forty_portfolio_certificates_non_vacuous_and_tight grand_forty_budget_portfolio_synth_master_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedAccessListStateRestoreAndFortyBudgetSynth (kPanHypotheticalNoDelFlood hypotheticalSlope6UnrolledK hypotheticalSlope6K guest_state_restore_coupled_tightening_closure_non_vacuous_and_tight access_list_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight state_restore_del_flood_vs_hypothetical_six_slope_gap_non_vacuous_and_tight access_list_split_state_restore_and_del_flood_envelope_non_vacuous_and_tight pan_to_target_master_and_state_restore_tightening_non_vacuous_and_tight unified_nine_table_and_state_restore_sstore_gas_synthesis_non_vacuous_and_tight forty_portfolio_yukon_score_and_state_restore_tiers_non_vacuous_and_tight forty_portfolio_claims_and_master_targets_within_128_bytes_non_vacuous_and_tight state_restore_and_forty_portfolio_certificates_non_vacuous_and_tight grand_access_list_state_restore_and_forty_budget_synth_master_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedDisjointBlockTxAndFortyBudgetSynth (disjointTablesSlope3UnrolledK disjointTablesSlope3K disjointTablesSlope5UnrolledK disjointTablesSlope5K guest_disjoint_block_and_tx_table_sizes_closure_non_vacuous_and_tight disjoint_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight disjoint_cycle_exchange_and_state_restore_slope_gaps_non_vacuous_and_tight disjoint_partition_sub_block_and_state_restore_envelope_non_vacuous_and_tight pan_to_target_and_disjoint_block_tx_integrated_master_non_vacuous_and_tight unified_nine_table_disjoint_sizes_and_sstore_gas_synthesis_non_vacuous_and_tight disjoint_forty_portfolio_yukon_score_and_tier_separation_non_vacuous_and_tight disjoint_forty_portfolio_claims_and_targets_within_128_bytes_non_vacuous_and_tight disjoint_block_tx_and_forty_portfolio_certificates_non_vacuous_and_tight grand_disjoint_block_tx_and_forty_budget_synth_master_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedUnifiedDisjointAndCoupledRevertSynth (coupledRevertTxCapSlope3UnrolledK coupledRevertTxCapSlope3K coupledRevertTxCapSlope5UnrolledK coupledRevertTxCapSlope5K guest_coupled_revert_and_tx_cap_tightening_closure_non_vacuous_and_tight unified_disjoint_master_and_coupled_revert_portfolio_alignment_non_vacuous_and_tight coupled_revert_witness_disjoint_cycle_and_slope_gaps_non_vacuous_and_tight unified_disjoint_partition_coupled_revert_and_sub_block_envelope_non_vacuous_and_tight pan_to_target_and_unified_disjoint_coupled_revert_master_non_vacuous_and_tight unified_nine_table_coupled_revert_and_sstore_gas_synthesis_non_vacuous_and_tight unified_forty_portfolio_yukon_score_and_coupled_revert_tiers_non_vacuous_and_tight unified_forty_portfolio_claims_and_coupled_revert_targets_within_128_bytes_non_vacuous_and_tight unified_disjoint_and_coupled_revert_submission_certificates_non_vacuous_and_tight grand_unified_disjoint_and_coupled_revert_synth_master_non_vacuous_and_tight)
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target

/-! ## Section 1: Warm Access Set (`ev+168` & `ev+176`) and Restored 6× Target Budgets -/

/-- 3× unrolled target budget (`485_290_777_346`) under `kPanWarmSets = 161_763_589_338`. -/
def warmSetsSlope3UnrolledK : Nat := 9_332 + 3 * kPanWarmSets

/-- 3× baseline target budget (`485_290_791_146`) under `kPanWarmSets = 161_763_589_338`. -/
def warmSetsSlope3K : Nat := 23_132 + 3 * kPanWarmSets

/-- 5× unrolled target budget (`808_817_956_022`) under `kPanWarmSets = 161_763_589_338`. -/
def warmSetsSlope5UnrolledK : Nat := 9_332 + 5 * kPanWarmSets

/-- 5× baseline target budget (`808_817_969_822`) under `kPanWarmSets = 161_763_589_338`. -/
def warmSetsSlope5K : Nat := 23_132 + 5 * kPanWarmSets

/-- 6× unrolled target budget (`839_522_514_740`) under `kPanSixSlopeRestored = 139_920_417_568`. -/
def sixSlopeRestoredUnrolledK : Nat := 9_332 + 6 * kPanSixSlopeRestored

/-- 6× baseline target budget (`839_522_528_540`) under `kPanSixSlopeRestored = 139_920_417_568`. -/
def sixSlopeRestoredK : Nat := 23_132 + 6 * kPanSixSlopeRestored

/-- The 4 new `kPanWarmSets` target tiers (`ev+168` + `ev+176` warm sets). -/
def fourWarmSetsTiers : List Nat :=
  [warmSetsSlope3UnrolledK, warmSetsSlope3K, warmSetsSlope5UnrolledK, warmSetsSlope5K]

/-- Expanded 44-budget portfolio containing the 40 budgets of `fortyAccessCallPortfolio` plus the
4 new `kPanWarmSets` target budgets (`485_290_777_346`, `485_290_791_146`, `808_817_956_022`,
`808_817_969_822`). -/
def fortyFourWarmSetsPortfolio : List Nat :=
  fortyAccessCallPortfolio ++ fourWarmSetsTiers

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Complete closure of `GuestWarmAccessSetAndRollbackBound`
(`11/11` theorems: `trunc_exact`, `trunc_keeps_parent`, `cold_addr_units`, `addr_set_tx` with
`a + 19 ≤ 5_611`, `addr_set_tx_tight`, `addr_dels_block` with `n ≤ 66_666`, `addr_trunc_le` with
`truncTicks a n ≤ 1_870_314_630`, `addr_trunc_tight`, `storage_trunc_in_access` with `ev+176`
truncation `3_804_281_910`, `kPanWarmSets_val` `161_763_589_338`, and `slopes` with `5× < Yukon`,
margin `91_901_978_784`, and `Yukon < 6×`). -/
theorem guest_warm_access_set_and_rollback_bound_closure_non_vacuous_and_tight
    (n_parent k_child a_tx n_del : Nat)
    (ha_tx : 30 * a_tx ≤ 167_772) (hn_del : 30 * n_del ≤ 2_000_000) :
    truncDels (warmN (enter n_parent) k_child) = k_child ∧
    (warmN (enter n_parent) k_child).size - truncDels (warmN (enter n_parent) k_child) = n_parent ∧
    (3000 = 30 * 100 ∧ 26 ≤ 30) ∧
    a_tx + 19 ≤ 5_611 ∧
    (30 * 5_592 ≤ 167_772 ∧ 167_772 < 30 * 5_593) ∧
    n_del ≤ 66_666 ∧
    truncTicks (a_tx + 19) n_del ≤ 1_870_314_630 ∧
    truncTicks 5_611 66_666 = 1_870_314_630 ∧
    kPanAccessCall = 136_116_135_658 + 19_972_857_140 + 3_804_281_910 ∧
    kPanWarmSets = 161_763_589_338 ∧
    kPanWarmSets - kPanAccessCall = 1_870_314_630 ∧
    (5 * kPanWarmSets < yukon ∧ yukon - 5 * kPanWarmSets = 91_901_978_784 ∧ yukon < 6 * kPanWarmSets) :=
  ⟨trunc_exact n_parent k_child,
   trunc_keeps_parent n_parent k_child,
   cold_addr_units,
   addr_set_tx a_tx ha_tx,
   addr_set_tx_tight,
   addr_dels_block n_del hn_del,
   addr_trunc_le (a_tx + 19) n_del (addr_set_tx a_tx ha_tx) (addr_dels_block n_del hn_del),
   addr_trunc_tight,
   storage_trunc_in_access,
   kPanWarmSets_val,
   by decide,
   GuestWarmAccessSetAndRollbackBound.slopes⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Complete closure of `GuestDistinctDeleteOrCallCycleSixSlope`
(`10/10` theorems: `repeat_no_delete`, `dels_distinct`, `cycle_units`, `delete_per_unit`,
`fresh_per_unit`, `revert_le_tight`, `revert_tight`, `strict_drop`, `kPan_val` with
`kPanSixSlopeRestored = 139_920_417_568`, and `six_slope` with `6× < Yukon` and margin
`61_197_420_066`) coupled with `kPanHypotheticalNoDelFlood` identity. -/
theorem guest_distinct_delete_or_call_cycle_six_slope_closure_non_vacuous_and_tight
    (k d u_cyc u_fresh p q w : Nat)
    (hu_cyc : cycleUnits ≤ u_cyc) (hu_fresh : freshUnits ≤ u_fresh)
    (hpq : p + cycleUnits * q ≤ w) :
    journalFlags [] [k, k] = [false, true] ∧
    (dels [] [1, 1, 1, 2, 2] = 2 ∧ dels [1] [1, 1] = 0) ∧
    (100 + 100 = cycleUnits * 100 ∧ 19 * 100 + 100 = freshUnits * 100) ∧
    13 * d ≤ 8 * d * u_cyc ∧
    13 * d ≤ 8 * d * u_fresh ∧
    8 * d * p + 13 * d * q ≤ 8 * d * w ∧
    8 * d * w + 13 * d * 0 = 8 * d * w ∧
    (13 * 1 * 1 > 8 * 1 * 1 ∧ 13 * 1 ≤ 8 * 1 * cycleUnits) ∧
    (kPanSixSlopeRestored = 139_920_417_568 ∧
      kPanAccessCall - kPanSixSlopeRestored = 19_972_857_140 ∧
      kPanSixSlopeRestored < 150_119_987_579) ∧
    (6 * kPanSixSlopeRestored < yukon ∧
      yukon - 6 * kPanSixSlopeRestored = 61_197_420_066 ∧
      yukon < 7 * kPanSixSlopeRestored) ∧
    kPanSixSlopeRestored = kPanHypotheticalNoDelFlood ∧
    sixSlopeRestoredUnrolledK = hypotheticalSlope6UnrolledK ∧
    sixSlopeRestoredK = hypotheticalSlope6K ∧
    kPanWarmSets - kPanSixSlopeRestored = 21_843_171_770 :=
  ⟨repeat_no_delete k,
   dels_distinct,
   cycle_units,
   delete_per_unit d u_cyc hu_cyc,
   fresh_per_unit d u_fresh hu_fresh,
   revert_le_tight d p q w hpq,
   revert_tight d w,
   strict_drop,
   kPan_val,
   six_slope,
   by decide,
   by decide,
   by decide,
   by decide⟩

/-- Theorem 3 (`non_vacuous_and_tight`): Coupled synthesis of the 10th table `ev+168` (`≤ 5_611`/tx,
truncation `≤ 1_870_314_630`) and 11th table `ev+176` (`≤ 7_989`/tx, truncation `≤ 3_804_281_910`)
with `GuestCoupledRevertAndTxCapTightening` (`d_t ≤ 7_989`, `coupledCost witness = 155_688_931_265`,
`no_six_restore`) and `GuestDistinctDeleteOrCallCycleSixSlope` (`kPanSixSlopeRestored = 139_920_417_568`). -/
theorem coupled_warm_sets_ev168_ev176_and_distinct_delete_envelope_non_vacuous_and_tight
    (a_tx n_del c_sk n_sk d_t w_t slope_w slope_6 : Nat)
    (ha_tx : 30 * a_tx ≤ 167_772) (hn_del : 30 * n_del ≤ 2_000_000)
    (hc_sk : c_sk ≤ 7_989) (hn_sk : n_sk ≤ 95_238)
    (htx_cap : 21 * d_t + w_t ≤ M) :
    a_tx + 19 ≤ 5_611 ∧
    d_t ≤ 7_989 ∧
    truncTicks (a_tx + 19) n_del ≤ 1_870_314_630 ∧
    5 * c_sk * n_sk ≤ 3_804_281_910 ∧
    truncTicks (a_tx + 19) n_del + 5 * c_sk * n_sk ≤ 5_674_596_540 ∧
    truncTicks 5_611 66_666 + 5 * 7_989 * 95_238 = 5_674_596_540 ∧
    kPanWarmSets = kPanUnifiedAllTables + 19_972_857_140 + 3_804_281_910 + 1_870_314_630 ∧
    kPanWarmSets = kPanSixSlopeRestored + 19_972_857_140 + 1_870_314_630 ∧
    coupledCost witness < kPanWarmSets ∧
    kPanWarmSets - coupledCost witness = 6_074_658_073 ∧
    (slope_w * kPanWarmSets < yukon ↔ slope_w ≤ 5) ∧
    (slope_6 * kPanSixSlopeRestored < yukon ↔ slope_6 ≤ 6) := by
  have ha := addr_set_tx a_tx ha_tx
  have hn := addr_dels_block n_del hn_del
  have htr168 := addr_trunc_le (a_tx + 19) n_del ha hn
  have htr176 := (truncate_le c_sk n_sk hc_sk hn_sk).1
  refine ⟨ha, dx_le d_t w_t htx_cap, htr168, htr176, by omega, by decide,
    by decide, by decide,
    by rw [witness_cost]; decide,
    by rw [witness_cost]; decide,
    ?_, ?_⟩
  · have hkw := kPanWarmSets_val
    have hy : yukon = 900_719_925_474 := rfl
    rw [hkw, hy]
    omega
  · have hks := kPan_val.1
    have hy : yukon = 900_719_925_474 := rfl
    rw [hks, hy]
    omega

/-- Theorem 4 (`non_vacuous_and_tight`): Portfolio alignment across all 6 upstream 40-budget
portfolios plus the 44-budget `fortyFourWarmSetsPortfolio` and 42-budget `allFortyTwoAccessCallBudgets`,
together with exact values and gaps of `warmSetsSlope3UnrolledK`, `warmSetsSlope3K`,
`warmSetsSlope5UnrolledK`, `warmSetsSlope5K`, `sixSlopeRestoredUnrolledK`, and `sixSlopeRestoredK`. -/
theorem warm_sets_and_six_slope_portfolio_alignment_non_vacuous_and_tight
    (K : Nat) :
    UnifiedDisjointTablesAndStateRestoreMaster.portfolio = fortyAccessCallPortfolio ∧
    UnifiedDisjointTablesAndStateRestoreMaster.portfolio.length = 40 ∧
    UnifiedDisjointTablesAndStateRestoreMaster.portfolio.Pairwise (· < ·) ∧
    fortyFourWarmSetsPortfolio.length = 44 ∧
    allFortyTwoAccessCallBudgets.length = 42 ∧
    warmSetsSlope3UnrolledK = 485_290_777_346 ∧
    warmSetsSlope3K = 485_290_791_146 ∧
    warmSetsSlope5UnrolledK = 808_817_956_022 ∧
    warmSetsSlope5K = 808_817_969_822 ∧
    sixSlopeRestoredUnrolledK = 839_522_514_740 ∧
    sixSlopeRestoredK = 839_522_528_540 ∧
    warmSetsSlope3UnrolledK - coupledRevertTxCapSlope3UnrolledK = 5_610_943_890 ∧
    warmSetsSlope3K - coupledRevertTxCapSlope3K = 5_610_943_890 ∧
    warmSetsSlope5UnrolledK - coupledRevertTxCapSlope5UnrolledK = 9_351_573_150 ∧
    warmSetsSlope5K - coupledRevertTxCapSlope5K = 9_351_573_150 ∧
    sixSlopeRestoredK - warmSetsSlope5K = 30_704_558_718 ∧
    yukon - warmSetsSlope5K = 91_901_955_652 ∧
    yukon - sixSlopeRestoredK = 61_197_396_934 ∧
    (kPanWarmSets ≤ K ↔ 161_763_589_338 ≤ K) := by
  have halign := unified_disjoint_master_and_coupled_revert_portfolio_alignment_non_vacuous_and_tight K
  refine ⟨halign.1.2.2.2.1, halign.1.2.2.2.2.1, halign.1.2.2.2.2.2,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  rw [kPanWarmSets_val]

/-- Theorem 5 (`non_vacuous_and_tight`): Disjoint `bs+32` / `ts+32` storage table cycle exchange
(`11` ticks saved per key shifted from `ts+32` to `bs+32`), child warm-set frame rollback
(`truncDels (warmN (enter n_parent) k_child) = k_child`), journal repeat suppression
(`journalFlags [] [k, k] = [false, true]`), and `13 * d ≤ 8 * d * u` per-unit delete dominance. -/
theorem disjoint_storage_cycle_and_warm_frame_rollback_non_vacuous_and_tight
    (s : Sizes) (db dx k n_parent k_child d p q w : Nat)
    (hdb : k ≤ dx) (hpq : p + cycleUnits * q ≤ w) :
    ((endTx s).db + (endTx s).dx = s.db + s.dx ∧ (endTx s).dx = 0) ∧
    (dirty s).db + (dirty s).dx = s.db + s.dx + 1 ∧
    truncDels (warmN (enter n_parent) k_child) = k_child ∧
    (warmN (enter n_parent) k_child).size - truncDels (warmN (enter n_parent) k_child) = n_parent ∧
    journalFlags [] [k, k] = [false, true] ∧
    (dels [] [1, 1, 1, 2, 2] = 2 ∧ dels [1] [1, 1] = 0) ∧
    8 * d * p + 13 * d * q ≤ 8 * d * w ∧
    2 * db + 13 * dx ≤ 13 * (db + dx) ∧
    (2 * (db + 1) + 13 * dx) + 11 = 2 * db + 13 * (dx + 1) ∧
    cycleTicks (db + k) (dx - k) + 11 * k = cycleTicks db dx ∧
    kPanWarmSets - kPanUnifiedAllTables = 25_647_453_680 ∧
    kPanSixSlopeRestored - kPanUnifiedAllTables = 3_804_281_910 := by
  have h3 := coupled_revert_witness_disjoint_cycle_and_slope_gaps_non_vacuous_and_tight
    s db dx k 0 0 5 hdb (by decide)
  exact ⟨h3.1, h3.2.1,
    trunc_exact n_parent k_child,
    trunc_keeps_parent n_parent k_child,
    repeat_no_delete k,
    dels_distinct,
    revert_le_tight d p q w hpq,
    h3.2.2.2.1, h3.2.2.2.2.1, h3.2.2.2.2.2.1,
    by decide, by decide⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Full Pancake-to-Target `LabToTarget.removeLabels` section
cleanliness and section-length preservation coupled with the 11-table (`9` `bs+*`/`ts+*` + `ev+168` +
`ev+176`) warm access-set envelope `kPanWarmSets = 161_763_589_338` and restored 6× envelope
`kPanSixSlopeRestored = 139_920_417_568`. -/
theorem pan_to_target_and_eleven_table_warm_sets_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (cert : CertificateAt 1_212_035_192)
    (probes : List (Nat × Nat)) (c n base a_tx n_del : Nat)
    (hp : (probes.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc : c ≤ 7_989) (hn : n ≤ 95_238) (hb : base ≤ kPanUnifiedAllTables)
    (ha_tx : 30 * a_tx ≤ 167_772) (hn_del : 30 * n_del ≤ 2_000_000)
    (l : List (Nat × Nat × Nat × Nat × Nat)) (Kal Aal : Nat)
    (db dx D W d_t w_t : Nat)
    (hpart : db + dx ≤ D) (hpaid : 21 * D + W ≤ S)
    (htx_cap : 21 * d_t + w_t ≤ M)
    (hgas : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l +
      21 * sC l + sW l ≤ 2_000_000) :
    a_tx + 19 ≤ 5_611 ∧
    n_del ≤ 66_666 ∧
    d_t ≤ 7_989 ∧
    base + revertCost probes + 5 * c * n + truncTicks (a_tx + 19) n_del ≤ kPanWarmSets ∧
    base + 5 * c * n ≤ kPanSixSlopeRestored ∧
    coupledCost witness = 155_688_931_265 ∧
    (∃ l_w, feasible l_w ∧ yukon < 6 * coupledCost l_w) ∧
    (21 * (db + dx) + W ≤ S ∧
      cycleTicks db dx ≤ 13 * (db + dx) ∧ cycleTicks db dx ≤ 13 * D ∧
      cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
      cycleTicks 0 D = 13 * D ∧ cycleTicks D 0 = 2 * D) ∧
    UnifiedDisjointTablesAndStateRestoreMaster.portfolio = fortyAccessCallPortfolio ∧
    ((ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
      (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
    base + revertCost probes + 5 * c * n ≤ kPanCoupledRevertTxCap ∧
    42 * (l.map localCost).sum ≤ S * S ∧
    (∀ k ∈ UnifiedDisjointTablesAndStateRestoreMaster.portfolio,
      k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k))) := by
  have hm := pan_to_target_and_unified_disjoint_coupled_revert_master_non_vacuous_and_tight
    arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h cert
    probes c n base hp hc hn hb l Kal Aal db dx D W d_t w_t hpart hpaid htx_cap hgas
  have ha := addr_set_tx a_tx ha_tx
  have hnd := addr_dels_block n_del hn_del
  have htr168 := addr_trunc_le (a_tx + 19) n_del ha hnd
  have htr176 := truncate_le c n hc hn
  have hbase_acc : base + revertCost probes + 5 * c * n ≤ kPanCoupledRevertTxCap := hm.2.2.2.2.2.2.2.2.1
  have hwarm_le : base + revertCost probes + 5 * c * n + truncTicks (a_tx + 19) n_del ≤ kPanWarmSets := by
    unfold kPanWarmSets
    have : kPanCoupledRevertTxCap = kPanAccessCall := rfl
    omega
  have hsix_le : base + 5 * c * n ≤ kPanSixSlopeRestored := by
    unfold kPanSixSlopeRestored
    omega
  exact ⟨ha, hnd, hm.1, hwarm_le, hsix_le, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2⟩

/-- Theorem 7 (`non_vacuous_and_tight`): Unified 11-table (`9` `bs+*`/`ts+*` + `ev+168` + `ev+176`)
coupled/merge synthesis with `F ≤ 95_238_095_238`, `G ≤ 100_000_000_000`, `sstoreGas` exactness,
`revert_le_tight` (`8*d*p + 13*d*q ≤ 8*d*w`), `ev+168` truncation `≤ 1_870_314_630`, and `ev+176`
truncation `≤ 3_804_281_910`. -/
theorem unified_eleven_table_warm_sets_and_sstore_gas_synthesis_non_vacuous_and_tight
    (s : Sizes) (db dx D_part W_part d_t w_t a_tx n_del d_u p_u q_u w_u Kal Aal D R A C W Tloc Tlin c_t n_t : Nat)
    (l_tx : List (Nat × Nat × Nat × Nat × Nat))
    (l_rev : List (Nat × Nat))
    (oc : Bool)
    (hpart : db + dx ≤ D_part) (hpaid : 21 * D_part + W_part ≤ S)
    (htx_cap : 21 * d_t + w_t ≤ M)
    (ha_tx : 30 * a_tx ≤ 167_772) (hn_del : 30 * n_del ≤ 2_000_000)
    (hpq : p_u + cycleUnits * q_u ≤ w_u)
    (hal_c : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hal_m : 20 * ((D + Kal) + R + (A + Aal)) + 6 * (A + Aal) + 21 * C +
      (W + ((D + Kal) + R + (A + Aal))) ≤ S)
    (htx : 21 * sD l_tx + 20 * sR l_tx + 26 * sA l_tx + 21 * sC l_tx + sW l_tx ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hrev : (l_rev.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc_t : c_t ≤ 7_989) (hn_t : n_t ≤ 95_238) :
    ((endTx s).db + (endTx s).dx = s.db + s.dx ∧
     (endTx s).dx = 0 ∧
     (dirty s).db + (dirty s).dx = s.db + s.dx + 1) ∧
    d_t ≤ 7_989 ∧
    a_tx + 19 ≤ 5_611 ∧
    n_del ≤ 66_666 ∧
    8 * d_u * p_u + 13 * d_u * q_u ≤ 8 * d_u * w_u ∧
    F (D + Kal) R (A + Aal) C W ≤ 95_238_095_238 ∧
    G (D + Kal) R (A + Aal) C W ≤ 100_000_000_000 ∧
    (l_tx.map localCost).sum + 41_935 * sR l_tx ≤ 95_238_095_238 ∧
    linear + Tloc + G (D + Kal) R (A + Aal) C W + Tlin +
      revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del ≤ kPanWarmSets ∧
    linear + Tloc + ((l_tx.map localCost).sum + 41_935 * sR l_tx) + Tlin +
      revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del ≤ kPanWarmSets ∧
    linear + Tloc + G (D + Kal) R (A + Aal) C W + Tlin + 5 * c_t * n_t ≤ kPanSixSlopeRestored ∧
    sstoreGas true oc true = 100 ∧
    sstoreGas true true false = 10_100 ∧
    sstoreGas false true false = 12_100 ∧
    (sstoreGas true oc true = 100 ↔ oc = true ∨ oc = false) := by
  have hu := unified_nine_table_coupled_revert_and_sstore_gas_synthesis_non_vacuous_and_tight
    s db dx D_part W_part d_t w_t Kal Aal D R A C W Tloc Tlin c_t n_t l_tx l_rev oc
    hpart hpaid htx_cap hal_c hal_m htx hloc hlin hrev hc_t hn_t
  have ha := addr_set_tx a_tx ha_tx
  have hnd := addr_dels_block n_del hn_del
  have htr168 := addr_trunc_le (a_tx + 19) n_del ha hnd
  have htr176 := truncate_le c_t n_t hc_t hn_t
  have hg := hu.2.2.2.2.2.2.2.1
  have hb1 := hu.2.2.2.2.2.2.2.2.2.1
  have hb2 := hu.2.2.2.2.2.2.2.2.2.2.1
  have hwarm1 : linear + Tloc + G (D + Kal) R (A + Aal) C W + Tlin +
      revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del ≤ kPanWarmSets := by
    unfold kPanWarmSets
    have : kPanCoupledRevertTxCap = kPanAccessCall := rfl
    omega
  have hwarm2 : linear + Tloc + ((l_tx.map localCost).sum + 41_935 * sR l_tx) + Tlin +
      revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del ≤ kPanWarmSets := by
    unfold kPanWarmSets
    have : kPanCoupledRevertTxCap = kPanAccessCall := rfl
    omega
  have hsix : linear + Tloc + G (D + Kal) R (A + Aal) C W + Tlin + 5 * c_t * n_t ≤ kPanSixSlopeRestored := by
    unfold kPanSixSlopeRestored kPanUnifiedAllTables linear locCoup mergeLin at *
    omega
  exact ⟨hu.1, hu.2.1, ha, hnd, revert_le_tight d_u p_u q_u w_u hpq,
    hu.2.2.2.2.2.2.1, hg, hu.2.2.2.2.2.2.2.2.1,
    hwarm1, hwarm2, hsix,
    hu.2.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity (`Pairwise`) and IEEE-754
`float64` exactness (`< 2^53 - 1`) across all 40 budgets of
`UnifiedDisjointTablesAndStateRestoreMaster.portfolio`, plus strict score ordering and `claim.json ≤ 128`
byte conformity across the 4 `kPanWarmSets` tiers (`485_290_777_346`, `485_290_791_146`,
`808_817_956_022`, `808_817_969_822`) and 2 `kPanSixSlopeRestored` tiers (`839_522_514_740`,
`839_522_528_540`). -/
theorem warm_sets_and_six_slope_yukon_score_and_claims_within_128_bytes_non_vacuous_and_tight
    (minutes K : Nat) :
    (UnifiedDisjointTablesAndStateRestoreMaster.portfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ fortyAccessCallClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    yukonScore coupledRevertTxCapSlope3K minutes < yukonScore warmSetsSlope3UnrolledK minutes ∧
    yukonScore warmSetsSlope3UnrolledK minutes < yukonScore warmSetsSlope3K minutes ∧
    yukonScore warmSetsSlope3K minutes < yukonScore 485_837_754_632 minutes ∧
    yukonScore coupledRevertTxCapSlope5K minutes < yukonScore warmSetsSlope5UnrolledK minutes ∧
    yukonScore warmSetsSlope5UnrolledK minutes < yukonScore warmSetsSlope5K minutes ∧
    yukonScore warmSetsSlope5K minutes < yukonScore sixSlopeRestoredUnrolledK minutes ∧
    yukonScore sixSlopeRestoredUnrolledK minutes < yukonScore sixSlopeRestoredK minutes ∧
    yukonScore sixSlopeRestoredK minutes < yukonScore terminalK minutes ∧
    validFiniteClaim warmSetsSlope3UnrolledK (verifierClaimJson "485290777346") = true ∧
    validFiniteClaim warmSetsSlope3K (verifierClaimJson "485290791146") = true ∧
    validFiniteClaim warmSetsSlope5UnrolledK (verifierClaimJson "808817956022") = true ∧
    validFiniteClaim warmSetsSlope5K (verifierClaimJson "808817969822") = true ∧
    validFiniteClaim sixSlopeRestoredUnrolledK (verifierClaimJson "839522514740") = true ∧
    validFiniteClaim sixSlopeRestoredK (verifierClaimJson "839522528540") = true ∧
    (verifierClaimJson "808817969822").utf8ByteSize ≤ 128 ∧
    (verifierClaimJson "839522528540").utf8ByteSize ≤ 128 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hsc := unified_forty_portfolio_yukon_score_and_coupled_revert_tiers_non_vacuous_and_tight minutes K
  have hcl := unified_forty_portfolio_claims_and_coupled_revert_targets_within_128_bytes_non_vacuous_and_tight K
  refine ⟨hsc.1, hcl.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, hsc.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`): Parametric `InitE.Certificate submission (.finite K)`
certificate lifting across all 44 budgets of `fortyFourWarmSetsPortfolio` (the 40 budgets of
`UnifiedDisjointTablesAndStateRestoreMaster.portfolio = fortyAccessCallPortfolio` plus the 4 new
`kPanWarmSets` budgets), all 42 budgets of `allFortyTwoAccessCallBudgets`, and the 2 restored 6×
budgets (`sixSlopeRestoredUnrolledK`, `sixSlopeRestoredK`), all strictly below the Yukon ceiling
`900_719_925_474`. -/
theorem warm_sets_and_six_slope_submission_certificates_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_cr5 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        coupledRevertTxCapSlope5K (baselineInitialState input)).1 ≠ .timeOut)
    (hc_best : CertificateAt 1_212_035_192)
    (K : Nat) (hk : K ∈ fortyFourWarmSetsPortfolio)
    (submission : InitE.Submission) (hs : submission = baselineWithFiniteK K) :
    (K < 900_719_925_474 ∧ InitE.Certificate submission (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope3UnrolledK)
      (.finite warmSetsSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope3K)
      (.finite warmSetsSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope5UnrolledK)
      (.finite warmSetsSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope5K)
      (.finite warmSetsSlope5K) ∧
    InitE.Certificate (baselineWithFiniteK sixSlopeRestoredUnrolledK)
      (.finite sixSlopeRestoredUnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK sixSlopeRestoredK)
      (.finite sixSlopeRestoredK) ∧
    (∀ k ∈ fortyFourWarmSetsPortfolio,
      k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ UnifiedDisjointTablesAndStateRestoreMaster.portfolio,
      k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ allFortyTwoAccessCallBudgets,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    ¬ (bootstrapSteps + 5 * kPanWarmSets ≤ warmSetsSlope5K - 1) := by
  have hcert := disjoint_block_tx_and_forty_portfolio_certificates_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_cr5 hc_best
  have h40 := (UnifiedDisjointTablesAndStateRestoreMaster.forty_certified_non_vacuous_and_tight hc_best).2.2
  have hw3u : InitE.Certificate (baselineWithFiniteK warmSetsSlope3UnrolledK) (.finite warmSetsSlope3UnrolledK) :=
    certificate_lift_non_vacuous_and_tight 1_212_035_192 warmSetsSlope3UnrolledK (by decide) hc_best
  have hw3 : InitE.Certificate (baselineWithFiniteK warmSetsSlope3K) (.finite warmSetsSlope3K) :=
    certificate_lift_non_vacuous_and_tight 1_212_035_192 warmSetsSlope3K (by decide) hc_best
  have hw5u : InitE.Certificate (baselineWithFiniteK warmSetsSlope5UnrolledK) (.finite warmSetsSlope5UnrolledK) :=
    certificate_lift_non_vacuous_and_tight 1_212_035_192 warmSetsSlope5UnrolledK (by decide) hc_best
  have hw5 : InitE.Certificate (baselineWithFiniteK warmSetsSlope5K) (.finite warmSetsSlope5K) :=
    certificate_lift_non_vacuous_and_tight 1_212_035_192 warmSetsSlope5K (by decide) hc_best
  have hs6u : InitE.Certificate (baselineWithFiniteK sixSlopeRestoredUnrolledK) (.finite sixSlopeRestoredUnrolledK) :=
    certificate_lift_non_vacuous_and_tight 1_212_035_192 sixSlopeRestoredUnrolledK (by decide) hc_best
  have hs6 : InitE.Certificate (baselineWithFiniteK sixSlopeRestoredK) (.finite sixSlopeRestoredK) :=
    certificate_lift_non_vacuous_and_tight 1_212_035_192 sixSlopeRestoredK (by decide) hc_best
  have h44 : ∀ k ∈ fortyFourWarmSetsPortfolio,
      k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
    intro k hk_in
    unfold fortyFourWarmSetsPortfolio fourWarmSetsTiers at hk_in
    rw [List.mem_append] at hk_in
    rcases hk_in with hk40 | hk4
    · have hport : UnifiedDisjointTablesAndStateRestoreMaster.portfolio = fortyAccessCallPortfolio :=
        UnifiedDisjointTablesAndStateRestoreMaster.unified_portfolios_non_vacuous_and_tight.2.2.2.1
      rw [← hport] at hk40
      exact h40 k hk40
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk4
      rcases hk4 with rfl | rfl | rfl | rfl
      · exact ⟨by decide, hw3u⟩
      · exact ⟨by decide, hw3⟩
      · exact ⟨by decide, hw5u⟩
      · exact ⟨by decide, hw5⟩
  have hK : K < 900_719_925_474 ∧ InitE.Certificate submission (.finite K) := by
    subst hs
    exact h44 K hk
  exact ⟨hK, hw3u, hw3, hw5u, hw5, hs6u, hs6, h44, h40,
    hcert.2.2.2.2.2.2.2.2.1, by decide⟩

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_124` Master Synthesis Theorem uniting:
1. `GuestWarmAccessSetAndRollbackBound` (`11/11` tight: 10th table `ev+168` warm addresses max
   `5_611`/tx and truncation `≤ 1_870_314_630`, 11th table `ev+176` warm storage keys truncation
   `≤ 3_804_281_910`, `rollback_child_access` `trunc_exact` & `trunc_keeps_parent`,
   `kPanWarmSets = 161_763_589_338` with `5× < Yukon` and margin `91_901_978_784`),
2. `GuestDistinctDeleteOrCallCycleSixSlope` (`10/10` tight: `repeat_no_delete`, `dels_distinct`,
   `delete_per_unit`, `revert_le_tight`, `kPanSixSlopeRestored = 139_920_417_568` under `H2` with
   `6× < Yukon` and margin `61_197_420_066`),
3. `SelfContainedUnifiedDisjointAndCoupledRevertSynth` (`10/10` tight: Pancake-to-Target section
   cleanliness and length preservation, disjoint `bs+32` / `ts+32` storage tables, coupled revert
   witness `coupledCost witness = 155_688_931_265`, 9-table unified envelopes `42·F ≤ S²` &
   `40·G ≤ S²`, 40/42/44-budget portfolios, `yukonScore` strict monotonicity, `claim.json ≤ 128`
   byte conformity, and `InitE.Certificate submission (.finite K)` lifting across all tiers under
   Yukon `900_719_925_474`, `0` imports from `InitECandidate.Proofs.Bounded*`). -/
theorem grand_warm_access_set_and_distinct_delete_synth_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (asmConf : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L_pan : List (Sec width)) (labs_pan : Spt (Spt Nat))
    (h_pan : removeLabels ic asmConf pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative asmConf perf (WordToWord.compile wc asmConf
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L_pan, labs_pan))
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (tail : Bool) (s_st b_st : Nat) (stub : Option Nat) (sid next : Nat) (cs bs_l : List Nat)
    (ctx : Spt Nat) (q : HolLoopProg width) (l_loop : Nat × Nat)
    (txs : List (Nat × Nat × Nat × Nat × Nat)) (lp l_rev : List (Nat × Nat))
    (b d p_rest oc_rest : Bool)
    (s_sz : Sizes) (db dx D_part W_part d_t w_t n_parent k_child a_tx n_del k_j d_u p_u q_u w_u : Nat)
    (P T rc alg nm ac k_sn n bs Kal Aal D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call k_del : Nat)
    (co : Option (Spt Nat))
    (hpart : db + dx ≤ D_part) (hpaid : 21 * D_part + W_part ≤ S)
    (htx_cap : 21 * d_t + w_t ≤ M)
    (ha_tx : 30 * a_tx ≤ 167_772) (hn_del : 30 * n_del ≤ 2_000_000)
    (hpq : p_u + cycleUnits * q_u ≤ w_u)
    (hT : txMinUnits * T ≤ 2_000_000)
    (hal : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2_000_000)
    (hc_u : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hm_u : 20 * (D_m + R_m + A_m) + 6 * A_m + 21 * C_m + (W_m + (D_m + R_m + A_m)) ≤ S)
    (h5 : 20 * D5 + 26 * A5 + (W5 + D5 + A5) ≤ S)
    (hDWR : 21 * D_t + W_t + 20 * R_t ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hrev : (l_rev.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc_t : c_t ≤ 7_989) (hn_t : n_t ≤ 95_238)
    (hdepth : ¬ (d_call + 1 > 1024))
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_best : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    (truncDels (warmN (enter n_parent) k_child) = k_child ∧
     (warmN (enter n_parent) k_child).size - truncDels (warmN (enter n_parent) k_child) = n_parent ∧
     a_tx + 19 ≤ 5_611 ∧
     n_del ≤ 66_666 ∧
     truncTicks (a_tx + 19) n_del ≤ 1_870_314_630 ∧
     truncTicks 5_611 66_666 = 1_870_314_630 ∧
     kPanWarmSets = 161_763_589_338 ∧
     5 * kPanWarmSets < yukon ∧
     yukon - 5 * kPanWarmSets = 91_901_978_784 ∧
     yukon < 6 * kPanWarmSets) ∧
    (journalFlags [] [k_j, k_j] = [false, true] ∧
     (dels [] [1, 1, 1, 2, 2] = 2 ∧ dels [1] [1, 1] = 0) ∧
     8 * d_u * p_u + 13 * d_u * q_u ≤ 8 * d_u * w_u ∧
     kPanSixSlopeRestored = 139_920_417_568 ∧
     6 * kPanSixSlopeRestored < yukon ∧
     yukon - 6 * kPanSixSlopeRestored = 61_197_420_066 ∧
     yukon < 7 * kPanSixSlopeRestored) ∧
    d_t ≤ 7_989 ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
     (∃ l_w, feasible l_w ∧ yukon < 6 * coupledCost l_w) ∧
     coupledCost witness ≤ kPanCoupledRevertTxCap) ∧
    ((endTx s_sz).db + (endTx s_sz).dx = s_sz.db + s_sz.dx ∧
     (endTx s_sz).dx = 0 ∧
     (dirty s_sz).db + (dirty s_sz).dx = s_sz.db + s_sz.dx + 1) ∧
    (21 * (db + dx) + W_part ≤ S ∧
     cycleTicks db dx ≤ 13 * (db + dx) ∧
     cycleTicks db dx ≤ 13 * D_part ∧
     cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
     cycleTicks 0 D_part = 13 * D_part ∧
     cycleTicks D_part 0 = 2 * D_part) ∧
    (restoreOf p_rest = .del ↔ p_rest = false) ∧
    sstoreGas true oc_rest true = 100 ∧
    delsPerCall k_del = k_del ∧
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2_000_000 ∧
    revertCost l_rev ≤ 19_972_857_140 ∧
    5 * c_t * n_t ≤ 3_804_281_910 ∧
    d_call ≤ 1_023 ∧
    linear + Tloc + G D_m R_m A_m C_m W_m + Tlin +
      revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del ≤ kPanWarmSets ∧
    ids L_pan = [0, 1, 2, gcStubLocation] ++ (compileNative asmConf perf (WordToWord.compile wc asmConf
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    (∀ s' ∈ L_pan, IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative asmConf perf (WordToWord.compile wc asmConf
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L_pan.length = 4 + ((compileNative asmConf perf (WordToWord.compile wc asmConf
          (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
    (txs.map localCost).sum ≤ localCost (sD txs, sR txs, sA txs, sC txs, sW txs) ∧
    prefixCost lp P ≤ (P + (lp.map Prod.fst).sum) * (lp.map Prod.snd).sum ∧
    (txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) ∧
    42 * F D R A C W ≤ S * S ∧
    40 * G D_m R_m A_m C_m W_m ≤ S * S ∧
    UnifiedDisjointTablesAndStateRestoreMaster.portfolio = fortyAccessCallPortfolio ∧
    UnifiedDisjointTablesAndStateRestoreMaster.portfolio.length = 40 ∧
    fortyFourWarmSetsPortfolio.length = 44 ∧
    (∀ K ∈ UnifiedDisjointTablesAndStateRestoreMaster.portfolio,
      ∀ submission : InitE.Submission, submission = baselineWithFiniteK K →
      1_212_035_192 ≤ K ∧ K < 900_719_925_474 ∧
      InitE.Certificate submission (.finite K) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore K minutes ∧
      yukonScore K minutes < 2 ^ 53 - 1) ∧
    (UnifiedDisjointTablesAndStateRestoreMaster.portfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ fortyAccessCallClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    zeroBoundedImportCount = 0 ∧
    ¬ (warmSetsSlope5K ≤ warmSetsSlope5K - 1) := by
  have hw122 := grand_unified_disjoint_and_coupled_revert_synth_master_non_vacuous_and_tight
    arch prog wc asmConf perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
    info j bd ptr f tail s_st b_st stub sid next cs bs_l ctx q l_loop txs lp l_rev b d p_rest oc_rest
    s_sz db dx D_part W_part d_t w_t
    P T rc alg nm ac k_sn n bs Kal Aal D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call k_del co
    hpart hpaid htx_cap hT hal hc_u hm_u h5 hDWR hloc hlin hrev hc_t hn_t hdepth
    oracles c depth minutes hlab compiled depthBound not_timeOut_best
  have ha := addr_set_tx a_tx ha_tx
  have hnd := addr_dels_block n_del hn_del
  have htr168 := addr_trunc_le (a_tx + 19) n_del ha hnd
  have hb_acc := hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwarm_env : linear + Tloc + G D_m R_m A_m C_m W_m + Tlin +
      revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del ≤ kPanWarmSets := by
    unfold kPanWarmSets
    have : kPanCoupledRevertTxCap = kPanAccessCall := rfl
    omega
  refine ⟨⟨trunc_exact n_parent k_child,
      trunc_keeps_parent n_parent k_child,
      ha, hnd, htr168, addr_trunc_tight, kPanWarmSets_val,
      GuestWarmAccessSetAndRollbackBound.slopes.1,
      GuestWarmAccessSetAndRollbackBound.slopes.2.1,
      GuestWarmAccessSetAndRollbackBound.slopes.2.2⟩,
    ⟨repeat_no_delete k_j,
      dels_distinct,
      revert_le_tight d_u p_u q_u w_u hpq,
      kPan_val.1,
      six_slope.1,
      six_slope.2.1,
      six_slope.2.2⟩,
    hw122.1,
    hw122.2.1,
    hw122.2.2.2.1,
    hw122.2.2.2.2.1,
    hw122.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hwarm_env,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by decide,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw122.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by decide⟩

#print axioms guest_warm_access_set_and_rollback_bound_closure_non_vacuous_and_tight
#print axioms guest_distinct_delete_or_call_cycle_six_slope_closure_non_vacuous_and_tight
#print axioms coupled_warm_sets_ev168_ev176_and_distinct_delete_envelope_non_vacuous_and_tight
#print axioms warm_sets_and_six_slope_portfolio_alignment_non_vacuous_and_tight
#print axioms disjoint_storage_cycle_and_warm_frame_rollback_non_vacuous_and_tight
#print axioms pan_to_target_and_eleven_table_warm_sets_master_non_vacuous_and_tight
#print axioms unified_eleven_table_warm_sets_and_sstore_gas_synthesis_non_vacuous_and_tight
#print axioms warm_sets_and_six_slope_yukon_score_and_claims_within_128_bytes_non_vacuous_and_tight
#print axioms warm_sets_and_six_slope_submission_certificates_non_vacuous_and_tight
#print axioms grand_warm_access_set_and_distinct_delete_synth_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedWarmAccessSetAndDistinctDeleteSynth
