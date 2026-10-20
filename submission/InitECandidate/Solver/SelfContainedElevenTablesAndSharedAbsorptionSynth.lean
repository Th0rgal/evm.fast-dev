import InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption
import InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound
import InitECandidate.Solver.SelfContainedWarmAccessSetAndDistinctDeleteSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedElevenTablesAndSharedAbsorptionSynth` — Wave 5 Atomic Worker `W5_128`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`GuestElevenTablesSharedBudgetAbsorption` (`10/10` tight)**:
   - Shared block budget `B + u2 + u3 + u4 ≤ S` across the storage/revert regime (`40·blk ≤ B²`,
     `84·loc ≤ M·B`), `ev+176` truncation (`21·t2 ≤ 5·7_989·u2`), `ev+168` truncation
     (`30·t3 ≤ 5·5_611·u3`), and `ev+168` warm address probes (`60·t4 ≤ (M + 2_280)·u4`),
   - Side-regime per-unit slopes `≤ 2_835` (`side_slopes`) vs storage loss `≥ 50_000`/unit
     (`storage_loss`), proving `shared_absorption`:
     `blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571` (`shared_tight`),
   - Shared envelope `kPanElevenTablesShared = 156_088_992_805` (`kPan_val`, gain `11_342_996_533`
     over `kPanElevenTables`),
   - Tight bracket between the feasible 12-tx lower witness `coupledCost witness = 155_688_931_265`
     (`lower_witness`) and `kPanElevenTablesShared = 156_088_992_805` (`bracket` width `400_061_540`
     ticks, `bracket_rel` `< 0.26%`),
   - Exact `5×` margin `120_274_961_449` under Yukon (`five_margin`) and unconditional `6×` failure
     even at the lower witness (`six_fails`).
2. **`GuestElevenTablesAndWarmAddressProbeBound` (`10/10` tight)**:
   - Warm address probe ticks `txProbe (a, w) = 2 * (a + 19) * w = 2 * (a * w) + 38 * w` (`probe_expand`),
   - Single-tx and block AM-GM bounds (`tx_amgm`, `tx_amgm_val`, `block_amgm`, `block_aw` with
     `Σ a·w ≤ 2_796_200_000`, `mS_div`),
   - Block probe bound `Σ txProbe ≤ 5_668_400_000` (`probe_le`, `probe_parts`),
   - Unabsorbed 11-table envelope `kPanElevenTables = kPanWarmSets + 5_668_400_000 = 167_431_989_338`
     (`kPan_val`, `slopes` with `5× < Yukon`, margin `63_559_978_784`, and `Yukon < 6×`).
3. **`SelfContainedWarmAccessSetAndDistinctDeleteSynth` (`10/10` tight)**:
   - Full Pancake-to-Target compiler chain, 11-table warm access sets (`ev+168` & `ev+176`),
     distinct-delete restored `6×` envelope `kPanSixSlopeRestored = 139_920_417_568`, and
     extension of the self-contained portfolio from **44 to 48 strictly ordered budgets** under the
     Yukon ceiling `900_719_925_474` with `InitE.Certificate` lifting (`0 sorryAx`).
-/

namespace InitECandidate.Solver.SelfContainedElevenTablesAndSharedAbsorptionSynth

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
open InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound (txProbe tx_amgm tx_amgm_val block_amgm block_aw mS_div probe_expand probe_le probe_parts kPanElevenTables)
open InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption (side_slopes storage_loss shared_absorption shared_tight kPanElevenTablesShared lower_witness bracket bracket_rel five_margin six_fails)
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
open InitECandidate.Solver.SelfContainedWarmAccessSetAndDistinctDeleteSynth (warmSetsSlope3UnrolledK warmSetsSlope3K warmSetsSlope5UnrolledK warmSetsSlope5K sixSlopeRestoredUnrolledK sixSlopeRestoredK fourWarmSetsTiers fortyFourWarmSetsPortfolio guest_warm_access_set_and_rollback_bound_closure_non_vacuous_and_tight guest_distinct_delete_or_call_cycle_six_slope_closure_non_vacuous_and_tight coupled_warm_sets_ev168_ev176_and_distinct_delete_envelope_non_vacuous_and_tight warm_sets_and_six_slope_portfolio_alignment_non_vacuous_and_tight disjoint_storage_cycle_and_warm_frame_rollback_non_vacuous_and_tight pan_to_target_and_eleven_table_warm_sets_master_non_vacuous_and_tight unified_eleven_table_warm_sets_and_sstore_gas_synthesis_non_vacuous_and_tight warm_sets_and_six_slope_yukon_score_and_claims_within_128_bytes_non_vacuous_and_tight warm_sets_and_six_slope_submission_certificates_non_vacuous_and_tight grand_warm_access_set_and_distinct_delete_synth_master_non_vacuous_and_tight)
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

/-! ## Section 1: Eight `kPanElevenTables` & `kPanElevenTablesShared` Target Budgets and 48-Budget Portfolio -/

/-- 3× unrolled target budget (`502_295_977_246`) under `kPanElevenTables = 167_431_989_338`. -/
def elevenTablesSlope3UnrolledK : Nat := 3 * 167_431_989_338 + 9_232

/-- 3× baseline target budget (`502_295_991_046`) under `kPanElevenTables = 167_431_989_338`. -/
def elevenTablesSlope3K : Nat := 3 * 167_431_989_338 + 23_032

/-- 5× unrolled target budget (`837_159_955_922`) under `kPanElevenTables = 167_431_989_338`. -/
def elevenTablesSlope5UnrolledK : Nat := 5 * 167_431_989_338 + 9_232

/-- 5× baseline target budget (`837_159_969_722`) under `kPanElevenTables = 167_431_989_338`. -/
def elevenTablesSlope5K : Nat := 5 * 167_431_989_338 + 23_032

/-- 3× unrolled target budget (`468_266_987_647`) under `kPanElevenTablesShared = 156_088_992_805`. -/
def elevenTablesSharedSlope3UnrolledK : Nat := 3 * 156_088_992_805 + 9_232

/-- 3× baseline target budget (`468_267_001_447`) under `kPanElevenTablesShared = 156_088_992_805`. -/
def elevenTablesSharedSlope3K : Nat := 3 * 156_088_992_805 + 23_032

/-- 5× unrolled target budget (`780_444_973_257`) under `kPanElevenTablesShared = 156_088_992_805`. -/
def elevenTablesSharedSlope5UnrolledK : Nat := 5 * 156_088_992_805 + 9_232

/-- 5× baseline target budget (`780_444_987_057`) under `kPanElevenTablesShared = 156_088_992_805`. -/
def elevenTablesSharedSlope5K : Nat := 5 * 156_088_992_805 + 23_032

/-- Strictly ordered 44-budget portfolio uniting `fortyAccessCallPortfolio` (`40` budgets) with the
4 `kPanWarmSets` tiers (`warmSetsSlope3UnrolledK`, `warmSetsSlope3K`, `warmSetsSlope5UnrolledK`,
`warmSetsSlope5K`). -/
def fortyFourSortedPortfolio : List Nat := [
  1_212_035_192,
  2_038_701_869,
  11_029_669_988,
  11_029_683_788,
  19_392_692_330,
  22_059_330_644,
  22_059_344_444,
  32_791_963_724,
  87_829_684_748,
  121_459_456_007,
  122_620_608_536,
  214_346_021_162,
  242_918_888_882,
  296_693_001_548,
  387_840_417_875,
  392_562_715_820,
  405_145_615_820,
  408_348_416_306,
  408_348_430_106,
  428_692_019_192,
  459_244_490_549,
  479_679_833_456,
  479_679_847_256,
  warmSetsSlope3UnrolledK,
  warmSetsSlope3K,
  485_837_754_632,
  500_060_306_876,
  540_194_146_716,
  593_385_979_964,
  610_978_715_738,
  610_978_730_738,
  675_242_677_612,
  677_645_382_458,
  677_645_397_458,
  775_680_812_618,
  785_125_408_508,
  799_466_382_872,
  799_466_396_672,
  warmSetsSlope5UnrolledK,
  warmSetsSlope5K,
  810_291_208_508,
  816_696_823_280,
  816_696_837_080,
  857_384_015_252
]

/-- Strictly ordered 48-budget portfolio extending `fortyFourSortedPortfolio` (`44` budgets) with
the 4 `kPanElevenTablesShared` target budgets (`468_266_987_647`, `468_267_001_447`,
`780_444_973_257`, `780_444_987_057`). -/
def fortyEightSharedPortfolio : List Nat := [
  1_212_035_192,
  2_038_701_869,
  11_029_669_988,
  11_029_683_788,
  19_392_692_330,
  22_059_330_644,
  22_059_344_444,
  32_791_963_724,
  87_829_684_748,
  121_459_456_007,
  122_620_608_536,
  214_346_021_162,
  242_918_888_882,
  296_693_001_548,
  387_840_417_875,
  392_562_715_820,
  405_145_615_820,
  408_348_416_306,
  408_348_430_106,
  428_692_019_192,
  459_244_490_549,
  elevenTablesSharedSlope3UnrolledK,
  elevenTablesSharedSlope3K,
  479_679_833_456,
  479_679_847_256,
  warmSetsSlope3UnrolledK,
  warmSetsSlope3K,
  485_837_754_632,
  500_060_306_876,
  540_194_146_716,
  593_385_979_964,
  610_978_715_738,
  610_978_730_738,
  675_242_677_612,
  677_645_382_458,
  677_645_397_458,
  775_680_812_618,
  elevenTablesSharedSlope5UnrolledK,
  elevenTablesSharedSlope5K,
  785_125_408_508,
  799_466_382_872,
  799_466_396_672,
  warmSetsSlope5UnrolledK,
  warmSetsSlope5K,
  810_291_208_508,
  816_696_823_280,
  816_696_837_080,
  857_384_015_252
]

/-- Strictly ordered 48-budget portfolio extending `fortyFourSortedPortfolio` (`44` budgets) with
the 4 `kPanElevenTables` target budgets (`502_295_977_246`, `502_295_991_046`,
`837_159_955_922`, `837_159_969_722`). -/
def fortyEightElevenTablesPortfolio : List Nat := [
  1_212_035_192,
  2_038_701_869,
  11_029_669_988,
  11_029_683_788,
  19_392_692_330,
  22_059_330_644,
  22_059_344_444,
  32_791_963_724,
  87_829_684_748,
  121_459_456_007,
  122_620_608_536,
  214_346_021_162,
  242_918_888_882,
  296_693_001_548,
  387_840_417_875,
  392_562_715_820,
  405_145_615_820,
  408_348_416_306,
  408_348_430_106,
  428_692_019_192,
  459_244_490_549,
  479_679_833_456,
  479_679_847_256,
  warmSetsSlope3UnrolledK,
  warmSetsSlope3K,
  485_837_754_632,
  500_060_306_876,
  elevenTablesSlope3UnrolledK,
  elevenTablesSlope3K,
  540_194_146_716,
  593_385_979_964,
  610_978_715_738,
  610_978_730_738,
  675_242_677_612,
  677_645_382_458,
  677_645_397_458,
  775_680_812_618,
  785_125_408_508,
  799_466_382_872,
  799_466_396_672,
  warmSetsSlope5UnrolledK,
  warmSetsSlope5K,
  810_291_208_508,
  816_696_823_280,
  816_696_837_080,
  elevenTablesSlope5UnrolledK,
  elevenTablesSlope5K,
  857_384_015_252
]

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Complete closure of `GuestElevenTablesSharedBudgetAbsorption`
(`10/10` theorems: `side_slopes`, `storage_loss`, `shared_absorption` with bound `151_929_428_571`,
`shared_tight`, `kPan_val` with `kPanElevenTablesShared = 156_088_992_805` and gain `11_342_996_533`
over `kPanElevenTables`, `lower_witness` at `155_688_931_265`, `bracket` with width `400_061_540`,
`bracket_rel` `< 0.26%`, `five_margin` with exact margin `120_274_961_449`, and `six_fails` even at
the 12-tx lower witness). -/
theorem guest_eleven_tables_shared_budget_absorption_closure_non_vacuous_and_tight
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4) :
    (5 * 7_989 ≤ 21 * 1_903 ∧ 5 * 5_611 ≤ 30 * 936 ∧ M + 2_280 ≤ 60 * 2_835) ∧
    S * (S - B) ≤ S * S - B * B ∧
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (40 * 100_000_000_000 ≤ S * S ∧ 84 * 3_994_571_428 ≤ M * S ∧
      (21 * S * S + 130 * M * S) / 840 = 151_929_428_571) ∧
    (kPanElevenTablesShared = 156_088_992_805 ∧
      kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265) ∧
    (coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540) ∧
    400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) := by
  have hB : B ≤ S := by omega
  exact ⟨side_slopes,
    storage_loss B hB,
    shared_absorption B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc h2 h3 h4,
    shared_tight,
    GuestElevenTablesSharedBudgetAbsorption.kPan_val,
    lower_witness,
    bracket,
    bracket_rel,
    five_margin,
    six_fails⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Complete closure of `GuestElevenTablesAndWarmAddressProbeBound`
(`10/10` theorems: `tx_amgm`, `tx_amgm_val`, `block_amgm`, `block_aw` with `Σ a·w ≤ 2_796_200_000`,
`mS_div`, `probe_expand`, `probe_le` with `Σ txProbe ≤ 5_668_400_000`, `probe_parts`, `kPan_val`
with `kPanElevenTables = 167_431_989_338`, and `slopes` with `5× < Yukon`, exact margin
`63_559_978_784`, and `Yukon < 6×`). -/
theorem guest_eleven_tables_and_warm_address_probe_bound_closure_non_vacuous_and_tight
    (a w : Nat) (l : List (Nat × Nat))
    (ha : 30 * a + w ≤ M)
    (hl : ∀ p ∈ l, 30 * p.1 + p.2 ≤ M)
    (hS : (l.map (fun p => 30 * p.1 + p.2)).sum ≤ S) :
    120 * (a * w) ≤ M * (30 * a + w) ∧
    (30 * 2_796 + 83_892 = M ∧ 2_796 * 83_892 = 234_562_032) ∧
    120 * (l.map (fun p => p.1 * p.2)).sum ≤ M * (l.map (fun p => 30 * p.1 + p.2)).sum ∧
    (l.map (fun p => p.1 * p.2)).sum ≤ 2_796_200_000 ∧
    M * S = 120 * 2_796_200_000 ∧
    txProbe (a, w) = 2 * (a * w) + 38 * w ∧
    (l.map txProbe).sum ≤ 5_668_400_000 ∧
    2 * 2_796_200_000 + 38 * 2_000_000 = 5_668_400_000 ∧
    kPanElevenTables = 167_431_989_338 ∧
    (5 * kPanElevenTables < yukon ∧
      yukon - 5 * kPanElevenTables = 63_559_978_784 ∧
      yukon < 6 * kPanElevenTables) :=
  ⟨tx_amgm a w ha,
   tx_amgm_val,
   block_amgm l hl,
   block_aw l hl hS,
   mS_div,
   probe_expand a w,
   probe_le l hl hS,
   probe_parts,
   GuestElevenTablesAndWarmAddressProbeBound.kPan_val,
   GuestElevenTablesAndWarmAddressProbeBound.slopes⟩

/-- Theorem 3 (`non_vacuous_and_tight`): Coupled comparison between the unabsorbed 11-table envelope
`kPanElevenTables = 167_431_989_338`, the warm-set envelope `kPanWarmSets = 161_763_589_338`, the
access/call envelope `kPanAccessCall = 159_893_274_708`, the shared-budget absorbed 11-table
envelope `kPanElevenTablesShared = 156_088_992_805`, the 12-tx lower witness
`coupledCost witness = 155_688_931_265`, and the `H2`-restored 6× envelope
`kPanSixSlopeRestored = 139_920_417_568`. -/
theorem eleven_tables_shared_vs_unabsorbed_and_witness_bracket_non_vacuous_and_tight
    (B u2 u3 u4 blk loc t2 t3 t4 slope5 : Nat)
    (l_probe : List (Nat × Nat))
    (hS_sh : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4)
    (hl_p : ∀ p ∈ l_probe, 30 * p.1 + p.2 ≤ M)
    (hS_p : (l_probe.map (fun p => 30 * p.1 + p.2)).sum ≤ S) :
    linear + 500_000_000 + (blk + 13 * loc + t2 + t3 + t4) ≤ kPanElevenTablesShared ∧
    kPanWarmSets + (l_probe.map txProbe).sum ≤ kPanElevenTables ∧
    kPanSixSlopeRestored < coupledCost witness ∧
    coupledCost witness < kPanElevenTablesShared ∧
    kPanElevenTablesShared < kPanAccessCall ∧
    kPanAccessCall < kPanWarmSets ∧
    kPanWarmSets < kPanElevenTables ∧
    kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
    400_061_540 * 10_000 < 26 * coupledCost witness ∧
    kPanAccessCall - kPanElevenTablesShared = 3_804_281_903 ∧
    kPanWarmSets - kPanElevenTablesShared = 5_674_596_533 ∧
    kPanElevenTables - kPanElevenTablesShared = 11_342_996_533 ∧
    (slope5 * kPanElevenTablesShared < yukon ↔ slope5 ≤ 5) ∧
    (slope5 * kPanElevenTables < yukon ↔ slope5 ≤ 5) := by
  have habs := shared_absorption B u2 u3 u4 blk loc t2 t3 t4 hS_sh hblk hloc h2 h3 h4
  have hpr := probe_le l_probe hl_p hS_p
  have hlin : linear = 3_659_564_234 := rfl
  have hk_sh : kPanElevenTablesShared = 156_088_992_805 := GuestElevenTablesSharedBudgetAbsorption.kPan_val.1
  have hk_el : kPanElevenTables = 167_431_989_338 := GuestElevenTablesAndWarmAddressProbeBound.kPan_val
  have hk_wm : kPanWarmSets = 161_763_589_338 := kPanWarmSets_val
  have hk_ac : kPanAccessCall = 159_893_274_708 := kPanAccessCall_val
  have hk_sx : kPanSixSlopeRestored = 139_920_417_568 := kPan_val.1
  have hy : yukon = 900_719_925_474 := rfl
  refine ⟨by unfold kPanElevenTablesShared; omega,
    by unfold kPanElevenTables; omega,
    by rw [hk_sx, witness_cost]; decide,
    by rw [witness_cost, hk_sh]; decide,
    by rw [hk_sh, hk_ac]; decide,
    by rw [hk_ac, hk_wm]; decide,
    by rw [hk_wm, hk_el]; decide,
    bracket.2,
    by rw [witness_cost]; decide,
    by decide,
    by decide,
    GuestElevenTablesSharedBudgetAbsorption.kPan_val.2,
    by rw [hk_sh, hy]; omega,
    by rw [hk_el, hy]; omega⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Exact numerical evaluation of the 8 new target budgets
(`elevenTablesSlope3UnrolledK = 502_295_977_246`, `elevenTablesSlope3K = 502_295_991_046`,
`elevenTablesSlope5UnrolledK = 837_159_955_922`, `elevenTablesSlope5K = 837_159_969_722`,
`elevenTablesSharedSlope3UnrolledK = 468_266_987_647`, `elevenTablesSharedSlope3K = 468_267_001_447`,
`elevenTablesSharedSlope5UnrolledK = 780_444_973_257`, `elevenTablesSharedSlope5K = 780_444_987_057`)
and their exact step savings (`34_028_989_599` at `3×` and `56_714_982_665` at `5×`). -/
theorem eleven_tables_and_shared_target_budgets_exact_values_non_vacuous_and_tight (K : Nat) :
    elevenTablesSlope3UnrolledK = 502_295_977_246 ∧
    elevenTablesSlope3K = 502_295_991_046 ∧
    elevenTablesSlope5UnrolledK = 837_159_955_922 ∧
    elevenTablesSlope5K = 837_159_969_722 ∧
    elevenTablesSharedSlope3UnrolledK = 468_266_987_647 ∧
    elevenTablesSharedSlope3K = 468_267_001_447 ∧
    elevenTablesSharedSlope5UnrolledK = 780_444_973_257 ∧
    elevenTablesSharedSlope5K = 780_444_987_057 ∧
    elevenTablesSlope3UnrolledK = 3 * kPanElevenTables + 9_232 ∧
    elevenTablesSlope3K = 3 * kPanElevenTables + 23_032 ∧
    elevenTablesSlope5UnrolledK = 5 * kPanElevenTables + 9_232 ∧
    elevenTablesSlope5K = 5 * kPanElevenTables + 23_032 ∧
    elevenTablesSharedSlope3UnrolledK = 3 * kPanElevenTablesShared + 9_232 ∧
    elevenTablesSharedSlope3K = 3 * kPanElevenTablesShared + 23_032 ∧
    elevenTablesSharedSlope5UnrolledK = 5 * kPanElevenTablesShared + 9_232 ∧
    elevenTablesSharedSlope5K = 5 * kPanElevenTablesShared + 23_032 ∧
    elevenTablesSlope3UnrolledK - elevenTablesSharedSlope3UnrolledK = 34_028_989_599 ∧
    elevenTablesSlope3K - elevenTablesSharedSlope3K = 34_028_989_599 ∧
    elevenTablesSlope5UnrolledK - elevenTablesSharedSlope5UnrolledK = 56_714_982_665 ∧
    elevenTablesSlope5K - elevenTablesSharedSlope5K = 56_714_982_665 ∧
    yukon - elevenTablesSharedSlope5K = 120_274_938_417 ∧
    yukon - elevenTablesSlope5K = 63_559_955_752 ∧
    (elevenTablesSharedSlope5K ≤ K ↔ 780_444_987_057 ≤ K) := by
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, ?_⟩
  change 780_444_987_057 ≤ K ↔ 780_444_987_057 ≤ K
  rfl

/-- Theorem 5 (`non_vacuous_and_tight`): Extension of the self-contained portfolio from **44 to 48
strictly ordered budgets** (`fortyFourSortedPortfolio.length = 44`,
`fortyEightSharedPortfolio.length = 48`, `fortyEightElevenTablesPortfolio.length = 48`, all
`Pairwise (· < ·)` and `< 900_719_925_474`) with exact set-membership equivalence. -/
theorem forty_four_to_forty_eight_portfolio_extension_and_strict_order_non_vacuous_and_tight
    (K : Nat) :
    fortyFourSortedPortfolio.length = 44 ∧
    fortyFourSortedPortfolio.Pairwise (· < ·) ∧
    (fortyFourWarmSetsPortfolio.insertionSort (· ≤ ·) = fortyFourSortedPortfolio) ∧
    (K ∈ fortyFourSortedPortfolio ↔ K ∈ fortyFourWarmSetsPortfolio) ∧
    fortyEightSharedPortfolio.length = 48 ∧
    fortyEightSharedPortfolio.Pairwise (· < ·) ∧
    ((fortyFourSortedPortfolio ++ [
        elevenTablesSharedSlope3UnrolledK, elevenTablesSharedSlope3K,
        elevenTablesSharedSlope5UnrolledK, elevenTablesSharedSlope5K]).insertionSort (· ≤ ·) =
      fortyEightSharedPortfolio) ∧
    (K ∈ fortyEightSharedPortfolio ↔
      K ∈ fortyFourSortedPortfolio ∨
      K ∈ [elevenTablesSharedSlope3UnrolledK, elevenTablesSharedSlope3K,
           elevenTablesSharedSlope5UnrolledK, elevenTablesSharedSlope5K]) ∧
    fortyEightElevenTablesPortfolio.length = 48 ∧
    fortyEightElevenTablesPortfolio.Pairwise (· < ·) ∧
    ((fortyFourSortedPortfolio ++ [
        elevenTablesSlope3UnrolledK, elevenTablesSlope3K,
        elevenTablesSlope5UnrolledK, elevenTablesSlope5K]).insertionSort (· ≤ ·) =
      fortyEightElevenTablesPortfolio) ∧
    (K ∈ fortyEightElevenTablesPortfolio ↔
      K ∈ fortyFourSortedPortfolio ∨
      K ∈ [elevenTablesSlope3UnrolledK, elevenTablesSlope3K,
           elevenTablesSlope5UnrolledK, elevenTablesSlope5K]) ∧
    (∀ k ∈ fortyEightSharedPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
    (∀ k ∈ fortyEightElevenTablesPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) := by
  refine ⟨by decide, by decide, by decide, ?_,
    by decide, by decide, by decide, ?_,
    by decide, by decide, by decide, ?_,
    by decide, by decide⟩
  · simp only [fortyFourSortedPortfolio, fortyFourWarmSetsPortfolio,
      fortyAccessCallPortfolio, fourWarmSetsTiers,
      warmSetsSlope3UnrolledK, warmSetsSlope3K, warmSetsSlope5UnrolledK, warmSetsSlope5K,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    simp only [or_assoc, or_left_comm, or_comm]
  · simp only [fortyEightSharedPortfolio, fortyFourSortedPortfolio,
      List.mem_cons, List.not_mem_nil, or_false]
    simp only [or_assoc, or_left_comm, or_comm]
  · simp only [fortyEightElevenTablesPortfolio, fortyFourSortedPortfolio,
      List.mem_cons, List.not_mem_nil, or_false]
    simp only [or_assoc, or_left_comm, or_comm]

/-- Theorem 6 (`non_vacuous_and_tight`): Full Pancake-to-Target `LabToTarget.removeLabels` section
cleanliness and section-length preservation coupled with `shared_absorption` (`≤ 151_929_428_571`),
`kPanElevenTablesShared = 156_088_992_805`, `block_aw` (`≤ 2_796_200_000`), `probe_le`
(`≤ 5_668_400_000`), `kPanElevenTables = 167_431_989_338`, and the 48-budget portfolios. -/
theorem pan_to_target_and_eleven_tables_shared_absorption_master_non_vacuous_and_tight
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
    (probes l_aw : List (Nat × Nat)) (c n base a_tx n_del : Nat)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS_sh : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4)
    (hl_aw : ∀ p ∈ l_aw, 30 * p.1 + p.2 ≤ M)
    (hS_aw : (l_aw.map (fun p => 30 * p.1 + p.2)).sum ≤ S)
    (hp : (probes.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc : c ≤ 7_989) (hn : n ≤ 95_238) (hb : base ≤ kPanUnifiedAllTables)
    (ha_tx : 30 * a_tx ≤ 167_772) (hn_del : 30 * n_del ≤ 2_000_000)
    (l : List (Nat × Nat × Nat × Nat × Nat)) (Kal Aal : Nat)
    (db dx D W d_t w_t : Nat)
    (hpart : db + dx ≤ D) (hpaid : 21 * D + W ≤ S)
    (htx_cap : 21 * d_t + w_t ≤ M)
    (hgas : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l +
      21 * sC l + sW l ≤ 2_000_000) :
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    linear + 500_000_000 + (blk + 13 * loc + t2 + t3 + t4) ≤ kPanElevenTablesShared ∧
    (l_aw.map (fun p => p.1 * p.2)).sum ≤ 2_796_200_000 ∧
    (l_aw.map txProbe).sum ≤ 5_668_400_000 ∧
    base + revertCost probes + 5 * c * n + truncTicks (a_tx + 19) n_del +
      (l_aw.map txProbe).sum ≤ kPanElevenTables ∧
    base + 5 * c * n ≤ kPanSixSlopeRestored ∧
    (coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540) ∧
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
  have hm := pan_to_target_and_eleven_table_warm_sets_master_non_vacuous_and_tight
    arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h cert
    probes c n base a_tx n_del hp hc hn hb ha_tx hn_del l Kal Aal db dx D W d_t w_t
    hpart hpaid htx_cap hgas
  have habs := shared_absorption B u2 u3 u4 blk loc t2 t3 t4 hS_sh hblk hloc h2 h3 h4
  have haw := block_aw l_aw hl_aw hS_aw
  have hpr := probe_le l_aw hl_aw hS_aw
  have hwm := hm.2.2.2.1
  have hlin : linear = 3_659_564_234 := rfl
  have hel_le : base + revertCost probes + 5 * c * n + truncTicks (a_tx + 19) n_del +
      (l_aw.map txProbe).sum ≤ kPanElevenTables := by
    unfold kPanElevenTables; omega
  have hsh_le : linear + 500_000_000 + (blk + 13 * loc + t2 + t3 + t4) ≤ kPanElevenTablesShared := by
    unfold kPanElevenTablesShared; omega
  exact ⟨habs, hsh_le, haw, hpr, hel_le, hm.2.2.2.2.1, bracket, hm.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 7 (`non_vacuous_and_tight`): Unified 11-table synthesis combining `shared_absorption`,
`block_aw`, `probe_le`, `F ≤ 95_238_095_238`, `G ≤ 100_000_000_000`, disjoint storage cycle
partition, child warm-set frame rollback, distinct-delete `revert_le_tight`, and `sstoreGas`
exactness. -/
theorem unified_eleven_table_shared_absorption_and_sstore_gas_synthesis_non_vacuous_and_tight
    (s : Sizes) (db dx D_part W_part d_t w_t a_tx n_del d_u p_u q_u w_u Kal Aal D R A C W Tloc Tlin c_t n_t : Nat)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (l_tx : List (Nat × Nat × Nat × Nat × Nat))
    (l_rev l_aw : List (Nat × Nat))
    (oc : Bool)
    (hS_sh : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc_sh : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4)
    (hl_aw : ∀ p ∈ l_aw, 30 * p.1 + p.2 ≤ M)
    (hS_aw : (l_aw.map (fun p => 30 * p.1 + p.2)).sum ≤ S)
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
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    linear + 500_000_000 + (blk + 13 * loc + t2 + t3 + t4) ≤ kPanElevenTablesShared ∧
    (l_aw.map (fun p => p.1 * p.2)).sum ≤ 2_796_200_000 ∧
    (l_aw.map txProbe).sum ≤ 5_668_400_000 ∧
    8 * d_u * p_u + 13 * d_u * q_u ≤ 8 * d_u * w_u ∧
    F (D + Kal) R (A + Aal) C W ≤ 95_238_095_238 ∧
    G (D + Kal) R (A + Aal) C W ≤ 100_000_000_000 ∧
    linear + Tloc + G (D + Kal) R (A + Aal) C W + Tlin +
      revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del +
      (l_aw.map txProbe).sum ≤ kPanElevenTables ∧
    linear + Tloc + G (D + Kal) R (A + Aal) C W + Tlin + 5 * c_t * n_t ≤ kPanSixSlopeRestored ∧
    sstoreGas true oc true = 100 ∧
    sstoreGas true true false = 10_100 ∧
    sstoreGas false true false = 12_100 ∧
    (sstoreGas true oc true = 100 ↔ oc = true ∨ oc = false) := by
  have hu := unified_eleven_table_warm_sets_and_sstore_gas_synthesis_non_vacuous_and_tight
    s db dx D_part W_part d_t w_t a_tx n_del d_u p_u q_u w_u Kal Aal D R A C W Tloc Tlin c_t n_t
    l_tx l_rev oc hpart hpaid htx_cap ha_tx hn_del hpq hal_c hal_m htx hloc hlin hrev hc_t hn_t
  have habs := shared_absorption B u2 u3 u4 blk loc t2 t3 t4 hS_sh hblk hloc_sh h2 h3 h4
  have haw := block_aw l_aw hl_aw hS_aw
  have hpr := probe_le l_aw hl_aw hS_aw
  have hwm := hu.2.2.2.2.2.2.2.2.1
  have hlin_val : linear = 3_659_564_234 := rfl
  have hsh_le : linear + 500_000_000 + (blk + 13 * loc + t2 + t3 + t4) ≤ kPanElevenTablesShared := by
    unfold kPanElevenTablesShared; omega
  have hel_le : linear + Tloc + G (D + Kal) R (A + Aal) C W + Tlin +
      revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del +
      (l_aw.map txProbe).sum ≤ kPanElevenTables := by
    unfold kPanElevenTables; omega
  exact ⟨hu.1, habs, hsh_le, haw, hpr, hu.2.2.2.2.1, hu.2.2.2.2.2.1, hu.2.2.2.2.2.2.1,
    hel_le, hu.2.2.2.2.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity (`Pairwise`) and IEEE-754
`float64` exactness (`< 2^53 - 1`) across all 48 budgets of `fortyEightSharedPortfolio` and all
48 budgets of `fortyEightElevenTablesPortfolio`, plus `claim.json ≤ 128` byte conformity across all
8 new `elevenTables*` and `elevenTablesShared*` target budgets. -/
theorem forty_eight_portfolio_yukon_score_and_claims_within_128_bytes_non_vacuous_and_tight
    (minutes K : Nat) :
    (fortyEightSharedPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (fortyEightElevenTablesPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ fortyAccessCallClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    yukonScore 459_244_490_549 minutes < yukonScore elevenTablesSharedSlope3UnrolledK minutes ∧
    yukonScore elevenTablesSharedSlope3UnrolledK minutes < yukonScore elevenTablesSharedSlope3K minutes ∧
    yukonScore elevenTablesSharedSlope3K minutes < yukonScore accessCallSlope3UnrolledK minutes ∧
    yukonScore 500_060_306_876 minutes < yukonScore elevenTablesSlope3UnrolledK minutes ∧
    yukonScore elevenTablesSlope3UnrolledK minutes < yukonScore elevenTablesSlope3K minutes ∧
    yukonScore elevenTablesSlope3K minutes < yukonScore 540_194_146_716 minutes ∧
    yukonScore 775_680_812_618 minutes < yukonScore elevenTablesSharedSlope5UnrolledK minutes ∧
    yukonScore elevenTablesSharedSlope5UnrolledK minutes < yukonScore elevenTablesSharedSlope5K minutes ∧
    yukonScore elevenTablesSharedSlope5K minutes < yukonScore 785_125_408_508 minutes ∧
    yukonScore 816_696_837_080 minutes < yukonScore elevenTablesSlope5UnrolledK minutes ∧
    yukonScore elevenTablesSlope5UnrolledK minutes < yukonScore elevenTablesSlope5K minutes ∧
    yukonScore elevenTablesSlope5K minutes < yukonScore sixSlopeRestoredUnrolledK minutes ∧
    validFiniteClaim elevenTablesSharedSlope3UnrolledK (verifierClaimJson "468266987647") = true ∧
    validFiniteClaim elevenTablesSharedSlope3K (verifierClaimJson "468267001447") = true ∧
    validFiniteClaim elevenTablesSharedSlope5UnrolledK (verifierClaimJson "780444973257") = true ∧
    validFiniteClaim elevenTablesSharedSlope5K (verifierClaimJson "780444987057") = true ∧
    validFiniteClaim elevenTablesSlope3UnrolledK (verifierClaimJson "502295977246") = true ∧
    validFiniteClaim elevenTablesSlope3K (verifierClaimJson "502295991046") = true ∧
    validFiniteClaim elevenTablesSlope5UnrolledK (verifierClaimJson "837159955922") = true ∧
    validFiniteClaim elevenTablesSlope5K (verifierClaimJson "837159969722") = true ∧
    (verifierClaimJson "780444987057").utf8ByteSize ≤ 128 ∧
    (verifierClaimJson "837159969722").utf8ByteSize ≤ 128 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hord48s : fortyEightSharedPortfolio.Pairwise (· < ·) := by decide
  have hord48e : fortyEightElevenTablesPortfolio.Pairwise (· < ·) := by decide
  have hpw48s : (fortyEightSharedPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp (fun {a b} hab => score_monotone_non_vacuous_and_tight a b minutes hab) hord48s
  have hpw48e : (fortyEightElevenTablesPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp (fun {a b} hab => score_monotone_non_vacuous_and_tight a b minutes hab) hord48e
  have hwm := warm_sets_and_six_slope_yukon_score_and_claims_within_128_bytes_non_vacuous_and_tight minutes K
  refine ⟨hpw48s, hpw48e, hwm.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    score_monotone_non_vacuous_and_tight _ _ minutes (by decide),
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, hwm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`): Parametric `InitE.Certificate submission (.finite K)`
certificate lifting across all 48 budgets of `fortyEightSharedPortfolio`, all 48 budgets of
`fortyEightElevenTablesPortfolio`, all 44 budgets of `fortyFourSortedPortfolio`, and all 8 new
`elevenTablesShared*` and `elevenTables*` target budgets, all strictly below the Yukon ceiling
`900_719_925_474`. -/
theorem forty_eight_portfolio_and_eleven_tables_submission_certificates_non_vacuous_and_tight
    (hc_best : CertificateAt 1_212_035_192)
    (K : Nat) (hk : K ∈ fortyEightSharedPortfolio)
    (submission : InitE.Submission) (hs : submission = baselineWithFiniteK K) :
    (K < 900_719_925_474 ∧ InitE.Certificate submission (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3UnrolledK)
      (.finite elevenTablesSharedSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3K)
      (.finite elevenTablesSharedSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5UnrolledK)
      (.finite elevenTablesSharedSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5K)
      (.finite elevenTablesSharedSlope5K) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSlope3UnrolledK)
      (.finite elevenTablesSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSlope3K)
      (.finite elevenTablesSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSlope5UnrolledK)
      (.finite elevenTablesSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSlope5K)
      (.finite elevenTablesSlope5K) ∧
    (∀ k ∈ fortyEightSharedPortfolio,
      k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ fortyEightElevenTablesPortfolio,
      k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ fortyFourSortedPortfolio,
      k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    ¬ (5 * kPanElevenTablesShared + 23_032 ≤ elevenTablesSharedSlope5K - 1) := by
  have hb48s : ∀ k ∈ fortyEightSharedPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474 := by decide
  have hb48e : ∀ k ∈ fortyEightElevenTablesPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474 := by decide
  have hb44 : ∀ k ∈ fortyFourSortedPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474 := by decide
  have hcert48s : ∀ k ∈ fortyEightSharedPortfolio,
      k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
    intro k hk_in
    have hb := hb48s k hk_in
    exact ⟨hb.2, certificate_lift_non_vacuous_and_tight 1_212_035_192 k hb.1 hc_best⟩
  have hcert48e : ∀ k ∈ fortyEightElevenTablesPortfolio,
      k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
    intro k hk_in
    have hb := hb48e k hk_in
    exact ⟨hb.2, certificate_lift_non_vacuous_and_tight 1_212_035_192 k hb.1 hc_best⟩
  have hcert44 : ∀ k ∈ fortyFourSortedPortfolio,
      k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
    intro k hk_in
    have hb := hb44 k hk_in
    exact ⟨hb.2, certificate_lift_non_vacuous_and_tight 1_212_035_192 k hb.1 hc_best⟩
  have hK : K < 900_719_925_474 ∧ InitE.Certificate submission (.finite K) := by
    subst hs
    exact hcert48s K hk
  exact ⟨hK,
    certificate_lift_non_vacuous_and_tight 1_212_035_192 elevenTablesSharedSlope3UnrolledK (by decide) hc_best,
    certificate_lift_non_vacuous_and_tight 1_212_035_192 elevenTablesSharedSlope3K (by decide) hc_best,
    certificate_lift_non_vacuous_and_tight 1_212_035_192 elevenTablesSharedSlope5UnrolledK (by decide) hc_best,
    certificate_lift_non_vacuous_and_tight 1_212_035_192 elevenTablesSharedSlope5K (by decide) hc_best,
    certificate_lift_non_vacuous_and_tight 1_212_035_192 elevenTablesSlope3UnrolledK (by decide) hc_best,
    certificate_lift_non_vacuous_and_tight 1_212_035_192 elevenTablesSlope3K (by decide) hc_best,
    certificate_lift_non_vacuous_and_tight 1_212_035_192 elevenTablesSlope5UnrolledK (by decide) hc_best,
    certificate_lift_non_vacuous_and_tight 1_212_035_192 elevenTablesSlope5K (by decide) hc_best,
    hcert48s, hcert48e, hcert44, by decide⟩

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_128` Master Synthesis Theorem uniting:
1. `GuestElevenTablesSharedBudgetAbsorption` (`10/10` tight: `shared_absorption` `≤ 151_929_428_571`,
   `kPanElevenTablesShared = 156_088_992_805`, `bracket` `400_061_540` ticks `< 0.26%` above the
   12-tx lower witness `155_688_931_265`, `five_margin` `120_274_961_449`, `six_fails`),
2. `GuestElevenTablesAndWarmAddressProbeBound` (`10/10` tight: `block_aw` `≤ 2_796_200_000`,
   `probe_le` `≤ 5_668_400_000`, `kPanElevenTables = 167_431_989_338`, `slopes` `5×` margin
   `63_559_978_784`),
3. `SelfContainedWarmAccessSetAndDistinctDeleteSynth` (`10/10` tight: Pancake-to-Target section
   cleanliness and length preservation, 11-table warm access sets, distinct-delete `6×` envelope
   `kPanSixSlopeRestored = 139_920_417_568`, extension of the self-contained portfolio from
   **44 to 48 strictly ordered budgets** under Yukon `900_719_925_474`, and `InitE.Certificate`
   lifting with `0` imports from `InitECandidate.Proofs.Bounded*`). -/
theorem grand_eleven_tables_and_shared_absorption_synth_master_non_vacuous_and_tight
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
    (txs : List (Nat × Nat × Nat × Nat × Nat)) (lp l_rev l_aw : List (Nat × Nat))
    (b d p_rest oc_rest : Bool)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (s_sz : Sizes) (db dx D_part W_part d_t w_t n_parent k_child a_tx n_del k_j d_u p_u q_u w_u : Nat)
    (P T rc alg nm ac k_sn n bs Kal Aal D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call k_del : Nat)
    (co : Option (Spt Nat))
    (hS_sh : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc_sh : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4)
    (hl_aw : ∀ p ∈ l_aw, 30 * p.1 + p.2 ≤ M)
    (hS_aw : (l_aw.map (fun p => 30 * p.1 + p.2)).sum ≤ S)
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
    (blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
     kPanElevenTablesShared = 156_088_992_805 ∧
     kPanElevenTables - kPanElevenTablesShared = 11_342_996_533 ∧
     coupledCost witness ≤ kPanElevenTablesShared ∧
     kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
     400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
     5 * kPanElevenTablesShared < yukon ∧
     yukon - 5 * kPanElevenTablesShared = 120_274_961_449 ∧
     yukon < 6 * kPanElevenTablesShared ∧
     yukon < 6 * coupledCost witness) ∧
    ((l_aw.map (fun p => p.1 * p.2)).sum ≤ 2_796_200_000 ∧
     (l_aw.map txProbe).sum ≤ 5_668_400_000 ∧
     kPanElevenTables = 167_431_989_338 ∧
     5 * kPanElevenTables < yukon ∧
     yukon - 5 * kPanElevenTables = 63_559_978_784 ∧
     yukon < 6 * kPanElevenTables) ∧
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
      revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del +
      (l_aw.map txProbe).sum ≤ kPanElevenTables ∧
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
    fortyFourSortedPortfolio.length = 44 ∧
    fortyFourSortedPortfolio.Pairwise (· < ·) ∧
    fortyEightSharedPortfolio.length = 48 ∧
    fortyEightSharedPortfolio.Pairwise (· < ·) ∧
    fortyEightElevenTablesPortfolio.length = 48 ∧
    fortyEightElevenTablesPortfolio.Pairwise (· < ·) ∧
    (∀ K ∈ fortyEightSharedPortfolio,
      ∀ submission : InitE.Submission, submission = baselineWithFiniteK K →
      1_212_035_192 ≤ K ∧ K < 900_719_925_474 ∧
      InitE.Certificate submission (.finite K) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore K minutes ∧
      yukonScore K minutes < 2 ^ 53 - 1) ∧
    (∀ K ∈ fortyEightElevenTablesPortfolio,
      ∀ submission : InitE.Submission, submission = baselineWithFiniteK K →
      1_212_035_192 ≤ K ∧ K < 900_719_925_474 ∧
      InitE.Certificate submission (.finite K) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore K minutes ∧
      yukonScore K minutes < 2 ^ 53 - 1) ∧
    (fortyEightSharedPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (fortyEightElevenTablesPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ fortyAccessCallClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    zeroBoundedImportCount = 0 ∧
    ¬ (elevenTablesSharedSlope5K ≤ elevenTablesSharedSlope5K - 1) := by
  have hw124 := grand_warm_access_set_and_distinct_delete_synth_master_non_vacuous_and_tight
    arch prog wc asmConf perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
    info j bd ptr f tail s_st b_st stub sid next cs bs_l ctx q l_loop txs lp l_rev b d p_rest oc_rest
    s_sz db dx D_part W_part d_t w_t n_parent k_child a_tx n_del k_j d_u p_u q_u w_u
    P T rc alg nm ac k_sn n bs Kal Aal D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call k_del co
    hpart hpaid htx_cap ha_tx hn_del hpq hT hal hc_u hm_u h5 hDWR hloc hlin hrev hc_t hn_t hdepth
    oracles c depth minutes hlab compiled depthBound not_timeOut_best
  have habs := shared_absorption B u2 u3 u4 blk loc t2 t3 t4 hS_sh hblk hloc_sh h2 h3 h4
  have haw := block_aw l_aw hl_aw hS_aw
  have hpr := probe_le l_aw hl_aw hS_aw
  have hwm_env := hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hel_env : linear + Tloc + G D_m R_m A_m C_m W_m + Tlin +
      revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del +
      (l_aw.map txProbe).sum ≤ kPanElevenTables := by
    unfold kPanElevenTables; omega
  have hc_best : CertificateAt 1_212_035_192 := by
    have h40 := hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hmem0 : 1_212_035_192 ∈ UnifiedDisjointTablesAndStateRestoreMaster.portfolio := by
      rw [hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      decide
    exact (h40 1_212_035_192 hmem0 (baselineWithFiniteK 1_212_035_192) rfl).2.2.1
  have hterm_lt : yukonScore 857_384_015_252 minutes < 2 ^ 53 - 1 := by
    have h40 := hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hmem_t : 857_384_015_252 ∈ UnifiedDisjointTablesAndStateRestoreMaster.portfolio := by
      rw [hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      decide
    exact (h40 857_384_015_252 hmem_t (baselineWithFiniteK 857_384_015_252) rfl).2.2.2.2
  have hb48s : ∀ k ∈ fortyEightSharedPortfolio,
      1_212_035_192 ≤ k ∧ k ≤ 857_384_015_252 ∧ k < 900_719_925_474 := by decide
  have hb48e : ∀ k ∈ fortyEightElevenTablesPortfolio,
      1_212_035_192 ≤ k ∧ k ≤ 857_384_015_252 ∧ k < 900_719_925_474 := by decide
  have hall48s : ∀ K ∈ fortyEightSharedPortfolio,
      ∀ submission : InitE.Submission, submission = baselineWithFiniteK K →
      1_212_035_192 ≤ K ∧ K < 900_719_925_474 ∧
      InitE.Certificate submission (.finite K) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore K minutes ∧
      yukonScore K minutes < 2 ^ 53 - 1 := by
    intro K hK submission hs
    subst hs
    have hb := hb48s K hK
    have hsc1 : yukonScore 1_212_035_192 minutes ≤ yukonScore K minutes := by
      unfold yukonScore; omega
    have hsc2 : yukonScore K minutes ≤ yukonScore 857_384_015_252 minutes := by
      unfold yukonScore; omega
    exact ⟨hb.1, hb.2.2,
      certificate_lift_non_vacuous_and_tight 1_212_035_192 K hb.1 hc_best,
      hsc1, Nat.lt_of_le_of_lt hsc2 hterm_lt⟩
  have hall48e : ∀ K ∈ fortyEightElevenTablesPortfolio,
      ∀ submission : InitE.Submission, submission = baselineWithFiniteK K →
      1_212_035_192 ≤ K ∧ K < 900_719_925_474 ∧
      InitE.Certificate submission (.finite K) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore K minutes ∧
      yukonScore K minutes < 2 ^ 53 - 1 := by
    intro K hK submission hs
    subst hs
    have hb := hb48e K hK
    have hsc1 : yukonScore 1_212_035_192 minutes ≤ yukonScore K minutes := by
      unfold yukonScore; omega
    have hsc2 : yukonScore K minutes ≤ yukonScore 857_384_015_252 minutes := by
      unfold yukonScore; omega
    exact ⟨hb.1, hb.2.2,
      certificate_lift_non_vacuous_and_tight 1_212_035_192 K hb.1 hc_best,
      hsc1, Nat.lt_of_le_of_lt hsc2 hterm_lt⟩
  have hsc48 := forty_eight_portfolio_yukon_score_and_claims_within_128_bytes_non_vacuous_and_tight minutes 0
  refine ⟨⟨habs,
      GuestElevenTablesSharedBudgetAbsorption.kPan_val.1,
      GuestElevenTablesSharedBudgetAbsorption.kPan_val.2,
      bracket.1, bracket.2, bracket_rel,
      five_margin.1, five_margin.2,
      six_fails.1, six_fails.2⟩,
    ⟨haw, hpr,
      GuestElevenTablesAndWarmAddressProbeBound.kPan_val,
      GuestElevenTablesAndWarmAddressProbeBound.slopes.1,
      GuestElevenTablesAndWarmAddressProbeBound.slopes.2.1,
      GuestElevenTablesAndWarmAddressProbeBound.slopes.2.2⟩,
    hw124.1,
    hw124.2.1,
    hw124.2.2.1,
    hw124.2.2.2.1,
    hw124.2.2.2.2.1,
    hw124.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hel_env,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by decide, by decide, by decide, by decide, by decide, by decide,
    hall48s, hall48e, hsc48.1, hsc48.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw124.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by decide⟩

#print axioms guest_eleven_tables_shared_budget_absorption_closure_non_vacuous_and_tight
#print axioms guest_eleven_tables_and_warm_address_probe_bound_closure_non_vacuous_and_tight
#print axioms eleven_tables_shared_vs_unabsorbed_and_witness_bracket_non_vacuous_and_tight
#print axioms eleven_tables_and_shared_target_budgets_exact_values_non_vacuous_and_tight
#print axioms forty_four_to_forty_eight_portfolio_extension_and_strict_order_non_vacuous_and_tight
#print axioms pan_to_target_and_eleven_tables_shared_absorption_master_non_vacuous_and_tight
#print axioms unified_eleven_table_shared_absorption_and_sstore_gas_synthesis_non_vacuous_and_tight
#print axioms forty_eight_portfolio_yukon_score_and_claims_within_128_bytes_non_vacuous_and_tight
#print axioms forty_eight_portfolio_and_eleven_tables_submission_certificates_non_vacuous_and_tight
#print axioms grand_eleven_tables_and_shared_absorption_synth_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedElevenTablesAndSharedAbsorptionSynth
