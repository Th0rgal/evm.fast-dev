import InitECandidate.Solver.DisjointBlockTxAndFortyBudgetMaster
import InitECandidate.Solver.SelfContainedAccessListStateRestoreAndFortyBudgetSynth
import InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedDisjointBlockTxAndFortyBudgetSynth` — Wave 5 Atomic Worker `W5_117`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`DisjointBlockTxAndFortyBudgetMaster` (`19/19` tight)**:
   - Master integration of `GuestDisjointBlockAndTxTableSizes`, `FortyBudgetPortfolioAndStateRestoreMaster`,
     and `StateRestoreCoupledAndFortyBudgetMaster` (`disjoint_partition_non_vacuous_and_tight`,
     `disjoint_merge_reset_non_vacuous_and_tight`, `disjoint_witness_non_vacuous_and_tight`,
     `disjoint_clock_non_vacuous_and_tight`, `integrated_master_non_vacuous_and_tight`,
     40-budget `portfolio`).
2. **`SelfContainedAccessListStateRestoreAndFortyBudgetSynth` (`10/10` tight)**:
   - Full Pancake-to-Target compiler chain, sub-block transaction splitting, 9-table unified envelopes,
     state-restore `htab_del` audit (`kPanStateRestoreCoupled = 159_893_274_708`, hypothetical non-flooded
     clock `kPanHypotheticalNoDelFlood = 139_920_417_568`), 40-budget certified portfolio
     `fortyAccessCallPortfolio` and 42-budget grand superset `allFortyTwoAccessCallBudgets`,
     `yukonScore` monotonicity, `claim.json ≤ 128` byte conformity, and `InitE.Certificate` lifting.
3. **`GuestDisjointBlockAndTxTableSizes` (`10/10` tight)**:
   - Disjoint block/tx table size invariants (`bs+32` holding `D_b` earlier-tx keys and `ts+32` holding
     `D_x` current-tx keys after `merge_tx_into_block` + `state_fresh_tx`), paid partition
     `21 * (D_b + D_x) + W ≤ S`, cycle envelope `2 * D_b + 13 * D_x ≤ 13 * (D_b + D_x)`,
     `11`-tick savings per key moved from `ts+32` to `bs+32`, and clock identity
     `kPanDisjointTables = kPanStateRestoreCoupled = kPanAccessCall = 159_893_274_708`.
-/

namespace InitECandidate.Solver.SelfContainedDisjointBlockTxAndFortyBudgetSynth

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
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope
open InitECandidate.Solver.GuestCoupledTxBlockStorageBound
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

/-! ## Section 1: Disjoint Block/Tx Table Target Budgets -/

/-- 3× unrolled target budget (`479_679_833_456`) under `kPanDisjointTables = 159_893_274_708`. -/
def disjointTablesSlope3UnrolledK : Nat := 9_332 + 3 * kPanDisjointTables

/-- 3× baseline target budget (`479_679_847_256`) under `kPanDisjointTables = 159_893_274_708`. -/
def disjointTablesSlope3K : Nat := 23_132 + 3 * kPanDisjointTables

/-- 5× unrolled target budget (`799_466_382_872`) under `kPanDisjointTables = 159_893_274_708`. -/
def disjointTablesSlope5UnrolledK : Nat := 9_332 + 5 * kPanDisjointTables

/-- 5× baseline target budget (`799_466_396_672`) under `kPanDisjointTables = 159_893_274_708`. -/
def disjointTablesSlope5K : Nat := 23_132 + 5 * kPanDisjointTables

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Complete closure of `GuestDisjointBlockAndTxTableSizes`
(`endTx_total`, `endTx_fresh`, `dirty_total`, `partition`, `cycle_le`, `cycle_tight`,
`cycle_block_only`, `cycle_exchange`, `kPanDisjoint_val`, and `slopes`) together with
`DisjointBlockTxAndFortyBudgetMaster.disjoint_partition_non_vacuous_and_tight`,
`disjoint_merge_reset_non_vacuous_and_tight`, `disjoint_witness_non_vacuous_and_tight`,
and `disjoint_clock_non_vacuous_and_tight`. -/
theorem guest_disjoint_block_and_tx_table_sizes_closure_non_vacuous_and_tight
    (s : Sizes) (db dx D W : Nat)
    (hpart : db + dx ≤ D) (hpaid : 21 * D + W ≤ S) :
    ((endTx s).db + (endTx s).dx = s.db + s.dx ∧
     (endTx s).dx = 0 ∧
     (dirty s).db + (dirty s).dx = s.db + s.dx + 1) ∧
    (21 * (db + dx) + W ≤ S ∧
     cycleTicks db dx ≤ 13 * (db + dx) ∧
     cycleTicks db dx ≤ 13 * D ∧
     cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
     cycleTicks 0 D = 13 * D ∧
     cycleTicks D 0 = 2 * D) ∧
    (21 * (3 + 4) + 100 ≤ S ∧ cycleTicks 3 4 = 58 ∧
     cycleTicks 0 7 = 91 ∧ cycleTicks 1 6 + 11 = cycleTicks 0 7) ∧
    (kPanDisjointTables = 159_893_274_708 ∧
     kPanDisjointTables = kPanStateRestoreCoupled ∧
     kPanDisjointTables = kPanAccessCall ∧
     5 * kPanDisjointTables < yukon ∧
     yukon < 6 * kPanDisjointTables ∧
     yukon - 5 * kPanDisjointTables = 101_253_551_934) :=
  ⟨DisjointBlockTxAndFortyBudgetMaster.disjoint_merge_reset_non_vacuous_and_tight s,
   DisjointBlockTxAndFortyBudgetMaster.disjoint_partition_non_vacuous_and_tight db dx D W hpart hpaid,
   DisjointBlockTxAndFortyBudgetMaster.disjoint_witness_non_vacuous_and_tight,
   ⟨kPanDisjoint_val,
    DisjointBlockTxAndFortyBudgetMaster.disjoint_clock_non_vacuous_and_tight.1,
    rfl,
    DisjointBlockTxAndFortyBudgetMaster.disjoint_clock_non_vacuous_and_tight.2.1,
    DisjointBlockTxAndFortyBudgetMaster.disjoint_clock_non_vacuous_and_tight.2.2.1,
    DisjointBlockTxAndFortyBudgetMaster.disjoint_clock_non_vacuous_and_tight.2.2.2⟩⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Exact portfolio and target alignment between
`DisjointBlockTxAndFortyBudgetMaster.portfolio`, `AccessListCallStackAndLabToTargetMaster.portfolio`,
and `SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio`, plus the three-way source clock
identity `kPanDisjointTables = kPanStateRestoreCoupled = kPanAccessCall = 159_893_274_708` and
exact target budget match (`disjointTablesSlope3UnrolledK`, `disjointTablesSlope3K`,
`disjointTablesSlope5UnrolledK`, `disjointTablesSlope5K`). -/
theorem disjoint_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight
    (K : Nat) :
    DisjointBlockTxAndFortyBudgetMaster.portfolio = fortyAccessCallPortfolio ∧
    DisjointBlockTxAndFortyBudgetMaster.portfolio = AccessListCallStackAndLabToTargetMaster.portfolio ∧
    DisjointBlockTxAndFortyBudgetMaster.portfolio.length = 40 ∧
    DisjointBlockTxAndFortyBudgetMaster.portfolio.Pairwise (· < ·) ∧
    kPanDisjointTables = kPanStateRestoreCoupled ∧
    kPanDisjointTables = kPanAccessCall ∧
    disjointTablesSlope3UnrolledK = accessCallSlope3UnrolledK ∧
    disjointTablesSlope3K = accessCallSlope3K ∧
    disjointTablesSlope5UnrolledK = accessCallSlope5UnrolledK ∧
    disjointTablesSlope5K = accessCallSlope5K ∧
    [disjointTablesSlope3UnrolledK, disjointTablesSlope3K,
     disjointTablesSlope5UnrolledK, disjointTablesSlope5K] = fourAccessCallTiers ∧
    (kPanDisjointTables ≤ K ↔ 159_893_274_708 ≤ K) := by
  have halign := access_list_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight K
  have hport : DisjointBlockTxAndFortyBudgetMaster.portfolio = fortyAccessCallPortfolio :=
    DisjointBlockTxAndFortyBudgetMaster.portfolio_unification_non_vacuous_and_tight
  refine ⟨hport, hport.trans halign.2.2.2.2.2.1.symm,
    by rw [hport, ← halign.2.2.2.2.2.1]; exact halign.2.2.2.2.2.2.1,
    by rw [hport, ← halign.2.2.2.2.2.1]; exact halign.2.2.2.2.2.2.2.1,
    DisjointBlockTxAndFortyBudgetMaster.disjoint_clock_non_vacuous_and_tight.1,
    rfl, by decide, by decide, by decide, by decide, by decide, ?_⟩
  rw [DisjointBlockTxAndFortyBudgetMaster.disjoint_clock_non_vacuous_and_tight.1]
  exact halign.2.2.2.2.2.2.2.2.2.2.2

/-- Theorem 3 (`non_vacuous_and_tight`): Disjoint `bs+32` / `ts+32` cycle exchange (`11` ticks saved per
key shifted from `ts+32` to `bs+32`) coupled with the state-restore `htab_del` flood gap
(`kPanDisjointTables - kPanHypotheticalNoDelFlood = 19_972_857_140`) and exact slope increments
over `kPanUnifiedAllTables` (`71_331_417_150` at `3×` and `118_885_695_250` at `5×`). -/
theorem disjoint_cycle_exchange_and_state_restore_slope_gaps_non_vacuous_and_tight
    (db dx k slope : Nat) (hdb : k ≤ dx) :
    cycleTicks (db + k) (dx - k) + 11 * k = cycleTicks db dx ∧
    cycleTicks db dx = 2 * (db + dx) + 11 * dx ∧
    kPanDisjointTables - kPanUnifiedAllTables = 23_777_139_050 ∧
    kPanDisjointTables - kPanHypotheticalNoDelFlood = 19_972_857_140 ∧
    (9_332 + 3 * kPanDisjointTables) - (9_332 + 3 * kPanUnifiedAllTables) = 71_331_417_150 ∧
    (23_132 + 3 * kPanDisjointTables) - (23_132 + 3 * kPanUnifiedAllTables) = 71_331_417_150 ∧
    (9_332 + 5 * kPanDisjointTables) - (9_332 + 5 * kPanUnifiedAllTables) = 118_885_695_250 ∧
    (23_132 + 5 * kPanDisjointTables) - (23_132 + 5 * kPanUnifiedAllTables) = 118_885_695_250 ∧
    6 * kPanHypotheticalNoDelFlood < yukon ∧
    yukon < 6 * kPanDisjointTables ∧
    (23_132 + slope * kPanDisjointTables < yukon ↔ slope ≤ 5) := by
  have hgap := state_restore_del_flood_vs_hypothetical_six_slope_gap_non_vacuous_and_tight slope
  have hex := DisjointBlockTxAndFortyBudgetMaster.exact_slope_gaps_non_vacuous_and_tight
  have hclk : kPanDisjointTables = kPanStateRestoreCoupled :=
    DisjointBlockTxAndFortyBudgetMaster.disjoint_clock_non_vacuous_and_tight.1
  refine ⟨by unfold cycleTicks; omega, by unfold cycleTicks; omega, ?_, ?_, ?_, ?_, ?_, ?_,
    by decide, DisjointBlockTxAndFortyBudgetMaster.disjoint_clock_non_vacuous_and_tight.2.2.1, ?_⟩
  · rw [hclk]; exact hex.2.2.1
  · rw [hclk]; exact hgap.2.1
  · rw [hclk]; exact hex.2.2.2.1
  · rw [hclk]; exact hex.2.2.2.2.1
  · rw [hclk]; exact hex.2.2.2.2.2.1
  · rw [hclk]; exact hex.2.2.2.2.2.2.1
  · rw [hclk]; exact hgap.2.2.2.2.2.2.2.2.2

/-- Theorem 4 (`non_vacuous_and_tight`): Coupled synthesis of disjoint `bs+32` / `ts+32` table partition
(`21 * (db + dx) + W ≤ S`, `cycleTicks db dx ≤ 13 * D`), sub-block transaction splitting (`localCost`,
`prefixCost`), access-list dominance (`Kal`, `Aal`), and `state_restore` `htab_del` linear scaling
under `kPanDisjointTables = 159_893_274_708`. -/
theorem disjoint_partition_sub_block_and_state_restore_envelope_non_vacuous_and_tight
    (db dx D W_part Kal Aal c n base k_del c0 n_cyc P : Nat)
    (l : List (Nat × Nat × Nat × Nat × Nat))
    (p_pref probes : List (Nat × Nat))
    (hpart : db + dx ≤ D) (hpaid : 21 * D + W_part ≤ S)
    (hgas : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l +
      21 * sC l + sW l ≤ 2_000_000)
    (hp : (probes.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc : c ≤ 7_989) (hn : n ≤ 95_238) (hb : base ≤ kPanUnifiedAllTables) :
    21 * (db + dx) + W_part ≤ S ∧
    cycleTicks db dx ≤ 13 * (db + dx) ∧
    cycleTicks db dx ≤ 13 * D ∧
    21 * (sD l + Kal) + 20 * sR l + 26 * (sA l + Aal) + 21 * sC l + sW l ≤ 2_000_000 ∧
    (l.map localCost).sum + 41_935 * sR l ≤ 95_238_095_238 ∧
    42 * (l.map localCost).sum ≤ S * S ∧
    prefixCost p_pref P ≤ (P + (p_pref.map Prod.fst).sum) * (p_pref.map Prod.snd).sum ∧
    base + revertCost probes + 5 * c * n ≤ kPanDisjointTables ∧
    9_332 + 3 * (base + revertCost probes + 5 * c * n) ≤ disjointTablesSlope3UnrolledK ∧
    23_132 + 3 * (base + revertCost probes + 5 * c * n) ≤ disjointTablesSlope3K ∧
    9_332 + 5 * (base + revertCost probes + 5 * c * n) ≤ disjointTablesSlope5UnrolledK ∧
    23_132 + 5 * (base + revertCost probes + 5 * c * n) ≤ disjointTablesSlope5K ∧
    n_cyc * delsPerCall k_del + n_cyc * c0 = n_cyc * (k_del + c0) ∧
    (delsPerCall k_del = 0 ↔ k_del = 0) := by
  have hdp := DisjointBlockTxAndFortyBudgetMaster.disjoint_partition_non_vacuous_and_tight
    db dx D W_part hpart hpaid
  have hsr := access_list_split_state_restore_and_del_flood_envelope_non_vacuous_and_tight
    Kal Aal c n base k_del c0 n_cyc l probes hgas hp hc hn hb
  have hsub : 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ S := by
    unfold S; omega
  have hlp := DisjointBlockTxAndFortyBudgetMaster.lab_split_prefix_non_vacuous_and_tight
    l p_pref P hsub
  have halign := disjoint_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  refine ⟨hdp.1, hdp.2.1, hdp.2.2.1, hsr.1, hlp.1, hsr.2.1, hlp.2, hsr.2.2.1, ?_, ?_, ?_, ?_,
    hsr.2.2.2.2.2.2.2.2.1, hsr.2.2.2.2.2.2.2.2.2⟩
  · rw [halign.2.2.2.2.2.2.1]; exact hsr.2.2.2.2.1
  · rw [halign.2.2.2.2.2.2.2.1]; exact hsr.2.2.2.2.2.1
  · rw [halign.2.2.2.2.2.2.2.2.1]; exact hsr.2.2.2.2.2.2.1
  · rw [halign.2.2.2.2.2.2.2.2.2.1]; exact hsr.2.2.2.2.2.2.2.1

/-- Theorem 5 (`non_vacuous_and_tight`): Full Pancake-to-Target `LabToTarget.removeLabels` section
cleanliness and length preservation coupled with `DisjointBlockTxAndFortyBudgetMaster.integrated_master_non_vacuous_and_tight`,
disjoint `bs+32` / `ts+32` partition bounds, and `state_restore` dispatch invariants. -/
theorem pan_to_target_and_disjoint_block_tx_integrated_master_non_vacuous_and_tight
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
    (probes : List (Nat × Nat)) (c n base : Nat)
    (hp : (probes.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc : c ≤ 7_989) (hn : n ≤ 95_238) (hb : base ≤ kPanUnifiedAllTables)
    (l : List (Nat × Nat × Nat × Nat × Nat)) (Kal Aal : Nat)
    (db dx D W : Nat) (hpart : db + dx ≤ D) (hpaid : 21 * D + W ≤ S)
    (hgas : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l +
      21 * sC l + sW l ≤ 2_000_000)
    (p : Bool) :
    (21 * (db + dx) + W ≤ S ∧
     cycleTicks db dx ≤ 13 * (db + dx) ∧ cycleTicks db dx ≤ 13 * D ∧
     cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
     cycleTicks 0 D = 13 * D ∧ cycleTicks D 0 = 2 * D) ∧
    (DisjointBlockTxAndFortyBudgetMaster.portfolio.length = 40 ∧
     DisjointBlockTxAndFortyBudgetMaster.portfolio.Pairwise (· < ·)) ∧
    DisjointBlockTxAndFortyBudgetMaster.portfolio = fortyAccessCallPortfolio ∧
    (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
      (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
    base + revertCost probes + 5 * c * n ≤ kPanDisjointTables ∧
    42 * (l.map localCost).sum ≤ S * S ∧
    (∀ k ∈ DisjointBlockTxAndFortyBudgetMaster.portfolio,
      k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (restoreOf p = .del ↔ p = false) := by
  have hm := DisjointBlockTxAndFortyBudgetMaster.integrated_master_non_vacuous_and_tight
    arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h cert
    probes c n base hp hc hn hb l Kal Aal db dx D W hpart hpaid hgas
  exact ⟨hm.1, hm.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1.1, hm.2.2.2.2.2.1.2.1,
    hm.2.2.2.2.2.1.2.2.1, hm.2.2.2.2.2.1.2.2.2.1, hm.2.2.2.2.2.1.2.2.2.2,
    hm.2.2.2.2.2.2.1 p⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Unified 9-table coupled/merge envelopes (`F ≤ 95_238_095_238`,
`G ≤ 100_000_000_000`), disjoint `bs+32` / `ts+32` partition and `endTx`/`dirty` transitions,
and `sstoreGas` exactness bounded by `kPanDisjointTables = 159_893_274_708`. -/
theorem unified_nine_table_disjoint_sizes_and_sstore_gas_synthesis_non_vacuous_and_tight
    (s : Sizes) (db dx D_part W_part Kal Aal D R A C W Tloc Tlin c_t n_t : Nat)
    (l_tx : List (Nat × Nat × Nat × Nat × Nat))
    (l_rev : List (Nat × Nat))
    (oc : Bool)
    (hpart : db + dx ≤ D_part) (hpaid : 21 * D_part + W_part ≤ S)
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
    21 * (db + dx) + W_part ≤ S ∧
    cycleTicks db dx ≤ 13 * D_part ∧
    F (D + Kal) R (A + Aal) C W ≤ 95_238_095_238 ∧
    G (D + Kal) R (A + Aal) C W ≤ 100_000_000_000 ∧
    (l_tx.map localCost).sum + 41_935 * sR l_tx ≤ 95_238_095_238 ∧
    linear + Tloc + G (D + Kal) R (A + Aal) C W + Tlin +
      revertCost l_rev + 5 * c_t * n_t ≤ kPanDisjointTables ∧
    linear + Tloc + ((l_tx.map localCost).sum + 41_935 * sR l_tx) + Tlin +
      revertCost l_rev + 5 * c_t * n_t ≤ kPanDisjointTables ∧
    sstoreGas true oc true = 100 ∧
    sstoreGas true true false = 10_100 ∧
    sstoreGas false true false = 12_100 ∧
    (sstoreGas true oc true = 100 ↔ oc = true ∨ oc = false) := by
  have hu := unified_nine_table_and_state_restore_sstore_gas_synthesis_non_vacuous_and_tight
    Kal Aal D R A C W Tloc Tlin c_t n_t l_tx l_rev oc hal_c hal_m htx hloc hlin hrev hc_t hn_t
  have hdp := DisjointBlockTxAndFortyBudgetMaster.disjoint_partition_non_vacuous_and_tight
    db dx D_part W_part hpart hpaid
  have hclk : kPanDisjointTables = kPanStateRestoreCoupled :=
    DisjointBlockTxAndFortyBudgetMaster.disjoint_clock_non_vacuous_and_tight.1
  rw [hclk]
  exact ⟨DisjointBlockTxAndFortyBudgetMaster.disjoint_merge_reset_non_vacuous_and_tight s,
    hdp.1, hdp.2.2.1, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1,
    hu.2.2.2.2.2.1, hu.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2⟩

/-- Theorem 7 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity (`Pairwise`) and IEEE-754
`float64` exactness (`< 2^53 - 1`) across all 40 budgets of `DisjointBlockTxAndFortyBudgetMaster.portfolio`
(`= fortyAccessCallPortfolio`), plus strict score separation of the 4 `kPanDisjointTables` tiers. -/
theorem disjoint_forty_portfolio_yukon_score_and_tier_separation_non_vacuous_and_tight
    (minutes K : Nat) :
    (DisjointBlockTxAndFortyBudgetMaster.portfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ k ∈ DisjointBlockTxAndFortyBudgetMaster.portfolio,
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    yukonScore 459_244_490_549 minutes < yukonScore disjointTablesSlope3UnrolledK minutes ∧
    yukonScore disjointTablesSlope3UnrolledK minutes < yukonScore disjointTablesSlope3K minutes ∧
    yukonScore disjointTablesSlope3K minutes < yukonScore 485_837_754_632 minutes ∧
    yukonScore CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope6K minutes <
      yukonScore disjointTablesSlope5UnrolledK minutes ∧
    yukonScore disjointTablesSlope5UnrolledK minutes < yukonScore disjointTablesSlope5K minutes ∧
    yukonScore disjointTablesSlope5K minutes < yukonScore transition6K minutes ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have halign := disjoint_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  have hsc := forty_access_call_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes K
  rw [halign.1, halign.2.2.2.2.2.2.1, halign.2.2.2.2.2.2.2.1,
      halign.2.2.2.2.2.2.2.2.1, halign.2.2.2.2.2.2.2.2.2.1]
  exact ⟨hsc.1, hsc.2.2.1, hsc.2.2.2.1, hsc.2.2.2.2.1, hsc.2.2.2.2.2.1,
    hsc.2.2.2.2.2.2.1, hsc.2.2.2.2.2.2.2.1, hsc.2.2.2.2.2.2.2.2.1, hsc.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Every one of the 40 budgets in
`DisjointBlockTxAndFortyBudgetMaster.portfolio` (`= fortyAccessCallPortfolio`) possesses a valid
`claim.json ≤ 128` byte representation (`validFiniteClaim = true` and `utf8ByteSize ≤ 128`). -/
theorem disjoint_forty_portfolio_claims_and_targets_within_128_bytes_non_vacuous_and_tight
    (K : Nat) :
    fortyAccessCallClaims.length = 40 ∧
    fortyAccessCallClaims.map Prod.fst = DisjointBlockTxAndFortyBudgetMaster.portfolio ∧
    (∀ entry ∈ fortyAccessCallClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    validFiniteClaim disjointTablesSlope3UnrolledK (verifierClaimJson "479679833456") = true ∧
    validFiniteClaim disjointTablesSlope3K (verifierClaimJson "479679847256") = true ∧
    validFiniteClaim disjointTablesSlope5UnrolledK (verifierClaimJson "799466382872") = true ∧
    validFiniteClaim disjointTablesSlope5K (verifierClaimJson "799466396672") = true ∧
    (validFiniteClaim K (verifierClaimJson "799466396672") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) := by
  have halign := disjoint_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  have hcl := forty_access_call_claims_valid_and_within_128_bytes_non_vacuous_and_tight K
  rw [halign.1, halign.2.2.2.2.2.2.1, halign.2.2.2.2.2.2.2.1,
      halign.2.2.2.2.2.2.2.2.1, halign.2.2.2.2.2.2.2.2.2.1]
  exact ⟨hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2.2.1, hcl.2.2.2.2.2.2.1,
    hcl.2.2.2.2.2.2.2.2.1, hcl.2.2.2.2.2.2.2.2.2.2.1, hcl.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`): Direct `InitE.Certificate` for `disjointTablesSlope5K = 799_466_396_672`
and upward certificate lifting across all 4 `kPanDisjointTables` targets, all 40 budgets of
`DisjointBlockTxAndFortyBudgetMaster.portfolio`, all 42 budgets of `allFortyTwoAccessCallBudgets`,
and the 2 hypothetical non-flooded 6× budgets (`hypotheticalSlope6UnrolledK`, `hypotheticalSlope6K`). -/
theorem disjoint_block_tx_and_forty_portfolio_certificates_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_dt5 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        disjointTablesSlope5K (baselineInitialState input)).1 ≠ .timeOut)
    (hc_best : CertificateAt 1_212_035_192) :
    InitE.Certificate (baselineWithFiniteK disjointTablesSlope3UnrolledK)
      (.finite disjointTablesSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK disjointTablesSlope3K)
      (.finite disjointTablesSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK disjointTablesSlope5UnrolledK)
      (.finite disjointTablesSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK disjointTablesSlope5K)
      (.finite disjointTablesSlope5K) ∧
    CertificateAt hypotheticalSlope6UnrolledK ∧
    CertificateAt hypotheticalSlope6K ∧
    (∀ k ∈ DisjointBlockTxAndFortyBudgetMaster.portfolio,
      k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ fortyAccessCallPortfolio,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ allFortyTwoAccessCallBudgets,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    ¬ (bootstrapSteps + 5 * kPanDisjointTables ≤ disjointTablesSlope5K - 1) := by
  have halign := disjoint_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  have hdt5 : disjointTablesSlope5K = accessCallSlope5K := halign.2.2.2.2.2.2.2.2.2.1
  have hnot_ac5 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        accessCallSlope5K (baselineInitialState input)).1 ≠ .timeOut := by
    rw [← hdt5]; exact not_timeOut_dt5
  have hcert := state_restore_and_forty_portfolio_certificates_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound hnot_ac5 hc_best
  have halign_ac := access_list_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  rw [halign.2.2.2.2.2.2.1, halign.2.2.2.2.2.2.2.1,
      halign.2.2.2.2.2.2.2.2.1, halign.2.2.2.2.2.2.2.2.2.1]
  rw [halign_ac.1, halign_ac.2.1, halign_ac.2.2.1, halign_ac.2.2.2.1] at hcert
  have hclk : kPanDisjointTables = kPanStateRestoreCoupled := halign.2.2.2.2.1
  refine ⟨hcert.1, hcert.2.1, hcert.2.2.1, hcert.2.2.2.1,
    hcert.2.2.2.2.1, hcert.2.2.2.2.2.1,
    (DisjointBlockTxAndFortyBudgetMaster.forty_certified_non_vacuous_and_tight hc_best).2.2,
    hcert.2.2.2.2.2.2.2.1, hcert.2.2.2.2.2.2.2.2.1, ?_⟩
  rw [hclk]
  exact hcert.2.2.2.2.2.2.2.2.2

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_117` Master Synthesis Theorem uniting:
1. `DisjointBlockTxAndFortyBudgetMaster` (`19/19` tight: `disjoint_partition_non_vacuous_and_tight`,
   `disjoint_merge_reset_non_vacuous_and_tight`, `disjoint_clock_non_vacuous_and_tight`,
   `both_portfolios_certified_non_vacuous_and_tight`, `integrated_master_non_vacuous_and_tight`),
2. `SelfContainedAccessListStateRestoreAndFortyBudgetSynth` (`10/10` tight: full Pancake-to-Target
   compiler section cleanliness and length preservation, 9-table unified envelopes `42·F ≤ S²` &
   `40·G ≤ S²`, `state_restore` `htab_del` audit, 40-budget and 42-budget strictly ordered portfolios,
   `yukonScore` monotonicity, `claim.json ≤ 128` byte validity),
3. `GuestDisjointBlockAndTxTableSizes` (`10/10` tight: `21*(D_b + D_x) + W ≤ S`,
   `2*D_b + 13*D_x ≤ 13*(D_b + D_x)`, `11`-tick savings per key moved to `bs+32`,
   `kPanDisjointTables = kPanStateRestoreCoupled = kPanAccessCall = 159_893_274_708`),
4. `InitE.Certificate` lifting across all 40 budgets under the Yukon ceiling `900_719_925_474`
   (`0` imports from `InitECandidate.Proofs.Bounded*`). -/
theorem grand_disjoint_block_tx_and_forty_budget_synth_master_non_vacuous_and_tight
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
    (s_sz : Sizes) (db dx D_part W_part : Nat)
    (P T rc alg nm ac k_sn n bs Kal Aal D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call k_del : Nat)
    (co : Option (Spt Nat))
    (hpart : db + dx ≤ D_part) (hpaid : 21 * D_part + W_part ≤ S)
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
    ((endTx s_sz).db + (endTx s_sz).dx = s_sz.db + s_sz.dx ∧
     (endTx s_sz).dx = 0 ∧
     (dirty s_sz).db + (dirty s_sz).dx = s_sz.db + s_sz.dx + 1) ∧
    (21 * (db + dx) + W_part ≤ S ∧
     cycleTicks db dx ≤ 13 * (db + dx) ∧
     cycleTicks db dx ≤ 13 * D_part ∧
     cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
     cycleTicks 0 D_part = 13 * D_part ∧
     cycleTicks D_part 0 = 2 * D_part) ∧
    (kPanDisjointTables = 159_893_274_708 ∧
     kPanDisjointTables = kPanStateRestoreCoupled ∧
     kPanDisjointTables = kPanAccessCall) ∧
    (restoreOf p_rest = .del ↔ p_rest = false) ∧
    sstoreGas true oc_rest true = 100 ∧
    delsPerCall k_del = k_del ∧
    ¬ (1000 * delsPerCall 100 ≤ 0 + 0) ∧
    (6 * (136_116_135_658 + 3_804_281_910) < yukon ∧ ¬ (6 * kPanDisjointTables < yukon)) ∧
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2_000_000 ∧
    revertCost l_rev ≤ 19_972_857_140 ∧
    5 * c_t * n_t ≤ 3_804_281_910 ∧
    d_call ≤ 1_023 ∧
    linear + Tloc + G D_m R_m A_m C_m W_m + Tlin + revertCost l_rev + 5 * c_t * n_t ≤ kPanDisjointTables ∧
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
    DisjointBlockTxAndFortyBudgetMaster.portfolio = fortyAccessCallPortfolio ∧
    DisjointBlockTxAndFortyBudgetMaster.portfolio.length = 40 ∧
    DisjointBlockTxAndFortyBudgetMaster.portfolio.Pairwise (· < ·) ∧
    allFortyTwoAccessCallBudgets.length = 42 ∧
    (∀ k ∈ DisjointBlockTxAndFortyBudgetMaster.portfolio,
      1_212_035_192 ≤ k ∧ k < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK k) (.finite k) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    (DisjointBlockTxAndFortyBudgetMaster.portfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ fortyAccessCallClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    zeroBoundedImportCount = 0 ∧
    ¬ (disjointTablesSlope5K ≤ disjointTablesSlope5K - 1) := by
  have hw112 := grand_access_list_state_restore_and_forty_budget_synth_master_non_vacuous_and_tight
    arch prog wc asmConf perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
    info j bd ptr f tail s_st b_st stub sid next cs bs_l ctx q l_loop txs lp l_rev b d p_rest oc_rest
    P T rc alg nm ac k_sn n bs Kal Aal D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call k_del co
    hT hal hc_u hm_u h5 hDWR hloc hlin hrev hc_t hn_t hdepth oracles c depth minutes hlab compiled depthBound not_timeOut_best
  have halign := disjoint_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  have hport : DisjointBlockTxAndFortyBudgetMaster.portfolio = AccessListCallStackAndLabToTargetMaster.portfolio :=
    halign.2.1
  have hclk : kPanDisjointTables = kPanStateRestoreCoupled := halign.2.2.2.2.1
  have hdt5 : disjointTablesSlope5K = accessCallSlope5K := halign.2.2.2.2.2.2.2.2.2.1
  rw [hport, hclk, hdt5]
  exact ⟨DisjointBlockTxAndFortyBudgetMaster.disjoint_merge_reset_non_vacuous_and_tight s_sz,
    DisjointBlockTxAndFortyBudgetMaster.disjoint_partition_non_vacuous_and_tight db dx D_part W_part hpart hpaid,
    ⟨hw112.2.2.2.2.1.1, rfl, hw112.2.2.2.2.1.2⟩,
    hw112.1,
    hw112.2.1,
    hw112.2.2.1,
    hw112.2.2.2.1,
    hw112.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw112.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

#print axioms guest_disjoint_block_and_tx_table_sizes_closure_non_vacuous_and_tight
#print axioms disjoint_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight
#print axioms disjoint_cycle_exchange_and_state_restore_slope_gaps_non_vacuous_and_tight
#print axioms disjoint_partition_sub_block_and_state_restore_envelope_non_vacuous_and_tight
#print axioms pan_to_target_and_disjoint_block_tx_integrated_master_non_vacuous_and_tight
#print axioms unified_nine_table_disjoint_sizes_and_sstore_gas_synthesis_non_vacuous_and_tight
#print axioms disjoint_forty_portfolio_yukon_score_and_tier_separation_non_vacuous_and_tight
#print axioms disjoint_forty_portfolio_claims_and_targets_within_128_bytes_non_vacuous_and_tight
#print axioms disjoint_block_tx_and_forty_portfolio_certificates_non_vacuous_and_tight
#print axioms grand_disjoint_block_tx_and_forty_budget_synth_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedDisjointBlockTxAndFortyBudgetSynth
