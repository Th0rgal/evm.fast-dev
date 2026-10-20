import InitECandidate.Solver.AccessListCallStackAndLabToTargetMaster
import InitECandidate.Solver.SelfContainedFortyBudgetPortfolioSynth
import InitECandidate.Solver.GuestStateRestoreCoupledTightening

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedAccessListStateRestoreAndFortyBudgetSynth` — Wave 5 Atomic Worker `W5_112`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`AccessListCallStackAndLabToTargetMaster` (`44/44` tight)**:
   - Master integration of `GuestAccessListAndCallStackDominance`, `SubBlockTxSplittingAndPanToLabMaster`,
     and `LabToTargetSectionCleanPreservation` (`access_call_lab_to_target_master_non_vacuous_and_tight`,
     `access_list_split_coupled_non_vacuous_and_tight`, `state_restore_envelope_non_vacuous_and_tight`,
     40-budget `portfolio`).
2. **`SelfContainedFortyBudgetPortfolioSynth` (`10/10` tight)**:
   - Full Pancake-to-Target compiler chain, sub-block transaction splitting, 9-table unified envelopes,
     40-budget certified portfolio `fortyAccessCallPortfolio` and 42-budget grand superset
     `allFortyTwoAccessCallBudgets`, `yukonScore` monotonicity, `claim.json ≤ 128` byte conformity,
     and `InitE.Certificate` lifting.
3. **`GuestStateRestoreCoupledTightening` (`11/11` tight)**:
   - Negative result proving that `htab_del` count in `state_restore` is `Θ(W)` rather than `≤ D + R`:
     `restore_dispatch`, `noop_warm_gas`, `changing_write_gas`, `noop_absent_deletes`, `rewrite_sets`,
     `dels_per_call`, `dels_vs_units`, `del_bound_refuted`, `kPanStateRestoreCoupled = kPanAccessCall = 159_893_274_708`,
     `slopes` (`5× < yukon < 6×`), and `hypothetical_fix` (`6 * (136_116_135_658 + 3_804_281_910) < yukon`).
-/

namespace InitECandidate.Solver.SelfContainedAccessListStateRestoreAndFortyBudgetSynth

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

/-! ## Section 1: State-Restore Coupled Target Budgets & Hypothetical Fix Definitions -/

/-- Hypothetical tightened source clock if `htab_del` were bounded by `D + R` (`139_920_417_568`):
`kPanUnifiedAllTables + 3_804_281_910 = 136_116_135_658 + 3_804_281_910 = 139_920_417_568`. -/
def kPanHypotheticalNoDelFlood : Nat := kPanUnifiedAllTables + 3_804_281_910

/-- Hypothetical 6× unrolled target budget (`839_522_514_740 < yukon`) if `htab_del` flooding were absent. -/
def hypotheticalSlope6UnrolledK : Nat := 9_332 + 6 * kPanHypotheticalNoDelFlood

/-- Hypothetical 6× baseline target budget (`839_522_528_540 < yukon`) if `htab_del` flooding were absent. -/
def hypotheticalSlope6K : Nat := 23_132 + 6 * kPanHypotheticalNoDelFlood

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Complete closure of `GuestStateRestoreCoupledTightening`
(`restore_dispatch`, `noop_warm_gas`, `changing_write_gas`, `noop_absent_deletes`, `rewrite_sets`,
`dels_per_call`, `dels_vs_units`, `del_bound_refuted`, `kPanStateRestoreCoupled_val`, `slopes`,
and `hypothetical_fix`). -/
theorem guest_state_restore_coupled_tightening_closure_non_vacuous_and_tight
    (p oc : Bool) (k c0 n : Nat) :
    (restoreOf p = .del ↔ p = false) ∧
    sstoreGas true oc true = 100 ∧
    (sstoreGas true true false = 10_100 ∧ sstoreGas false true false = 12_100) ∧
    (restoreOf (jsetStep false).1 = .del ∧ sstoreGas true true true = 100) ∧
    restoreOf (jsetStep true).1 = .set ∧
    delsPerCall k = k ∧
    n * delsPerCall k + n * c0 = n * (k + c0) ∧
    ¬ (1000 * delsPerCall 100 ≤ 0 + 0) ∧
    (kPanStateRestoreCoupled = 159_893_274_708 ∧ kPanStateRestoreCoupled = kPanAccessCall) ∧
    (5 * kPanStateRestoreCoupled < yukon ∧ yukon < 6 * kPanStateRestoreCoupled) ∧
    (6 * (136_116_135_658 + 3_804_281_910) < yukon ∧ ¬ (6 * kPanStateRestoreCoupled < yukon)) :=
  ⟨restore_dispatch p,
   noop_warm_gas oc,
   changing_write_gas,
   noop_absent_deletes,
   rewrite_sets,
   dels_per_call k,
   dels_vs_units k c0 n,
   del_bound_refuted,
   kPanStateRestoreCoupled_val,
   GuestStateRestoreCoupledTightening.slopes,
   hypothetical_fix⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Exact portfolio and target alignment between
`AccessListCallStackAndLabToTargetMaster` (`portfolio`, `accessCallTargets`,
`accessCallSlope3UnrolledK`, `accessCallSlope3K`, `accessCallSlope5UnrolledK`, `accessCallSlope5K`)
and `SelfContainedFortyBudgetPortfolioSynth` (`fortyAccessCallPortfolio`, `fourAccessCallTiers`),
plus the state-restore clock identity `kPanStateRestoreCoupled = kPanAccessCall = 159_893_274_708`. -/
theorem access_list_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight
    (K : Nat) :
    AccessListCallStackAndLabToTargetMaster.accessCallSlope3UnrolledK = accessCallSlope3UnrolledK ∧
    AccessListCallStackAndLabToTargetMaster.accessCallSlope3K = accessCallSlope3K ∧
    AccessListCallStackAndLabToTargetMaster.accessCallSlope5UnrolledK = accessCallSlope5UnrolledK ∧
    AccessListCallStackAndLabToTargetMaster.accessCallSlope5K = accessCallSlope5K ∧
    AccessListCallStackAndLabToTargetMaster.accessCallTargets = fourAccessCallTiers ∧
    AccessListCallStackAndLabToTargetMaster.portfolio = fortyAccessCallPortfolio ∧
    AccessListCallStackAndLabToTargetMaster.portfolio.length = 40 ∧
    AccessListCallStackAndLabToTargetMaster.portfolio.Pairwise (· < ·) ∧
    kPanStateRestoreCoupled = kPanAccessCall ∧
    9_332 + 5 * kPanStateRestoreCoupled = accessCallSlope5UnrolledK ∧
    23_132 + 5 * kPanStateRestoreCoupled = accessCallSlope5K ∧
    (kPanStateRestoreCoupled ≤ K ↔ 159_893_274_708 ≤ K) := by
  have ha := access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight 0
  have hm := AccessListCallStackAndLabToTargetMaster.target_values_non_vacuous_and_tight
  have hk := kPanStateRestoreCoupled_val
  have heq1 : AccessListCallStackAndLabToTargetMaster.accessCallSlope3UnrolledK = accessCallSlope3UnrolledK := by
    rw [hm.1, ha.1]
  have heq2 : AccessListCallStackAndLabToTargetMaster.accessCallSlope3K = accessCallSlope3K := by
    rw [hm.2.1, ha.2.1]
  have heq3 : AccessListCallStackAndLabToTargetMaster.accessCallSlope5UnrolledK = accessCallSlope5UnrolledK := by
    rw [hm.2.2.1, ha.2.2.1]
  have heq4 : AccessListCallStackAndLabToTargetMaster.accessCallSlope5K = accessCallSlope5K := by
    rw [hm.2.2.2, ha.2.2.2.1]
  have htargets : AccessListCallStackAndLabToTargetMaster.accessCallTargets = fourAccessCallTiers := by
    unfold AccessListCallStackAndLabToTargetMaster.accessCallTargets fourAccessCallTiers
    rw [heq1, heq2, heq3, heq4]
  refine ⟨heq1, heq2, heq3, heq4, htargets, by decide,
    AccessListCallStackAndLabToTargetMaster.portfolio_count_non_vacuous_and_tight,
    AccessListCallStackAndLabToTargetMaster.portfolio_order_non_vacuous_and_tight,
    hk.2, ?_, ?_, ?_⟩
  · rw [hk.1, ha.2.2.1]
  · rw [hk.1, ha.2.2.2.1]
  · rw [hk.1]

/-- Theorem 3 (`non_vacuous_and_tight`): Exact evaluation of the hypothetical non-flooded restore clock
`kPanHypotheticalNoDelFlood = 139_920_417_568` and its 6× target budgets (`hypotheticalSlope6UnrolledK = 839_522_514_740`,
`hypotheticalSlope6K = 839_522_528_540 < yukon`), contrasted with the actual `htab_del`-flooded clock
`kPanStateRestoreCoupled = 159_893_274_708` where `yukon < 6 * kPanStateRestoreCoupled` (`959_359_648_248`). -/
theorem state_restore_del_flood_vs_hypothetical_six_slope_gap_non_vacuous_and_tight
    (slope : Nat) :
    kPanHypotheticalNoDelFlood = 139_920_417_568 ∧
    kPanStateRestoreCoupled - kPanHypotheticalNoDelFlood = 19_972_857_140 ∧
    hypotheticalSlope6UnrolledK = 839_522_514_740 ∧
    hypotheticalSlope6K = 839_522_528_540 ∧
    hypotheticalSlope6UnrolledK < hypotheticalSlope6K ∧
    hypotheticalSlope6K < terminalK ∧
    terminalK < yukon ∧
    yukon < 6 * kPanStateRestoreCoupled ∧
    6 * kPanStateRestoreCoupled - yukon = 58_639_722_774 ∧
    (23_132 + slope * kPanStateRestoreCoupled < yukon ↔ slope ≤ 5) := by
  have h10 := (access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight slope).2.2.2.2.2.2.2.2.2.2.2.2
  rw [bootstrapSteps_eq] at h10
  have hk : kPanStateRestoreCoupled = kPanAccessCall := kPanStateRestoreCoupled_val.2
  rw [hk]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, h10⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Coupled synthesis of `AccessListCallStackAndLabToTargetMaster`
(`access_list_split_coupled_non_vacuous_and_tight`, `state_restore_envelope_non_vacuous_and_tight`,
`slope3_absorption_non_vacuous_and_tight`, `slope5_absorption_non_vacuous_and_tight`) with
`GuestStateRestoreCoupledTightening` (`dels_per_call`, `dels_vs_units`, `del_bound_refuted`). -/
theorem access_list_split_state_restore_and_del_flood_envelope_non_vacuous_and_tight
    (Kal Aal c n base k_del c0 n_cyc : Nat)
    (l : List (Nat × Nat × Nat × Nat × Nat))
    (probes : List (Nat × Nat))
    (hgas : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l +
      21 * sC l + sW l ≤ 2_000_000)
    (hp : (probes.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc : c ≤ 7_989) (hn : n ≤ 95_238) (hb : base ≤ kPanUnifiedAllTables) :
    21 * (sD l + Kal) + 20 * sR l + 26 * (sA l + Aal) + 21 * sC l + sW l ≤ 2_000_000 ∧
    42 * (l.map localCost).sum ≤ S * S ∧
    base + revertCost probes + 5 * c * n ≤ kPanAccessCall ∧
    base + revertCost probes + 5 * c * n ≤ kPanStateRestoreCoupled ∧
    9_332 + 3 * (base + revertCost probes + 5 * c * n) ≤ accessCallSlope3UnrolledK ∧
    23_132 + 3 * (base + revertCost probes + 5 * c * n) ≤ accessCallSlope3K ∧
    9_332 + 5 * (base + revertCost probes + 5 * c * n) ≤ accessCallSlope5UnrolledK ∧
    23_132 + 5 * (base + revertCost probes + 5 * c * n) ≤ accessCallSlope5K ∧
    n_cyc * delsPerCall k_del + n_cyc * c0 = n_cyc * (k_del + c0) ∧
    (delsPerCall k_del = 0 ↔ k_del = 0) := by
  have h1 := AccessListCallStackAndLabToTargetMaster.access_list_split_coupled_non_vacuous_and_tight
    Kal Aal l hgas
  have h2 := AccessListCallStackAndLabToTargetMaster.state_restore_envelope_non_vacuous_and_tight
    probes c n base hp hc hn hb
  have halign := access_list_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  have hpost3 : 3 * (base + revertCost probes + 5 * c * n) ≤ 3 * kPanAccessCall :=
    Nat.mul_le_mul_left 3 h2
  have hpost5 : 5 * (base + revertCost probes + 5 * c * n) ≤ 5 * kPanAccessCall :=
    Nat.mul_le_mul_left 5 h2
  have hs3 := AccessListCallStackAndLabToTargetMaster.slope3_absorption_non_vacuous_and_tight _ hpost3
  have hs5 := AccessListCallStackAndLabToTargetMaster.slope5_absorption_non_vacuous_and_tight _ hpost5
  rw [halign.1, halign.2.1] at hs3
  rw [halign.2.2.1, halign.2.2.2.1] at hs5
  have hhk : kPanStateRestoreCoupled = kPanAccessCall := kPanStateRestoreCoupled_val.2
  refine ⟨h1.1, h1.2, h2, by rw [hhk]; exact h2, hs3.1, hs3.2, hs5.1, hs5.2,
    dels_vs_units k_del c0 n_cyc, ?_⟩
  rw [dels_per_call]

/-- Theorem 5 (`non_vacuous_and_tight`): Full Pancake-to-Target `LabToTarget.removeLabels` section
cleanliness and length preservation (`access_call_lab_to_target_master_non_vacuous_and_tight`)
coupled with `GuestStateRestoreCoupledTightening` (`restore_dispatch`, `noop_absent_deletes`,
`rewrite_sets`) and `WordToWord.fullCompileSingle` zero-`storeConstsAllowance` invariance. -/
theorem pan_to_target_master_and_state_restore_tightening_non_vacuous_and_tight
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
    (hgas : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l +
      21 * sC l + sW l ≤ 2_000_000)
    (p : Bool) :
    (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
      (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
    base + revertCost probes + 5 * c * n ≤ kPanStateRestoreCoupled ∧
    42 * (l.map localCost).sum ≤ S * S ∧
    (∀ k ∈ fortyAccessCallPortfolio, k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (restoreOf (jsetStep false).1 = .del ∧ restoreOf (jsetStep true).1 = .set) ∧
    (restoreOf p = .del ↔ p = false) := by
  have hm := AccessListCallStackAndLabToTargetMaster.access_call_lab_to_target_master_non_vacuous_and_tight
    arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h cert probes c n base hp hc hn hb l Kal Aal hgas
  have halign := access_list_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  have hport : AccessListCallStackAndLabToTargetMaster.portfolio = fortyAccessCallPortfolio := halign.2.2.2.2.2.1
  have hk : kPanStateRestoreCoupled = kPanAccessCall := halign.2.2.2.2.2.2.2.2.1
  rw [hport] at hm
  exact ⟨hm.1, hm.2.1, by rw [hk]; exact hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2,
    ⟨noop_absent_deletes.1, rewrite_sets⟩, restore_dispatch p⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Unified 9-table coupled/merge envelopes (`F ≤ 95_238_095_238`,
`G ≤ 100_000_000_000`) plus `revertCost` and warm-set truncation bounded by `kPanStateRestoreCoupled = 159_893_274_708`,
together with `sstoreGas` exactness across clean/dirty/warm/cold cases. -/
theorem unified_nine_table_and_state_restore_sstore_gas_synthesis_non_vacuous_and_tight
    (Kal Aal D R A C W Tloc Tlin c_t n_t : Nat)
    (l_tx : List (Nat × Nat × Nat × Nat × Nat))
    (l_rev : List (Nat × Nat))
    (oc : Bool)
    (hal_c : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hal_m : 20 * ((D + Kal) + R + (A + Aal)) + 6 * (A + Aal) + 21 * C +
      (W + ((D + Kal) + R + (A + Aal))) ≤ S)
    (htx : 21 * sD l_tx + 20 * sR l_tx + 26 * sA l_tx + 21 * sC l_tx + sW l_tx ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hrev : (l_rev.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc_t : c_t ≤ 7_989) (hn_t : n_t ≤ 95_238) :
    F (D + Kal) R (A + Aal) C W ≤ 95_238_095_238 ∧
    G (D + Kal) R (A + Aal) C W ≤ 100_000_000_000 ∧
    (l_tx.map localCost).sum + 41_935 * sR l_tx ≤ 95_238_095_238 ∧
    linear + Tloc + G (D + Kal) R (A + Aal) C W + Tlin +
      revertCost l_rev + 5 * c_t * n_t ≤ kPanStateRestoreCoupled ∧
    linear + Tloc + ((l_tx.map localCost).sum + 41_935 * sR l_tx) + Tlin +
      revertCost l_rev + 5 * c_t * n_t ≤ kPanStateRestoreCoupled ∧
    sstoreGas true oc true = 100 ∧
    sstoreGas true true false = 10_100 ∧
    sstoreGas false true false = 12_100 ∧
    (sstoreGas true oc true = 100 ↔ oc = true ∨ oc = false) := by
  have hd := access_list_sub_block_and_unified_envelope_dominance_non_vacuous_and_tight
    Kal Aal D R A C W Tloc Tlin c_t n_t 0 l_tx l_rev hal_c hal_m htx hloc hlin hrev hc_t hn_t
  have hk : kPanStateRestoreCoupled = kPanAccessCall := kPanStateRestoreCoupled_val.2
  rw [hk]
  refine ⟨hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1,
    noop_warm_gas oc, changing_write_gas.1, changing_write_gas.2, ?_⟩
  cases oc <;> decide

/-- Theorem 7 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity (`Pairwise`) and IEEE-754
`float64` exactness (`< 2^53 - 1`) across all 40 budgets of `AccessListCallStackAndLabToTargetMaster.portfolio`
(`= fortyAccessCallPortfolio`), plus strict score separation of the 4 `kPanStateRestoreCoupled` tiers. -/
theorem forty_portfolio_yukon_score_and_state_restore_tiers_non_vacuous_and_tight
    (minutes K : Nat) :
    (AccessListCallStackAndLabToTargetMaster.portfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ k ∈ AccessListCallStackAndLabToTargetMaster.portfolio,
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    yukonScore 459_244_490_549 minutes <
      yukonScore AccessListCallStackAndLabToTargetMaster.accessCallSlope3UnrolledK minutes ∧
    yukonScore AccessListCallStackAndLabToTargetMaster.accessCallSlope3UnrolledK minutes <
      yukonScore AccessListCallStackAndLabToTargetMaster.accessCallSlope3K minutes ∧
    yukonScore AccessListCallStackAndLabToTargetMaster.accessCallSlope3K minutes <
      yukonScore 485_837_754_632 minutes ∧
    yukonScore CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope6K minutes <
      yukonScore AccessListCallStackAndLabToTargetMaster.accessCallSlope5UnrolledK minutes ∧
    yukonScore AccessListCallStackAndLabToTargetMaster.accessCallSlope5UnrolledK minutes <
      yukonScore AccessListCallStackAndLabToTargetMaster.accessCallSlope5K minutes ∧
    yukonScore AccessListCallStackAndLabToTargetMaster.accessCallSlope5K minutes <
      yukonScore transition6K minutes ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have halign := access_list_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  have hsc := forty_access_call_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes K
  rw [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2.1, halign.2.2.2.2.2.1]
  exact ⟨hsc.1, hsc.2.2.1, hsc.2.2.2.1, hsc.2.2.2.2.1, hsc.2.2.2.2.2.1,
    hsc.2.2.2.2.2.2.1, hsc.2.2.2.2.2.2.2.1, hsc.2.2.2.2.2.2.2.2.1, hsc.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Every one of the 40 budgets in
`AccessListCallStackAndLabToTargetMaster.portfolio` (`= fortyAccessCallPortfolio`) possesses a valid
`claim.json ≤ 128` byte representation (`validFiniteClaim = true` and `utf8ByteSize ≤ 128`). -/
theorem forty_portfolio_claims_and_master_targets_within_128_bytes_non_vacuous_and_tight
    (K : Nat) :
    fortyAccessCallClaims.length = 40 ∧
    fortyAccessCallClaims.map Prod.fst = AccessListCallStackAndLabToTargetMaster.portfolio ∧
    (∀ entry ∈ fortyAccessCallClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    validFiniteClaim AccessListCallStackAndLabToTargetMaster.accessCallSlope3UnrolledK
      (verifierClaimJson "479679833456") = true ∧
    validFiniteClaim AccessListCallStackAndLabToTargetMaster.accessCallSlope3K
      (verifierClaimJson "479679847256") = true ∧
    validFiniteClaim AccessListCallStackAndLabToTargetMaster.accessCallSlope5UnrolledK
      (verifierClaimJson "799466382872") = true ∧
    validFiniteClaim AccessListCallStackAndLabToTargetMaster.accessCallSlope5K
      (verifierClaimJson "799466396672") = true ∧
    (validFiniteClaim K (verifierClaimJson "799466396672") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) := by
  have halign := access_list_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  have hcl := forty_access_call_claims_valid_and_within_128_bytes_non_vacuous_and_tight K
  rw [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2.1, halign.2.2.2.2.2.1]
  exact ⟨hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2.2.1, hcl.2.2.2.2.2.2.1,
    hcl.2.2.2.2.2.2.2.2.1, hcl.2.2.2.2.2.2.2.2.2.2.1, hcl.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`): Direct `InitE.Certificate` for `accessCallSlope5K = 799_466_396_672`
and upward certificate lifting across all 4 `AccessListCallStackAndLabToTargetMaster` targets, all 40
budgets of `AccessListCallStackAndLabToTargetMaster.portfolio`, all 42 budgets of `allFortyTwoAccessCallBudgets`,
and the 2 hypothetical non-flooded 6× budgets (`hypotheticalSlope6UnrolledK`, `hypotheticalSlope6K`). -/
theorem state_restore_and_forty_portfolio_certificates_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_ac5 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        accessCallSlope5K (baselineInitialState input)).1 ≠ .timeOut)
    (hc_best : CertificateAt 1_212_035_192) :
    InitE.Certificate (baselineWithFiniteK AccessListCallStackAndLabToTargetMaster.accessCallSlope3UnrolledK)
      (.finite AccessListCallStackAndLabToTargetMaster.accessCallSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK AccessListCallStackAndLabToTargetMaster.accessCallSlope3K)
      (.finite AccessListCallStackAndLabToTargetMaster.accessCallSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK AccessListCallStackAndLabToTargetMaster.accessCallSlope5UnrolledK)
      (.finite AccessListCallStackAndLabToTargetMaster.accessCallSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK AccessListCallStackAndLabToTargetMaster.accessCallSlope5K)
      (.finite AccessListCallStackAndLabToTargetMaster.accessCallSlope5K) ∧
    CertificateAt hypotheticalSlope6UnrolledK ∧
    CertificateAt hypotheticalSlope6K ∧
    (∀ k ∈ AccessListCallStackAndLabToTargetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ fortyAccessCallPortfolio,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ allFortyTwoAccessCallBudgets,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    ¬ (bootstrapSteps + 5 * kPanStateRestoreCoupled ≤ accessCallSlope5K - 1) := by
  have hcert := access_call_and_forty_portfolio_certificates_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_ac5 hc_best
  have hh6u : 1_212_035_192 ≤ hypotheticalSlope6UnrolledK := by decide
  have hh6 : 1_212_035_192 ≤ hypotheticalSlope6K := by decide
  have hk : kPanStateRestoreCoupled = kPanAccessCall := kPanStateRestoreCoupled_val.2
  refine ⟨AccessListCallStackAndLabToTargetMaster.accessCallSlope3UnrolledK_certificate_non_vacuous_and_tight hc_best,
    AccessListCallStackAndLabToTargetMaster.accessCallSlope3K_certificate_non_vacuous_and_tight hc_best,
    AccessListCallStackAndLabToTargetMaster.accessCallSlope5UnrolledK_certificate_non_vacuous_and_tight hc_best,
    AccessListCallStackAndLabToTargetMaster.accessCallSlope5K_certificate_non_vacuous_and_tight hc_best,
    certificate_lift_non_vacuous_and_tight _ _ hh6u hc_best,
    certificate_lift_non_vacuous_and_tight _ _ hh6 hc_best,
    AccessListCallStackAndLabToTargetMaster.portfolio_certificates_non_vacuous_and_tight hc_best,
    hcert.2.2.2.2.1,
    hcert.2.2.2.2.2.1,
    by rw [hk]; exact hcert.2.2.2.2.2.2.2.2⟩

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_112` Master Synthesis Theorem uniting:
1. `AccessListCallStackAndLabToTargetMaster` (`44/44` tight: `panToTarget_sections_clean`,
   `panToTarget_sections_length`, `access_list_split_coupled_non_vacuous_and_tight`,
   `state_restore_envelope_non_vacuous_and_tight`, `portfolio.length = 40`),
2. `SelfContainedFortyBudgetPortfolioSynth` (`10/10` tight: `42·F ≤ S²`, `40·G ≤ S²`,
   `kPanUnifiedAllTables = 136_116_135_658`, `kPanAccessCall = 159_893_274_708`, 40-budget and
   42-budget strictly ordered portfolios, `yukonScore` monotonicity, `claim.json ≤ 128` byte validity),
3. `GuestStateRestoreCoupledTightening` (`11/11` tight: `restore_dispatch`, `noop_warm_gas`,
   `dels_per_call`, `del_bound_refuted`, `kPanStateRestoreCoupled = kPanAccessCall`,
   `hypothetical_fix`),
4. `InitE.Certificate` lifting across all 40 budgets under the Yukon ceiling `900_719_925_474`
   (`0` imports from `InitECandidate.Proofs.Bounded*`). -/
theorem grand_access_list_state_restore_and_forty_budget_synth_master_non_vacuous_and_tight
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
    (P T rc alg nm ac k_sn n bs Kal Aal D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call k_del : Nat)
    (co : Option (Spt Nat))
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
    (restoreOf p_rest = .del ↔ p_rest = false) ∧
    sstoreGas true oc_rest true = 100 ∧
    delsPerCall k_del = k_del ∧
    ¬ (1000 * delsPerCall 100 ≤ 0 + 0) ∧
    (kPanStateRestoreCoupled = 159_893_274_708 ∧ kPanStateRestoreCoupled = kPanAccessCall) ∧
    (6 * (136_116_135_658 + 3_804_281_910) < yukon ∧ ¬ (6 * kPanStateRestoreCoupled < yukon)) ∧
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2_000_000 ∧
    revertCost l_rev ≤ 19_972_857_140 ∧
    5 * c_t * n_t ≤ 3_804_281_910 ∧
    d_call ≤ 1_023 ∧
    linear + Tloc + G D_m R_m A_m C_m W_m + Tlin + revertCost l_rev + 5 * c_t * n_t ≤ kPanStateRestoreCoupled ∧
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
    AccessListCallStackAndLabToTargetMaster.portfolio = fortyAccessCallPortfolio ∧
    AccessListCallStackAndLabToTargetMaster.portfolio.length = 40 ∧
    AccessListCallStackAndLabToTargetMaster.portfolio.Pairwise (· < ·) ∧
    allFortyTwoAccessCallBudgets.length = 42 ∧
    (∀ k ∈ AccessListCallStackAndLabToTargetMaster.portfolio,
      1_212_035_192 ≤ k ∧ k < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK k) (.finite k) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    (AccessListCallStackAndLabToTargetMaster.portfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ fortyAccessCallClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    zeroBoundedImportCount = 0 ∧
    ¬ (accessCallSlope5K ≤ accessCallSlope5K - 1) := by
  have hw107 := grand_forty_budget_portfolio_synth_master_non_vacuous_and_tight
    arch prog wc asmConf perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
    info j bd ptr f tail s_st b_st stub sid next cs bs_l ctx q l_loop txs lp l_rev b d
    P T rc alg nm ac k_sn n bs Kal Aal D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call co
    hT hal hc_u hm_u h5 hDWR hloc hlin hrev hc_t hn_t hdepth oracles c depth minutes hlab compiled depthBound not_timeOut_best
  have halign := access_list_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  have hport : AccessListCallStackAndLabToTargetMaster.portfolio = fortyAccessCallPortfolio := halign.2.2.2.2.2.1
  have hk : kPanStateRestoreCoupled = kPanAccessCall := kPanStateRestoreCoupled_val.2
  rw [hport]
  exact ⟨restore_dispatch p_rest,
    noop_warm_gas oc_rest,
    dels_per_call k_del,
    del_bound_refuted,
    kPanStateRestoreCoupled_val,
    hypothetical_fix,
    hw107.1,
    hw107.2.1,
    hw107.2.2.1,
    hw107.2.2.2.1,
    by rw [hk]; exact hw107.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    rfl,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw107.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

#print axioms guest_state_restore_coupled_tightening_closure_non_vacuous_and_tight
#print axioms access_list_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight
#print axioms state_restore_del_flood_vs_hypothetical_six_slope_gap_non_vacuous_and_tight
#print axioms access_list_split_state_restore_and_del_flood_envelope_non_vacuous_and_tight
#print axioms pan_to_target_master_and_state_restore_tightening_non_vacuous_and_tight
#print axioms unified_nine_table_and_state_restore_sstore_gas_synthesis_non_vacuous_and_tight
#print axioms forty_portfolio_yukon_score_and_state_restore_tiers_non_vacuous_and_tight
#print axioms forty_portfolio_claims_and_master_targets_within_128_bytes_non_vacuous_and_tight
#print axioms state_restore_and_forty_portfolio_certificates_non_vacuous_and_tight
#print axioms grand_access_list_state_restore_and_forty_budget_synth_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedAccessListStateRestoreAndFortyBudgetSynth
