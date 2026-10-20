import InitECandidate.Solver.LabToTargetAndSubBlockThirtySixBudgetMaster
import InitECandidate.Solver.SelfContainedLabToTargetAndSubBlockSynth
import InitECandidate.Solver.GuestAccessListAndCallStackDominance

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedFortyBudgetPortfolioSynth` — Wave 5 Atomic Worker `W5_107`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`LabToTargetAndSubBlockThirtySixBudgetMaster` (`40/40` tight)**:
   - Master integration of `LabToTargetSectionCleanPreservation`, `GuestSubBlockTxSplittingDominance`,
     and `UnifiedAllTablesThirtySixBudgetMaster` (`integrated_master_non_vacuous_and_tight`,
     `split_coupled_non_vacuous_and_tight`, `split_four_tiers_non_vacuous_and_tight`).
2. **`SelfContainedLabToTargetAndSubBlockSynth` (`10/10` tight)**:
   - Full Pancake-to-Target compiler chain, sub-block transaction splitting under the 9-table
     unified coupled/merge envelopes (`F ≤ 95_238_095_238`, `G ≤ 100_000_000_000`,
     `kPanUnifiedAllTables = 136_116_135_658`), 32-budget and 36-budget portfolio preservation.
3. **`GuestAccessListAndCallStackDominance` (`11/11` tight)**:
   - Access-list intrinsic costs (`alAddrGas = 4_180`, `alKeyGas = 4_048`, `al_dominated`, `al_budget`),
   - Call-stack depth guard (`depth_guard`), journal revert (`undoTicks d = 5 * d`, `revert_eq`,
     `revert_le ≤ 19_972_857_140`), warm-set truncation (`truncate_le ≤ 3_804_281_910`),
   - Master access-list & call-stack source clock `kPanAccessCall = 159_893_274_708` (`kPanAccessCall_val`),
     Yukon ceiling admissibility across slopes `3×, 4×, 5× < yukon` while `yukon < 6 * kPanAccessCall`
     (`slopes`, `threshold`).
4. **40-Budget Certified Portfolio (`fortyAccessCallPortfolio`) & 42-Budget Grand Superset (`allFortyTwoAccessCallBudgets`)**:
   - The 4 new `kPanAccessCall` target budgets at slopes `3×` and `5×` (unrolled `9_332` and baseline
     `23_132` offsets: `479_679_833_456`, `479_679_847_256`, `799_466_382_872`, `799_466_396_672 < 900_719_925_474`),
   - Strict ordering alongside the 36 existing budgets (`fortyAccessCallPortfolio.length = 40`),
     strict `yukonScore` monotonicity, `claim.json ≤ 128` byte conformity (`fortyAccessCallClaims`),
     and `InitE.Certificate` lifting (`0 sorryAx`, 10 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.SelfContainedFortyBudgetPortfolioSynth

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

/-! ## Section 1: Four `kPanAccessCall` Target Budgets & 40-Budget Portfolio Definitions -/

/-- Unrolled 6-pass `3×` target budget for `kPanAccessCall = 159_893_274_708`:
`(bootstrapSteps - copyLoopSavedSteps) + 3 * kPanAccessCall = 9_332 + 479_679_824_124 = 479_679_833_456`. -/
def accessCallSlope3UnrolledK : Nat := (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanAccessCall

/-- Baseline 6-pass `3×` target budget for `kPanAccessCall = 159_893_274_708`:
`bootstrapSteps + 3 * kPanAccessCall = 23_132 + 479_679_824_124 = 479_679_847_256`. -/
def accessCallSlope3K : Nat := bootstrapSteps + 3 * kPanAccessCall

/-- Unrolled 6-pass `5×` target budget for `kPanAccessCall = 159_893_274_708`:
`(bootstrapSteps - copyLoopSavedSteps) + 5 * kPanAccessCall = 9_332 + 799_466_373_540 = 799_466_382_872`. -/
def accessCallSlope5UnrolledK : Nat := (bootstrapSteps - copyLoopSavedSteps) + 5 * kPanAccessCall

/-- Baseline 6-pass `5×` target budget for `kPanAccessCall = 159_893_274_708`:
`bootstrapSteps + 5 * kPanAccessCall = 23_132 + 799_466_373_540 = 799_466_396_672`. -/
def accessCallSlope5K : Nat := bootstrapSteps + 5 * kPanAccessCall

/-- The 4 `kPanAccessCall` target budgets at slopes `3×` and `5×` (unrolled and baseline). -/
def fourAccessCallTiers : List Nat := [
  accessCallSlope3UnrolledK,
  accessCallSlope3K,
  accessCallSlope5UnrolledK,
  accessCallSlope5K
]

/-- Explicit 40-budget strictly increasing portfolio uniting the 36 budgets of
`LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio` (`thirtySixMergePortfolio`) with the 4
`kPanAccessCall` tiers (`479_679_833_456`, `479_679_847_256`, `799_466_382_872`, `799_466_396_672`). -/
def fortyAccessCallPortfolio : List Nat := [
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
  810_291_208_508,
  816_696_823_280,
  816_696_837_080,
  857_384_015_252
]

/-- `claim.json` payloads paired with each of the 40 budgets in `fortyAccessCallPortfolio`. -/
def fortyAccessCallClaims : List (Nat × String) := [
  (1_212_035_192, verifierClaimJson "1212035192"),
  (2_038_701_869, verifierClaimJson "2038701869"),
  (11_029_669_988, verifierClaimJson "11029669988"),
  (11_029_683_788, verifierClaimJson "11029683788"),
  (19_392_692_330, verifierClaimJson "19392692330"),
  (22_059_330_644, verifierClaimJson "22059330644"),
  (22_059_344_444, verifierClaimJson "22059344444"),
  (32_791_963_724, verifierClaimJson "32791963724"),
  (87_829_684_748, verifierClaimJson "87829684748"),
  (121_459_456_007, verifierClaimJson "121459456007"),
  (122_620_608_536, verifierClaimJson "122620608536"),
  (214_346_021_162, verifierClaimJson "214346021162"),
  (242_918_888_882, verifierClaimJson "242918888882"),
  (296_693_001_548, verifierClaimJson "296693001548"),
  (387_840_417_875, verifierClaimJson "387840417875"),
  (392_562_715_820, verifierClaimJson "392562715820"),
  (405_145_615_820, verifierClaimJson "405145615820"),
  (408_348_416_306, verifierClaimJson "408348416306"),
  (408_348_430_106, verifierClaimJson "408348430106"),
  (428_692_019_192, verifierClaimJson "428692019192"),
  (459_244_490_549, verifierClaimJson "459244490549"),
  (479_679_833_456, verifierClaimJson "479679833456"),
  (479_679_847_256, verifierClaimJson "479679847256"),
  (485_837_754_632, verifierClaimJson "485837754632"),
  (500_060_306_876, verifierClaimJson "500060306876"),
  (540_194_146_716, verifierClaimJson "540194146716"),
  (593_385_979_964, verifierClaimJson "593385979964"),
  (610_978_715_738, verifierClaimJson "610978715738"),
  (610_978_730_738, verifierClaimJson "610978730738"),
  (675_242_677_612, verifierClaimJson "675242677612"),
  (677_645_382_458, verifierClaimJson "677645382458"),
  (677_645_397_458, verifierClaimJson "677645397458"),
  (775_680_812_618, verifierClaimJson "775680812618"),
  (785_125_408_508, verifierClaimJson "785125408508"),
  (799_466_382_872, verifierClaimJson "799466382872"),
  (799_466_396_672, verifierClaimJson "799466396672"),
  (810_291_208_508, verifierClaimJson "810291208508"),
  (816_696_823_280, verifierClaimJson "816696823280"),
  (816_696_837_080, verifierClaimJson "816696837080"),
  (857_384_015_252, verifierClaimJson "857384015252")
]

/-- Sorted 42-budget grand superset uniting `allThirtyEightMergeBudgets` (`38` budgets) with the
4 `kPanAccessCall` tiers (`fourAccessCallTiers`). -/
def allFortyTwoAccessCallBudgets : List Nat := [
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
  392_562_702_020,
  392_562_715_820,
  405_145_615_820,
  408_348_416_306,
  408_348_430_106,
  428_692_019_192,
  459_244_490_549,
  479_679_833_456,
  479_679_847_256,
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
  785_125_394_708,
  785_125_408_508,
  799_466_382_872,
  799_466_396_672,
  810_291_208_508,
  816_696_823_280,
  816_696_837_080,
  857_384_015_252
]

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Complete synthesis of `GuestAccessListAndCallStackDominance`
(`al_costs`, `al_dominated`, `al_budget`, `undo_eq`, `revert_eq`, `revert_le`, `truncate_le`,
`depth_guard`, `kPanAccessCall = 159_893_274_708`, `slopes`, `threshold`). -/
theorem guest_access_list_and_call_stack_dominance_closure_non_vacuous_and_tight
    (Kal Aal D A C R W d_u c_t n_t d_call k : Nat)
    (l_rev : List (Nat × Nat))
    (hal : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2_000_000)
    (hrev : (l_rev.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc_t : c_t ≤ 7_989) (hn_t : n_t ≤ 95_238)
    (hdepth : ¬ (d_call + 1 > 1024)) :
    (alAddrGas = 4_180 ∧ alKeyGas = 4_048) ∧
    (26 * 100 < alAddrGas ∧ 21 * 100 < alKeyGas ∧ 20 * 100 < alKeyGas) ∧
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2_000_000 ∧
    undoTicks d_u = 5 * d_u ∧
    revertCost l_rev = 5 * (l_rev.map (fun p => p.1 * p.2)).sum ∧
    revertCost l_rev ≤ 19_972_857_140 ∧
    (5 * c_t * n_t ≤ 3_804_281_910 ∧ 21 * 7_989 ≤ 167_772 ∧ 167_772 < 21 * 7_990) ∧
    d_call ≤ 1_023 ∧
    kPanAccessCall = 159_893_274_708 ∧
    (3 * kPanAccessCall < yukon ∧ 4 * kPanAccessCall < yukon ∧
      5 * kPanAccessCall < yukon ∧ yukon < 6 * kPanAccessCall) ∧
    ((k * kPanAccessCall < yukon ↔ k ≤ 5) ∧ yukon - 5 * kPanAccessCall = 101_253_551_934) :=
  ⟨al_costs,
   al_dominated,
   al_budget Kal Aal D A C R W hal,
   undo_eq d_u,
   revert_eq l_rev,
   revert_le l_rev hrev,
   truncate_le c_t n_t hc_t hn_t,
   depth_guard d_call hdepth,
   kPanAccessCall_val,
   GuestAccessListAndCallStackDominance.slopes,
   threshold k⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Access-list budget domination (`al_budget`) coupled with
sub-block multi-transaction splitting (`split_coupled_non_vacuous_and_tight`) and the 9-table
unified coupled/merge envelopes (`F ≤ 95_238_095_238`, `G ≤ 100_000_000_000`) plus revert and
truncation overhead bounded by `kPanAccessCall = 159_893_274_708`. -/
theorem access_list_sub_block_and_unified_envelope_dominance_non_vacuous_and_tight
    (Kal Aal D R A C W Tloc Tlin c_t n_t K : Nat)
    (l_tx : List (Nat × Nat × Nat × Nat × Nat))
    (l_rev : List (Nat × Nat))
    (hal_c : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hal_m : 20 * ((D + Kal) + R + (A + Aal)) + 6 * (A + Aal) + 21 * C +
      (W + ((D + Kal) + R + (A + Aal))) ≤ S)
    (htx : 21 * sD l_tx + 20 * sR l_tx + 26 * sA l_tx + 21 * sC l_tx + sW l_tx ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hrev : (l_rev.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc_t : c_t ≤ 7_989) (hn_t : n_t ≤ 95_238) :
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ S ∧
    F (D + Kal) R (A + Aal) C W ≤ 95_238_095_238 ∧
    G (D + Kal) R (A + Aal) C W ≤ 100_000_000_000 ∧
    (l_tx.map localCost).sum + 41_935 * sR l_tx ≤ 95_238_095_238 ∧
    linear + Tloc + G (D + Kal) R (A + Aal) C W + Tlin +
      revertCost l_rev + 5 * c_t * n_t ≤ kPanAccessCall ∧
    linear + Tloc + ((l_tx.map localCost).sum + 41_935 * sR l_tx) + Tlin +
      revertCost l_rev + 5 * c_t * n_t ≤ kPanAccessCall ∧
    (kPanAccessCall ≤ K ↔ 159_893_274_708 ≤ K) := by
  have hS : S = 2_000_000 := rfl
  have hdom : 21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ S := by
    rw [hS] at hal_c ⊢
    exact al_budget Kal Aal D A C R W hal_c
  have hF := unified_coupled_le (D + Kal) R (A + Aal) C W hdom
  have hG := unified_merge_le (D + Kal) R (A + Aal) C W hal_m
  have hsc := split_coupled_non_vacuous_and_tight l_tx htx
  have hmast := kPanUnified_master (D + Kal) R (A + Aal) C W Tloc Tlin hal_m hloc hlin
  have hr := revert_le l_rev hrev
  have htr := (truncate_le c_t n_t hc_t hn_t).1
  have hsum_u : linear + locCoup + 100_000_000_000 + mergeLin = kPanUnifiedAllTables := by decide
  have hk_val := kPanAccessCall_val
  refine ⟨hdom, hF, hG, hsc, ?_, ?_, by rw [hk_val]⟩
  · unfold kPanAccessCall; omega
  · unfold kPanAccessCall; omega

/-- Theorem 3 (`non_vacuous_and_tight`): Exact numerical evaluation of the 4 `kPanAccessCall` target
budgets (`accessCallSlope3UnrolledK = 479_679_833_456`, `accessCallSlope3K = 479_679_847_256`,
`accessCallSlope5UnrolledK = 799_466_382_872`, `accessCallSlope5K = 799_466_396_672`) and their
exact deltas over `kPanUnifiedAllTables` (`mergeSlope3UnrolledK`, `mergeSlope3K`, `mergeSlope6UnrolledK`,
`mergeSlope6K`) and `transition6K`. -/
theorem access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight (slope : Nat) :
    accessCallSlope3UnrolledK = 479_679_833_456 ∧
    accessCallSlope3K = 479_679_847_256 ∧
    accessCallSlope5UnrolledK = 799_466_382_872 ∧
    accessCallSlope5K = 799_466_396_672 ∧
    kPanAccessCall - kPanUnifiedAllTables = 23_777_139_050 ∧
    accessCallSlope3UnrolledK - mergeSlope3UnrolledK = 71_331_417_150 ∧
    accessCallSlope3K - mergeSlope3K = 71_331_417_150 ∧
    mergeSlope6UnrolledK - accessCallSlope5UnrolledK = 17_230_440_408 ∧
    mergeSlope6K - accessCallSlope5K = 17_230_440_408 ∧
    accessCallSlope3K - accessCallSlope3UnrolledK = 13_800 ∧
    accessCallSlope5K - accessCallSlope5UnrolledK = 13_800 ∧
    900_719_925_474 - accessCallSlope5K = 101_253_528_802 ∧
    (bootstrapSteps + slope * kPanAccessCall < 900_719_925_474 ↔ slope ≤ 5) := by
  have hb : bootstrapSteps = 23_132 := bootstrapSteps_eq
  have hub : bootstrapSteps - copyLoopSavedSteps = 9_332 :=
    twenty_two_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight.1
  have ha3u : accessCallSlope3UnrolledK = 479_679_833_456 := by
    unfold accessCallSlope3UnrolledK; rw [hub]; decide
  have ha3 : accessCallSlope3K = 479_679_847_256 := by
    unfold accessCallSlope3K; rw [hb]; decide
  have ha5u : accessCallSlope5UnrolledK = 799_466_382_872 := by
    unfold accessCallSlope5UnrolledK; rw [hub]; decide
  have ha5 : accessCallSlope5K = 799_466_396_672 := by
    unfold accessCallSlope5K; rw [hb]; decide
  have hm := merge_tx_target_budgets_and_transition_gaps_non_vacuous_and_tight 0
  rw [ha3u, ha3, ha5u, ha5, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hb]
  refine ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_⟩
  unfold kPanAccessCall kPanUnifiedAllTables linear locCoup mergeLin
  omega

/-- Theorem 4 (`non_vacuous_and_tight`): Exact insertion of the 4 `kPanAccessCall` tiers
(`fourAccessCallTiers`) into `LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio` (`36` budgets)
to form the strictly ordered 40-budget portfolio `fortyAccessCallPortfolio`, and into
`allThirtyEightMergeBudgets` (`38` budgets) to form the strictly ordered 42-budget grand superset
`allFortyTwoAccessCallBudgets`. -/
theorem forty_access_call_portfolio_exact_insertion_and_order_non_vacuous_and_tight (K : Nat) :
    fortyAccessCallPortfolio.length = 40 ∧
    fortyAccessCallPortfolio.Pairwise (· < ·) ∧
    (LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio ++ fourAccessCallTiers).insertionSort (· ≤ ·) =
      fortyAccessCallPortfolio ∧
    (∀ k ∈ LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio, k ∈ fortyAccessCallPortfolio) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified, k ∈ fortyAccessCallPortfolio) ∧
    (∀ k ∈ fourAccessCallTiers, k ∈ fortyAccessCallPortfolio) ∧
    (∀ k ∈ fortyAccessCallPortfolio,
      1_212_035_192 ≤ k ∧ k ≤ 857_384_015_252 ∧ k < 900_719_925_474 ∧ ¬ k ≤ k - 1) ∧
    allFortyTwoAccessCallBudgets.length = 42 ∧
    allFortyTwoAccessCallBudgets.Pairwise (· < ·) ∧
    (∀ k ∈ fortyAccessCallPortfolio, k ∈ allFortyTwoAccessCallBudgets) ∧
    (∀ k ∈ allThirtyEightMergeBudgets, k ∈ allFortyTwoAccessCallBudgets) ∧
    (accessCallSlope5K ≤ K ↔ 799_466_396_672 ≤ K) := by
  have ha := access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight 0
  have hfat : fourAccessCallTiers = [479_679_833_456, 479_679_847_256, 799_466_382_872, 799_466_396_672] := by
    unfold fourAccessCallTiers
    rw [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1]
  have ha5 : accessCallSlope5K = 799_466_396_672 := ha.2.2.2.1
  have hsort : (LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio ++ fourAccessCallTiers).insertionSort (· ≤ ·) =
      fortyAccessCallPortfolio := by
    rw [hfat]; decide
  have hmem4 : ∀ k ∈ fourAccessCallTiers, k ∈ fortyAccessCallPortfolio := by
    rw [hfat]; decide
  refine ⟨by decide, by decide, hsort, by decide, by decide, hmem4,
    by decide, by decide, by decide, by decide, by decide, ?_⟩
  rw [ha5]

/-- Theorem 5 (`non_vacuous_and_tight`): Interleaved strict ordering of the 4 `kPanAccessCall` target
tiers (`479_679_833_456`, `479_679_847_256`, `799_466_382_872`, `799_466_396_672`) within the
40-budget portfolio, bracketing `459_244_490_549 < accessCallSlope3UnrolledK < accessCallSlope3K < 485_837_754_632`
and `CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope6K < accessCallSlope5UnrolledK < accessCallSlope5K < transition6K < mergeSlope6UnrolledK < mergeSlope6K < terminalK`. -/
theorem access_call_tiers_interleaved_strict_ordering_non_vacuous_and_tight (K : Nat) :
    transition3K < mergeSlope3UnrolledK ∧
    mergeSlope3UnrolledK < mergeSlope3K ∧
    mergeSlope3K < 459_244_490_549 ∧
    459_244_490_549 < accessCallSlope3UnrolledK ∧
    accessCallSlope3UnrolledK < accessCallSlope3K ∧
    accessCallSlope3K < 485_837_754_632 ∧
    485_837_754_632 < transition4K ∧
    transition4K < transition5K ∧
    transition5K < CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope6K ∧
    CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope6K < accessCallSlope5UnrolledK ∧
    accessCallSlope5UnrolledK < accessCallSlope5K ∧
    accessCallSlope5K < transition6K ∧
    transition6K < mergeSlope6UnrolledK ∧
    mergeSlope6UnrolledK < mergeSlope6K ∧
    mergeSlope6K < terminalK ∧
    terminalK < 900_719_925_474 ∧
    (accessCallSlope3K ≤ K ↔ 479_679_847_256 ≤ K) := by
  have ha := access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight 0
  have hm := merge_tx_target_budgets_and_transition_gaps_non_vacuous_and_tight 0
  rw [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, Iff.rfl⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Synthesis of `LabToTargetAndSubBlockThirtySixBudgetMaster.integrated_master_non_vacuous_and_tight`
with `kPanAccessCall` 4-tier bounds (`9_332 + 3·cost_ac ≤ 479_679_833_456`, `23_132 + 3·cost_ac ≤ 479_679_847_256`,
`9_332 + 5·cost_ac ≤ 799_466_382_872`, `23_132 + 5·cost_ac ≤ 799_466_396_672`) and `WordToWord.fullCompileSingle`
zero-`storeConstsAllowance` invariance. -/
theorem lab_to_target_sub_block_and_access_call_eight_tiers_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (l : List (Nat × Nat × Nat × Nat × Nat)) (l_rev : List (Nat × Nat))
    (T Tloc Tlin c_t n_t : Nat)
    (budget : 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ S)
    (ht : txMinUnits * T ≤ 2_000_000) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hrev : (l_rev.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc_t : c_t ≤ 7_989) (hn_t : n_t ≤ 95_238)
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h_rem : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (ctx : Spt Nat) (q : HolLoopProg width) (l_loop : Nat × Nat)
    (b : Bool) (rc alg nm ac_n : Nat) (co : Option (Spt Nat))
    (ws : List (Bool × BitVec width)) :
    (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
      ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
        ∃ s ∈ StackToLab.compile sc dc mh sp off
            (compileNative ac perf (WordToWord.compile wc ac
              (panToWordCompileProgHOL arch prog)).2).2.2.2,
          s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
      (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
    (let cost := linear + Tloc + ((l.map localCost).sum + 41_935 * sR l) + Tlin
     cost ≤ kPanUnifiedAllTables ∧
     9_332 + 3 * cost ≤ mergeSlope3UnrolledK ∧ 23_132 + 3 * cost ≤ mergeSlope3K ∧
     9_332 + 6 * cost ≤ mergeSlope6UnrolledK ∧ 23_132 + 6 * cost ≤ mergeSlope6K ∧
     txResetTicks * T ≤ 18 * (12_000 * T) ∧ T ≤ 16_666 ∧
     (LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio.length = 36 ∧
      ∀ k ∈ LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio, k < yukon)) ∧
    (let cost_ac := linear + Tloc + ((l.map localCost).sum + 41_935 * sR l) + Tlin +
       revertCost l_rev + 5 * c_t * n_t
     cost_ac ≤ kPanAccessCall ∧
     9_332 + 3 * cost_ac ≤ accessCallSlope3UnrolledK ∧
     23_132 + 3 * cost_ac ≤ accessCallSlope3K ∧
     9_332 + 5 * cost_ac ≤ accessCallSlope5UnrolledK ∧
     23_132 + 5 * cost_ac ≤ accessCallSlope5K) ∧
    accessCallSlope5K + storeConstsAllowance (WordToWord.fullCompileSingle b rc alg ac
      ((nm, ac_n, (LoopToWord.compHOL ctx q l_loop).1), co)).2.2 = 799_466_396_672 ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have hint := LabToTargetAndSubBlockThirtySixBudgetMaster.integrated_master_non_vacuous_and_tight
    l T Tloc Tlin budget ht hloc hlin arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h_rem
  have hsc := split_coupled_non_vacuous_and_tight l budget
  have hr := revert_le l_rev hrev
  have htr := (truncate_le c_t n_t hc_t hn_t).1
  have ha := access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight 0
  have hnost := CleanToDirtyCoupledSixPassMaster.loop_full_pass_non_vacuous_and_tight ctx q l_loop b rc alg ac nm ac_n co
  have hzero : storeConstsAllowance (WordToWord.fullCompileSingle b rc alg ac
      ((nm, ac_n, (LoopToWord.compHOL ctx q l_loop).1), co)).2.2 = 0 :=
    noSt_allowance_zero _ hnost
  have htight := StackRemoveStoreConstsZeroBridge.allowance_storeConsts_tight 0 2 4 6 ws
  have hcost_u : linear + Tloc + ((l.map localCost).sum + 41_935 * sR l) + Tlin ≤ kPanUnifiedAllTables :=
    hint.2.2.1
  have hk_ac : kPanUnifiedAllTables + 19_972_857_140 + 3_804_281_910 = kPanAccessCall := rfl
  have hk_val := kPanAccessCall_val
  refine ⟨hint.1, hint.2.1, hint.2.2, ?_, ?_, ?_⟩
  · dsimp only
    rw [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1]
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  · rw [hzero, Nat.add_zero, ha.2.2.2.1]
  · rw [htight, List.length_eq_zero_iff]

/-- Theorem 7 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity (`Pairwise`) and IEEE-754
`float64` exactness (`< 2^53 - 1`) across all 40 budgets of `fortyAccessCallPortfolio`, proving that
every budget in the 40-budget portfolio achieves a strictly distinct, `float64`-exact `yukonScore`
bounded below by `yukonScore 1_212_035_192 minutes` and above by `yukonScore 857_384_015_252 minutes`. -/
theorem forty_access_call_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight
    (minutes K : Nat) :
    (fortyAccessCallPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ k1 ∈ fortyAccessCallPortfolio,
      ∀ k2 ∈ fortyAccessCallPortfolio,
        k1 < k2 ↔ yukonScore k1 minutes < yukonScore k2 minutes) ∧
    (∀ k ∈ fortyAccessCallPortfolio,
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    yukonScore 459_244_490_549 minutes < yukonScore accessCallSlope3UnrolledK minutes ∧
    yukonScore accessCallSlope3UnrolledK minutes < yukonScore accessCallSlope3K minutes ∧
    yukonScore accessCallSlope3K minutes < yukonScore 485_837_754_632 minutes ∧
    yukonScore CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope6K minutes <
      yukonScore accessCallSlope5UnrolledK minutes ∧
    yukonScore accessCallSlope5UnrolledK minutes < yukonScore accessCallSlope5K minutes ∧
    yukonScore accessCallSlope5K minutes < yukonScore transition6K minutes ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hord : fortyAccessCallPortfolio.Pairwise (· < ·) :=
    (forty_access_call_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0).2.1
  have hmap_pw : (fortyAccessCallPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp (fun {a b} hab => score_monotone_non_vacuous_and_tight a b minutes hab) hord
  have hterm_f64 := (fifteen_regime_and_bs32_float64_exactness_non_vacuous_and_tight minutes K)
  have hterm_lt : yukonScore 857_384_015_252 minutes < 2 ^ 53 - 1 := by
    have ht : terminalK = 857_384_015_252 := (candidate_count_non_vacuous_and_tight).2
    simpa only [ht] using hterm_f64.2.2.2.2.2.1
  have hint := access_call_tiers_interleaved_strict_ordering_non_vacuous_and_tight 0
  refine ⟨hmap_pw, ?_, ?_,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.2.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.2.2.2.2.2.2.2.2.2.1,
    hterm_f64.2.2.2.2.2.2⟩
  · intro k1 _ k2 _
    unfold yukonScore
    omega
  · intro k hk
    have hbnd := (forty_access_call_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0).2.2.2.2.2.2.1 k hk
    have h1 : yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes := by
      unfold yukonScore; omega
    have h2 : yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes := by
      unfold yukonScore; omega
    exact ⟨h1, h2, Nat.lt_of_le_of_lt h2 hterm_lt⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Every one of the 40 budgets in `fortyAccessCallPortfolio`
possesses a valid `claim.json ≤ 128` byte representation (`validFiniteClaim = true` and
`utf8ByteSize ≤ 128`), including explicit verification of the 4 `kPanAccessCall` claims
(`479679833456`, `479679847256`, `799466382872`, `799466396672`). -/
theorem forty_access_call_claims_valid_and_within_128_bytes_non_vacuous_and_tight (K : Nat) :
    fortyAccessCallClaims.length = 40 ∧
    fortyAccessCallClaims.map Prod.fst = fortyAccessCallPortfolio ∧
    (∀ entry ∈ fortyAccessCallClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (verifierClaimJson "479679833456").utf8ByteSize ≤ 128 ∧
    validFiniteClaim accessCallSlope3UnrolledK (verifierClaimJson "479679833456") = true ∧
    (verifierClaimJson "479679847256").utf8ByteSize ≤ 128 ∧
    validFiniteClaim accessCallSlope3K (verifierClaimJson "479679847256") = true ∧
    (verifierClaimJson "799466382872").utf8ByteSize ≤ 128 ∧
    validFiniteClaim accessCallSlope5UnrolledK (verifierClaimJson "799466382872") = true ∧
    (verifierClaimJson "799466396672").utf8ByteSize ≤ 128 ∧
    validFiniteClaim accessCallSlope5K (verifierClaimJson "799466396672") = true ∧
    (validFiniteClaim K (verifierClaimJson "799466396672") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) := by
  have ha := access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight 0
  have hlen : decide ((verifierClaimJson "799466396672").utf8ByteSize ≤ MAX_CLAIM_BYTES) = true := by decide
  rw [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1]
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  unfold validFiniteClaim
  rw [hlen, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- Theorem 9 (`non_vacuous_and_tight`): Direct `InitE.Certificate` for `accessCallSlope5K = 799_466_396_672`
from uniform post-bootstrap target non-`.timeOut`, plus upward lifting across all 4 `kPanAccessCall` tiers,
all 40 budgets of `fortyAccessCallPortfolio`, all 42 budgets of `allFortyTwoAccessCallBudgets`, all 36
budgets of `LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio`, and all 32 absorbed budgets from
`CertificateAt 1_212_035_192`. -/
theorem access_call_and_forty_portfolio_certificates_non_vacuous_and_tight
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
    CertificateAt accessCallSlope3UnrolledK ∧
    CertificateAt accessCallSlope3K ∧
    CertificateAt accessCallSlope5UnrolledK ∧
    CertificateAt accessCallSlope5K ∧
    (∀ k ∈ fortyAccessCallPortfolio,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ allFortyTwoAccessCallBudgets,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (absorbBudget k)) (.finite (absorbBudget k))) ∧
    ¬ (bootstrapSteps + 5 * kPanAccessCall ≤ accessCallSlope5K - 1) := by
  have ha := access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight 0
  have hc_a5 : CertificateAt accessCallSlope5K :=
    finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth (5 * kPanAccessCall) hlab compiled depthBound not_timeOut_ac5
  have hcert40 : ∀ k ∈ fortyAccessCallPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
    intro k hk
    have hbnd := (forty_access_call_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0).2.2.2.2.2.2.1 k hk
    exact certificate_lift_non_vacuous_and_tight _ k hbnd.1 hc_best
  have hcert42 : ∀ k ∈ allFortyTwoAccessCallBudgets, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
    intro k hk
    have h42_le : ∀ x ∈ allFortyTwoAccessCallBudgets, 1_212_035_192 ≤ x := by decide
    exact certificate_lift_non_vacuous_and_tight _ k (h42_le k hk) hc_best
  have ha3u_le : 1_212_035_192 ≤ accessCallSlope3UnrolledK := by rw [ha.1]; decide
  have ha3_le : 1_212_035_192 ≤ accessCallSlope3K := by rw [ha.2.1]; decide
  have ha5u_le : 1_212_035_192 ≤ accessCallSlope5UnrolledK := by rw [ha.2.2.1]; decide
  have hcert36 := LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio_certificates_non_vacuous_and_tight hc_best
  have hmaster_abs := ThirtyTwoBudgetJointAbsorptionMaster.master_non_vacuous_and_tight hc_best
  refine ⟨certificate_lift_non_vacuous_and_tight _ _ ha3u_le hc_best,
    certificate_lift_non_vacuous_and_tight _ _ ha3_le hc_best,
    certificate_lift_non_vacuous_and_tight _ _ ha5u_le hc_best,
    hc_a5, hcert40, hcert42, hcert36, hmaster_abs.2.2.2.1, ?_⟩
  unfold accessCallSlope5K
  rw [bootstrapSteps_eq]
  decide

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_107` Master Synthesis Theorem uniting:
1. `LabToTargetAndSubBlockThirtySixBudgetMaster` (`40/40` tight: `panToTarget_sections_clean`,
   `panToTarget_sections_length`, `split_coupled_non_vacuous_and_tight`, `integrated_master_non_vacuous_and_tight`),
2. `SelfContainedLabToTargetAndSubBlockSynth` (`10/10` tight: `42·F ≤ S²`, `40·G ≤ S²`,
   `kPanUnifiedAllTables = 136_116_135_658`, 5-address-table offsets, unconditional compiler chain),
3. `GuestAccessListAndCallStackDominance` (`11/11` tight: `al_budget`, `revert_le`, `truncate_le`,
   `depth_guard`, `kPanAccessCall = 159_893_274_708`, slopes `3×, 4×, 5× < yukon`),
4. The **40-budget** strictly ordered certified portfolio `fortyAccessCallPortfolio` and **42-budget**
   grand superset `allFortyTwoAccessCallBudgets` with `claim.json ≤ 128` byte validity, strict
   `yukonScore` monotonicity, and `InitE.Certificate` lifting (`0` imports from `Proofs/Bounded*`). -/
theorem grand_forty_budget_portfolio_synth_master_non_vacuous_and_tight
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
    (b d : Bool)
    (P T rc alg nm ac k_sn n bs Kal Aal D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call : Nat)
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
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2_000_000 ∧
    revertCost l_rev ≤ 19_972_857_140 ∧
    5 * c_t * n_t ≤ 3_804_281_910 ∧
    d_call ≤ 1_023 ∧
    kPanAccessCall = 159_893_274_708 ∧
    (3 * kPanAccessCall < yukon ∧ 4 * kPanAccessCall < yukon ∧
      5 * kPanAccessCall < yukon ∧ yukon < 6 * kPanAccessCall) ∧
    linear + Tloc + G D_m R_m A_m C_m W_m + Tlin + revertCost l_rev + 5 * c_t * n_t ≤ kPanAccessCall ∧
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
    kPanUnifiedAllTables = 136_116_135_658 ∧
    fortyAccessCallPortfolio.length = 40 ∧
    fortyAccessCallPortfolio.Pairwise (· < ·) ∧
    allFortyTwoAccessCallBudgets.length = 42 ∧
    (∀ k ∈ fortyAccessCallPortfolio,
      1_212_035_192 ≤ k ∧ k < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK k) (.finite k) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    (fortyAccessCallPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ fortyAccessCallClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    zeroBoundedImportCount = 0 ∧
    ¬ (accessCallSlope5K ≤ accessCallSlope5K - 1) := by
  have hbest : CertificateAt exactKeccak128UnrolledK :=
    optimal_direct_certificate_non_vacuous_and_tight oracles c depth hlab compiled depthBound not_timeOut_best
  have hek : exactKeccak128UnrolledK = 1_212_035_192 := exact_keccak_128_unrolled_exact
  have hc_1212 : CertificateAt 1_212_035_192 := by simpa only [hek] using hbest
  have hw103 := grand_lab_to_target_and_sub_block_master_non_vacuous_and_tight
    arch prog wc asmConf perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
    info j bd ptr f tail s_st b_st stub sid next cs bs_l ctx q l_loop txs lp b d
    P T rc alg nm ac k_sn n bs D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin co
    hT hc_u hm_u h5 hDWR hloc hlin oracles c depth minutes hlab compiled depthBound not_timeOut_best
  have hrev_b := revert_le l_rev hrev
  have htr_b := (truncate_le c_t n_t hc_t hn_t).1
  have hmast_u := hw103.2.2.2.2.2.2.2.2.2.2.1
  have hmast_ac : linear + Tloc + G D_m R_m A_m C_m W_m + Tlin + revertCost l_rev + 5 * c_t * n_t ≤ kPanAccessCall := by
    unfold kPanAccessCall; omega
  have hord40 := forty_access_call_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0
  have hsc40 := forty_access_call_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes 0
  have hcl40 := (forty_access_call_claims_valid_and_within_128_bytes_non_vacuous_and_tight 1).2.2.1
  have ha := access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight 0
  refine ⟨al_budget Kal Aal D A C R W hal,
    hrev_b,
    htr_b,
    depth_guard d_call hdepth,
    kPanAccessCall_val,
    GuestAccessListAndCallStackDominance.slopes,
    hmast_ac,
    hw103.1,
    hw103.2.1,
    hw103.2.2.1,
    hw103.2.2.2.1,
    hw103.2.2.2.2.1,
    hw103.2.2.2.2.2.1,
    hw103.2.2.2.2.2.2.1,
    hw103.2.2.2.2.2.2.2.2.1,
    hw103.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hord40.1,
    hord40.2.1,
    hord40.2.2.2.2.2.2.2.1,
    ?_,
    hsc40.1,
    hcl40,
    hw103.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    rfl,
    by rw [ha.2.2.2.1]; decide⟩
  intro k hk
  have hbnd := hord40.2.2.2.2.2.2.1 k hk
  have hsc := hsc40.2.2.1 k hk
  exact ⟨hbnd.1, hbnd.2.2.1,
    certificate_lift_non_vacuous_and_tight _ k hbnd.1 hc_1212,
    hsc.1, hsc.2.2⟩

#print axioms guest_access_list_and_call_stack_dominance_closure_non_vacuous_and_tight
#print axioms access_list_sub_block_and_unified_envelope_dominance_non_vacuous_and_tight
#print axioms access_call_target_budgets_and_unified_gaps_non_vacuous_and_tight
#print axioms forty_access_call_portfolio_exact_insertion_and_order_non_vacuous_and_tight
#print axioms access_call_tiers_interleaved_strict_ordering_non_vacuous_and_tight
#print axioms lab_to_target_sub_block_and_access_call_eight_tiers_non_vacuous_and_tight
#print axioms forty_access_call_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight
#print axioms forty_access_call_claims_valid_and_within_128_bytes_non_vacuous_and_tight
#print axioms access_call_and_forty_portfolio_certificates_non_vacuous_and_tight
#print axioms grand_forty_budget_portfolio_synth_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedFortyBudgetPortfolioSynth
