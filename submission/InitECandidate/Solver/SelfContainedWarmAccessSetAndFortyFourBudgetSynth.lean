import InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound
import InitECandidate.Solver.DistinctDeleteCycleAndCoupledRevertMaster
import InitECandidate.Solver.SelfContainedCoupledRevertTxCapAndDisjointTablesSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedWarmAccessSetAndFortyFourBudgetSynth` — Wave 5 Atomic Worker `W5_126`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`GuestWarmAccessSetAndRollbackBound` (`11/11` tight)**:
   - The 10th and 11th hash tables `ev+168` (warm addresses, 20-byte keys) and `ev+176` (warm storage
     keys, 52-byte `addr‖key`), per-frame rollback via `htab_truncate` (`trunc_exact`, `trunc_keeps_parent`),
   - Cold address cost (`3_000 = 30 * 100` gas ≥ `26 * 100`, `cold_addr_units`),
   - Per-tx `ev+168` size cap under EIP-7825 (`a + 19 ≤ 5_611` when `30 * a ≤ 167_772`, `addr_set_tx`,
     `addr_set_tx_tight`), per-block deleted address entries (`n ≤ 66_666`, `addr_dels_block`),
   - `ev+168` truncation envelope (`truncTicks a n = 5 * a * n ≤ 1_870_314_630`, `addr_trunc_le`,
     `addr_trunc_tight`), `ev+176` truncation already in `kPanAccessCall` (`storage_trunc_in_access`),
   - Master warm-access-set source clock `kPanWarmSets = kPanAccessCall + 1_870_314_630 = 161_763_589_338`
     (`kPanWarmSets_val`) and Yukon slopes (`5 * kPanWarmSets < yukon`, margin `91_901_978_784`,
     `yukon < 6 * kPanWarmSets`, `slopes`).
2. **`DistinctDeleteCycleAndCoupledRevertMaster` (`15/15` tight)**:
   - Conditional `H2` distinct-delete / call-cycle audit (`repeat_no_delete`, `dels_distinct`,
     `cycle_units`, `revert_le_tight`, `conditional_six_slope`, `kPanSixSlopeRestored = 139_920_417_568`)
     coexisting with the unconditional five-slope bound (`unconditional_five_slope`, `no_six_restore`),
     per-tx dirty cap (`d_t ≤ 7_989`), disjoint `bs+32` / `ts+32` partition, `LabToTarget.removeLabels`
     clean sections, and 40-budget portfolio (`integrated_master_non_vacuous_and_tight`).
3. **`SelfContainedCoupledRevertTxCapAndDisjointTablesSynth` (`10/10` tight)**:
   - Self-contained coupled revert & per-tx EIP-7825 cap (`d_t ≤ 7_989`, `coupledCost witness = 155_688_931_265`),
     disjoint block/tx storage tables, 30-tier hierarchy (`thirtyTierHierarchy`), 40-budget portfolio,
     and full Pancake-to-Target `removeLabels` clean-section preservation (`0` `Bounded*` imports).
4. **44-Budget Certified Portfolio (`fortyFourWarmSetsPortfolio`) & 46-Budget Grand Superset (`allFortySixWarmSetsBudgets`)**:
   - The 4 new `kPanWarmSets` target budgets at slopes `3×` and `5×` (unrolled `9_332` and baseline
     `23_132` offsets: `485_290_777_346`, `485_290_791_146`, `808_817_956_022`, `808_817_969_822 < 900_719_925_474`,
     plus the 100-tick tighter ceilings `485_290_777_246`, `485_290_791_046`, `808_817_955_922`, `808_817_969_722`),
   - Strict ordering alongside the 40 existing budgets (`fortyFourWarmSetsPortfolio.length = 44`),
     strict `yukonScore` monotonicity, `claim.json ≤ 128` byte conformity (`fortyFourWarmSetsClaims`),
     and `InitE.Certificate` lifting (`0 sorryAx`, 10 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.SelfContainedWarmAccessSetAndFortyFourBudgetSynth

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Proofs.BootstrapSteps
open InitECandidate.Proofs.BootstrapCopy
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Proofs.BootstrapAsmComposition
open InitECandidate.Proofs.BootstrapTrace
open InitECandidate.Solver
open InitECandidate.Solver.FastHalt
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedIsoReducedK
open InitECandidate.Solver.SelfContainedBasicBlockBridge
open InitECandidate.Solver.SelfContainedSixPassMaster
open InitECandidate.Solver.PanToWordNoStoreConsts
open InitECandidate.Solver.PanToStackNoStoreConsts
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts
open InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts
open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock
open InitECandidate.Solver.LabToTargetSectionCleanPreservation
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.GuestEvmStepOpcodeBounds
open InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds
open InitECandidate.Solver.GuestBlockVsTxHtabBounds
open InitECandidate.Solver.GuestJointBlockGasHtabBound hiding M
open InitECandidate.Solver.GuestDirtyWriteHtabDominance
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope
open InitECandidate.Solver.GuestCoupledTxBlockStorageBound hiding M
open InitECandidate.Solver.GuestSstoreWarmCoeffAudit
open InitECandidate.Solver.GuestSstoreCleanToDirtyTransition
open InitECandidate.Solver.GuestJointTransitionInsertionBound
open InitECandidate.Solver.GuestMergeTxUnionEnvelope
open InitECandidate.Solver.GuestMultiAddressMergeDominance
open InitECandidate.Solver.GuestFiveAddrTablesMergeBound
open InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope
open InitECandidate.Solver.GuestSubBlockTxSplittingDominance
open InitECandidate.Solver.GuestAccessListAndCallStackDominance
open InitECandidate.Solver.GuestStateRestoreCoupledTightening
open InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes
open InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening
  (M coupledCost feasible witness tx_cap dx_le witness_budget witness_feasible
   witness_totals witness_cost six_target no_six_restore witness_le_access
   kPanCoupledRevertTxCap)
open InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope
  (journalFlags dels repeat_no_delete dels_distinct cycleUnits freshUnits
   cycle_units delete_per_unit fresh_per_unit revert_le_tight revert_tight
   strict_drop kPanSixSlopeRestored kPan_val six_slope)
open InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound
  (Frame enter warm truncDels warmN trunc_exact trunc_keeps_parent
   cold_addr_units addr_set_tx addr_set_tx_tight addr_dels_block
   truncTicks addr_trunc_le addr_trunc_tight storage_trunc_in_access
   kPanWarmSets kPanWarmSets_val)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt certificate_lift_non_vacuous_and_tight)
open InitECandidate.Solver.StateRestoreAndAccessCallFortyBudgetMaster
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts
open InitECandidate.Solver.WordSimpPreservesNoStoreConsts
open InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
open InitECandidate.Solver.HtabQuadraticCollisionMax
open InitECandidate.Solver.HtabQuadraticPipelineCert
open InitECandidate.Solver.PurifiedSolverIndex
open InitECandidate.Solver.PurifiedSubmissionBound
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.YukonVerifyScriptAudit
open InitECandidate.Solver.PanToCrepExactClockIso
open InitECandidate.Solver.LoopWordStackExactClockIso
open InitECandidate.Solver.WordToStackClockExactOffset
open InitECandidate.Solver.StackNamesExactClockIso
open InitECandidate.Solver.FourPassClockIsometryChain
open InitECandidate.Solver.StackRemoveClockOriginAudit
open InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
open InitECandidate.Solver.PerTxEip7825TargetMasterK
open InitECandidate.Solver.RiscvBootAndCopyLoopCert
open InitECandidate.Solver.RiscvSszFastRejectAndBootCert
open InitECandidate.Solver.SelfContainedPush31MasterK
open InitECandidate.Solver.SelfContainedSolutionCandidates
open InitECandidate.Solver.SelfContainedAllAxesSynthesis
open InitECandidate.Solver.SelfContainedCompleteCampaignCert
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitECandidate.Solver.ExactKeccakSixPassReducedCert
open InitECandidate.Solver.ExactKeccakCopyLoopUnrolledCert
open InitECandidate.Solver.SelfContainedTenCandidateHierarchy
open InitECandidate.Solver.SelfContainedTwelveTierSynthesis
open InitECandidate.Solver.SelfContainedSsaCseAndBs32Synth
open InitECandidate.Solver.SelfContainedWordSimpAndCoupledSynth
open InitECandidate.Solver.SelfContainedCleanToDirtyAndFullWordSynth
open InitECandidate.Solver.SelfContainedPanToStackAndJointTransitionSynth
open InitECandidate.Solver.SelfContainedStackRemoveNamesAndMultiAddrSynth
open InitECandidate.Solver.SelfContainedUnifiedAllTablesAndStackNamesSynth
open InitECandidate.Solver.SelfContainedSubBlockTxSplittingAndUnifiedSynth
open InitECandidate.Solver.SelfContainedAccessListCallStackAndLabToTargetSynth
open InitECandidate.Solver.SelfContainedStateRestoreAndFortyBudgetSynth
open InitECandidate.Solver.SelfContainedDisjointTablesAndStateRestoreSynth
open InitECandidate.Solver.SelfContainedCoupledRevertTxCapAndDisjointTablesSynth
open InitECandidate.Solver.SelfContainedFortyBudgetPortfolioSynth
  (fourAccessCallTiers fortyAccessCallPortfolio fortyAccessCallClaims allFortyTwoAccessCallBudgets)
open InitECandidate.Solver.DistinctDeleteCycleAndCoupledRevertMaster
open Flapjack
open Flapjack.LoopToWord
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.StackLang

/-! ## Section 1: Four `kPanWarmSets` Target Budgets & 44-Budget Portfolio Definitions -/

/-- Unrolled-`copyLoop` (`9_332`) target ceiling for `kPanWarmSets = 161_763_589_338`
at `3×` slope: `9_332 + 3 * 161_763_589_338 = 485_290_777_346`. -/
def warmSetsSlope3UnrolledK : Nat :=
  (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanWarmSets

/-- Baseline-bootstrap (`23_132`) target ceiling for `kPanWarmSets = 161_763_589_338`
at `3×` slope: `23_132 + 3 * 161_763_589_338 = 485_290_791_146`. -/
def warmSetsSlope3K : Nat :=
  bootstrapSteps + 3 * kPanWarmSets

/-- Unrolled-`copyLoop` (`9_332`) target ceiling for `kPanWarmSets = 161_763_589_338`
at `5×` slope: `9_332 + 5 * 161_763_589_338 = 808_817_956_022`. -/
def warmSetsSlope5UnrolledK : Nat :=
  (bootstrapSteps - copyLoopSavedSteps) + 5 * kPanWarmSets

/-- Baseline-bootstrap (`23_132`) target ceiling for `kPanWarmSets = 161_763_589_338`
at `5×` slope: `23_132 + 5 * 161_763_589_338 = 808_817_969_822`. -/
def warmSetsSlope5K : Nat :=
  bootstrapSteps + 5 * kPanWarmSets

/-- The 4 `kPanWarmSets` target budgets at slopes `3×` and `5×` (unrolled and baseline). -/
def fourWarmSetsTiers : List Nat := [
  warmSetsSlope3UnrolledK,
  warmSetsSlope3K,
  warmSetsSlope5UnrolledK,
  warmSetsSlope5K
]

/-- The 4 tighter (-100 tick) warm-sets candidate tiers (`485_290_777_246`, `485_290_791_046`,
`808_817_955_922`, `808_817_969_722`). -/
def fourWarmSetsTightTiers : List Nat := [
  485_290_777_246,
  485_290_791_046,
  808_817_955_922,
  808_817_969_722
]

/-- Explicit 44-budget strictly increasing portfolio uniting the 40 budgets of
`coupledRevertFortyBudgetPortfolio` (`fortyAccessCallPortfolio`) with the 4 `kPanWarmSets`
tiers (`485_290_777_346`, `485_290_791_146`, `808_817_956_022`, `808_817_969_822`). -/
def fortyFourWarmSetsPortfolio : List Nat := [
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
  485_290_777_346,
  485_290_791_146,
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
  808_817_956_022,
  808_817_969_822,
  810_291_208_508,
  816_696_823_280,
  816_696_837_080,
  857_384_015_252
]

/-- `claim.json` payloads paired with each of the 44 budgets in `fortyFourWarmSetsPortfolio`. -/
def fortyFourWarmSetsClaims : List (Nat × String) := [
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
  (485_290_777_346, verifierClaimJson "485290777346"),
  (485_290_791_146, verifierClaimJson "485290791146"),
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
  (808_817_956_022, verifierClaimJson "808817956022"),
  (808_817_969_822, verifierClaimJson "808817969822"),
  (810_291_208_508, verifierClaimJson "810291208508"),
  (816_696_823_280, verifierClaimJson "816696823280"),
  (816_696_837_080, verifierClaimJson "816696837080"),
  (857_384_015_252, verifierClaimJson "857384015252")
]

/-- Sorted 46-budget grand superset uniting `allFortyTwoAccessCallBudgets` (`42` budgets) with the
4 `kPanWarmSets` tiers (`fourWarmSetsTiers`). -/
def allFortySixWarmSetsBudgets : List Nat := [
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
  485_290_777_346,
  485_290_791_146,
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
  808_817_956_022,
  808_817_969_822,
  810_291_208_508,
  816_696_823_280,
  816_696_837_080,
  857_384_015_252
]

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`, **Complete Closure of `GuestWarmAccessSetAndRollbackBound` (`11/11` tight): 10th & 11th Tables `ev+168` / `ev+176` & `kPanWarmSets = 161_763_589_338`**):
Unites all 11 theorems of `GuestWarmAccessSetAndRollbackBound`:
- `trunc_exact` (`truncDels (warmN (enter n) k) = k`) and `trunc_keeps_parent`
  (`(warmN (enter n) k).size - truncDels (warmN (enter n) k) = n`),
- `cold_addr_units` (`3000 = 30 * 100 ∧ 26 ≤ 30`),
- `addr_set_tx` (`a + 19 ≤ 5611` when `30 * a ≤ 167772`) and `addr_set_tx_tight` (`30 * 5592 ≤ 167772 ∧ 167772 < 30 * 5593`),
- `addr_dels_block` (`n ≤ 66666` when `30 * n ≤ 2000000`),
- `addr_trunc_le` (`truncTicks a_c n_c ≤ 1870314630` for `a_c ≤ 5611`, `n_c ≤ 66666`) and
  `addr_trunc_tight` (`truncTicks 5611 66666 = 1870314630`),
- `storage_trunc_in_access` (`kPanAccessCall = 136116135658 + 19972857140 + 3804281910`),
- `kPanWarmSets_val` (`kPanWarmSets = 161763589338`), and
- `slopes` (`5 * kPanWarmSets < yukon ∧ yukon - 5 * kPanWarmSets = 91901978784 ∧ yukon < 6 * kPanWarmSets`). -/
theorem guest_warm_access_set_and_rollback_bound_complete_audit_non_vacuous_and_tight
    (n_f k_f a n a_c n_c : Nat)
    (ha_tx : 30 * a ≤ 167772) (hn_blk : 30 * n ≤ 2000000)
    (ha_c : a_c ≤ 5611) (hn_c : n_c ≤ 66666) :
    truncDels (warmN (enter n_f) k_f) = k_f ∧
    (warmN (enter n_f) k_f).size - truncDels (warmN (enter n_f) k_f) = n_f ∧
    (3000 = 30 * 100 ∧ 26 ≤ 30) ∧
    a + 19 ≤ 5611 ∧
    (30 * 5592 ≤ 167772 ∧ 167772 < 30 * 5593) ∧
    n ≤ 66666 ∧
    truncTicks a_c n_c ≤ 1870314630 ∧
    truncTicks 5611 66666 = 1870314630 ∧
    kPanAccessCall = 136116135658 + 19972857140 + 3804281910 ∧
    kPanWarmSets = 161763589338 ∧
    (5 * kPanWarmSets < yukon ∧ yukon - 5 * kPanWarmSets = 91901978784 ∧ yukon < 6 * kPanWarmSets) :=
  ⟨trunc_exact n_f k_f,
   trunc_keeps_parent n_f k_f,
   cold_addr_units,
   addr_set_tx a ha_tx,
   addr_set_tx_tight,
   addr_dels_block n hn_blk,
   addr_trunc_le a_c n_c ha_c hn_c,
   addr_trunc_tight,
   storage_trunc_in_access,
   kPanWarmSets_val,
   GuestWarmAccessSetAndRollbackBound.slopes⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **Coupled Synthesis of `DistinctDeleteCycleAndCoupledRevertMaster` (`15/15` tight) with `GuestWarmAccessSetAndRollbackBound` (`ev+168` / `ev+176`)**):
Couples `DistinctDeleteCycleAndCoupledRevertMaster.integrated_master_non_vacuous_and_tight`
(`repeat_no_delete_non_vacuous_and_tight`, `dels_distinct_non_vacuous_and_tight`,
`cycle_units_non_vacuous_and_tight`, `revert_le_tight_non_vacuous_and_tight`,
`conditional_six_slope_non_vacuous_and_tight`, `unconditional_five_slope_non_vacuous_and_tight`,
`tx_dirty_cap_non_vacuous_and_tight`, `disjoint_partition_non_vacuous_and_tight`,
`no_six_restore_non_vacuous_and_tight`, `panToTarget_sections_clean_non_vacuous_and_tight`,
`panToTarget_sections_length_non_vacuous_and_tight`, `forty_certified_non_vacuous_and_tight`,
`submission_certificate_non_vacuous_and_tight`, `self_contained_alignment_non_vacuous_and_tight`)
directly with the 10th and 11th tables (`ev+168` and `ev+176`) envelope `kPanWarmSets = 161_763_589_338`. -/
theorem distinct_delete_cycle_coupled_revert_and_warm_sets_master_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (cert : CertificateAt 1212035192)
    (db dx D W d_t w_t : Nat) (hpart : db + dx ≤ D)
    (hpaid : 21 * D + W ≤ S) (htx : 21 * d_t + w_t ≤ M)
    (d p q w : Nat) (H2 : p + cycleUnits * q ≤ w)
    (a_c n_c : Nat) (ha_c : a_c ≤ 5611) (hn_c : n_c ≤ 66666) :
    ((journalFlags [] [d_t, d_t] = [false, true] ∧
      dels [] [1, 1, 1, 2, 2] = 2 ∧ dels [1] [1, 1] = 0) ∧
     (100 + 100 = cycleUnits * 100 ∧ 19 * 100 + 100 = freshUnits * 100) ∧
     (8 * d * p + 13 * d * q ≤ 8 * d * w ∧
      kPanSixSlopeRestored = 139920417568 ∧
      kPanAccessCall - kPanSixSlopeRestored = 19972857140 ∧
      6 * kPanSixSlopeRestored < yukon ∧
      yukon - 6 * kPanSixSlopeRestored = 61197420066 ∧
      yukon < 7 * kPanSixSlopeRestored) ∧
     (kPanAccessCall = 159893274708 ∧
      5 * kPanAccessCall < yukon ∧ yukon < 6 * kPanAccessCall ∧
      kPanDisjointTables = kPanAccessCall) ∧
     (d_t ≤ 7989 ∧ 21 * 7989 ≤ M ∧ M < 21 * 7990) ∧
     (21 * (db + dx) + W ≤ S ∧
      cycleTicks db dx ≤ 13 * (db + dx) ∧ cycleTicks db dx ≤ 13 * D ∧
      cycleTicks 0 D = 13 * D ∧ cycleTicks D 0 = 2 * D ∧
      cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1)) ∧
     (feasible witness ∧ coupledCost witness = 155688931265 ∧
      yukon < 6 * coupledCost witness ∧
      ∃ l, feasible l ∧ yukon < 6 * coupledCost l) ∧
     (kPanCoupledRevertTxCap = 159893274708 ∧
      kPanCoupledRevertTxCap = kPanDisjointTables ∧
      kPanCoupledRevertTxCap = kPanStateRestoreCoupled ∧
      coupledCost witness ≤ kPanCoupledRevertTxCap ∧
      5 * kPanCoupledRevertTxCap < yukon ∧ yukon < 6 * kPanCoupledRevertTxCap) ∧
     (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
      ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
        ∃ s ∈ StackToLab.compile sc dc mh sp off
            (compileNative ac perf (WordToWord.compile wc ac
              (panToWordCompileProgHOL arch prog)).2).2.2.2,
          s.sectionId = s'.sectionId ∧ CleanSection s) ∧
     (DistinctDeleteCycleAndCoupledRevertMaster.portfolio.length = 40 ∧
      DistinctDeleteCycleAndCoupledRevertMaster.portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ DistinctDeleteCycleAndCoupledRevertMaster.portfolio, K < 900719925474 ∧
        ∃ submission : InitE.Submission, submission = baselineWithFiniteK K ∧
          InitE.Certificate submission (.finite K))) ∧
    L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
    8 * d * w + 13 * d * 0 = 8 * d * w ∧
    truncTicks a_c n_c ≤ 1870314630 ∧
    kPanAccessCall + truncTicks a_c n_c ≤ kPanWarmSets ∧
    kPanWarmSets - kPanAccessCall = 1870314630 ∧
    kPanWarmSets - kPanSixSlopeRestored = 21843171770 ∧
    (5 * kPanWarmSets < yukon ∧ yukon - 5 * kPanWarmSets = 91901978784 ∧ yukon < 6 * kPanWarmSets) := by
  have hint := DistinctDeleteCycleAndCoupledRevertMaster.integrated_master_non_vacuous_and_tight
    arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h cert
    db dx D W d_t w_t hpart hpaid htx d p q w H2
  have hlen := DistinctDeleteCycleAndCoupledRevertMaster.panToTarget_sections_length_non_vacuous_and_tight
    arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h
  have htr := addr_trunc_le a_c n_c ha_c hn_c
  have hsum : kPanAccessCall + truncTicks a_c n_c ≤ kPanWarmSets := by
    unfold kPanWarmSets; omega
  exact ⟨hint, hlen, revert_tight d w, htr, hsum, by decide, by decide,
    GuestWarmAccessSetAndRollbackBound.slopes⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Exact Numerical Evaluation of the `kPanWarmSets` Target Tiers (`485_290_777_346`, `485_290_791_146`, `808_817_956_022`, `808_817_969_822` & Tight `-100` Variants `485_290_777_246`, `485_290_791_046`, `808_817_955_922`, `808_817_969_722`) & Gaps over `kPanAccessCall` / `kPanUnifiedAllTables`**):
Proves exact numerical values for `warmSetsSlope3UnrolledK`, `warmSetsSlope3K`,
`warmSetsSlope5UnrolledK`, `warmSetsSlope5K` and their `-100` counterparts, exact `13_800`-step
unrolled `copyLoop` savings, exact `ev+168` truncation increments (`3 * 1_870_314_630 = 5_610_943_890`
at `3×` and `5 * 1_870_314_630 = 9_351_573_150` at `5×`), 1-tick tightness boundaries, and slope threshold `slope ≤ 5`. -/
theorem warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight
    (k minutes slope : Nat) :
    warmSetsSlope3UnrolledK = 485_290_777_346 ∧
    warmSetsSlope3K = 485_290_791_146 ∧
    warmSetsSlope5UnrolledK = 808_817_956_022 ∧
    warmSetsSlope5K = 808_817_969_822 ∧
    warmSetsSlope3UnrolledK - 100 = 485_290_777_246 ∧
    warmSetsSlope3K - 100 = 485_290_791_046 ∧
    warmSetsSlope5UnrolledK - 100 = 808_817_955_922 ∧
    warmSetsSlope5K - 100 = 808_817_969_722 ∧
    kPanWarmSets - kPanCoupledRevertTxCap = 1_870_314_630 ∧
    kPanWarmSets - kPanUnifiedAllTables = 25_647_453_680 ∧
    warmSetsSlope3UnrolledK - coupledRevertTxCapSlope3UnrolledK = 5_610_943_890 ∧
    warmSetsSlope3K - coupledRevertTxCapSlope3K = 5_610_943_890 ∧
    warmSetsSlope5UnrolledK - coupledRevertTxCapSlope5UnrolledK = 9_351_573_150 ∧
    warmSetsSlope5K - coupledRevertTxCapSlope5K = 9_351_573_150 ∧
    warmSetsSlope3K - warmSetsSlope3UnrolledK = 13_800 ∧
    warmSetsSlope5K - warmSetsSlope5UnrolledK = 13_800 ∧
    900_719_925_474 - warmSetsSlope5K = 91_901_955_652 ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanWarmSets ≤ warmSetsSlope3UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 3 * kPanWarmSets ≤ warmSetsSlope3K - 1) ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 5 * kPanWarmSets ≤ warmSetsSlope5UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 5 * kPanWarmSets ≤ warmSetsSlope5K - 1) ∧
    (warmSetsSlope3K ≤ k + copyLoopSavedSteps ↔ warmSetsSlope3UnrolledK ≤ k) ∧
    (warmSetsSlope5K ≤ k + copyLoopSavedSteps ↔ warmSetsSlope5UnrolledK ≤ k) ∧
    yukonScore warmSetsSlope3K minutes - yukonScore warmSetsSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore warmSetsSlope5K minutes - yukonScore warmSetsSlope5UnrolledK minutes = 138_000_000 ∧
    (bootstrapSteps + slope * kPanWarmSets < 900_719_925_474 ↔ slope ≤ 5) := by
  have hb : bootstrapSteps = 23_132 := bootstrapSteps_eq
  have hcl : copyLoopSavedSteps = 13_800 := copy_loop_saved_exact
  have hub : bootstrapSteps - copyLoopSavedSteps = 9_332 := by rw [hb, hcl]
  have hkw : kPanWarmSets = 161_763_589_338 := kPanWarmSets_val
  have hkc : kPanCoupledRevertTxCap = 159_893_274_708 := rfl
  have hku : kPanUnifiedAllTables = 136_116_135_658 := kPanUnified_val.1
  have hcr := coupled_revert_tx_cap_and_disjoint_tables_target_tiers_coincide_non_vacuous_and_tight 0 0
  have hw3u : warmSetsSlope3UnrolledK = 485_290_777_346 := by
    unfold warmSetsSlope3UnrolledK; rw [hub, hkw]
  have hw3 : warmSetsSlope3K = 485_290_791_146 := by
    unfold warmSetsSlope3K; rw [hb, hkw]
  have hw5u : warmSetsSlope5UnrolledK = 808_817_956_022 := by
    unfold warmSetsSlope5UnrolledK; rw [hub, hkw]
  have hw5 : warmSetsSlope5K = 808_817_969_822 := by
    unfold warmSetsSlope5K; rw [hb, hkw]
  have hcr3u : coupledRevertTxCapSlope3UnrolledK = 479_679_833_456 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcr3 : coupledRevertTxCapSlope3K = 479_679_847_256 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcr5u : coupledRevertTxCapSlope5UnrolledK = 799_466_382_872 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcr5 : coupledRevertTxCapSlope5K = 799_466_396_672 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hcr
  rw [hw3u, hw3, hw5u, hw5, hcr3u, hcr3, hcr5u, hcr5, hb, hcl, hkw, hkc, hku]
  unfold yukonScore
  omega

/-- Theorem 4 (`non_vacuous_and_tight`, **44-Budget Portfolio Exact Insertion (`fortyFourWarmSetsPortfolio`), Strict Ordering & 46-Budget Grand Superset (`allFortySixWarmSetsBudgets`)**):
Proves that inserting the 4 `kPanWarmSets` target tiers (`fourWarmSetsTiers`:
`485_290_777_346`, `485_290_791_146`, `808_817_956_022`, `808_817_969_822`) into the 40-budget
portfolio `coupledRevertFortyBudgetPortfolio` (`= fortyAccessCallPortfolio = DistinctDeleteCycleAndCoupledRevertMaster.portfolio`)
produces the strictly ordered **44-budget** portfolio `fortyFourWarmSetsPortfolio` under the Yukon ceiling
`900_719_925_474`, and into `allFortyTwoAccessCallBudgets` produces the **46-budget** grand superset
`allFortySixWarmSetsBudgets`. -/
theorem forty_four_warm_sets_portfolio_exact_insertion_and_order_non_vacuous_and_tight (K : Nat) :
    fortyFourWarmSetsPortfolio.length = 44 ∧
    fortyFourWarmSetsPortfolio.Pairwise (· < ·) ∧
    (coupledRevertFortyBudgetPortfolio ++ fourWarmSetsTiers).insertionSort (· ≤ ·) =
      fortyFourWarmSetsPortfolio ∧
    (DistinctDeleteCycleAndCoupledRevertMaster.portfolio ++ fourWarmSetsTiers).insertionSort (· ≤ ·) =
      fortyFourWarmSetsPortfolio ∧
    (∀ k ∈ coupledRevertFortyBudgetPortfolio, k ∈ fortyFourWarmSetsPortfolio) ∧
    (∀ k ∈ DistinctDeleteCycleAndCoupledRevertMaster.portfolio, k ∈ fortyFourWarmSetsPortfolio) ∧
    (∀ k ∈ fourWarmSetsTiers, k ∈ fortyFourWarmSetsPortfolio) ∧
    (∀ k ∈ fortyFourWarmSetsPortfolio,
      1_212_035_192 ≤ k ∧ k ≤ 857_384_015_252 ∧ k < 900_719_925_474 ∧ ¬ k ≤ k - 1) ∧
    allFortySixWarmSetsBudgets.length = 46 ∧
    allFortySixWarmSetsBudgets.Pairwise (· < ·) ∧
    (allFortyTwoAccessCallBudgets ++ fourWarmSetsTiers).insertionSort (· ≤ ·) =
      allFortySixWarmSetsBudgets ∧
    (∀ k ∈ fortyFourWarmSetsPortfolio, k ∈ allFortySixWarmSetsBudgets) ∧
    (∀ k ∈ allFortyTwoAccessCallBudgets, k ∈ allFortySixWarmSetsBudgets) ∧
    (warmSetsSlope5K ≤ K ↔ 808_817_969_822 ≤ K) := by
  have hw := warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight 0 0 0
  have hfwt : fourWarmSetsTiers = [485_290_777_346, 485_290_791_146, 808_817_956_022, 808_817_969_822] := by
    unfold fourWarmSetsTiers
    rw [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1]
  have hw5 : warmSetsSlope5K = 808_817_969_822 := hw.2.2.2.1
  have hsort1 : (coupledRevertFortyBudgetPortfolio ++ fourWarmSetsTiers).insertionSort (· ≤ ·) =
      fortyFourWarmSetsPortfolio := by
    rw [hfwt]; decide
  have hsort2 : (DistinctDeleteCycleAndCoupledRevertMaster.portfolio ++ fourWarmSetsTiers).insertionSort (· ≤ ·) =
      fortyFourWarmSetsPortfolio := by
    rw [hfwt]; decide
  have hsort46 : (allFortyTwoAccessCallBudgets ++ fourWarmSetsTiers).insertionSort (· ≤ ·) =
      allFortySixWarmSetsBudgets := by
    rw [hfwt]; decide
  have hmem4 : ∀ k ∈ fourWarmSetsTiers, k ∈ fortyFourWarmSetsPortfolio := by
    rw [hfwt]; decide
  refine ⟨by decide, by decide, hsort1, hsort2, by decide, by decide, hmem4,
    by decide, by decide, by decide, hsort46, by decide, by decide, ?_⟩
  rw [hw5]

/-- Theorem 5 (`non_vacuous_and_tight`, **Interleaved Strict Ordering of the `kPanWarmSets` Tiers & Tight `-100` Variants within the 44-Budget Portfolio**):
Proves that the new `kPanWarmSets` budgets sit in strict interleaved order between existing tiers:
`459_244_490_549 < coupledRevertTxCapSlope3UnrolledK (479_679_833_456) < coupledRevertTxCapSlope3K (479_679_847_256) < 485_290_777_246 < warmSetsSlope3UnrolledK (485_290_777_346) < 485_290_791_046 < warmSetsSlope3K (485_290_791_146) < 485_837_754_632`
and
`coupledSlope6K (785_125_408_508) < coupledRevertTxCapSlope5UnrolledK (799_466_382_872) < coupledRevertTxCapSlope5K (799_466_396_672) < 808_817_955_922 < warmSetsSlope5UnrolledK (808_817_956_022) < 808_817_969_722 < warmSetsSlope5K (808_817_969_822) < transitionSlope6UnrolledK (810_291_208_508)`. -/
theorem warm_sets_tiers_interleaved_strict_ordering_non_vacuous_and_tight (K : Nat) :
    459_244_490_549 < coupledRevertTxCapSlope3UnrolledK ∧
    coupledRevertTxCapSlope3UnrolledK < coupledRevertTxCapSlope3K ∧
    coupledRevertTxCapSlope3K < 485_290_777_246 ∧
    485_290_777_246 < warmSetsSlope3UnrolledK ∧
    warmSetsSlope3UnrolledK < 485_290_791_046 ∧
    485_290_791_046 < warmSetsSlope3K ∧
    warmSetsSlope3K < 485_837_754_632 ∧
    485_837_754_632 < 500_060_306_876 ∧
    coupledSlope6K < coupledRevertTxCapSlope5UnrolledK ∧
    coupledRevertTxCapSlope5UnrolledK < coupledRevertTxCapSlope5K ∧
    coupledRevertTxCapSlope5K < 808_817_955_922 ∧
    808_817_955_922 < warmSetsSlope5UnrolledK ∧
    warmSetsSlope5UnrolledK < 808_817_969_722 ∧
    808_817_969_722 < warmSetsSlope5K ∧
    warmSetsSlope5K < transitionSlope6UnrolledK ∧
    transitionSlope6UnrolledK < 816_696_823_280 ∧
    816_696_823_280 < 816_696_837_080 ∧
    816_696_837_080 < 857_384_015_252 ∧
    857_384_015_252 < 900_719_925_474 ∧
    (warmSetsSlope3K ≤ K ↔ 485_290_791_146 ≤ K) := by
  have hw := warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight 0 0 0
  have hcr := coupled_revert_tx_cap_and_disjoint_tables_target_tiers_coincide_non_vacuous_and_tight 0 0
  have hcr3u : coupledRevertTxCapSlope3UnrolledK = 479_679_833_456 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcr3 : coupledRevertTxCapSlope3K = 479_679_847_256 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcr5u : coupledRevertTxCapSlope5UnrolledK = 799_466_382_872 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcr5 : coupledRevertTxCapSlope5K = 799_466_396_672 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hcr3u, hcr3, hcr5u, hcr5]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, Iff.rfl⟩

/-- Theorem 6 (`non_vacuous_and_tight`, **Eleven-Table Sub-Block Split-Revert & Warm-Set Truncation Envelope (`ev+168` + `ev+176` + 9 `bs+*`/`ts+*` Tables) Bounded by `kPanWarmSets`**):
Unites the 9-table sub-block multi-tx split envelope, `ts+32` call-stack journal revert (`revertCost r`),
`ev+176` storage warm-set truncation (`5 * c * n ≤ 3_804_281_910`), and `ev+168` address warm-set
truncation (`truncTicks a_c n_c ≤ 1_870_314_630`) under `kPanWarmSets = 161_763_589_338`, together with
the 4 target budget inequalities (`warmSetsSlope3UnrolledK`, `warmSetsSlope3K`, `warmSetsSlope5UnrolledK`,
`warmSetsSlope5K`), per-tx EIP-7825 dirty cap `d_t ≤ 7_989`, and per-tx `ev+168` size cap `a + 19 ≤ 5_611`. -/
theorem eleven_table_split_revert_and_warm_sets_truncation_envelope_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat)) (r : List (Nat × Nat))
    (T Tloc Tlin c n a_c n_c d_t w_t a n_blk : Nat)
    (htx : 21 * d_t + w_t ≤ M)
    (ha_tx : 30 * a ≤ 167772) (hn_blk : 30 * n_blk ≤ 2000000)
    (budget : 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ S)
    (ht : txMinUnits * T ≤ 2000000) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hr : (r.map (fun p => p.1 * p.2)).sum ≤ 3994571428)
    (hc : c ≤ 7989) (hn : n ≤ 95238)
    (ha_c : a_c ≤ 5611) (hn_c : n_c ≤ 66666) :
    d_t ≤ 7989 ∧
    a + 19 ≤ 5611 ∧
    n_blk ≤ 66666 ∧
    coupledCost witness = 155688931265 ∧
    (∃ lw, feasible lw ∧ yukon < 6 * coupledCost lw) ∧
    (let cost10 := linear + Tloc + ((l.map localCost).sum + 41935 * sR l) + Tlin +
        revertCost r + 5 * c * n
     let cost11 := cost10 + truncTicks a_c n_c
     cost10 ≤ kPanCoupledRevertTxCap ∧
     truncTicks a_c n_c ≤ 1870314630 ∧
     cost11 ≤ kPanWarmSets ∧
     9332 + 3 * cost11 ≤ warmSetsSlope3UnrolledK ∧
     23132 + 3 * cost11 ≤ warmSetsSlope3K ∧
     9332 + 5 * cost11 ≤ warmSetsSlope5UnrolledK ∧
     23132 + 5 * cost11 ≤ warmSetsSlope5K ∧
     warmSetsSlope5K < yukon ∧
     txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) := by
  have h40 := forty_budget_master_portfolio_unification_and_split_revert_envelope_non_vacuous_and_tight
    l r T Tloc Tlin c n d_t w_t htx budget ht hloc hlin hr hc hn
  have htr := addr_trunc_le a_c n_c ha_c hn_c
  have hw := warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight 0 0 0
  have hc10 := h40.2.2.2.2.2.2.2.2.2.2.1
  have hreset := h40.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hT_le := h40.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk_eq : kPanCoupledRevertTxCap = kPanAccessCall := rfl
  refine ⟨h40.1, addr_set_tx a ha_tx, addr_dels_block n_blk hn_blk, h40.2.1, h40.2.2.1, ?_⟩
  dsimp only
  rw [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1]
  have hc11 : linear + Tloc + ((l.map localCost).sum + 41935 * sR l) + Tlin +
      revertCost r + 5 * c * n + truncTicks a_c n_c ≤ kPanWarmSets := by
    unfold kPanWarmSets; omega
  have h_yuk : 808_817_969_822 < yukon := by decide
  have h_wVal : kPanWarmSets = 161_763_589_338 := kPanWarmSets_val
  refine ⟨hc10, htr, hc11, by omega, by omega, by omega, by omega, h_yuk, hreset, hT_le⟩

/-- Theorem 7 (`non_vacuous_and_tight`, **Strict `yukonScore` Monotonicity & IEEE-754 `float64` Exactness (`< 2^53 - 1`) across all 44 Budgets of `fortyFourWarmSetsPortfolio`**):
Proves that `(fortyFourWarmSetsPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·)` holds
for every runtime `minutes`, every budget in `fortyFourWarmSetsPortfolio` satisfies
`yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes < 2^53 - 1`,
and the `kPanWarmSets` tiers sit in strict `yukonScore` order between their neighbours. -/
theorem forty_four_warm_sets_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight
    (minutes K : Nat) :
    (fortyFourWarmSetsPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ k1 ∈ fortyFourWarmSetsPortfolio,
      ∀ k2 ∈ fortyFourWarmSetsPortfolio,
        k1 < k2 ↔ yukonScore k1 minutes < yukonScore k2 minutes) ∧
    (∀ k ∈ fortyFourWarmSetsPortfolio,
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    yukonScore coupledRevertTxCapSlope3K minutes < yukonScore warmSetsSlope3UnrolledK minutes ∧
    yukonScore warmSetsSlope3UnrolledK minutes < yukonScore warmSetsSlope3K minutes ∧
    yukonScore warmSetsSlope3K minutes < yukonScore 485_837_754_632 minutes ∧
    yukonScore coupledRevertTxCapSlope5K minutes < yukonScore warmSetsSlope5UnrolledK minutes ∧
    yukonScore warmSetsSlope5UnrolledK minutes < yukonScore warmSetsSlope5K minutes ∧
    yukonScore warmSetsSlope5K minutes < yukonScore transitionSlope6UnrolledK minutes ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hord : fortyFourWarmSetsPortfolio.Pairwise (· < ·) :=
    (forty_four_warm_sets_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0).2.1
  have h_mono : ∀ {a b : Nat}, a < b → yukonScore a minutes < yukonScore b minutes := by
    intro a b hab; unfold yukonScore; omega
  have hmap_pw : (fortyFourWarmSetsPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp h_mono hord
  have h40_sc := SelfContainedFortyBudgetPortfolioSynth.forty_access_call_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes K
  have hterm_lt : yukonScore 857_384_015_252 minutes < 2 ^ 53 - 1 :=
    (h40_sc.2.2.1 857_384_015_252 (by decide)).2.2
  have hint := warm_sets_tiers_interleaved_strict_ordering_non_vacuous_and_tight 0
  have hlt1 : coupledRevertTxCapSlope3K < warmSetsSlope3UnrolledK :=
    Nat.lt_trans hint.2.2.1 hint.2.2.2.1
  have hlt2 : warmSetsSlope3UnrolledK < warmSetsSlope3K :=
    Nat.lt_trans hint.2.2.2.2.1 hint.2.2.2.2.2.1
  have hlt3 : warmSetsSlope3K < 485_837_754_632 :=
    hint.2.2.2.2.2.2.1
  have hlt4 : coupledRevertTxCapSlope5K < warmSetsSlope5UnrolledK :=
    Nat.lt_trans hint.2.2.2.2.2.2.2.2.2.2.1 hint.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt5 : warmSetsSlope5UnrolledK < warmSetsSlope5K :=
    Nat.lt_trans hint.2.2.2.2.2.2.2.2.2.2.2.2.1 hint.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt6 : warmSetsSlope5K < transitionSlope6UnrolledK :=
    hint.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hmap_pw, ?_, ?_,
    h_mono hlt1,
    h_mono hlt2,
    h_mono hlt3,
    h_mono hlt4,
    h_mono hlt5,
    h_mono hlt6,
    h40_sc.2.2.2.2.2.2.2.2.2⟩
  · intro k1 _ k2 _
    unfold yukonScore; omega
  · intro k hk
    have hbnd := (forty_four_warm_sets_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0).2.2.2.2.2.2.2.1 k hk
    have h1 : yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes := by
      unfold yukonScore; omega
    have h2 : yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes := by
      unfold yukonScore; omega
    exact ⟨h1, h2, Nat.lt_of_le_of_lt h2 hterm_lt⟩

/-- Theorem 8 (`non_vacuous_and_tight`, **All 44 Budgets in `fortyFourWarmSetsPortfolio` Possess Valid `claim.json ≤ 128` Byte Payloads (`fortyFourWarmSetsClaims`)**):
Proves that every one of the 44 `(K, json)` pairs in `fortyFourWarmSetsClaims` satisfies
`json.utf8ByteSize ≤ 128` and `validFiniteClaim K json = true`, including explicit verification
of the `kPanWarmSets` claims (`485290777346`, `485290791146`, `808817956022`, `808817969822`, and
`485290777246`, `485290791046`, `808817955922`, `808817969722`). -/
theorem forty_four_warm_sets_claims_valid_and_within_128_bytes_non_vacuous_and_tight (K : Nat) :
    fortyFourWarmSetsClaims.length = 44 ∧
    fortyFourWarmSetsClaims.map Prod.fst = fortyFourWarmSetsPortfolio ∧
    (∀ entry ∈ fortyFourWarmSetsClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (verifierClaimJson "485290777346").utf8ByteSize ≤ 128 ∧
    validFiniteClaim warmSetsSlope3UnrolledK (verifierClaimJson "485290777346") = true ∧
    (verifierClaimJson "485290791146").utf8ByteSize ≤ 128 ∧
    validFiniteClaim warmSetsSlope3K (verifierClaimJson "485290791146") = true ∧
    (verifierClaimJson "808817956022").utf8ByteSize ≤ 128 ∧
    validFiniteClaim warmSetsSlope5UnrolledK (verifierClaimJson "808817956022") = true ∧
    (verifierClaimJson "808817969822").utf8ByteSize ≤ 128 ∧
    validFiniteClaim warmSetsSlope5K (verifierClaimJson "808817969822") = true ∧
    validFiniteClaim 485_290_777_246 (verifierClaimJson "485290777246") = true ∧
    validFiniteClaim 485_290_791_046 (verifierClaimJson "485290791046") = true ∧
    validFiniteClaim 808_817_955_922 (verifierClaimJson "808817955922") = true ∧
    validFiniteClaim 808_817_969_722 (verifierClaimJson "808817969722") = true ∧
    (validFiniteClaim K (verifierClaimJson "808817969822") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) := by
  have hw := warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight 0 0 0
  have hlen : decide ((verifierClaimJson "808817969822").utf8ByteSize ≤ MAX_CLAIM_BYTES) = true := by decide
  rw [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1]
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  unfold validFiniteClaim
  rw [hlen, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- Theorem 9 (`non_vacuous_and_tight`, **Direct Target Non-`.timeOut` to 44-Budget, 46-Budget & 30-Tier `InitE.Certificate submission (.finite K)` Bridge**):
Proves that uniform target non-`.timeOut` at `exactKeccak128UnrolledK = 1_212_035_192` yields
`CertificateAt 1_212_035_192`, which simultaneously certifies:
- Every `K ∈ fortyFourWarmSetsPortfolio` (`44` budgets) with an explicit concrete
  `submission = baselineWithFiniteK K` satisfying `K < 900_719_925_474 ∧ InitE.Certificate submission (.finite K)`,
- Every `K ∈ fourWarmSetsTightTiers` (`485_290_777_246`, `485_290_791_046`, `808_817_955_922`, `808_817_969_722`),
- Every `K ∈ allFortySixWarmSetsBudgets` (`46` budgets),
- Every `K ∈ coupledRevertFortyBudgetPortfolio` (`40` budgets) and `thirtyTierHierarchy` (`30` tiers),
- All 4 `warmSetsSlope*` target ceilings, all 4 `coupledRevertTxCapSlope*` ceilings, and `.infinity`. -/
theorem warm_sets_forty_four_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_u128 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    CertificateAt 1212035192 ∧
    (fortyFourWarmSetsPortfolio.length = 44 ∧
     fortyFourWarmSetsPortfolio.Pairwise (· < ·) ∧
     ∀ K ∈ fortyFourWarmSetsPortfolio, K < 900_719_925_474 ∧
       ∃ submission : InitE.Submission,
         submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (∀ K ∈ fourWarmSetsTightTiers, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (allFortySixWarmSetsBudgets.length = 46 ∧
     allFortySixWarmSetsBudgets.Pairwise (· < ·) ∧
     ∀ K ∈ allFortySixWarmSetsBudgets, K < 900_719_925_474 ∧
       InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (∀ K ∈ coupledRevertFortyBudgetPortfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (∀ K ∈ thirtyTierHierarchy, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope3UnrolledK) (.finite warmSetsSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope3K) (.finite warmSetsSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope5UnrolledK) (.finite warmSetsSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope5K) (.finite warmSetsSlope5K) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope3UnrolledK) (.finite coupledRevertTxCapSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope3K) (.finite coupledRevertTxCapSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope5UnrolledK) (.finite coupledRevertTxCapSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope5K) (.finite coupledRevertTxCapSlope5K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity := by
  have hcert7 := coupled_revert_tx_cap_forty_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_u128
  have hc1212 : CertificateAt 1212035192 := hcert7.1
  have hord44 := forty_four_warm_sets_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0
  have h44_cert : ∀ K ∈ fortyFourWarmSetsPortfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K) := by
    intro K hK
    have hbnd := hord44.2.2.2.2.2.2.2.1 K hK
    exact ⟨hbnd.2.2.1, baselineWithFiniteK K, rfl,
      certificate_lift_non_vacuous_and_tight _ K hbnd.1 hc1212⟩
  have h4_tight_cert : ∀ K ∈ fourWarmSetsTightTiers, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K) := by
    intro K hK
    have hbnd : ∀ x ∈ fourWarmSetsTightTiers, 1212035192 ≤ x ∧ x < 900_719_925_474 := by decide
    have hb := hbnd K hK
    exact ⟨hb.2, baselineWithFiniteK K, rfl,
      certificate_lift_non_vacuous_and_tight _ K hb.1 hc1212⟩
  have h46_cert : ∀ K ∈ allFortySixWarmSetsBudgets, K < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
    intro K hK
    have h46_le : ∀ x ∈ allFortySixWarmSetsBudgets, 1212035192 ≤ x ∧ x < 900_719_925_474 := by decide
    have hb := h46_le K hK
    exact ⟨hb.2, certificate_lift_non_vacuous_and_tight _ K hb.1 hc1212⟩
  have hw := warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight 0 0 0
  have hw3u_le : 1212035192 ≤ warmSetsSlope3UnrolledK := by rw [hw.1]; decide
  have hw3_le : 1212035192 ≤ warmSetsSlope3K := by rw [hw.2.1]; decide
  have hw5u_le : 1212035192 ≤ warmSetsSlope5UnrolledK := by rw [hw.2.2.1]; decide
  have hw5_le : 1212035192 ≤ warmSetsSlope5K := by rw [hw.2.2.2.1]; decide
  exact ⟨hc1212,
    ⟨hord44.1, hord44.2.1, h44_cert⟩,
    h4_tight_cert,
    ⟨hord44.2.2.2.2.2.2.2.2.1, hord44.2.2.2.2.2.2.2.2.2.1, h46_cert⟩,
    hcert7.2.1.2.2.2,
    hcert7.2.2.2.1,
    certificate_lift_non_vacuous_and_tight _ _ hw3u_le hc1212,
    certificate_lift_non_vacuous_and_tight _ _ hw3_le hc1212,
    certificate_lift_non_vacuous_and_tight _ _ hw5u_le hc1212,
    certificate_lift_non_vacuous_and_tight _ _ hw5_le hc1212,
    hcert7.2.2.2.2.1,
    hcert7.2.2.2.2.2.1,
    hcert7.2.2.2.2.2.2.1,
    hcert7.2.2.2.2.2.2.2.1,
    hcert7.2.2.2.2.2.2.2.2⟩

/-- Theorem 10 (`non_vacuous_and_tight`, **Master Wave 5 (`W5_126`) Self-Contained Warm Access-Set (`ev+168` / `ev+176`), Distinct-Delete/Call-Cycle, Coupled Revert & 44-Budget Campaign Certificate**):
Simultaneously unites:
- Concrete `InitE.Certificate submission (.finite K)` (`submission = baselineWithFiniteK K`) across all
  **44 budgets** in `fortyFourWarmSetsPortfolio` under the Yukon ceiling `900_719_925_474`, all 4
  `fourWarmSetsTightTiers` (`485_290_777_246`, `485_290_791_046`, `808_817_955_922`, `808_817_969_722`),
  all **46 budgets** in `allFortySixWarmSetsBudgets`, all **40 budgets** in `coupledRevertFortyBudgetPortfolio`,
  all **30 tiers** in `thirtyTierHierarchy`, all 4 `warmSetsSlope*` ceilings, all 4 `coupledRevertTxCapSlope*`
  ceilings, and `.infinity`,
- Complete 10th and 11th table (`ev+168` and `ev+176`) warm access-set & rollback audit
  (`GuestWarmAccessSetAndRollbackBound`, `11/11` tight: `trunc_exact`, `trunc_keeps_parent`,
  `cold_addr_units`, `addr_set_tx`, `addr_dels_block`, `addr_trunc_le ≤ 1_870_314_630`,
  `kPanWarmSets = 161_763_589_338`, `5 * kPanWarmSets < yukon`, margin `91_901_978_784`),
- Complete distinct-delete / call-cycle conditional & unconditional synthesis
  (`DistinctDeleteCycleAndCoupledRevertMaster`, `15/15` tight: `repeat_no_delete`, `dels_distinct`,
  `cycle_units`, `revert_le_tight` under `H2`, `kPanSixSlopeRestored = 139_920_417_568`,
  unconditional `no_six_restore` at `155_688_931_265`),
- Complete coupled revert & per-tx EIP-7825 dirty-key cap tightening (`d_t ≤ 7_989`), disjoint
  `bs+32` / `ts+32` partition, `state_restore` / `jset` / `op_sstore` audit, EIP-2930 access-list &
  call-stack dominance, sub-block multi-tx splitting, `LabToTarget.removeLabels` clean-section
  preservation, `fortyFourWarmSetsClaims` `≤ 128`-byte compliance, and purified `.Solver` path
  admission (`0` `Bounded*` imports). -/
theorem master_warm_access_set_and_forty_four_budget_self_contained_campaign_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (panProg : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (cAsm : AsmConfigExact width) (perf j : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp ptr : Nat)
    (off bd : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (hpan : removeLabels ic cAsm pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2)) = some (L', labs'))
    (p : HolProg width) (hp : StackNoSt p = true)
    (s : Sizes) (d_t w_t db dx n_f k_f a n_blk a_c n_c d_del p_del q_del w_del : Nat)
    (l : List (Nat × Nat × Nat × Nat × Nat)) (lP lRev : List (Nat × Nat))
    (oracles : List (Option (Spt Nat))) (c : Backend.Config)
    (depth minutes P T Kal Aal D R A C W Tloc Tlin cWarm nWarm dCall k : Nat)
    (pBool ocBool : Bool)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (htx : 21 * d_t + w_t ≤ M)
    (ha_tx : 30 * a ≤ 167772) (hn_blk : 30 * n_blk ≤ 2000000)
    (ha_c : a_c ≤ 5611) (hn_c : n_c ≤ 66666)
    (H2 : p_del + cycleUnits * q_del ≤ w_del)
    (hpart : db + dx ≤ D)
    (hT : txMinUnits * T ≤ 2000000)
    (hal : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2000000)
    (hF : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hG : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup)
    (hlin : Tlin ≤ mergeLin)
    (hrev : (lRev.map (fun q => q.1 * q.2)).sum ≤ 3994571428)
    (hcWarm : cWarm ≤ 7989)
    (hnWarm : nWarm ≤ 95238)
    (hdepth : ¬ (dCall + 1 > 1024))
    (not_timeOut_u128 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    fortyFourWarmSetsPortfolio.length = 44 ∧
    fortyFourWarmSetsPortfolio.Pairwise (· < ·) ∧
    (∀ K ∈ fortyFourWarmSetsPortfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (∀ K ∈ fourWarmSetsTightTiers, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    allFortySixWarmSetsBudgets.length = 46 ∧
    (∀ K ∈ allFortySixWarmSetsBudgets, K < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (fortyFourWarmSetsPortfolio.map (fun k_b => yukonScore k_b minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ fortyFourWarmSetsClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope3UnrolledK) (.finite warmSetsSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope3K) (.finite warmSetsSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope5UnrolledK) (.finite warmSetsSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope5K) (.finite warmSetsSlope5K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    truncDels (warmN (enter n_f) k_f) = k_f ∧
    (warmN (enter n_f) k_f).size - truncDels (warmN (enter n_f) k_f) = n_f ∧
    (3000 = 30 * 100 ∧ 26 ≤ 30) ∧
    a + 19 ≤ 5611 ∧
    n_blk ≤ 66666 ∧
    truncTicks a_c n_c ≤ 1870314630 ∧
    truncTicks 5611 66666 = 1870314630 ∧
    kPanWarmSets = 161_763_589_338 ∧
    (5 * kPanWarmSets < yukon ∧ yukon - 5 * kPanWarmSets = 91_901_978_784 ∧ yukon < 6 * kPanWarmSets) ∧
    (journalFlags [] [d_t, d_t] = [false, true] ∧
      dels [] [1, 1, 1, 2, 2] = 2 ∧ dels [1] [1, 1] = 0 ∧
      100 + 100 = cycleUnits * 100 ∧ 19 * 100 + 100 = freshUnits * 100 ∧
      8 * d_del * p_del + 13 * d_del * q_del ≤ 8 * d_del * w_del ∧
      kPanSixSlopeRestored = 139_920_417_568 ∧
      6 * kPanSixSlopeRestored < yukon ∧ yukon < 7 * kPanSixSlopeRestored) ∧
    (21 * 7989 ≤ M ∧ M < 21 * 7990) ∧
    d_t ≤ 7989 ∧
    feasible witness ∧
    coupledCost witness = 155_688_931_265 ∧
    (∃ lw, feasible lw ∧ yukon < 6 * coupledCost lw) ∧
    (endTx s).db + (endTx s).dx = s.db + s.dx ∧
    (endTx s).dx = 0 ∧
    (dirty s).db + (dirty s).dx = s.db + s.dx + 1 ∧
    21 * (db + dx) + W ≤ S ∧
    cycleTicks db dx ≤ 13 * D ∧
    cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
    (restoreOf pBool = .del ↔ pBool = false) ∧
    sstoreGas true ocBool true = 100 ∧
    delsPerCall k = k ∧
    ¬ (1000 * delsPerCall 100 ≤ 0 + 0) ∧
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2000000 ∧
    linear + Tloc + G D R A C W + Tlin + revertCost lRev + 5 * cWarm * nWarm + truncTicks a_c n_c ≤ kPanWarmSets ∧
    dCall ≤ 1023 ∧
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    prefixCost lP P ≤ (P + (lP.map Prod.fst).sum) * (lP.map Prod.snd).sum ∧
    (txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) ∧
    F D R A C W ≤ 95_238_095_238 ∧
    G D R A C W ≤ 100_000_000_000 ∧
    (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2.map Prod.fst ∧
     ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
       ∃ s ∈ StackToLab.compile sc dc mh sp off
           (compileNative cAsm perf (WordToWord.compile wc cAsm
             (panToWordCompileProgHOL arch panProg)).2).2.2.2,
         s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L'.length = 4 + ((compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2).length ∧
    (StackNoSt (StackRemove.comp j bd ptr p) = true ∧ FlattenVisitsSt p = false) ∧
    yukonScore warmSetsSlope3K minutes - yukonScore warmSetsSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore warmSetsSlope5K minutes - yukonScore warmSetsSlope5UnrolledK minutes = 138_000_000 ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedWarmAccessSetAndFortyFourBudgetSynth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedWarmAccessSetAndFortyFourBudgetSynth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hm := master_coupled_revert_tx_cap_and_disjoint_tables_self_contained_campaign_certificate_non_vacuous_and_tight
    arch panProg wc cAsm perf j sc dc mh sp ptr off bd ic pos labs ffis L' labs' hpan
    p hp s d_t w_t db dx l lP lRev oracles c depth minutes P T Kal Aal D R A C W Tloc Tlin cWarm nWarm dCall k
    pBool ocBool hlab compiled depthBound htx hpart hT hal hF hG hloc hlin hrev hcWarm hnWarm hdepth not_timeOut_u128
  have hcert9 := warm_sets_forty_four_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_u128
  have hsc44 := forty_four_warm_sets_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes 0
  have hcl44 := (forty_four_warm_sets_claims_valid_and_within_128_bytes_non_vacuous_and_tight 1).2.2.1
  have hw_aud := guest_warm_access_set_and_rollback_bound_complete_audit_non_vacuous_and_tight
    n_f k_f a n_blk a_c n_c ha_tx hn_blk ha_c hn_c
  have hw_gaps := warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight 0 minutes 0
  have hc10 := hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htr := hw_aud.2.2.2.2.2.2.1
  have hc11 : linear + Tloc + G D R A C W + Tlin + revertCost lRev + 5 * cWarm * nWarm + truncTicks a_c n_c ≤ kPanWarmSets := by
    have hk_eq : kPanCoupledRevertTxCap = kPanAccessCall := rfl
    unfold kPanWarmSets; omega
  refine ⟨hcert9.2.1.1,
    hcert9.2.1.2.1,
    hcert9.2.1.2.2,
    hcert9.2.2.1,
    hcert9.2.2.2.1.1,
    hcert9.2.2.2.1.2.2,
    hsc44.1,
    hcl44,
    hcert9.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hw_aud.1,
    hw_aud.2.1,
    hw_aud.2.2.1,
    hw_aud.2.2.2.1,
    hw_aud.2.2.2.2.2.1,
    htr,
    hw_aud.2.2.2.2.2.2.2.1,
    hw_aud.2.2.2.2.2.2.2.2.2.1,
    hw_aud.2.2.2.2.2.2.2.2.2.2,
    ⟨repeat_no_delete d_t, dels_distinct.1, dels_distinct.2, cycle_units.1, cycle_units.2,
      revert_le_tight d_del p_del q_del w_del H2, kPan_val.1, six_slope.1, six_slope.2.2⟩,
    tx_cap,
    dx_le d_t w_t htx,
    witness_feasible,
    witness_cost,
    no_six_restore,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc11,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw_gaps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw_gaps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by decide,
    by decide,
    rfl⟩

#print axioms guest_warm_access_set_and_rollback_bound_complete_audit_non_vacuous_and_tight
#print axioms distinct_delete_cycle_coupled_revert_and_warm_sets_master_non_vacuous_and_tight
#print axioms warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight
#print axioms forty_four_warm_sets_portfolio_exact_insertion_and_order_non_vacuous_and_tight
#print axioms warm_sets_tiers_interleaved_strict_ordering_non_vacuous_and_tight
#print axioms eleven_table_split_revert_and_warm_sets_truncation_envelope_non_vacuous_and_tight
#print axioms forty_four_warm_sets_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight
#print axioms forty_four_warm_sets_claims_valid_and_within_128_bytes_non_vacuous_and_tight
#print axioms warm_sets_forty_four_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
#print axioms master_warm_access_set_and_forty_four_budget_self_contained_campaign_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedWarmAccessSetAndFortyFourBudgetSynth
