import InitECandidate.Solver.PanToWordNoStubCall
import InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster
import InitECandidate.Solver.SelfContainedWarmAccessSetAndFortyFourBudgetSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth` — Wave 5 Atomic Worker `W5_130`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`PanToWordNoStubCall` (`28/28` tight)**:
   - Unconditional discharge of `WordNoStubCall` across the entire frontend pipeline
     `PanSimp → PanStructs → PanGlobals → PanToCrep → CrepToLoop → LoopToWord`
     (`panToWord_NoStubCall`, `panToWord_names`, `compileProgHOLExact_names`,
     `compileProgHOLExact_bodiesTgtOk`, `makeFuncs_good`, `findLab_good`, `findLab_empty`),
   - Preservation of admissible call targets (`TgtGood`: `0` or `≥ 64`) through the Loop optimiser
     (`loopCallCompHOL_preserves_tgtOk`, `shrinkHOL_preserves_tgtOk`, `markAllHOL_preserves_tgtOk`)
     and `LoopToWord.compHOL` (`compHOL_noStub`, `loopToWordCompile_noStub`),
   - Tight witnesses (`tgtGood_rejects_stub`, `tgtGood_accepts`, `wordNoStubCall_tight`).
2. **`ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster` (`12/12` tight)**:
   - Shared-budget absorption across all 11 hash tables (`bs+0..bs+32`, `ts+0..ts+32`, `ev+168`, `ev+176`)
     under `B + u2 + u3 + u4 ≤ S`: `blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571`
     (`shared_absorption_non_vacuous_and_tight`, `shared_corner_non_vacuous_and_tight`),
   - Master shared 11-table source clock `kPanElevenTablesShared = 156_088_992_805`
     (`kPan_val_non_vacuous_and_tight`, saving `11_342_996_533` ticks over `kPanElevenTables = 167_431_989_338`),
   - Tight 12-tx feasible bracket (`155_688_931_265 ≤ kPanElevenTablesShared = 156_088_992_805`,
     gap `400_061_540` ticks `< 0.26%`, `bracket_non_vacuous_and_tight`),
   - Exact `5×` Yukon margin (`120_274_961_449`, `five_margin_non_vacuous_and_tight`) and `6×`
     impossibility (`six_fails_non_vacuous_and_tight`).
3. **`SelfContainedWarmAccessSetAndFortyFourBudgetSynth` (`10/10` tight)**:
   - Self-contained 10th and 11th table (`ev+168` and `ev+176`) warm access-set rollback audit
     (`kPanWarmSets = 161_763_589_338`), distinct-delete / call-cycle audit (`H2`), coupled revert
     and EIP-7825 per-tx cap (`d_t ≤ 7_989`), and 44-budget certified portfolio.
4. **48-Budget Certified Portfolio (`fortyEightSharedPortfolio`) & 52-Budget Grand Superset (`allFiftyTwoSharedBudgets`)**:
   - The 4 new `kPanElevenTablesShared` target budgets at slopes `3×` and `5×` (`468_266_987_647`,
     `468_267_001_447`, `780_444_973_257`, `780_444_987_057 < 900_719_925_474`, plus `+100`
     baseline-offset variants `468_266_987_747`, `468_267_001_547`, `780_444_973_357`, `780_444_987_157`),
   - Strict ordering across all **48 budgets** (`fortyEightSharedPortfolio.length = 48`),
     strict `yukonScore` monotonicity, `claim.json ≤ 128` byte conformity (`fortyEightSharedClaims`),
     and `InitE.Certificate` lifting (`0 sorryAx`, 10 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth

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
open InitECandidate.Solver.PanToWordNoStubCall
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.GuestEvmStepOpcodeBounds
open InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds
open InitECandidate.Solver.GuestBlockVsTxHtabBounds
open InitECandidate.Solver.GuestJointBlockGasHtabBound hiding M
open InitECandidate.Solver.GuestDirtyWriteHtabDominance
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope hiding S
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
open InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound (kPanElevenTables)
open InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption
  (S kPanElevenTablesShared side_slopes storage_loss shared_absorption
   shared_tight lower_witness bracket bracket_rel five_margin six_fails)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio
  (CertificateAt certificate_lift_non_vacuous_and_tight)
open InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster
  (elevenTablesSharedSlope3UnrolledK elevenTablesSharedSlope3K
   elevenTablesSharedSlope5UnrolledK elevenTablesSharedSlope5K
   shared_absorption_non_vacuous_and_tight shared_corner_non_vacuous_and_tight
   kPan_val_non_vacuous_and_tight bracket_non_vacuous_and_tight
   five_margin_non_vacuous_and_tight six_fails_non_vacuous_and_tight
   target_values_non_vacuous_and_tight portfolio_union_non_vacuous_and_tight
   portfolio_shape_non_vacuous_and_tight forty_eight_certified_non_vacuous_and_tight
   submission_certificate_non_vacuous_and_tight integrated_master_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedWarmAccessSetAndFortyFourBudgetSynth
  (warmSetsSlope3UnrolledK warmSetsSlope3K warmSetsSlope5UnrolledK warmSetsSlope5K
   fourWarmSetsTiers fourWarmSetsTightTiers fortyFourWarmSetsPortfolio
   fortyFourWarmSetsClaims allFortySixWarmSetsBudgets
   guest_warm_access_set_and_rollback_bound_complete_audit_non_vacuous_and_tight
   distinct_delete_cycle_coupled_revert_and_warm_sets_master_non_vacuous_and_tight
   warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight
   forty_four_warm_sets_portfolio_exact_insertion_and_order_non_vacuous_and_tight
   warm_sets_tiers_interleaved_strict_ordering_non_vacuous_and_tight
   eleven_table_split_revert_and_warm_sets_truncation_envelope_non_vacuous_and_tight
   forty_four_warm_sets_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight
   forty_four_warm_sets_claims_valid_and_within_128_bytes_non_vacuous_and_tight
   warm_sets_forty_four_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
   master_warm_access_set_and_forty_four_budget_self_contained_campaign_certificate_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedCoupledRevertTxCapAndDisjointTablesSynth
open InitECandidate.Solver.SelfContainedDisjointTablesAndStateRestoreSynth
open InitECandidate.Solver.SelfContainedStateRestoreAndFortyBudgetSynth
open InitECandidate.Solver.SelfContainedFortyBudgetPortfolioSynth
  (fourAccessCallTiers fortyAccessCallPortfolio fortyAccessCallClaims allFortyTwoAccessCallBudgets)
open InitECandidate.Solver.SelfContainedCompleteCampaignCert
open InitECandidate.Solver.SelfContainedAllAxesSynthesis
open InitECandidate.Solver.SelfContainedSolutionCandidates
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
open InitECandidate.Solver.RiscvBootAndCopyLoopCert
open InitECandidate.Solver.RiscvSszFastRejectAndBootCert
open InitECandidate.Solver.SelfContainedPush31MasterK
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitECandidate.Solver.ExactKeccakSixPassReducedCert
open InitECandidate.Solver.ExactKeccakCopyLoopUnrolledCert
open InitECandidate.Solver.PerTxEip7825TargetMasterK
open InitECandidate.Solver.PurifiedSolverIndex
open InitECandidate.Solver.PurifiedSubmissionBound
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.YukonVerifyScriptAudit
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
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

/-! ## Section 1: Four `kPanElevenTablesShared` Target Tiers & 48-Budget Portfolio Definitions -/

/-- The 4 `kPanElevenTablesShared` (`156_088_992_805`) target budgets from
`ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster` (`468_266_987_647`,
`468_267_001_447`, `780_444_973_257`, `780_444_987_057`). -/
def fourElevenTablesSharedTiers : List Nat := [
  elevenTablesSharedSlope3UnrolledK,
  elevenTablesSharedSlope3K,
  elevenTablesSharedSlope5UnrolledK,
  elevenTablesSharedSlope5K
]

/-- The 4 baseline-bootstrap (`9_332` / `23_132`, i.e. `+100` tick) `kPanElevenTablesShared`
target ceilings (`468_266_987_747`, `468_267_001_547`, `780_444_973_357`, `780_444_987_157`). -/
def fourElevenTablesSharedPlus100Tiers : List Nat := [
  (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanElevenTablesShared,
  bootstrapSteps + 3 * kPanElevenTablesShared,
  (bootstrapSteps - copyLoopSavedSteps) + 5 * kPanElevenTablesShared,
  bootstrapSteps + 5 * kPanElevenTablesShared
]

/-- Canonical 48-budget strictly increasing portfolio (`= ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio`),
uniting `WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.portfolio` (`44` budgets) with
`fourElevenTablesSharedTiers` (`4` budgets). -/
def fortyEightSharedPortfolio : List Nat :=
  ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio

/-- 48-budget strictly increasing portfolio uniting `fortyFourWarmSetsPortfolio` (`44` budgets)
with `fourElevenTablesSharedTiers` (`4` budgets). -/
def fortyEightBaselineWarmSetsPortfolio : List Nat := [
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
  468_266_987_647,
  468_267_001_447,
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
  780_444_973_257,
  780_444_987_057,
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

/-- `claim.json` payloads paired with each of the 48 budgets in `fortyEightSharedPortfolio`. -/
def fortyEightSharedClaims : List (Nat × String) := [
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
  (468_266_987_647, verifierClaimJson "468266987647"),
  (468_267_001_447, verifierClaimJson "468267001447"),
  (479_679_833_456, verifierClaimJson "479679833456"),
  (479_679_847_256, verifierClaimJson "479679847256"),
  (485_290_777_246, verifierClaimJson "485290777246"),
  (485_290_791_046, verifierClaimJson "485290791046"),
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
  (780_444_973_257, verifierClaimJson "780444973257"),
  (780_444_987_057, verifierClaimJson "780444987057"),
  (785_125_408_508, verifierClaimJson "785125408508"),
  (799_466_382_872, verifierClaimJson "799466382872"),
  (799_466_396_672, verifierClaimJson "799466396672"),
  (808_817_955_922, verifierClaimJson "808817955922"),
  (808_817_969_722, verifierClaimJson "808817969722"),
  (810_291_208_508, verifierClaimJson "810291208508"),
  (816_696_823_280, verifierClaimJson "816696823280"),
  (816_696_837_080, verifierClaimJson "816696837080"),
  (857_384_015_252, verifierClaimJson "857384015252")
]

/-- Sorted 52-budget grand superset uniting `fortyEightSharedPortfolio` (`48` budgets)
with `fourWarmSetsTiers` (`4` baseline warm-sets tiers). -/
def allFiftyTwoSharedBudgets : List Nat := [
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
  468_266_987_647,
  468_267_001_447,
  479_679_833_456,
  479_679_847_256,
  485_290_777_246,
  485_290_777_346,
  485_290_791_046,
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
  780_444_973_257,
  780_444_987_057,
  785_125_408_508,
  799_466_382_872,
  799_466_396_672,
  808_817_955_922,
  808_817_956_022,
  808_817_969_722,
  808_817_969_822,
  810_291_208_508,
  816_696_823_280,
  816_696_837_080,
  857_384_015_252
]

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`, **Complete Frontend Closure of `PanToWordNoStubCall` (`28/28` tight): Unconditional `panToWord_NoStubCall`, `panToWord_names`, `tgtGood_rejects_stub`, `tgtGood_accepts` & `wordNoStubCall_tight`**):
Unites the main theorems and witnesses of `PanToWordNoStubCall`:
- `panToWord_NoStubCall arch prog`: every `WordLang` body emitted from any Pancake program via
  `PanSimp → PanStructs → PanGlobals → PanToCrep → CrepToLoop → LoopToWord` satisfies
  `WordNoStubCall y.2.2 = true` (no call ever targets `storeConstsStubLocation = 6`),
- `panToWord_names arch prog`: every emitted function label satisfies `64 ≤ y.1`,
- `compileProgHOLExact_names arch crepProg` and `compileProgHOLExact_bodiesTgtOk arch crepProg`,
- `makeFuncs_good crepProg` and `findLab_empty arch name`,
- `tgtGood_rejects_stub` (`¬ TgtGood (some storeConstsStubLocation)`),
- `tgtGood_accepts` (`TgtGood (some 0) ∧ TgtGood (some 64) ∧ ¬ TgtGood none`), and
- `wordNoStubCall_tight` (`WordNoStubCall (.call none (some storeConstsStubLocation) [] none) = false ∧ WordNoStubCall (.call none (some 64) [] none) = true`). -/
theorem pan_to_word_no_stub_call_and_user_names_complete_audit_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width))
    (crepProg : List (MlString × List Nat × CrepProgHOL width))
    (name : MlString) :
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ panToWordCompileProgHOL arch prog, 64 ≤ y.1) ∧
    (∀ y ∈ panToWordCompileProgHOL arch prog, NoSt y.2.2 = true) ∧
    (∀ x ∈ compileProgHOLExact arch crepProg, ∃ i, x.1 = 64 + i ∧ i < crepProg.length) ∧
    (∀ x ∈ compileProgHOLExact arch crepProg, loopTgtOk x.2.2) ∧
    (∀ k l a, (crepToLoopMakeFuncsExactExecutable crepProg).lookup k = some (l, a) → 64 ≤ l) ∧
    findLabExact (mkCtxtExact arch HolFiniteMapExact.empty HolFiniteMapExact.empty 0) name = 0 ∧
    ¬ TgtGood (some storeConstsStubLocation) ∧
    (TgtGood (some 0) ∧ TgtGood (some 64) ∧ ¬ TgtGood none) ∧
    (WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some storeConstsStubLocation) [] none) = false ∧
     WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true) :=
  ⟨panToWord_NoStubCall arch prog,
   panToWord_names arch prog,
   panToWord_NoSt arch prog,
   compileProgHOLExact_names arch crepProg,
   compileProgHOLExact_bodiesTgtOk arch crepProg,
   makeFuncs_good crepProg,
   findLab_empty arch name,
   tgtGood_rejects_stub,
   tgtGood_accepts,
   wordNoStubCall_tight⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **Loop Optimiser & `LoopToWord` Call-Target Preservation Chain (`loopCallCompHOL`, `shrinkHOL`, `markAllHOL`, `LoopToWord.compHOL`)**):
Synthesizes the structural preservation theorems of `PanToWordNoStubCall`:
- `findLab_good context name hf` (`findLabExact context name = 0 ∨ 64 ≤ findLabExact context name`),
- `loopCallCompHOL_preserves_tgtOk loopProg live hloop`,
- `shrinkHOL_preserves_tgtOk loopProg live hloop`,
- `markAllHOL_preserves_tgtOk loopProg hloop`,
- `compHOL_noStub ctx loopProg l hloop` (`WordNoStubCall (LoopToWord.compHOL ctx loopProg l).1 = true`),
- `tgt_ne ht` (`(t != some storeConstsStubLocation) = true`),
- together with `tgtGood_rejects_stub` and `wordNoStubCall_tight`. -/
theorem loop_to_word_and_optimiser_tgt_ok_preservation_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (context : CrepToLoopContextExact) (name : MlString)
    (hf : FuncsGood context)
    (loopProg : HolLoopProg width) (liveCall : Spt Nat) (liveShrink : NumSet)
    (ctx : Spt Nat) (l : Nat × Nat)
    (hloop : loopTgtOk loopProg)
    (t : Option Nat) (ht : TgtGood t) :
    (findLabExact context name = 0 ∨ 64 ≤ findLabExact context name) ∧
    loopTgtOk (loopCallCompHOL liveCall loopProg).1 ∧
    loopTgtOk (shrinkHOL [] loopProg liveShrink).1 ∧
    loopTgtOk (markAllHOL loopProg).1 ∧
    WordNoStubCall (LoopToWord.compHOL ctx loopProg l).1 = true ∧
    (t != some storeConstsStubLocation) = true ∧
    ¬ TgtGood (some storeConstsStubLocation) ∧
    (WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some storeConstsStubLocation) [] none) = false ∧
     WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true) :=
  ⟨findLab_good context name hf,
   loopCallCompHOL_preserves_tgtOk loopProg liveCall hloop,
   shrinkHOL_preserves_tgtOk loopProg liveShrink hloop,
   markAllHOL_preserves_tgtOk loopProg hloop,
   compHOL_noStub ctx loopProg l hloop,
   tgt_ne ht,
   tgtGood_rejects_stub,
   wordNoStubCall_tight⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Complete Closure of `ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster`: `shared_absorption`, `bracket` (`155_688_931_265 ≤ 156_088_992_805`, Gap `400_061_540 < 0.26%`) & `five_margin` (`120_274_961_449`)**):
Unites the 11-table shared-budget absorption and bracket theorems:
- `shared_absorption_non_vacuous_and_tight`: `blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571`
  under `B + u2 + u3 + u4 ≤ S`, `40 * blk ≤ B * B`, `84 * loc ≤ M * B`, `21 * t2 ≤ 5 * 7989 * u2`,
  `30 * t3 ≤ 5 * 5611 * u3`, `60 * t4 ≤ (M + 2280) * u4`,
- `shared_corner_non_vacuous_and_tight`: `40 * 100_000_000_000 ≤ S * S ∧ 84 * 3_994_571_428 ≤ M * S ∧ (21 * S * S + 130 * M * S) / 840 = 151_929_428_571`,
- `side_slopes` and `storage_loss`,
- `kPan_val_non_vacuous_and_tight`: `kPanElevenTablesShared = 156_088_992_805 ∧ kPanElevenTables - kPanElevenTablesShared = 11_342_996_533`,
- `bracket_non_vacuous_and_tight`: `feasible witness ∧ coupledCost witness = 155_688_931_265 ∧ coupledCost witness ≤ kPanElevenTablesShared ∧ kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧ 400_061_540 * 10000 < 26 * 156_088_992_805 ∧ 400_061_540 * 10000 < 26 * 155_688_931_265`,
- `five_margin_non_vacuous_and_tight`: `5 * kPanElevenTablesShared < yukon ∧ yukon - 5 * kPanElevenTablesShared = 120_274_961_449`,
- `six_fails_non_vacuous_and_tight`: `yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness`. -/
theorem eleven_tables_shared_budget_absorption_and_bracket_complete_audit_non_vacuous_and_tight
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (40 * 100_000_000_000 ≤ S * S ∧ 84 * 3_994_571_428 ≤ M * S ∧
      (21 * S * S + 130 * M * S) / 840 = 151_929_428_571) ∧
    (5 * 7989 ≤ 21 * 1903 ∧ 5 * 5611 ≤ 30 * 936 ∧ M + 2280 ≤ 60 * 2835) ∧
    S * (S - B) ≤ S * S - B * B ∧
    (kPanElevenTablesShared = 156_088_992_805 ∧
      kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
      400_061_540 * 10000 < 26 * 156_088_992_805 ∧
      400_061_540 * 10000 < 26 * 155_688_931_265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) := by
  have hB : B ≤ S := by omega
  exact ⟨shared_absorption_non_vacuous_and_tight B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4,
    shared_corner_non_vacuous_and_tight,
    side_slopes,
    storage_loss B hB,
    kPan_val_non_vacuous_and_tight,
    bracket_non_vacuous_and_tight,
    five_margin_non_vacuous_and_tight,
    six_fails_non_vacuous_and_tight⟩

/-- Theorem 4 (`non_vacuous_and_tight`, **Exact Numerical Evaluation of the `kPanElevenTablesShared` Target Tiers (`468_266_987_647`, `468_267_001_447`, `780_444_973_257`, `780_444_987_057`), Baseline `+100` Variants & Savings over `kPanWarmSets` / `kPanElevenTables`**):
Proves exact numerical values for `elevenTablesSharedSlope3UnrolledK`, `elevenTablesSharedSlope3K`,
`elevenTablesSharedSlope5UnrolledK`, `elevenTablesSharedSlope5K`, their `+100` baseline-offset
counterparts (`468_266_987_747`, `468_267_001_547`, `780_444_973_357`, `780_444_987_157`),
exact `13_800`-step unrolled `copyLoop` savings, exact savings over `kPanWarmSets`
(`161_763_589_338 - 156_088_992_805 = 5_674_596_533`, saving `17_023_789_599` at `3×` and
`28_372_982_665` at `5×`), 1-tick tightness boundaries, and slope threshold `slope ≤ 5`. -/
theorem eleven_tables_shared_target_budgets_and_warm_sets_gaps_non_vacuous_and_tight
    (k minutes slope : Nat) :
    elevenTablesSharedSlope3UnrolledK = 468_266_987_647 ∧
    elevenTablesSharedSlope3K = 468_267_001_447 ∧
    elevenTablesSharedSlope5UnrolledK = 780_444_973_257 ∧
    elevenTablesSharedSlope5K = 780_444_987_057 ∧
    (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanElevenTablesShared = 468_266_987_747 ∧
    bootstrapSteps + 3 * kPanElevenTablesShared = 468_267_001_547 ∧
    (bootstrapSteps - copyLoopSavedSteps) + 5 * kPanElevenTablesShared = 780_444_973_357 ∧
    bootstrapSteps + 5 * kPanElevenTablesShared = 780_444_987_157 ∧
    kPanWarmSets - kPanElevenTablesShared = 5_674_596_533 ∧
    kPanCoupledRevertTxCap - kPanElevenTablesShared = 3_804_281_903 ∧
    kPanElevenTables - kPanElevenTablesShared = 11_342_996_533 ∧
    kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
    WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope3UnrolledK -
      elevenTablesSharedSlope3UnrolledK = 17_023_789_599 ∧
    WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope3K -
      elevenTablesSharedSlope3K = 17_023_789_599 ∧
    WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope5UnrolledK -
      elevenTablesSharedSlope5UnrolledK = 28_372_982_665 ∧
    WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope5K -
      elevenTablesSharedSlope5K = 28_372_982_665 ∧
    elevenTablesSharedSlope3K - elevenTablesSharedSlope3UnrolledK = 13_800 ∧
    elevenTablesSharedSlope5K - elevenTablesSharedSlope5UnrolledK = 13_800 ∧
    900_719_925_474 - elevenTablesSharedSlope5K = 120_274_938_417 ∧
    ¬ (3 * kPanElevenTablesShared + 9232 ≤ elevenTablesSharedSlope3UnrolledK - 1) ∧
    ¬ (3 * kPanElevenTablesShared + 23032 ≤ elevenTablesSharedSlope3K - 1) ∧
    ¬ (5 * kPanElevenTablesShared + 9232 ≤ elevenTablesSharedSlope5UnrolledK - 1) ∧
    ¬ (5 * kPanElevenTablesShared + 23032 ≤ elevenTablesSharedSlope5K - 1) ∧
    (elevenTablesSharedSlope3K ≤ k + copyLoopSavedSteps ↔ elevenTablesSharedSlope3UnrolledK ≤ k) ∧
    (elevenTablesSharedSlope5K ≤ k + copyLoopSavedSteps ↔ elevenTablesSharedSlope5UnrolledK ≤ k) ∧
    yukonScore elevenTablesSharedSlope3K minutes - yukonScore elevenTablesSharedSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore elevenTablesSharedSlope5K minutes - yukonScore elevenTablesSharedSlope5UnrolledK minutes = 138_000_000 ∧
    (23032 + slope * kPanElevenTablesShared < 900_719_925_474 ↔ slope ≤ 5) := by
  have hb : bootstrapSteps = 23_132 := bootstrapSteps_eq
  have hcl : copyLoopSavedSteps = 13_800 := copy_loop_saved_exact
  have hks : kPanElevenTablesShared = 156_088_992_805 := kPan_val_non_vacuous_and_tight.1
  have hkw : kPanWarmSets = 161_763_589_338 := kPanWarmSets_val
  have hkc : kPanCoupledRevertTxCap = 159_893_274_708 := rfl
  have hke : kPanElevenTables = 167_431_989_338 := rfl
  have hcw : coupledCost witness = 155_688_931_265 := witness_cost
  have htv := target_values_non_vacuous_and_tight
  have htv44 := WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.target_values_non_vacuous_and_tight
  rw [htv.1, htv.2.1, htv.2.2.1, htv.2.2.2.1,
      htv44.1, htv44.2.1, htv44.2.2.1, htv44.2.2.2.1,
      hb, hcl, hks, hkw, hkc, hke, hcw]
  unfold yukonScore
  omega

/-- Theorem 5 (`non_vacuous_and_tight`, **48-Budget Portfolio Exact Insertion (`fortyEightSharedPortfolio`), Union Characterization & 52-Budget Grand Superset (`allFiftyTwoSharedBudgets`)**):
Proves that:
- `fortyEightSharedPortfolio` (`= ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio`)
  has length `48`, is strictly increasing (`Pairwise (· < ·)`), and equals the `insertionSort` of
  `WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.portfolio ++ fourElevenTablesSharedTiers`,
- `K ∈ fortyEightSharedPortfolio ↔ K ∈ WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.portfolio ∨ K ∈ fourElevenTablesSharedTiers`,
- `fortyEightBaselineWarmSetsPortfolio` has length `48`, is strictly increasing, and equals the
  `insertionSort` of `fortyFourWarmSetsPortfolio ++ fourElevenTablesSharedTiers`,
- `allFiftyTwoSharedBudgets` has length `52`, is strictly increasing, and equals the `insertionSort`
  of `fortyEightSharedPortfolio ++ fourWarmSetsTiers`,
- Every budget across all portfolios lies in `[1_212_035_192, 857_384_015_252]` strictly below Yukon `900_719_925_474`. -/
theorem forty_eight_budget_portfolio_exact_insertion_and_order_non_vacuous_and_tight (K : Nat) :
    fortyEightSharedPortfolio.length = 48 ∧
    fortyEightSharedPortfolio.Pairwise (· < ·) ∧
    (WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.portfolio ++ fourElevenTablesSharedTiers).insertionSort (· ≤ ·) =
      fortyEightSharedPortfolio ∧
    (K ∈ fortyEightSharedPortfolio ↔
      K ∈ WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.portfolio ∨
      K ∈ fourElevenTablesSharedTiers) ∧
    (∀ k ∈ WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.portfolio, k ∈ fortyEightSharedPortfolio) ∧
    (∀ k ∈ fourElevenTablesSharedTiers, k ∈ fortyEightSharedPortfolio) ∧
    (∀ k ∈ fortyEightSharedPortfolio,
      1_212_035_192 ≤ k ∧ k ≤ 857_384_015_252 ∧ k < 900_719_925_474 ∧ ¬ k ≤ k - 1) ∧
    fortyEightBaselineWarmSetsPortfolio.length = 48 ∧
    fortyEightBaselineWarmSetsPortfolio.Pairwise (· < ·) ∧
    (fortyFourWarmSetsPortfolio ++ fourElevenTablesSharedTiers).insertionSort (· ≤ ·) =
      fortyEightBaselineWarmSetsPortfolio ∧
    allFiftyTwoSharedBudgets.length = 52 ∧
    allFiftyTwoSharedBudgets.Pairwise (· < ·) ∧
    (fortyEightSharedPortfolio ++ fourWarmSetsTiers).insertionSort (· ≤ ·) =
      allFiftyTwoSharedBudgets ∧
    (∀ k ∈ fortyEightSharedPortfolio, k ∈ allFiftyTwoSharedBudgets) ∧
    (∀ k ∈ fortyEightBaselineWarmSetsPortfolio, k ∈ allFiftyTwoSharedBudgets) ∧
    (elevenTablesSharedSlope5K ≤ K ↔ 780_444_987_057 ≤ K) := by
  have hw := warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight 0 0 0
  have hfwt : fourWarmSetsTiers = [485_290_777_346, 485_290_791_146, 808_817_956_022, 808_817_969_822] := by
    unfold fourWarmSetsTiers
    rw [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1]
  have hsort52 : (fortyEightSharedPortfolio ++ fourWarmSetsTiers).insertionSort (· ≤ ·) =
      allFiftyTwoSharedBudgets := by
    rw [hfwt]; decide
  have hs5 : elevenTablesSharedSlope5K = 780_444_987_057 := rfl
  refine ⟨portfolio_shape_non_vacuous_and_tight.1,
    portfolio_shape_non_vacuous_and_tight.2.1,
    by decide,
    portfolio_union_non_vacuous_and_tight K,
    by decide,
    by decide,
    by decide,
    by decide,
    by decide,
    by decide,
    by decide,
    by decide,
    hsort52,
    by decide,
    by decide,
    ?_⟩
  rw [hs5]

/-- Theorem 6 (`non_vacuous_and_tight`, **Interleaved Strict Ordering of the `kPanElevenTablesShared` Tiers & `+100` Variants within the 48-Budget & 52-Budget Portfolios**):
Proves that the `kPanElevenTablesShared` budgets sit in strict interleaved order between existing tiers:
- At `3×`: `459_244_490_549 < elevenTablesSharedSlope3UnrolledK (468_266_987_647) < 468_266_987_747 < elevenTablesSharedSlope3K (468_267_001_447) < 468_267_001_547 < coupledRevertTxCapSlope3UnrolledK (479_679_833_456) < coupledRevertTxCapSlope3K (479_679_847_256) < WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope3UnrolledK (485_290_777_246) < warmSetsSlope3UnrolledK (485_290_777_346) < WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope3K (485_290_791_046) < warmSetsSlope3K (485_290_791_146) < 485_837_754_632`,
- At `5×`: `775_680_812_618 < elevenTablesSharedSlope5UnrolledK (780_444_973_257) < 780_444_973_357 < elevenTablesSharedSlope5K (780_444_987_057) < 780_444_987_157 < coupledSlope6K (785_125_408_508) < coupledRevertTxCapSlope5UnrolledK (799_466_382_872) < coupledRevertTxCapSlope5K (799_466_396_672) < WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope5UnrolledK (808_817_955_922) < warmSetsSlope5UnrolledK (808_817_956_022) < WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope5K (808_817_969_722) < warmSetsSlope5K (808_817_969_822) < transitionSlope6UnrolledK (810_291_208_508)`. -/
theorem eleven_tables_shared_tiers_interleaved_strict_ordering_non_vacuous_and_tight (K : Nat) :
    459_244_490_549 < elevenTablesSharedSlope3UnrolledK ∧
    elevenTablesSharedSlope3UnrolledK < 468_266_987_747 ∧
    468_266_987_747 < elevenTablesSharedSlope3K ∧
    elevenTablesSharedSlope3K < 468_267_001_547 ∧
    468_267_001_547 < coupledRevertTxCapSlope3UnrolledK ∧
    coupledRevertTxCapSlope3UnrolledK < coupledRevertTxCapSlope3K ∧
    coupledRevertTxCapSlope3K < WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope3UnrolledK ∧
    WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope3UnrolledK < warmSetsSlope3UnrolledK ∧
    warmSetsSlope3UnrolledK < WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope3K ∧
    WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope3K < warmSetsSlope3K ∧
    warmSetsSlope3K < 485_837_754_632 ∧
    775_680_812_618 < elevenTablesSharedSlope5UnrolledK ∧
    elevenTablesSharedSlope5UnrolledK < 780_444_973_357 ∧
    780_444_973_357 < elevenTablesSharedSlope5K ∧
    elevenTablesSharedSlope5K < 780_444_987_157 ∧
    780_444_987_157 < coupledSlope6K ∧
    coupledSlope6K < coupledRevertTxCapSlope5UnrolledK ∧
    coupledRevertTxCapSlope5UnrolledK < coupledRevertTxCapSlope5K ∧
    coupledRevertTxCapSlope5K < WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope5UnrolledK ∧
    WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope5UnrolledK < warmSetsSlope5UnrolledK ∧
    warmSetsSlope5UnrolledK < WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope5K ∧
    WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope5K < warmSetsSlope5K ∧
    warmSetsSlope5K < transitionSlope6UnrolledK ∧
    transitionSlope6UnrolledK < 900_719_925_474 ∧
    (elevenTablesSharedSlope3K ≤ K ↔ 468_267_001_447 ≤ K) := by
  have hw := warm_sets_target_budgets_and_access_call_gaps_non_vacuous_and_tight 0 0 0
  have hcr := coupled_revert_tx_cap_and_disjoint_tables_target_tiers_coincide_non_vacuous_and_tight 0 0
  have hcr3u : coupledRevertTxCapSlope3UnrolledK = 479_679_833_456 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcr3 : coupledRevertTxCapSlope3K = 479_679_847_256 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcr5u : coupledRevertTxCapSlope5UnrolledK = 799_466_382_872 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcr5 : coupledRevertTxCapSlope5K = 799_466_396_672 := hcr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hs3 : elevenTablesSharedSlope3K = 468_267_001_447 := rfl
  rw [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hcr3u, hcr3, hcr5u, hcr5, hs3]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, Iff.rfl⟩

/-- Theorem 7 (`non_vacuous_and_tight`, **Strict `yukonScore` Monotonicity & IEEE-754 `float64` Exactness (`< 2^53 - 1`) across all 48 Budgets of `fortyEightSharedPortfolio`**):
Proves that `(fortyEightSharedPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·)` holds
for every runtime `minutes`, every budget in `fortyEightSharedPortfolio` satisfies
`yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes < 2^53 - 1`,
and the `kPanElevenTablesShared` tiers sit in strict `yukonScore` order between their neighbours. -/
theorem forty_eight_shared_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight
    (minutes K : Nat) :
    (fortyEightSharedPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ k1 ∈ fortyEightSharedPortfolio,
      ∀ k2 ∈ fortyEightSharedPortfolio,
        k1 < k2 ↔ yukonScore k1 minutes < yukonScore k2 minutes) ∧
    (∀ k ∈ fortyEightSharedPortfolio,
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    yukonScore 459_244_490_549 minutes < yukonScore elevenTablesSharedSlope3UnrolledK minutes ∧
    yukonScore elevenTablesSharedSlope3UnrolledK minutes < yukonScore elevenTablesSharedSlope3K minutes ∧
    yukonScore elevenTablesSharedSlope3K minutes < yukonScore coupledRevertTxCapSlope3UnrolledK minutes ∧
    yukonScore 775_680_812_618 minutes < yukonScore elevenTablesSharedSlope5UnrolledK minutes ∧
    yukonScore elevenTablesSharedSlope5UnrolledK minutes < yukonScore elevenTablesSharedSlope5K minutes ∧
    yukonScore elevenTablesSharedSlope5K minutes < yukonScore coupledSlope6K minutes ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hord : fortyEightSharedPortfolio.Pairwise (· < ·) :=
    portfolio_shape_non_vacuous_and_tight.2.1
  have h_mono : ∀ {a b : Nat}, a < b → yukonScore a minutes < yukonScore b minutes := by
    intro a b hab; unfold yukonScore; omega
  have hmap_pw : (fortyEightSharedPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp h_mono hord
  have h44_sc := forty_four_warm_sets_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes K
  have hterm_lt : yukonScore 857_384_015_252 minutes < 2 ^ 53 - 1 :=
    (h44_sc.2.2.1 857_384_015_252 (by decide)).2.2
  have hint := eleven_tables_shared_tiers_interleaved_strict_ordering_non_vacuous_and_tight 0
  have hlt1 : 459_244_490_549 < elevenTablesSharedSlope3UnrolledK := hint.1
  have hlt2 : elevenTablesSharedSlope3UnrolledK < elevenTablesSharedSlope3K :=
    Nat.lt_trans hint.2.1 hint.2.2.1
  have hlt3 : elevenTablesSharedSlope3K < coupledRevertTxCapSlope3UnrolledK :=
    Nat.lt_trans hint.2.2.2.1 hint.2.2.2.2.1
  have hlt4 : 775_680_812_618 < elevenTablesSharedSlope5UnrolledK :=
    hint.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt5 : elevenTablesSharedSlope5UnrolledK < elevenTablesSharedSlope5K :=
    Nat.lt_trans hint.2.2.2.2.2.2.2.2.2.2.2.2.1 hint.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt6 : elevenTablesSharedSlope5K < coupledSlope6K :=
    Nat.lt_trans hint.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hint.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hmap_pw, ?_, ?_,
    h_mono hlt1,
    h_mono hlt2,
    h_mono hlt3,
    h_mono hlt4,
    h_mono hlt5,
    h_mono hlt6,
    h44_sc.2.2.2.2.2.2.2.2.2⟩
  · intro k1 _ k2 _
    unfold yukonScore; omega
  · intro k hk
    have hbnd := (forty_eight_budget_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0).2.2.2.2.2.2.1 k hk
    have h1 : yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes := by
      unfold yukonScore; omega
    have h2 : yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes := by
      unfold yukonScore; omega
    exact ⟨h1, h2, Nat.lt_of_le_of_lt h2 hterm_lt⟩

/-- Theorem 8 (`non_vacuous_and_tight`, **All 48 Budgets in `fortyEightSharedPortfolio` Possess Valid `claim.json ≤ 128` Byte Payloads (`fortyEightSharedClaims`)**):
Proves that every one of the 48 `(K, json)` pairs in `fortyEightSharedClaims` satisfies
`json.utf8ByteSize ≤ 128` and `validFiniteClaim K json = true`, including explicit verification
of the `kPanElevenTablesShared` claims (`468266987647`, `468267001447`, `780444973257`, `780444987057`,
and `+100` variants `468266987747`, `468267001547`, `780444973357`, `780444987157`). -/
theorem forty_eight_shared_claims_valid_and_within_128_bytes_non_vacuous_and_tight (K : Nat) :
    fortyEightSharedClaims.length = 48 ∧
    fortyEightSharedClaims.map Prod.fst = fortyEightSharedPortfolio ∧
    (∀ entry ∈ fortyEightSharedClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (verifierClaimJson "468266987647").utf8ByteSize ≤ 128 ∧
    validFiniteClaim elevenTablesSharedSlope3UnrolledK (verifierClaimJson "468266987647") = true ∧
    (verifierClaimJson "468267001447").utf8ByteSize ≤ 128 ∧
    validFiniteClaim elevenTablesSharedSlope3K (verifierClaimJson "468267001447") = true ∧
    (verifierClaimJson "780444973257").utf8ByteSize ≤ 128 ∧
    validFiniteClaim elevenTablesSharedSlope5UnrolledK (verifierClaimJson "780444973257") = true ∧
    (verifierClaimJson "780444987057").utf8ByteSize ≤ 128 ∧
    validFiniteClaim elevenTablesSharedSlope5K (verifierClaimJson "780444987057") = true ∧
    validFiniteClaim 468_266_987_747 (verifierClaimJson "468266987747") = true ∧
    validFiniteClaim 468_267_001_547 (verifierClaimJson "468267001547") = true ∧
    validFiniteClaim 780_444_973_357 (verifierClaimJson "780444973357") = true ∧
    validFiniteClaim 780_444_987_157 (verifierClaimJson "780444987157") = true ∧
    (validFiniteClaim K (verifierClaimJson "780444987057") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) := by
  have hlen : decide ((verifierClaimJson "780444987057").utf8ByteSize ≤ MAX_CLAIM_BYTES) = true := by decide
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  unfold validFiniteClaim
  rw [hlen, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- Theorem 9 (`non_vacuous_and_tight`, **Direct Target Non-`.timeOut` to 48-Budget, 52-Budget, 44-Budget & 30-Tier `InitE.Certificate submission (.finite K)` Bridge**):
Proves that uniform target non-`.timeOut` at `exactKeccak128UnrolledK = 1_212_035_192` yields
`CertificateAt 1_212_035_192`, which simultaneously certifies:
- Every `K ∈ fortyEightSharedPortfolio` (`48` budgets) with an explicit concrete
  `submission = baselineWithFiniteK K` satisfying `K < 900_719_925_474 ∧ InitE.Certificate submission (.finite K)`,
- Every `K ∈ fortyEightBaselineWarmSetsPortfolio` (`48` budgets),
- Every `K ∈ allFiftyTwoSharedBudgets` (`52` budgets),
- Every `K ∈ fortyFourWarmSetsPortfolio` (`44` budgets) and `thirtyTierHierarchy` (`30` tiers),
- All 4 `elevenTablesSharedSlope*` ceilings, all 4 `warmSetsSlope*` ceilings, and `.infinity`. -/
theorem forty_eight_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
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
    (fortyEightSharedPortfolio.length = 48 ∧
     fortyEightSharedPortfolio.Pairwise (· < ·) ∧
     ∀ K ∈ fortyEightSharedPortfolio, K < 900_719_925_474 ∧
       ∃ submission : InitE.Submission,
         submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (fortyEightBaselineWarmSetsPortfolio.length = 48 ∧
     fortyEightBaselineWarmSetsPortfolio.Pairwise (· < ·) ∧
     ∀ K ∈ fortyEightBaselineWarmSetsPortfolio, K < 900_719_925_474 ∧
       InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (allFiftyTwoSharedBudgets.length = 52 ∧
     allFiftyTwoSharedBudgets.Pairwise (· < ·) ∧
     ∀ K ∈ allFiftyTwoSharedBudgets, K < 900_719_925_474 ∧
       InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (∀ K ∈ fortyFourWarmSetsPortfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (∀ K ∈ thirtyTierHierarchy, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3UnrolledK) (.finite elevenTablesSharedSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3K) (.finite elevenTablesSharedSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5UnrolledK) (.finite elevenTablesSharedSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5K) (.finite elevenTablesSharedSlope5K) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope3UnrolledK) (.finite warmSetsSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope3K) (.finite warmSetsSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope5UnrolledK) (.finite warmSetsSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK warmSetsSlope5K) (.finite warmSetsSlope5K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity := by
  have hcert9 := warm_sets_forty_four_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_u128
  have hc1212 : CertificateAt 1212035192 := hcert9.1
  have hc48 := forty_eight_certified_non_vacuous_and_tight hc1212
  have h48_sub : ∀ K ∈ fortyEightSharedPortfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K) := by
    intro K hK
    have h := submission_certificate_non_vacuous_and_tight hc1212 K hK (baselineWithFiniteK K) rfl
    exact ⟨h.1, baselineWithFiniteK K, rfl, h.2⟩
  have h48_base : ∀ K ∈ fortyEightBaselineWarmSetsPortfolio, K < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
    intro K hK
    have hbnd : ∀ x ∈ fortyEightBaselineWarmSetsPortfolio, 1212035192 ≤ x ∧ x < 900_719_925_474 := by decide
    have hb := hbnd K hK
    exact ⟨hb.2, certificate_lift_non_vacuous_and_tight _ K hb.1 hc1212⟩
  have h52_cert : ∀ K ∈ allFiftyTwoSharedBudgets, K < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
    intro K hK
    have hbnd : ∀ x ∈ allFiftyTwoSharedBudgets, 1212035192 ≤ x ∧ x < 900_719_925_474 := by decide
    have hb := hbnd K hK
    exact ⟨hb.2, certificate_lift_non_vacuous_and_tight _ K hb.1 hc1212⟩
  exact ⟨hc1212,
    ⟨hc48.1, hc48.2.1, h48_sub⟩,
    ⟨by decide, by decide, h48_base⟩,
    ⟨by decide, by decide, h52_cert⟩,
    hcert9.2.1.2.2,
    hcert9.2.2.2.2.2.1,
    (hc48.2.2 elevenTablesSharedSlope3UnrolledK (by decide)).2,
    (hc48.2.2 elevenTablesSharedSlope3K (by decide)).2,
    (hc48.2.2 elevenTablesSharedSlope5UnrolledK (by decide)).2,
    (hc48.2.2 elevenTablesSharedSlope5K (by decide)).2,
    hcert9.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 10 (`non_vacuous_and_tight`, **Master Wave 5 (`W5_130`) Self-Contained `PanToWordNoStubCall`, Eleven-Table Shared Absorption (`kPanElevenTablesShared = 156_088_992_805`) & 48-Budget Campaign Certificate**):
Simultaneously unites:
- Unconditional frontend `WordNoStubCall` and user function label (`≥ 64`) guarantees from
  `PanToWordNoStubCall` (`panToWord_NoStubCall`, `panToWord_names`, `tgtGood_rejects_stub`,
  `tgtGood_accepts`, `wordNoStubCall_tight`) together with `LabToTarget.removeLabels` clean-section
  preservation (`panToTarget_sections_clean`, `panToTarget_sections_length`, `StackNoSt`, `FlattenVisitsSt`),
- Shared 11-table budget absorption (`blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571`), attainable
  storage corner (`(21 * S * S + 130 * M * S) / 840 = 151_929_428_571`), `kPanElevenTablesShared = 156_088_992_805`
  (saving `11_342_996_533` over `kPanElevenTables`), tight 12-tx feasible bracket
  (`155_688_931_265 ≤ kPanElevenTablesShared = 156_088_992_805`, gap `400_061_540 < 0.26%`),
  `5×` Yukon margin (`120_274_961_449`), and `6×` impossibility,
- Warm access-set rollback (`ev+168` / `ev+176`, `kPanWarmSets = 161_763_589_338`), distinct-delete
  payment under `H2`, and per-tx EIP-7825 caps (`d_t ≤ 7_989`, `a + 19 ≤ 5_611`, `n_blk ≤ 66_666`),
- Concrete `InitE.Certificate submission (.finite K)` (`submission = baselineWithFiniteK K`) across
  all **48 budgets** in `fortyEightSharedPortfolio`, all **48 budgets** in `fortyEightBaselineWarmSetsPortfolio`,
  all **52 budgets** in `allFiftyTwoSharedBudgets`, all **44 budgets** in `fortyFourWarmSetsPortfolio`,
  `fortyEightSharedClaims` `≤ 128`-byte compliance, and purified `.Solver` module path admission (`0` `Bounded*` imports). -/
theorem master_pan_to_word_no_stub_call_eleven_tables_shared_and_forty_eight_budget_campaign_certificate_non_vacuous_and_tight
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
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hblk : 40 * blk ≤ B * B) (hloc_b : 84 * loc ≤ M * B)
    (hu2 : 21 * t2 ≤ 5 * 7989 * u2) (hu3 : 30 * t3 ≤ 5 * 5611 * u3)
    (hu4 : 60 * t4 ≤ (M + 2280) * u4)
    (n_f k_f a n_blk a_c n_c d_t w_t d_del p_del q_del w_del minutes : Nat)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (htx : 21 * d_t + w_t ≤ M)
    (ha_tx : 30 * a ≤ 167772) (hn_blk : 30 * n_blk ≤ 2000000)
    (ha_c : a_c ≤ 5611) (hn_c : n_c ≤ 66666)
    (H2 : p_del + cycleUnits * q_del ≤ w_del)
    (not_timeOut_u128 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    (∀ y ∈ panToWordCompileProgHOL arch panProg, WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ panToWordCompileProgHOL arch panProg, 64 ≤ y.1) ∧
    ¬ TgtGood (some storeConstsStubLocation) ∧
    (TgtGood (some 0) ∧ TgtGood (some 64) ∧ ¬ TgtGood none) ∧
    (WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some storeConstsStubLocation) [] none) = false ∧
     WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true) ∧
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
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (40 * 100_000_000_000 ≤ S * S ∧ 84 * 3_994_571_428 ≤ M * S ∧
      (21 * S * S + 130 * M * S) / 840 = 151_929_428_571) ∧
    (kPanElevenTablesShared = 156_088_992_805 ∧
      kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
      400_061_540 * 10000 < 26 * 156_088_992_805 ∧
      400_061_540 * 10000 < 26 * 155_688_931_265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) ∧
    (truncDels (warmN (enter n_f) k_f) = k_f ∧
      (warmN (enter n_f) k_f).size - truncDels (warmN (enter n_f) k_f) = n_f) ∧
    (8 * d_del * p_del + 13 * d_del * q_del ≤ 8 * d_del * w_del ∧
      8 * d_del * w_del + 13 * d_del * 0 = 8 * d_del * w_del) ∧
    d_t ≤ 7989 ∧
    a + 19 ≤ 5611 ∧
    n_blk ≤ 66666 ∧
    truncTicks a_c n_c ≤ 1870314630 ∧
    kPanWarmSets = 161_763_589_338 ∧
    fortyEightSharedPortfolio.length = 48 ∧
    fortyEightSharedPortfolio.Pairwise (· < ·) ∧
    (∀ K ∈ fortyEightSharedPortfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    fortyEightBaselineWarmSetsPortfolio.length = 48 ∧
    (∀ K ∈ fortyEightBaselineWarmSetsPortfolio, K < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    allFiftyTwoSharedBudgets.length = 52 ∧
    (∀ K ∈ allFiftyTwoSharedBudgets, K < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (fortyEightSharedPortfolio.map (fun k_b => yukonScore k_b minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ fortyEightSharedClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3UnrolledK) (.finite elevenTablesSharedSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3K) (.finite elevenTablesSharedSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5UnrolledK) (.finite elevenTablesSharedSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5K) (.finite elevenTablesSharedSlope5K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    yukonScore elevenTablesSharedSlope3K minutes - yukonScore elevenTablesSharedSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore elevenTablesSharedSlope5K minutes - yukonScore elevenTablesSharedSlope5UnrolledK minutes = 138_000_000 ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hcert9 := forty_eight_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_u128
  have hint11 := integrated_master_non_vacuous_and_tight hcert9.1 n_f k_f d_del p_del q_del w_del H2
  have hw_aud := guest_warm_access_set_and_rollback_bound_complete_audit_non_vacuous_and_tight
    n_f k_f a n_blk a_c n_c ha_tx hn_blk ha_c hn_c
  have hsc48 := forty_eight_shared_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes 0
  have hcl48 := (forty_eight_shared_claims_valid_and_within_128_bytes_non_vacuous_and_tight 1).2.2.1
  have hts_gaps := eleven_tables_shared_target_budgets_and_warm_sets_gaps_non_vacuous_and_tight 0 minutes 0
  exact ⟨panToWord_NoStubCall arch panProg,
    panToWord_names arch panProg,
    tgtGood_rejects_stub,
    tgtGood_accepts,
    wordNoStubCall_tight,
    panToTarget_sections_clean arch panProg wc cAsm perf sc dc mh sp off ic pos labs ffis L' labs' hpan,
    panToTarget_sections_length arch panProg wc cAsm perf sc dc mh sp off ic pos labs ffis L' labs' hpan,
    ⟨u_stackRemoveComp j bd ptr p hp, not_visits_of_StackNoSt p hp⟩,
    shared_absorption_non_vacuous_and_tight B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc_b hu2 hu3 hu4,
    shared_corner_non_vacuous_and_tight,
    kPan_val_non_vacuous_and_tight,
    bracket_non_vacuous_and_tight,
    five_margin_non_vacuous_and_tight,
    six_fails_non_vacuous_and_tight,
    hint11.1,
    hint11.2.1,
    dx_le d_t w_t htx,
    hw_aud.2.2.2.1,
    hw_aud.2.2.2.2.2.1,
    hw_aud.2.2.2.2.2.2.1,
    hw_aud.2.2.2.2.2.2.2.2.2.1,
    hcert9.2.1.1,
    hcert9.2.1.2.1,
    hcert9.2.1.2.2,
    hcert9.2.2.1.1,
    hcert9.2.2.1.2.2,
    hcert9.2.2.2.1.1,
    hcert9.2.2.2.1.2.2,
    hsc48.1,
    hcl48,
    hcert9.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hts_gaps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hts_gaps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by decide,
    by decide,
    rfl⟩

#print axioms pan_to_word_no_stub_call_and_user_names_complete_audit_non_vacuous_and_tight
#print axioms loop_to_word_and_optimiser_tgt_ok_preservation_non_vacuous_and_tight
#print axioms eleven_tables_shared_budget_absorption_and_bracket_complete_audit_non_vacuous_and_tight
#print axioms eleven_tables_shared_target_budgets_and_warm_sets_gaps_non_vacuous_and_tight
#print axioms forty_eight_budget_portfolio_exact_insertion_and_order_non_vacuous_and_tight
#print axioms eleven_tables_shared_tiers_interleaved_strict_ordering_non_vacuous_and_tight
#print axioms forty_eight_shared_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight
#print axioms forty_eight_shared_claims_valid_and_within_128_bytes_non_vacuous_and_tight
#print axioms forty_eight_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
#print axioms master_pan_to_word_no_stub_call_eleven_tables_shared_and_forty_eight_budget_campaign_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth
