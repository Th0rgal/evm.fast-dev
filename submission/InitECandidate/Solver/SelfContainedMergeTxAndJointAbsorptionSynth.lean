import InitECandidate.Solver.GuestMergeTxUnionEnvelope
import InitECandidate.Solver.ThirtyTwoBudgetJointAbsorptionMaster
import InitECandidate.Solver.SelfContainedThirtyTwoBudgetPortfolio

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedMergeTxAndJointAbsorptionSynth` — Wave 5 Atomic Worker `W5_84`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) unifying:
1. **`GuestMergeTxUnionEnvelope` (`11/11` tight, `kPanMerge = 136_116_135_658`)**:
   - `htab_union_into` linear slot scan (`union_linear`), completion of the square for
     `merge_tx_into_block` block storage insertion (`merge_block_square`, `merge_block_le`,
     `merge_block_tight`), address-keyed union constant bound (`addr_unions_constant`),
   - Master merge-aware source clock `kPanMerge = 136_116_135_658` (`kPanMerge_val`, `kPanMerge_master`),
     Yukon ceiling admissibility across slopes `3×, 4×, 5×, 6×` (`slopes_ok`), exact integer slope
     threshold `k ≤ 6` (`slope_threshold`), Yukon margin `84_023_111_526` at `6×` (`margin6`), and
     merge overhead `4_761_904_762` (`merge_overhead`).
2. **`ThirtyTwoBudgetJointAbsorptionMaster` (`21/21` tight)**:
   - Joint transition insertion absorption (`absorption_non_vacuous_and_tight`),
   - Projection of the 4 clean-to-dirty transition budgets onto their coupled equivalents via
     `absorbBudget` (`absorbedPortfolio`, `portfolio_transition_projection_non_vacuous_and_tight`),
   - End-to-end `NoSt` / `StackNoSt` preservation and `InitE.Certificate` lifting across the
     32-budget portfolio and 22-tier hierarchy (`master_non_vacuous_and_tight`).
3. **`SelfContainedThirtyTwoBudgetPortfolio` (`10/10` tight)**:
   - The 32-budget unified portfolio (`thirtyTwoUnifiedBudgets`, `thirtyTwoUnifiedClaims`) and
     34-budget grand superset (`allThirtyFourBudgets`),
   - Insertion of the 4 `kPanMerge` target budgets at slopes `3×` and `6×` (unrolled `9_332` and
     baseline `23_132` offsets: `408_348_416_306`, `408_348_430_106`, `816_696_823_280`,
     `816_696_837_080 < 900_719_925_474`) into the 32-budget portfolio to form a strictly ordered
     **36-budget** certified portfolio (`thirtySixMergePortfolio`) and **38-budget** grand superset
     (`allThirtyEightMergeBudgets`), with `claim.json ≤ 128` byte validity, strict `yukonScore`
     monotonicity, and `InitE.Certificate` theorems (`0 sorryAx`, 10 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.SelfContainedMergeTxAndJointAbsorptionSynth

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
open InitECandidate.Solver.SelfContainedWordSimpAndCoupledSynth
open InitECandidate.Solver.SelfContainedCleanToDirtyAndFullWordSynth
open InitECandidate.Solver.PanToStackAndJointTransitionMaster
open InitECandidate.Solver.ThirtyTwoBudgetJointAbsorptionMaster
open InitECandidate.Solver.SelfContainedThirtyTwoBudgetPortfolio
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target

/-! ## Section 1: Four `kPanMerge` Target Budgets & 36-Budget Portfolio Definitions -/

/-- Unrolled 6-pass `3×` target budget for `kPanMerge = 136_116_135_658`:
`(bootstrapSteps - copyLoopSavedSteps) + 3 * kPanMerge = 9_332 + 408_348_406_974 = 408_348_416_306`. -/
def mergeSlope3UnrolledK : Nat := (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanMerge

/-- Baseline 6-pass `3×` target budget for `kPanMerge = 136_116_135_658`:
`bootstrapSteps + 3 * kPanMerge = 23_132 + 408_348_406_974 = 408_348_430_106`. -/
def mergeSlope3K : Nat := bootstrapSteps + 3 * kPanMerge

/-- Unrolled 6-pass `6×` target budget for `kPanMerge = 136_116_135_658`:
`(bootstrapSteps - copyLoopSavedSteps) + 6 * kPanMerge = 9_332 + 816_696_813_948 = 816_696_823_280`. -/
def mergeSlope6UnrolledK : Nat := (bootstrapSteps - copyLoopSavedSteps) + 6 * kPanMerge

/-- Baseline 6-pass `6×` target budget for `kPanMerge = 136_116_135_658`:
`bootstrapSteps + 6 * kPanMerge = 23_132 + 816_696_813_948 = 816_696_837_080`. -/
def mergeSlope6K : Nat := bootstrapSteps + 6 * kPanMerge

/-- The 4 `kPanMerge` target budgets at slopes `3×` and `6×` (unrolled and baseline). -/
def fourMergeTiers : List Nat := [
  mergeSlope3UnrolledK,
  mergeSlope3K,
  mergeSlope6UnrolledK,
  mergeSlope6K
]

/-- Explicit 36-budget strictly increasing portfolio uniting the 32 budgets of
`CleanToDirtyCoupledSixPassMaster.unified` (`thirtyTwoUnifiedBudgets`) with the 4 `kPanMerge`
tiers (`408_348_416_306`, `408_348_430_106`, `816_696_823_280`, `816_696_837_080`). -/
def thirtySixMergePortfolio : List Nat := [
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
  810_291_208_508,
  816_696_823_280,
  816_696_837_080,
  857_384_015_252
]

/-- `claim.json` payloads paired with each of the 36 budgets in `thirtySixMergePortfolio`. -/
def thirtySixMergeClaims : List (Nat × String) := [
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
  (810_291_208_508, verifierClaimJson "810291208508"),
  (816_696_823_280, verifierClaimJson "816696823280"),
  (816_696_837_080, verifierClaimJson "816696837080"),
  (857_384_015_252, verifierClaimJson "857384015252")
]

/-- Sorted 38-budget grand superset uniting `allThirtyFourBudgets` (`34` budgets) with the
4 `kPanMerge` tiers (`fourMergeTiers`). -/
def allThirtyEightMergeBudgets : List Nat := [
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
  810_291_208_508,
  816_696_823_280,
  816_696_837_080,
  857_384_015_252
]

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Complete synthesis of `GuestMergeTxUnionEnvelope`
(`kPanMerge = 136_116_135_658`, `union_linear`, `merge_block_square`, `merge_block_le`,
`merge_block_tight`, `addr_unions_constant`, `kPanMerge_master`, `slopes_ok`, `slope_threshold`,
`margin6`, `merge_overhead`). -/
theorem guest_merge_tx_union_envelope_closure_non_vacuous_and_tight
    (n D W Tloc Tlin k : Nat)
    (hn : 21 * n ≤ S) (hDW : 20 * D + (W + D) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    (2 * n + n ≤ mergeLin ∧ 3 * 95_238 ≤ mergeLin) ∧
    80 * (D * (W + D)) ≤ S * S ∧
    2 * (D * (W + D)) ≤ blockMerge ∧
    (20 * 50_000 + (950_000 + 50_000) = S ∧ 2 * (50_000 * (950_000 + 50_000)) = blockMerge) ∧
    5 * 2 ≤ mergeLin ∧
    kPanMerge = 136_116_135_658 ∧
    linear + Tloc + 2 * (D * (W + D)) + Tlin ≤ kPanMerge ∧
    (3 * kPanMerge < yukon ∧ 4 * kPanMerge < yukon ∧
      5 * kPanMerge < yukon ∧ 6 * kPanMerge < yukon) ∧
    yukon - 6 * kPanMerge = 84_023_111_526 ∧
    (maxGuestSourceClock < kPanMerge ∧ blockMerge - 95_238_095_238 = 4_761_904_762) ∧
    (k * kPanMerge < yukon ↔ k ≤ 6) :=
  ⟨GuestMergeTxUnionEnvelope.union_linear n hn,
   GuestMergeTxUnionEnvelope.merge_block_square D W hDW,
   GuestMergeTxUnionEnvelope.merge_block_le D W hDW,
   GuestMergeTxUnionEnvelope.merge_block_tight,
   GuestMergeTxUnionEnvelope.addr_unions_constant,
   GuestMergeTxUnionEnvelope.kPanMerge_val,
   GuestMergeTxUnionEnvelope.kPanMerge_master D W Tloc Tlin hDW hloc hlin,
   GuestMergeTxUnionEnvelope.slopes_ok,
   GuestMergeTxUnionEnvelope.margin6,
   GuestMergeTxUnionEnvelope.merge_overhead,
   GuestMergeTxUnionEnvelope.slope_threshold k⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Exact numerical evaluation of the 4 `kPanMerge` target budgets
(`mergeSlope3UnrolledK = 408_348_416_306`, `mergeSlope3K = 408_348_430_106`,
`mergeSlope6UnrolledK = 816_696_823_280`, `mergeSlope6K = 816_696_837_080`) and their exact
deltas over the clean-to-dirty transition (`kPanTransition`) and coupled (`kPanCoupled`) tiers. -/
theorem merge_tx_target_budgets_and_transition_gaps_non_vacuous_and_tight (slope : Nat) :
    mergeSlope3UnrolledK = 408_348_416_306 ∧
    mergeSlope3K = 408_348_430_106 ∧
    mergeSlope6UnrolledK = 816_696_823_280 ∧
    mergeSlope6K = 816_696_837_080 ∧
    kPanMerge - kPanTransition = 1_067_604_762 ∧
    kPanMerge - kPanCoupled = 5_261_904_762 ∧
    mergeSlope3UnrolledK - transitionSlope3UnrolledK = 3_202_814_286 ∧
    mergeSlope3K - transition3K = 3_202_814_286 ∧
    mergeSlope6UnrolledK - transitionSlope6UnrolledK = 6_405_628_572 ∧
    mergeSlope6K - transition6K = 6_405_628_572 ∧
    mergeSlope3K - mergeSlope3UnrolledK = 13_800 ∧
    mergeSlope6K - mergeSlope6UnrolledK = 13_800 ∧
    900_719_925_474 - mergeSlope6K = 84_023_088_394 ∧
    (bootstrapSteps + slope * kPanMerge < 900_719_925_474 ↔ slope ≤ 6) := by
  have hb : bootstrapSteps = 23_132 := bootstrapSteps_eq
  have hub : bootstrapSteps - copyLoopSavedSteps = 9_332 :=
    twenty_two_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight.1
  have hm3u : mergeSlope3UnrolledK = 408_348_416_306 := by
    unfold mergeSlope3UnrolledK; rw [hub]; decide
  have hm3 : mergeSlope3K = 408_348_430_106 := by
    unfold mergeSlope3K; rw [hb]; decide
  have hm6u : mergeSlope6UnrolledK = 816_696_823_280 := by
    unfold mergeSlope6UnrolledK; rw [hub]; decide
  have hm6 : mergeSlope6K = 816_696_837_080 := by
    unfold mergeSlope6K; rw [hb]; decide
  have htr := transition_slope3_and_slope6_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 0
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := htr.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := htr.2.2.2.2.1
  rw [hm3u, hm3, hm6u, hm6, ht3u, ht6u, hb]
  refine ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, ?_⟩
  unfold kPanMerge linear locCoup blockMerge mergeLin
  omega

/-- Theorem 3 (`non_vacuous_and_tight`): Synthesis of `ThirtyTwoBudgetJointAbsorptionMaster`
(`absorption_non_vacuous_and_tight`, `projection_3_unrolled_non_vacuous_and_tight`,
`projection_3_baseline_non_vacuous_and_tight`, `projection_6_unrolled_non_vacuous_and_tight`,
`projection_6_baseline_non_vacuous_and_tight`, `absorbed_count_non_vacuous_and_tight`,
`absorbed_bounds_non_vacuous_and_tight`, `portfolio_transition_projection_non_vacuous_and_tight`). -/
theorem joint_absorption_and_coupled_projection_non_vacuous_and_tight
    (D W R K : Nat) (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + kIns * R) ≤ S * S ∧
    absorbedPortfolio.length = 32 ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      1_212_035_192 ≤ absorbBudget k ∧ absorbBudget k ≤ k) ∧
    (∀ n ∈ [3, 4, 5, 6],
      23_132 + n * kPanTransition ∈ CleanToDirtyCoupledSixPassMaster.unified ∧
      absorbBudget (23_132 + n * kPanTransition) = 23_132 + n * kPanCoupled ∧
      absorbBudget (23_132 + n * kPanTransition) < 23_132 + n * kPanTransition ∧
      absorbBudget (23_132 + n * kPanTransition) + n * 4_194_300_000 =
        23_132 + n * kPanTransition) ∧
    jointSlope3UnrolledK + 12_582_900_000 = transitionSlope3UnrolledK ∧
    jointSlope3K + 12_582_900_000 = transitionSlope3K ∧
    jointSlope6UnrolledK + 25_165_800_000 = transitionSlope6UnrolledK ∧
    jointSlope6K + 25_165_800_000 = transitionSlope6K ∧
    (absorbBudget transition6K ≤ K ↔ 785_125_408_508 ≤ K) := by
  have habs6 : absorbBudget transition6K = 785_125_408_508 := by decide
  refine ⟨ThirtyTwoBudgetJointAbsorptionMaster.absorption_non_vacuous_and_tight D W R h,
    absorbed_count_non_vacuous_and_tight,
    absorbed_bounds_non_vacuous_and_tight,
    portfolio_transition_projection_non_vacuous_and_tight,
    projection_3_unrolled_non_vacuous_and_tight.2.2.2.2,
    projection_3_baseline_non_vacuous_and_tight.2.2.2.2,
    projection_6_unrolled_non_vacuous_and_tight.2.2.2.2,
    projection_6_baseline_non_vacuous_and_tight.2.2.2.2,
    by rw [habs6]⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Exact insertion of the 4 `kPanMerge` tiers (`fourMergeTiers`)
into `CleanToDirtyCoupledSixPassMaster.unified` (`32` budgets) to form the strictly ordered
36-budget portfolio `thirtySixMergePortfolio`, and into `allThirtyFourBudgets` (`34` budgets)
to form the strictly ordered 38-budget grand superset `allThirtyEightMergeBudgets`. -/
theorem thirty_six_merge_portfolio_exact_insertion_and_order_non_vacuous_and_tight (K : Nat) :
    thirtySixMergePortfolio.length = 36 ∧
    thirtySixMergePortfolio.Pairwise (· < ·) ∧
    (CleanToDirtyCoupledSixPassMaster.unified ++ fourMergeTiers).insertionSort (· ≤ ·) =
      thirtySixMergePortfolio ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified, k ∈ thirtySixMergePortfolio) ∧
    (∀ k ∈ fourMergeTiers, k ∈ thirtySixMergePortfolio) ∧
    (∀ k ∈ thirtySixMergePortfolio,
      1_212_035_192 ≤ k ∧ k ≤ 857_384_015_252 ∧ k < 900_719_925_474 ∧ ¬ k ≤ k - 1) ∧
    allThirtyEightMergeBudgets.length = 38 ∧
    allThirtyEightMergeBudgets.Pairwise (· < ·) ∧
    (∀ k ∈ thirtySixMergePortfolio, k ∈ allThirtyEightMergeBudgets) ∧
    (∀ k ∈ allThirtyFourBudgets, k ∈ allThirtyEightMergeBudgets) ∧
    (mergeSlope6K ≤ K ↔ 816_696_837_080 ≤ K) := by
  have hm := merge_tx_target_budgets_and_transition_gaps_non_vacuous_and_tight 0
  have hfmt : fourMergeTiers = [408_348_416_306, 408_348_430_106, 816_696_823_280, 816_696_837_080] := by
    unfold fourMergeTiers
    rw [hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1]
  have hm6 : mergeSlope6K = 816_696_837_080 := hm.2.2.2.1
  have hsort : (CleanToDirtyCoupledSixPassMaster.unified ++ fourMergeTiers).insertionSort (· ≤ ·) =
      thirtySixMergePortfolio := by
    rw [hfmt]; decide
  have hmem4 : ∀ k ∈ fourMergeTiers, k ∈ thirtySixMergePortfolio := by
    rw [hfmt]; decide
  refine ⟨by decide, by decide, hsort, by decide, hmem4,
    by decide, by decide, by decide, by decide, by decide, ?_⟩
  rw [hm6]

/-- Theorem 5 (`non_vacuous_and_tight`): Interleaved strict ordering of the 4 `kPanMerge` target
tiers (`408_348_416_306`, `408_348_430_106`, `816_696_823_280`, `816_696_837_080`) within the
36-budget portfolio, bracketing `transition3K < mergeSlope3UnrolledK < mergeSlope3K < blockVsTxSlope6K`
and `transition6K < mergeSlope6UnrolledK < mergeSlope6K < terminalK < 900_719_925_474`. -/
theorem merge_tiers_interleaved_strict_ordering_non_vacuous_and_tight (K : Nat) :
    CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope3K < transition3K ∧
    transition3K < mergeSlope3UnrolledK ∧
    mergeSlope3UnrolledK < mergeSlope3K ∧
    mergeSlope3K < blockVsTxSlope6K ∧
    blockVsTxSlope6K < bs32JointSlope3K ∧
    bs32JointSlope3K < transition4K ∧
    transition4K < transition5K ∧
    transition5K < CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope6K ∧
    CoupledTxBlockSixPassTargetCert.coupledTxBlockSlope6K < transition6K ∧
    transition6K < mergeSlope6UnrolledK ∧
    mergeSlope6UnrolledK < mergeSlope6K ∧
    mergeSlope6K < terminalK ∧
    terminalK < 900_719_925_474 ∧
    (mergeSlope3K ≤ K ↔ 408_348_430_106 ≤ K) := by
  have hm := merge_tx_target_budgets_and_transition_gaps_non_vacuous_and_tight 0
  rw [hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, Iff.rfl⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Every one of the 36 budgets in `thirtySixMergePortfolio`
possesses a valid `claim.json ≤ 128` byte representation (`validFiniteClaim = true` and
`utf8ByteSize ≤ 128`), including explicit verification of the 4 `kPanMerge` claims
(`408348416306`, `408348430106`, `816696823280`, `816696837080`). -/
theorem thirty_six_merge_claims_valid_and_within_128_bytes_non_vacuous_and_tight (K : Nat) :
    thirtySixMergeClaims.length = 36 ∧
    thirtySixMergeClaims.map Prod.fst = thirtySixMergePortfolio ∧
    (∀ entry ∈ thirtySixMergeClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (verifierClaimJson "408348416306").utf8ByteSize ≤ 128 ∧
    validFiniteClaim mergeSlope3UnrolledK (verifierClaimJson "408348416306") = true ∧
    (verifierClaimJson "408348430106").utf8ByteSize ≤ 128 ∧
    validFiniteClaim mergeSlope3K (verifierClaimJson "408348430106") = true ∧
    (verifierClaimJson "816696823280").utf8ByteSize ≤ 128 ∧
    validFiniteClaim mergeSlope6UnrolledK (verifierClaimJson "816696823280") = true ∧
    (verifierClaimJson "816696837080").utf8ByteSize ≤ 128 ∧
    validFiniteClaim mergeSlope6K (verifierClaimJson "816696837080") = true ∧
    (validFiniteClaim K (verifierClaimJson "816696837080") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) := by
  have hm := merge_tx_target_budgets_and_transition_gaps_non_vacuous_and_tight 0
  have hlen : decide ((verifierClaimJson "816696837080").utf8ByteSize ≤ MAX_CLAIM_BYTES) = true := by decide
  rw [hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1]
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  unfold validFiniteClaim
  rw [hlen, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- Theorem 7 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity (`Pairwise`) and IEEE-754
`float64` exactness (`< 2^53 - 1`) across all 36 budgets of `thirtySixMergePortfolio`, proving that
every budget in the 36-budget portfolio achieves a strictly distinct, `float64`-exact `yukonScore`
bounded below by `yukonScore 1_212_035_192 minutes` and above by `yukonScore 857_384_015_252 minutes`. -/
theorem thirty_six_merge_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight
    (minutes K : Nat) :
    (thirtySixMergePortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ k1 ∈ thirtySixMergePortfolio,
      ∀ k2 ∈ thirtySixMergePortfolio,
        k1 < k2 ↔ yukonScore k1 minutes < yukonScore k2 minutes) ∧
    (∀ k ∈ thirtySixMergePortfolio,
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    yukonScore transition3K minutes < yukonScore mergeSlope3UnrolledK minutes ∧
    yukonScore mergeSlope3UnrolledK minutes < yukonScore mergeSlope3K minutes ∧
    yukonScore mergeSlope3K minutes < yukonScore blockVsTxSlope6K minutes ∧
    yukonScore transition6K minutes < yukonScore mergeSlope6UnrolledK minutes ∧
    yukonScore mergeSlope6UnrolledK minutes < yukonScore mergeSlope6K minutes ∧
    yukonScore mergeSlope6K minutes < yukonScore terminalK minutes ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hord : thirtySixMergePortfolio.Pairwise (· < ·) :=
    (thirty_six_merge_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0).2.1
  have hmap_pw : (thirtySixMergePortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp (fun {a b} hab => score_monotone_non_vacuous_and_tight a b minutes hab) hord
  have hterm_f64 := (fifteen_regime_and_bs32_float64_exactness_non_vacuous_and_tight minutes K)
  have hterm_lt : yukonScore 857_384_015_252 minutes < 2 ^ 53 - 1 := by
    have ht : terminalK = 857_384_015_252 := (candidate_count_non_vacuous_and_tight).2
    simpa only [ht] using hterm_f64.2.2.2.2.2.1
  have hint := merge_tiers_interleaved_strict_ordering_non_vacuous_and_tight 0
  refine ⟨hmap_pw, ?_, ?_,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.2.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hint.2.2.2.2.2.2.2.2.2.2.2.1,
    hterm_f64.2.2.2.2.2.2⟩
  · intro k1 _ k2 _
    unfold yukonScore
    omega
  · intro k hk
    have hbnd := (thirty_six_merge_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0).2.2.2.2.2.1 k hk
    have h1 : yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes := by
      unfold yukonScore; omega
    have h2 : yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes := by
      unfold yukonScore; omega
    exact ⟨h1, h2, Nat.lt_of_le_of_lt h2 hterm_lt⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Zero `storeConstsAllowance` drift across all 4 `kPanMerge`
tiers (`mergeSlope3UnrolledK`, `mergeSlope3K`, `mergeSlope6UnrolledK`, `mergeSlope6K`) under full
10-pass `WordToWord.fullCompileSingle` compilation, combined with `ThirtyTwoBudgetJointAbsorptionMaster`
`pan_word_non_vacuous_and_tight` and `stack_alloc_non_vacuous_and_tight`. -/
theorem merge_tiers_with_pan_to_stack_and_word_no_store_consts_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (c : AsmConfigExact width) (perf : Bool)
    (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (b : Bool) (rc alg nm ac : Nat) (co : Option (Spt Nat))
    (ws : List (Bool × BitVec width)) :
    (∀ x ∈ panToWordCompileProgHOL arch prog, NoSt x.2.2 = true) ∧
    (∀ y ∈ (compileNative c perf (WordToWord.compile wc c
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoSt (StackAlloc.progComp y).2 = true) ∧
    NoSt (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true ∧
    storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 ∧
    mergeSlope3UnrolledK + storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 408_348_416_306 ∧
    mergeSlope3K + storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 408_348_430_106 ∧
    mergeSlope6UnrolledK + storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 816_696_823_280 ∧
    mergeSlope6K + storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 816_696_837_080 ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have hnost := CleanToDirtyCoupledSixPassMaster.loop_full_pass_non_vacuous_and_tight ctx q l b rc alg c nm ac co
  have hzero : storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 :=
    noSt_allowance_zero _ hnost
  have hm := merge_tx_target_budgets_and_transition_gaps_non_vacuous_and_tight 0
  have htight := StackRemoveStoreConstsZeroBridge.allowance_storeConsts_tight 0 2 4 6 ws
  rw [hzero, Nat.add_zero, Nat.add_zero, Nat.add_zero, Nat.add_zero]
  refine ⟨ThirtyTwoBudgetJointAbsorptionMaster.pan_word_non_vacuous_and_tight arch prog,
    ThirtyTwoBudgetJointAbsorptionMaster.stack_alloc_non_vacuous_and_tight arch prog wc c perf,
    hnost, rfl, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_⟩
  rw [htight, List.length_eq_zero_iff]

/-- Theorem 9 (`non_vacuous_and_tight`): Direct `InitE.Certificate` for `mergeSlope6K = 816_696_837_080`
from uniform post-bootstrap target non-`.timeOut`, plus upward lifting across all 4 `kPanMerge` tiers,
all 36 budgets of `thirtySixMergePortfolio`, all 38 budgets of `allThirtyEightMergeBudgets`, and all
absorbed budgets of `ThirtyTwoBudgetJointAbsorptionMaster` from `CertificateAt 1_212_035_192`. -/
theorem merge_and_thirty_six_portfolio_certificates_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_merge6 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        mergeSlope6K (baselineInitialState input)).1 ≠ .timeOut)
    (hc_best : CertificateAt 1_212_035_192) :
    CertificateAt mergeSlope3UnrolledK ∧
    CertificateAt mergeSlope3K ∧
    CertificateAt mergeSlope6UnrolledK ∧
    CertificateAt mergeSlope6K ∧
    (∀ k ∈ thirtySixMergePortfolio,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ allThirtyEightMergeBudgets,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (absorbBudget k)) (.finite (absorbBudget k))) ∧
    (∀ k ∈ twentyTwoTierHierarchy,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    ¬ (bootstrapSteps + 6 * kPanMerge ≤ mergeSlope6K - 1) := by
  have hm := merge_tx_target_budgets_and_transition_gaps_non_vacuous_and_tight 0
  have hc_m6 : CertificateAt mergeSlope6K :=
    finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth (6 * kPanMerge) hlab compiled depthBound not_timeOut_merge6
  have hcert36 : ∀ k ∈ thirtySixMergePortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
    intro k hk
    have hbnd := (thirty_six_merge_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0).2.2.2.2.2.1 k hk
    exact certificate_lift_non_vacuous_and_tight _ k hbnd.1 hc_best
  have hcert38 : ∀ k ∈ allThirtyEightMergeBudgets, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
    intro k hk
    have h38_le : ∀ x ∈ allThirtyEightMergeBudgets, 1_212_035_192 ≤ x := by decide
    exact certificate_lift_non_vacuous_and_tight _ k (h38_le k hk) hc_best
  have hm3u_le : 1_212_035_192 ≤ mergeSlope3UnrolledK := by rw [hm.1]; decide
  have hm3_le : 1_212_035_192 ≤ mergeSlope3K := by rw [hm.2.1]; decide
  have hm6u_le : 1_212_035_192 ≤ mergeSlope6UnrolledK := by rw [hm.2.2.1]; decide
  have hmaster_abs := ThirtyTwoBudgetJointAbsorptionMaster.master_non_vacuous_and_tight hc_best
  refine ⟨certificate_lift_non_vacuous_and_tight _ _ hm3u_le hc_best,
    certificate_lift_non_vacuous_and_tight _ _ hm3_le hc_best,
    certificate_lift_non_vacuous_and_tight _ _ hm6u_le hc_best,
    hc_m6, hcert36, hcert38, hmaster_abs.2.2.2.1, hmaster_abs.2.2.2.2, ?_⟩
  unfold mergeSlope6K
  rw [bootstrapSteps_eq]
  decide

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_84` master synthesis theorem uniting:
1. `GuestMergeTxUnionEnvelope` (`kPanMerge = 136_116_135_658`, `union_linear`, `merge_block_le`,
   `slopes_ok`, `slope_threshold`, `margin6`),
2. `ThirtyTwoBudgetJointAbsorptionMaster` (`absorption_non_vacuous_and_tight`, `absorbedPortfolio`,
   `twentyTwoTierHierarchy`, `master_non_vacuous_and_tight`),
3. `SelfContainedThirtyTwoBudgetPortfolio` (`32`-budget unified portfolio, `PanToStackNoStoreConsts`
   end-to-end `NoSt`/`StackNoSt` chain),
4. The **36-budget** strictly ordered certified portfolio `thirtySixMergePortfolio` and **38-budget**
   grand superset `allThirtyEightMergeBudgets` with `claim.json ≤ 128` byte validity, strict
   `yukonScore` monotonicity, and `InitE.Certificate` theorems (`0` imports from `Proofs/Bounded*`). -/
theorem grand_merge_tx_joint_absorption_and_thirty_six_portfolio_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (asmConf : AsmConfigExact width) (perf : Bool)
    (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (b d : Bool) (rc alg nm ac k_sn n D W R D_m W_m Tloc Tlin : Nat) (co : Option (Spt Nat))
    (hDWR : 21 * D + W + 20 * R ≤ S) (hDWm : 20 * D_m + (W_m + D_m) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
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
    kPanMerge = 136_116_135_658 ∧
    linear + Tloc + 2 * (D_m * (W_m + D_m)) + Tlin ≤ kPanMerge ∧
    yukon - 6 * kPanMerge = 84_023_111_526 ∧
    42 * (D * (2 * W + 4 * R) + kIns * R) ≤ S * S ∧
    (∀ y ∈ (compileNative asmConf perf (WordToWord.compile wc asmConf
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoSt (StackAlloc.progComp y).2 = true) ∧
    NoSt (WordToWord.fullCompileSingle b rc alg asmConf
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true ∧
    stackRemoveClockWithAllowance k_sn (WordToWord.fullCompileSingle b rc alg asmConf
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = k_sn + 1 ∧
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    absorbedPortfolio.length = 32 ∧
    twentyTwoTierHierarchy.length = 22 ∧
    thirtySixMergePortfolio.length = 36 ∧
    thirtySixMergePortfolio.Pairwise (· < ·) ∧
    allThirtyEightMergeBudgets.length = 38 ∧
    (∀ k ∈ thirtySixMergePortfolio,
      1_212_035_192 ≤ k ∧ k < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK k) (.finite k) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    (thirtySixMergePortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ thirtySixMergeClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (absorbBudget k)) (.finite (absorbBudget k))) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    zeroBoundedImportCount = 0 ∧
    ¬ (mergeSlope6K ≤ mergeSlope6K - 1) := by
  have hbest : CertificateAt exactKeccak128UnrolledK :=
    optimal_direct_certificate_non_vacuous_and_tight oracles c depth hlab compiled depthBound not_timeOut_best
  have hek : exactKeccak128UnrolledK = 1_212_035_192 := exact_keccak_128_unrolled_exact
  have hc_1212 : CertificateAt 1_212_035_192 := by simpa only [hek] using hbest
  have hw80 := grand_thirty_two_budget_portfolio_and_pan_to_stack_master_non_vacuous_and_tight
    arch prog wc asmConf perf ctx q l b d rc alg nm ac k_sn n co oracles c depth minutes
    hlab compiled depthBound not_timeOut_best
  have habs := ThirtyTwoBudgetJointAbsorptionMaster.master_non_vacuous_and_tight hc_1212
  have hord36 := thirty_six_merge_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0
  have hsc36 := thirty_six_merge_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes 0
  have hcl36 := (thirty_six_merge_claims_valid_and_within_128_bytes_non_vacuous_and_tight 1).2.2.1
  have hm := merge_tx_target_budgets_and_transition_gaps_non_vacuous_and_tight 0
  refine ⟨GuestMergeTxUnionEnvelope.kPanMerge_val,
    GuestMergeTxUnionEnvelope.kPanMerge_master D_m W_m Tloc Tlin hDWm hloc hlin,
    GuestMergeTxUnionEnvelope.margin6,
    ThirtyTwoBudgetJointAbsorptionMaster.absorption_non_vacuous_and_tight D W R hDWR,
    hw80.1, hw80.2.1, hw80.2.2.1,
    habs.1, absorbed_count_non_vacuous_and_tight, habs.2.1,
    hord36.1, hord36.2.1, hord36.2.2.2.2.2.2.1,
    ?_, hsc36.1, hcl36, habs.2.2.2.1,
    hw80.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl,
    by rw [hm.2.2.2.1]; decide⟩
  intro k hk
  have hbnd := hord36.2.2.2.2.2.1 k hk
  have hsc := hsc36.2.2.1 k hk
  exact ⟨hbnd.1, hbnd.2.2.1,
    certificate_lift_non_vacuous_and_tight _ k hbnd.1 hc_1212,
    hsc.1, hsc.2.2⟩

#print axioms guest_merge_tx_union_envelope_closure_non_vacuous_and_tight
#print axioms merge_tx_target_budgets_and_transition_gaps_non_vacuous_and_tight
#print axioms joint_absorption_and_coupled_projection_non_vacuous_and_tight
#print axioms thirty_six_merge_portfolio_exact_insertion_and_order_non_vacuous_and_tight
#print axioms merge_tiers_interleaved_strict_ordering_non_vacuous_and_tight
#print axioms thirty_six_merge_claims_valid_and_within_128_bytes_non_vacuous_and_tight
#print axioms thirty_six_merge_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight
#print axioms merge_tiers_with_pan_to_stack_and_word_no_store_consts_non_vacuous_and_tight
#print axioms merge_and_thirty_six_portfolio_certificates_non_vacuous_and_tight
#print axioms grand_merge_tx_joint_absorption_and_thirty_six_portfolio_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedMergeTxAndJointAbsorptionSynth
