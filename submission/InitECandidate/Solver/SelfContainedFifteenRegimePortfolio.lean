import InitECandidate.Solver.SelfContainedMidPassesAndSloadSynth
import InitECandidate.Solver.Bs32DominanceSixPassTargetCert
import InitECandidate.Solver.UnrolledTwelveCandidatePortfolio

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedFifteenRegimePortfolio` — Wave 5 Atomic Worker `W5_66`

Self-contained 15-regime portfolio (`0` imports from `InitECandidate.Proofs.Bounded*`) unifying:
1. **`UnrolledTwelveCandidatePortfolio`**: The 12 unrolled and reduced target candidates
   (`1_212_035_192` up to `428_692_019_192`) plus the slope-12 endpoint `terminalK = 857_384_015_252 < 900_719_925_474`,
2. **`Bs32DominanceSixPassTargetCert`**: The 4 `bs32` probe dominance target regimes:
   - `bs32StandaloneSlope3K = 296_693_001_548`,
   - `bs32TotalSlope3K = 387_840_417_875`,
   - `bs32StandaloneSlope6K = 593_385_979_964`,
   - `bs32TotalSlope6K = 775_680_812_618`,
3. **`SelfContainedMidPassesAndSloadSynth`**: The 3 `JointBlockGas` regimes
   (`121_459_456_007 < 242_918_888_882 < 485_837_754_632`), the 4 `SloadProbe` envelope regimes
   (`610_978_715_738 < 610_978_730_738 < 677_645_382_458 < 677_645_397_458`), and the 6-pass
   `WordToWord` `midTailChain` `NoSt` / zero `storeConstsAllowance` synthesis (`0 sorryAx`, 10 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.SelfContainedFifteenRegimePortfolio

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
open InitECandidate.Solver.SelfContainedSixPassMaster (sixPassReducedK sixPassSlope six_pass_slope_reduction reduced_baseline_compatible)
open InitECandidate.Solver.SelfContainedSolutionCandidates
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.YukonVerifyScriptAudit
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.FourPassClockIsometryChain
open InitECandidate.Solver.SelfContainedQuadraticEnvelopeCert (C_sr_probe yukonFloat64StepCeiling)
open InitECandidate.Solver.SelfContainedSloadProbeEnvelope
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
open InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
open InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
open InitECandidate.Solver.GuestBlockVsTxHtabBounds
open InitECandidate.Solver.GuestJointBlockGasHtabBound
open InitECandidate.Solver.GuestDirtyWriteHtabDominance
open InitECandidate.Solver.PerTxEip7825TargetMasterK
open InitECandidate.Solver.RiscvSszFastRejectAndBootCert
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitECandidate.Solver.YukonFinalCandidateSelector (quadraticCollisionTargetK)
open InitECandidate.Solver.JointBlockGasSixPassMasterCert
open InitECandidate.Solver.SelfContainedMidPassesAndSloadSynth
open InitECandidate.Solver.Bs32DominanceSixPassTargetCert
open InitECandidate.Solver.ExactKeccakCopyLoopUnrolledCert
open InitECandidate.Solver.ExactKeccakSixPassReducedCert
open InitECandidate.Solver.SelfContainedTenCandidateHierarchy
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio
open Flapjack
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target

/-! ## Section 1: Fifteen-Regime Portfolio & Unified 24-Regime Catalog Definitions -/

/-- The 15 principal named regimes spanning from `exactKeccak128UnrolledK = 1_212_035_192`
through the `JointBlockGas`, `Bs32Dominance`, and `SloadProbe` envelopes up to
`terminalK = blockVsTxSlope12K = 857_384_015_252 < 900_719_925_474`. -/
def fifteenPrincipalRegimes : List Nat := [
  exactKeccak128UnrolledK,
  exactKeccak0UnrolledK,
  sixPassUnrolledCopyLoopK,
  sixPassReducedK,
  exactKeccak128CandidateK,
  isoReducedCopyLoopK,
  isoReducedCandidateK,
  exactKeccakCandidateK,
  push31NoGcCandidateK,
  jointBlockGasSlope3K,
  perTxSixPassTargetK,
  bs32StandaloneSlope3K,
  bs32TotalSlope3K,
  sloadProbeEnvelopeTargetK,
  terminalK
]

/-- Explicit numerical values of the 15 principal regimes. -/
def fifteenPrincipalBudgets : List Nat := [
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
  296_693_001_548,
  387_840_417_875,
  677_645_397_458,
  857_384_015_252
]

/-- The 4 `bs32` dominance target regimes from `Bs32DominanceSixPassTargetCert`. -/
def bs32FourRegimes : List Nat := [
  bs32StandaloneSlope3K,
  bs32TotalSlope3K,
  bs32StandaloneSlope6K,
  bs32TotalSlope6K
]

/-- The 3 joint block-gas regimes from `JointBlockGasSixPassMasterCert`. -/
def jointBlockGasThreeRegimes : List Nat := [
  jointBlockGasSlope3K,
  jointBlockGasSlope6K,
  jointBlockGasSlope12K
]

/-- The 4 SLOAD probe envelope regimes from `SelfContainedMidPassesAndSloadSynth`. -/
def sloadProbeFourRegimes : List Nat := [
  coldSloadProbeZeroOffsetK,
  coldSloadProbeEnvelopeTargetK,
  sloadProbeZeroOffsetK,
  sloadProbeEnvelopeTargetK
]

/-- Complete 24-regime sorted catalog uniting all 12 `UnrolledTwelveCandidatePortfolio` candidates,
the 3 `JointBlockGas` regimes, the 4 `Bs32Dominance` regimes, the 4 `SloadProbe` regimes, and `terminalK`. -/
def allTwentyFourRegimes : List Nat := [
  exactKeccak128UnrolledK,
  exactKeccak0UnrolledK,
  sixPassUnrolledCopyLoopK,
  sixPassReducedK,
  exactKeccak128CandidateK,
  isoReducedCopyLoopK,
  isoReducedCandidateK,
  exactKeccakCandidateK,
  push31NoGcCandidateK,
  jointBlockGasSlope3K,
  perTxSixPassTargetK,
  blockVsTxSlope3K,
  jointBlockGasSlope6K,
  bs32StandaloneSlope3K,
  bs32TotalSlope3K,
  blockVsTxSlope6K,
  jointBlockGasSlope12K,
  bs32StandaloneSlope6K,
  coldSloadProbeZeroOffsetK,
  coldSloadProbeEnvelopeTargetK,
  sloadProbeZeroOffsetK,
  sloadProbeEnvelopeTargetK,
  bs32TotalSlope6K,
  terminalK
]

/-- `claim.json` payloads paired with each of the 15 principal regimes. -/
def fifteenRegimeClaims : List (Nat × String) := [
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
  (296_693_001_548, verifierClaimJson "296693001548"),
  (387_840_417_875, verifierClaimJson "387840417875"),
  (677_645_397_458, verifierClaimJson "677645397458"),
  (857_384_015_252, verifierClaimJson "857384015252")
]

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Portfolio Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Exact evaluation and counts of the 15 principal regimes
(`fifteenPrincipalRegimes = fifteenPrincipalBudgets`), the 12 `UnrolledTwelveCandidatePortfolio`
candidates, the 4 `Bs32Dominance` regimes (`296_693_001_548`, `387_840_417_875`, `593_385_979_964`,
`775_680_812_618`), the 3 `JointBlockGas` regimes (`121_459_456_007`, `242_918_888_882`,
`485_837_754_632`), and the 4 `SloadProbe` regimes (`610_978_715_738`, `610_978_730_738`,
`677_645_382_458`, `677_645_397_458`), with sharp Yukon multiplier bound on the minimum regime. -/
theorem fifteen_regime_catalog_values_and_counts_non_vacuous_and_tight (m : Nat) :
    fifteenPrincipalRegimes.length = 15 ∧
    fifteenPrincipalRegimes = fifteenPrincipalBudgets ∧
    candidates.length = 12 ∧
    bs32FourRegimes = [296_693_001_548, 387_840_417_875, 593_385_979_964, 775_680_812_618] ∧
    jointBlockGasThreeRegimes = [121_459_456_007, 242_918_888_882, 485_837_754_632] ∧
    sloadProbeFourRegimes = [610_978_715_738, 610_978_730_738, 677_645_382_458, 677_645_397_458] ∧
    allTwentyFourRegimes.length = 24 ∧
    (m * exactKeccak128UnrolledK < yukon ↔ m ≤ 743) := by
  have hsload := complete_twelve_regime_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hcz : coldSloadProbeZeroOffsetK = 610_978_715_738 := hsload.2.2.2.2.2.2.1
  have hce : coldSloadProbeEnvelopeTargetK = 610_978_730_738 := hsload.2.2.2.2.2.2.2.1
  have hsz : sloadProbeZeroOffsetK = 677_645_382_458 := hsload.2.2.2.2.2.2.2.2.1
  have hse : sloadProbeEnvelopeTargetK = 677_645_397_458 := hsload.2.2.2.2.2.2.2.2.2.1
  have hek : exactKeccak128UnrolledK = 1_212_035_192 := exact_keccak_128_unrolled_exact
  refine ⟨by decide, ?_, by decide, by decide, by decide, ?_, by decide, ?_⟩
  · unfold fifteenPrincipalRegimes fifteenPrincipalBudgets
    rw [hse]
    decide
  · unfold sloadProbeFourRegimes
    rw [hcz, hce, hsz, hse]
  · rw [hek]
    unfold yukon
    omega

/-- Theorem 2 (`non_vacuous_and_tight`): Complete strict ordering of the 15 principal regimes from
`exactKeccak128UnrolledK = 1_212_035_192` up to `terminalK = 857_384_015_252 < 900_719_925_474`,
together with exact step-budget gaps and membership bounds (`1_212_035_192 ≤ k ≤ 857_384_015_252`). -/
theorem fifteen_principal_regimes_strict_ordering_non_vacuous_and_tight (K : Nat) :
    exactKeccak128UnrolledK < exactKeccak0UnrolledK ∧
    exactKeccak0UnrolledK < sixPassUnrolledCopyLoopK ∧
    sixPassUnrolledCopyLoopK < sixPassReducedK ∧
    sixPassReducedK < exactKeccak128CandidateK ∧
    exactKeccak128CandidateK < isoReducedCopyLoopK ∧
    isoReducedCopyLoopK < isoReducedCandidateK ∧
    isoReducedCandidateK < exactKeccakCandidateK ∧
    exactKeccakCandidateK < push31NoGcCandidateK ∧
    push31NoGcCandidateK < jointBlockGasSlope3K ∧
    jointBlockGasSlope3K < perTxSixPassTargetK ∧
    perTxSixPassTargetK < bs32StandaloneSlope3K ∧
    bs32StandaloneSlope3K < bs32TotalSlope3K ∧
    bs32TotalSlope3K < sloadProbeEnvelopeTargetK ∧
    sloadProbeEnvelopeTargetK < terminalK ∧
    terminalK < 900_719_925_474 ∧
    (∀ k ∈ fifteenPrincipalRegimes, exactKeccak128UnrolledK ≤ k ∧ k ≤ terminalK ∧ ¬ k ≤ k - 1) ∧
    (terminalK ≤ K ↔ 857_384_015_252 ≤ K) := by
  have hsload := complete_twelve_regime_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hse : sloadProbeEnvelopeTargetK = 677_645_397_458 := hsload.2.2.2.2.2.2.2.2.2.1
  have hcat : fifteenPrincipalRegimes = fifteenPrincipalBudgets :=
    (fifteen_regime_catalog_values_and_counts_non_vacuous_and_tight 0).2.1
  have hterm : terminalK = 857_384_015_252 := (candidate_count_non_vacuous_and_tight).2
  have hek : exactKeccak128UnrolledK = 1_212_035_192 := exact_keccak_128_unrolled_exact
  rw [hse]
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro k hk
    rw [hcat] at hk
    rw [hek, hterm]
    simp only [fifteenPrincipalBudgets, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hterm]

/-- Theorem 3 (`non_vacuous_and_tight`): Complete 24-regime strict ordering across all 12
`UnrolledTwelveCandidatePortfolio` candidates, the 3 `JointBlockGas` regimes (`121_459_456_007`,
`242_918_888_882`, `485_837_754_632`), the 4 `Bs32Dominance` regimes (`296_693_001_548`,
`387_840_417_875`, `593_385_979_964`, `775_680_812_618`), the 4 `SloadProbe` regimes
(`610_978_715_738`, `610_978_730_738`, `677_645_382_458`, `677_645_397_458`), and `terminalK = 857_384_015_252`. -/
theorem twenty_four_regime_interleaved_strict_ordering_non_vacuous_and_tight (K : Nat) :
    push31NoGcCandidateK < jointBlockGasSlope3K ∧
    jointBlockGasSlope3K < perTxSixPassTargetK ∧
    perTxSixPassTargetK < blockVsTxSlope3K ∧
    blockVsTxSlope3K < jointBlockGasSlope6K ∧
    jointBlockGasSlope6K < bs32StandaloneSlope3K ∧
    bs32StandaloneSlope3K < bs32TotalSlope3K ∧
    bs32TotalSlope3K < blockVsTxSlope6K ∧
    blockVsTxSlope6K < jointBlockGasSlope12K ∧
    jointBlockGasSlope12K < bs32StandaloneSlope6K ∧
    bs32StandaloneSlope6K < coldSloadProbeZeroOffsetK ∧
    coldSloadProbeZeroOffsetK < coldSloadProbeEnvelopeTargetK ∧
    coldSloadProbeEnvelopeTargetK < sloadProbeZeroOffsetK ∧
    sloadProbeZeroOffsetK < sloadProbeEnvelopeTargetK ∧
    sloadProbeEnvelopeTargetK < bs32TotalSlope6K ∧
    bs32TotalSlope6K < terminalK ∧
    terminalK < quadraticCollisionTargetK ∧
    quadraticCollisionTargetK < yukon ∧
    (bs32TotalSlope6K ≤ K ↔ 775_680_812_618 ≤ K) := by
  have hsload := complete_twelve_regime_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hcz : coldSloadProbeZeroOffsetK = 610_978_715_738 := hsload.2.2.2.2.2.2.1
  have hce : coldSloadProbeEnvelopeTargetK = 610_978_730_738 := hsload.2.2.2.2.2.2.2.1
  have hsz : sloadProbeZeroOffsetK = 677_645_382_458 := hsload.2.2.2.2.2.2.2.2.1
  have hse : sloadProbeEnvelopeTargetK = 677_645_397_458 := hsload.2.2.2.2.2.2.2.2.2.1
  have hbs6 : bs32TotalSlope6K = 775_680_812_618 := bs32_total_slope6_exact
  rw [hcz, hce, hsz, hse, hbs6]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, Iff.rfl⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Integration of `Bs32DominanceSixPassTargetCert` with the
6-pass `WordToWord` `midTailChain`: for any `LoopToWord.compHOL` output, `midTailChain` preserves
`NoSt = true` and `storeConstsAllowance = 0`, so all 4 `bs32` target regimes (`296_693_001_548`,
`387_840_417_875`, `593_385_979_964`, `775_680_812_618`) incur zero `storeConsts` allowance drift,
while `2 * (D * W) ≤ bs32MaxProbeTicks = 95_238_095_238` is 1-tick tight at `(47_619, 1_000_001)`. -/
theorem bs32_four_regimes_with_mid_tail_zero_allowance_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) (b : Bool)
    (ctx : Spt Nat) (lp : HolLoopProg width) (labels : Nat × Nat)
    (D W : Nat) (hdw : noopColdUnits * D + W ≤ 2_000_000)
    (ws : List (Bool × BitVec width)) :
    bs32StandaloneSlope3K = 296_693_001_548 ∧
    bs32TotalSlope3K = 387_840_417_875 ∧
    bs32StandaloneSlope6K = 593_385_979_964 ∧
    bs32TotalSlope6K = 775_680_812_618 ∧
    2 * (D * W) ≤ bs32MaxProbeTicks ∧
    ¬ (2 * (47_619 * 1_000_001) ≤ bs32MaxProbeTicks - 1) ∧
    NoSt (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) = true ∧
    storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) = 0 ∧
    bs32StandaloneSlope3K +
      storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) =
        296_693_001_548 ∧
    bs32TotalSlope3K +
      storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) =
        387_840_417_875 ∧
    bs32StandaloneSlope6K +
      storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) =
        593_385_979_964 ∧
    bs32TotalSlope6K +
      storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) =
        775_680_812_618 ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have hmid := mid_tail_chain_preserves_noSt_and_zero_allowance_non_vacuous_and_tight
    c temp b (LoopToWord.compHOL ctx lp labels).1 (loopToWord_NoSt ctx lp labels) 0 ws
  have hnost := hmid.1
  have hzero := hmid.2.1
  have htight := hmid.2.2.2.2.2
  have hprobe := bs32_probe_bound D W hdw
  rw [hzero, Nat.add_zero, Nat.add_zero, Nat.add_zero, Nat.add_zero]
  exact ⟨bs32_standalone_slope3_exact, bs32_total_slope3_exact,
    bs32_standalone_slope6_exact, bs32_total_slope6_exact,
    hprobe, bs32_probe_one_tick_tight, hnost, rfl,
    bs32_standalone_slope3_exact, bs32_total_slope3_exact,
    bs32_standalone_slope6_exact, bs32_total_slope6_exact, htight⟩

/-- Theorem 5 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity across all 15 principal
regimes and optimality of `yukonScore exactKeccak128UnrolledK minutes` across the entire
15-regime portfolio (`fifteenPrincipalRegimes`). -/
theorem fifteen_regime_yukon_score_strict_ladder_and_optimality_non_vacuous_and_tight
    (minutes a b : Nat) :
    yukonScore exactKeccak128UnrolledK minutes < yukonScore exactKeccak0UnrolledK minutes ∧
    yukonScore exactKeccak0UnrolledK minutes < yukonScore sixPassUnrolledCopyLoopK minutes ∧
    yukonScore sixPassUnrolledCopyLoopK minutes < yukonScore sixPassReducedK minutes ∧
    yukonScore sixPassReducedK minutes < yukonScore exactKeccak128CandidateK minutes ∧
    yukonScore exactKeccak128CandidateK minutes < yukonScore isoReducedCopyLoopK minutes ∧
    yukonScore isoReducedCopyLoopK minutes < yukonScore isoReducedCandidateK minutes ∧
    yukonScore isoReducedCandidateK minutes < yukonScore exactKeccakCandidateK minutes ∧
    yukonScore exactKeccakCandidateK minutes < yukonScore push31NoGcCandidateK minutes ∧
    yukonScore push31NoGcCandidateK minutes < yukonScore jointBlockGasSlope3K minutes ∧
    yukonScore jointBlockGasSlope3K minutes < yukonScore perTxSixPassTargetK minutes ∧
    yukonScore perTxSixPassTargetK minutes < yukonScore bs32StandaloneSlope3K minutes ∧
    yukonScore bs32StandaloneSlope3K minutes < yukonScore bs32TotalSlope3K minutes ∧
    yukonScore bs32TotalSlope3K minutes < yukonScore sloadProbeEnvelopeTargetK minutes ∧
    yukonScore sloadProbeEnvelopeTargetK minutes < yukonScore terminalK minutes ∧
    yukonScore terminalK minutes < yukonScore 900_719_925_474 minutes ∧
    (∀ k ∈ fifteenPrincipalRegimes, yukonScore exactKeccak128UnrolledK minutes ≤ yukonScore k minutes) ∧
    (yukonScore a minutes < yukonScore b minutes ↔ a < b) := by
  have hord := fifteen_principal_regimes_strict_ordering_non_vacuous_and_tight 0
  refine ⟨score_monotone_non_vacuous_and_tight _ _ minutes hord.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.2.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    score_monotone_non_vacuous_and_tight _ _ minutes hord.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    ?_, ?_⟩
  · intro k hk
    have hle := (hord.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k hk).1
    unfold yukonScore
    omega
  · unfold yukonScore
    omega

/-- Theorem 6 (`non_vacuous_and_tight`): Exact IEEE-754 `float64` representability (`yukonScore k minutes < 2^53 - 1`)
for every regime `k ∈ fifteenPrincipalRegimes` and every `bs32` regime (`bs32StandaloneSlope3K`,
`bs32TotalSlope3K`, `bs32StandaloneSlope6K`, `bs32TotalSlope6K`), with sharp ceiling characterization
`yukonScore K 9999 < 2^53 - 1 ↔ K < 900_719_925_474`. -/
theorem fifteen_regime_and_bs32_float64_exactness_non_vacuous_and_tight (minutes K : Nat) :
    (∀ k ∈ fifteenPrincipalRegimes, yukonScore k minutes < 2 ^ 53 - 1) ∧
    yukonScore bs32StandaloneSlope3K minutes < 2 ^ 53 - 1 ∧
    yukonScore bs32TotalSlope3K minutes < 2 ^ 53 - 1 ∧
    yukonScore bs32StandaloneSlope6K minutes < 2 ^ 53 - 1 ∧
    yukonScore bs32TotalSlope6K minutes < 2 ^ 53 - 1 ∧
    yukonScore terminalK minutes < 2 ^ 53 - 1 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hord := fifteen_principal_regimes_strict_ordering_non_vacuous_and_tight 0
  have hterm : terminalK = 857_384_015_252 := (candidate_count_non_vacuous_and_tight).2
  have hm : min minutes 9999 ≤ 9999 := Nat.min_le_right _ _
  have hm9999 : min 9999 9999 = 9999 := rfl
  have hterm_score : yukonScore terminalK minutes < 2 ^ 53 - 1 := by
    rw [hterm]
    unfold yukonScore
    omega
  refine ⟨?_,
    bs32_standalone_slope3_score_representable minutes,
    bs32_total_slope3_score_representable minutes,
    bs32_standalone_slope6_score_representable minutes,
    bs32_total_slope6_score_representable minutes,
    hterm_score, ?_⟩
  · intro k hk
    have hle : k ≤ terminalK := (hord.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k hk).2.1
    have hk_le : yukonScore k minutes ≤ yukonScore terminalK minutes := by
      unfold yukonScore
      omega
    exact Nat.lt_of_le_of_lt hk_le hterm_score
  · unfold yukonScore
    rw [hm9999]
    omega

/-- Theorem 7 (`non_vacuous_and_tight`): `claim.json` byte-size (`≤ 128` bytes) and `validFiniteClaim`
conformance for all 15 principal regimes (`fifteenRegimeClaims`), plus exact `claim.json` validity for
the 4 `bs32` regimes and sharp positive finite `K` range `validFiniteClaim K (verifierClaimJson "1212035192") = true ↔ 0 < K ∧ K ≤ 900_719_925_473`. -/
theorem fifteen_regime_claims_valid_and_within_128_bytes_non_vacuous_and_tight (K : Nat) :
    fifteenRegimeClaims.length = 15 ∧
    fifteenRegimeClaims.map Prod.fst = fifteenPrincipalBudgets ∧
    (∀ entry ∈ fifteenRegimeClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (∀ entry ∈ claims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (verifierClaimJson "593385979964").utf8ByteSize ≤ 128 ∧
    validFiniteClaim 593_385_979_964 (verifierClaimJson "593385979964") = true ∧
    (verifierClaimJson "775680812618").utf8ByteSize ≤ 128 ∧
    validFiniteClaim 775_680_812_618 (verifierClaimJson "775680812618") = true ∧
    (validFiniteClaim K (verifierClaimJson "1212035192") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) := by
  have hlen : decide ((verifierClaimJson "1212035192").utf8ByteSize ≤ MAX_CLAIM_BYTES) = true := by decide
  refine ⟨by decide, by decide, by decide,
    claim_bytes_non_vacuous_and_tight,
    by decide, by decide, by decide, by decide, ?_⟩
  unfold validFiniteClaim
  rw [hlen, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- Theorem 8 (`non_vacuous_and_tight`): Master certificate selection theorem across all 15
principal regimes, all 12 `UnrolledTwelveCandidatePortfolio` candidates, all 4 `bs32` regimes,
all 3 `JointBlockGas` regimes, and all 4 `SloadProbe` regimes: a single `CertificateAt exactKeccak128UnrolledK`
lifts automatically to every regime in `fifteenPrincipalRegimes` and `allTwentyFourRegimes`. -/
theorem master_fifteen_and_twenty_four_regime_certificate_selection_non_vacuous_and_tight
    (hc : CertificateAt exactKeccak128UnrolledK) :
    (∀ k ∈ fifteenPrincipalRegimes, CertificateAt k) ∧
    (∀ k ∈ candidates, CertificateAt k) ∧
    (∀ k ∈ allTwentyFourRegimes, CertificateAt k) ∧
    CertificateAt bs32StandaloneSlope3K ∧
    CertificateAt bs32TotalSlope3K ∧
    CertificateAt bs32StandaloneSlope6K ∧
    CertificateAt bs32TotalSlope6K ∧
    CertificateAt jointBlockGasSlope3K ∧
    CertificateAt jointBlockGasSlope6K ∧
    CertificateAt jointBlockGasSlope12K ∧
    CertificateAt coldSloadProbeZeroOffsetK ∧
    CertificateAt coldSloadProbeEnvelopeTargetK ∧
    CertificateAt sloadProbeZeroOffsetK ∧
    CertificateAt sloadProbeEnvelopeTargetK ∧
    CertificateAt terminalK ∧
    ¬ (exactKeccak128UnrolledK ≤ exactKeccak128UnrolledK - 1) := by
  have hord := fifteen_principal_regimes_strict_ordering_non_vacuous_and_tight 0
  have h15 : ∀ k ∈ fifteenPrincipalRegimes, CertificateAt k := by
    intro k hk
    exact certificate_lift_non_vacuous_and_tight _ k
      (hord.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k hk).1 hc
  have h12 := optimal_certificate_selection_non_vacuous_and_tight hc
  have hsload := complete_twelve_regime_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hcz : coldSloadProbeZeroOffsetK = 610_978_715_738 := hsload.2.2.2.2.2.2.1
  have hce : coldSloadProbeEnvelopeTargetK = 610_978_730_738 := hsload.2.2.2.2.2.2.2.1
  have hsz : sloadProbeZeroOffsetK = 677_645_382_458 := hsload.2.2.2.2.2.2.2.2.1
  have hse : sloadProbeEnvelopeTargetK = 677_645_397_458 := hsload.2.2.2.2.2.2.2.2.2.1
  have h24 : ∀ k ∈ allTwentyFourRegimes, CertificateAt k := by
    intro k hk
    have hle : exactKeccak128UnrolledK ≤ k := by
      unfold allTwentyFourRegimes at hk
      rw [hcz, hce, hsz, hse] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact certificate_lift_non_vacuous_and_tight _ k hle hc
  exact ⟨h15, h12, h24,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hc,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hc,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hc,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hc,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hc,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hc,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hc,
    certificate_lift_non_vacuous_and_tight _ _ (by rw [hcz]; decide) hc,
    certificate_lift_non_vacuous_and_tight _ _ (by rw [hce]; decide) hc,
    certificate_lift_non_vacuous_and_tight _ _ (by rw [hsz]; decide) hc,
    certificate_lift_non_vacuous_and_tight _ _ (by rw [hse]; decide) hc,
    terminal_certificate_selection_non_vacuous_and_tight hc,
    by decide⟩

/-- Theorem 9 (`non_vacuous_and_tight`): Direct `InitE.Certificate` for `bs32StandaloneSlope3K = 296_693_001_548`
propagating upward to `bs32TotalSlope3K = 387_840_417_875`, `bs32StandaloneSlope6K = 593_385_979_964`,
the 4 `SloadProbe` regimes (`610_978_715_738`..`677_645_397_458`), `bs32TotalSlope6K = 775_680_812_618`,
and `terminalK = 857_384_015_252`, paired with the 6-pass `midTailChain` `NoSt` and zero
`storeConstsAllowance` guarantee and sharp 1-tick tightness. -/
theorem bs32_standalone_slope3_upward_portfolio_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (temp : Nat) (b : Bool)
    (ctx : Spt Nat) (lp : HolLoopProg width) (labels : Nat × Nat)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        bs32StandaloneSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = true ∧
    storeConstsAllowance (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = 0 ∧
    CertificateAt bs32StandaloneSlope3K ∧
    CertificateAt bs32TotalSlope3K ∧
    CertificateAt blockVsTxSlope6K ∧
    CertificateAt jointBlockGasSlope12K ∧
    CertificateAt bs32StandaloneSlope6K ∧
    CertificateAt coldSloadProbeZeroOffsetK ∧
    CertificateAt coldSloadProbeEnvelopeTargetK ∧
    CertificateAt sloadProbeZeroOffsetK ∧
    CertificateAt sloadProbeEnvelopeTargetK ∧
    CertificateAt bs32TotalSlope6K ∧
    CertificateAt terminalK ∧
    ¬ (bootstrapSteps + bs32_standalone_slope3_postSteps ≤ bs32StandaloneSlope3K - 1) := by
  have hmid := loop_to_word_mid_tail_chain_justifies_probe_and_six_pass_slopes_non_vacuous_and_tight
    asmConf temp b ctx lp labels 0 0 0
  have hbs3 : CertificateAt bs32StandaloneSlope3K :=
    bs32_standalone_slope3_finite_certificate oracles c depth hlab compiled depthBound not_timeOut
  have hsload := complete_twelve_regime_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hcz : coldSloadProbeZeroOffsetK = 610_978_715_738 := hsload.2.2.2.2.2.2.1
  have hce : coldSloadProbeEnvelopeTargetK = 610_978_730_738 := hsload.2.2.2.2.2.2.2.1
  have hsz : sloadProbeZeroOffsetK = 677_645_382_458 := hsload.2.2.2.2.2.2.2.2.1
  have hse : sloadProbeEnvelopeTargetK = 677_645_397_458 := hsload.2.2.2.2.2.2.2.2.2.1
  exact ⟨hmid.1, hmid.2.1, hbs3,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hbs3,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hbs3,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hbs3,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hbs3,
    certificate_lift_non_vacuous_and_tight _ _ (by rw [hcz]; decide) hbs3,
    certificate_lift_non_vacuous_and_tight _ _ (by rw [hce]; decide) hbs3,
    certificate_lift_non_vacuous_and_tight _ _ (by rw [hsz]; decide) hbs3,
    certificate_lift_non_vacuous_and_tight _ _ (by rw [hse]; decide) hbs3,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hbs3,
    certificate_lift_non_vacuous_and_tight _ _ (by decide) hbs3,
    bs32_standalone_slope3_saturated_one_tick_tight⟩

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_66` synthesis theorem unifying
`UnrolledTwelveCandidatePortfolio`, `Bs32DominanceSixPassTargetCert`, and
`SelfContainedMidPassesAndSloadSynth` with `0` imports from `InitECandidate.Proofs.Bounded*`:
under uniform target non-`.timeOut` at `exactKeccak128UnrolledK = 1_212_035_192`, all 15 principal
regimes and all 24 unified regimes satisfy `InitE.Certificate`, `midTailChain` preserves `NoSt = true`
and `storeConstsAllowance = 0` (`k_sr = k_sn + 1`), all `yukonScore` values are exact IEEE-754
`float64` integers (`< 2^53 - 1`), all `claim.json` strings are valid and `≤ 128` bytes, and
`zeroBoundedImportCount = 0`. -/
theorem end_to_end_self_contained_fifteen_regime_portfolio_master_cert_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (temp : Nat) (b : Bool)
    (ctx : Spt Nat) (lp : HolLoopProg width) (labels : Nat × Nat)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes k_sn : Nat)
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
    NoSt (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = true ∧
    storeConstsAllowance (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = 0 ∧
    stackRemoveClockWithAllowance k_sn
      (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = k_sn + 1 ∧
    (∀ k ∈ fifteenPrincipalRegimes, CertificateAt k) ∧
    (∀ k ∈ allTwentyFourRegimes, CertificateAt k) ∧
    (∀ k ∈ fifteenPrincipalRegimes,
      yukonScore exactKeccak128UnrolledK minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    (∀ entry ∈ fifteenRegimeClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    zeroBoundedImportCount = 0 ∧
    ¬ (exactKeccak128UnrolledK ≤ exactKeccak128UnrolledK - 1) := by
  have hmid := loop_to_word_mid_tail_chain_justifies_probe_and_six_pass_slopes_non_vacuous_and_tight
    asmConf temp b ctx lp labels k_sn 0 0
  have hbest : CertificateAt exactKeccak128UnrolledK :=
    optimal_direct_certificate_non_vacuous_and_tight oracles c depth hlab compiled depthBound not_timeOut_best
  have hsel := master_fifteen_and_twenty_four_regime_certificate_selection_non_vacuous_and_tight hbest
  have hscore_opt := (fifteen_regime_yukon_score_strict_ladder_and_optimality_non_vacuous_and_tight minutes 0 0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hscore_f64 := (fifteen_regime_and_bs32_float64_exactness_non_vacuous_and_tight minutes 0).1
  have hclaims := (fifteen_regime_claims_valid_and_within_128_bytes_non_vacuous_and_tight 1).2.2.1
  have hinf : InitE.Certificate InitE.baselineSubmission .infinity := by
    refine ⟨rfl, InitE.baselineSubmission_admitted, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, _, hm⟩ := hbest.correct input hgas outcome events hsrc hcov
    exact ⟨steps, trivial,
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission
        (.finite exactKeccak128UnrolledK) input outcome events steps).mp hm⟩
  refine ⟨hmid.1, hmid.2.1, hmid.2.2.1, hsel.1, hsel.2.2.1, ?_, hclaims, hinf, rfl, hsel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  intro k hk
  exact ⟨hscore_opt k hk, hscore_f64 k hk⟩

#print axioms fifteen_regime_catalog_values_and_counts_non_vacuous_and_tight
#print axioms fifteen_principal_regimes_strict_ordering_non_vacuous_and_tight
#print axioms twenty_four_regime_interleaved_strict_ordering_non_vacuous_and_tight
#print axioms bs32_four_regimes_with_mid_tail_zero_allowance_non_vacuous_and_tight
#print axioms fifteen_regime_yukon_score_strict_ladder_and_optimality_non_vacuous_and_tight
#print axioms fifteen_regime_and_bs32_float64_exactness_non_vacuous_and_tight
#print axioms fifteen_regime_claims_valid_and_within_128_bytes_non_vacuous_and_tight
#print axioms master_fifteen_and_twenty_four_regime_certificate_selection_non_vacuous_and_tight
#print axioms bs32_standalone_slope3_upward_portfolio_certificate_non_vacuous_and_tight
#print axioms end_to_end_self_contained_fifteen_regime_portfolio_master_cert_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedFifteenRegimePortfolio
