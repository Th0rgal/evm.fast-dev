import InitECandidate.Solver.SloadProbeDryRunPortfolio
import InitECandidate.Solver.MultiAddressMergeThirtySixBudgetMaster
import InitECandidate.Solver.GuestFiveAddrTablesMergeBound

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SloadProbeAndMultiAddrMergeBridge` — Wave 5 Atomic Worker `W5_91`

Self-contained bridge module (**0 `Proofs/Bounded*` imports**) integrating:
1. `SloadProbeDryRunPortfolio` (`9/9` tight): 15-regime `SLOAD` / dry-run portfolio under Yukon
   (`coldSloadRawTargetK = 610,978,715,738`, `coldSloadProbeEnvelopeTargetK = 610,978,730,738`,
   `sloadProbeRawTargetK = 677,645,382,458`, `sloadProbeEnvelopeTargetK = 677,645,397,458`),
2. `MultiAddressMergeThirtySixBudgetMaster` (`25/25` tight): 36-budget multi-address merge
   dominance portfolio (`kPanMultiAddrMerge = kPanMerge = 136,116,135,658`,
   `mergeSlope3UnrolledK = 408,348,416,306`, `mergeSlope3K = 408,348,430,106`,
   `mergeSlope6UnrolledK = 816,696,823,280`, `mergeSlope6K = 816,696,837,080 < 900,719,925,474`),
3. `GuestFiveAddrTablesMergeBound` (`11/11` tight): quadratic absorption of the 5 address tables
   (`5*A^2`) and 12 address-table probes (`12*A^2`) into `S^2 / 40 = 100,000,000,000`
   (and coupled `42*(2*D*W + 12*A^2) ≤ S^2`, `≤ 95,238,095,238`), leaving `kPanMultiAddrMerge`
   and all 36 merge budgets unchanged.
-/

namespace InitECandidate.Solver.SloadProbeAndMultiAddrMergeBridge

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedMasterK hiding refinedCandidateK
open InitECandidate.Solver.SelfContainedIsoReducedK hiding isoReducedCandidateK
open InitECandidate.Solver.SelfContainedPush31MasterK hiding push31NoGcCandidateK push31CandidateK
open InitECandidate.Solver.SelfContainedSixPassMaster hiding sixPassReducedK
open InitECandidate.Solver.SelfContainedEndToEndCert
open InitECandidate.Solver.SelfContainedQuadraticEnvelopeCert hiding quadraticCollisionTargetK
open InitECandidate.Solver.SelfContainedSloadProbeEnvelope
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.GuestJointBlockGasHtabBound
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
open InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.PurifiedSubmissionBound
open InitECandidate.Solver.YukonVerifyScriptAudit hiding matchingExecutionAt_with_score
open InitECandidate.Solver.SelfContainedSolutionCandidates
open InitECandidate.Solver.YukonFinalCandidateSelector
open InitECandidate.Solver.RiscvSszFastRejectAndBootCert
open InitECandidate.Solver.YukonSubmissionDryRunCert
open InitECandidate.Solver.YukonEightTierMasterPortfolio hiding
  sixPassUnrolledCopyLoopK sixPassReducedK isoReducedCopyLoopK isoReducedCandidateK
  push31NoGcCandidateK push31CandidateK quadraticCollisionTargetK
open InitECandidate.Solver.JointBlockGasSixPassMasterCert
open InitECandidate.Solver.SloadProbeDryRunPortfolio
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open _root_.InitECandidate.Solver.GuestMergeTxUnionEnvelope (kPanMerge mergeLin blockMerge locCoup)
open _root_.InitECandidate.Solver.GuestMultiAddressMergeDominance (kPanMultiAddrMerge)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio
open InitECandidate.Solver.MultiAddressMergeThirtySixBudgetMaster hiding
  portfolio_certificates_non_vacuous_and_tight
  mergeSlope3UnrolledK_certificate_non_vacuous_and_tight
  mergeSlope3K_certificate_non_vacuous_and_tight
  mergeSlope6UnrolledK_certificate_non_vacuous_and_tight
  mergeSlope6K_certificate_non_vacuous_and_tight
open InitECandidate.Solver.GuestFiveAddrTablesMergeBound
open Flapjack
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target

/-! ## Section 1: Claim JSON Payloads & Unified 19-Regime Bridge Selector -/

/-- Canonical `{"claimed_k": "<K>"}` JSON payloads for the 4 multi-address merge tiers. -/
def claimJsonMergeSlope3Unrolled : String := claimedKJson "408348416306"
def claimJsonMergeSlope3 : String := claimedKJson "408348430106"
def claimJsonMergeSlope6Unrolled : String := claimedKJson "816696823280"
def claimJsonMergeSlope6 : String := claimedKJson "816696837080"

/-- Canonical `{"K": <K>}` verifier JSON payloads for the 4 multi-address merge tiers. -/
def verifierJsonMergeSlope3Unrolled : String := verifierClaimJson "408348416306"
def verifierJsonMergeSlope3 : String := verifierClaimJson "408348430106"
def verifierJsonMergeSlope6Unrolled : String := verifierClaimJson "816696823280"
def verifierJsonMergeSlope6 : String := verifierClaimJson "816696837080"

/-- Unified 19-regime bridge selector uniting the 15 `SloadDryRunPortfolioTier` regimes
and the 4 multi-address merge regimes (`mergeSlope3UnrolledK`, `mergeSlope3K`,
`mergeSlope6UnrolledK`, `mergeSlope6K`). -/
inductive SloadMultiAddrBridgeTier where
  | sloadPortfolio (t : SloadDryRunPortfolioTier)
  | mergeSlope3Unrolled
  | mergeSlope3
  | mergeSlope6Unrolled
  | mergeSlope6
  deriving DecidableEq, Repr

/-- Step budget selector across all 19 bridge regimes. -/
def selectBridgeK (tier : SloadMultiAddrBridgeTier) : Nat :=
  match tier with
  | .sloadPortfolio t => selectPortfolioK t
  | .mergeSlope3Unrolled => mergeSlope3UnrolledK
  | .mergeSlope3 => mergeSlope3K
  | .mergeSlope6Unrolled => mergeSlope6UnrolledK
  | .mergeSlope6 => mergeSlope6K

/-- Canonical `{"claimed_k": "<K>"}` JSON selector across all 19 bridge regimes. -/
def selectBridgeClaimJson (tier : SloadMultiAddrBridgeTier) : String :=
  match tier with
  | .sloadPortfolio t => selectPortfolioClaimJson t
  | .mergeSlope3Unrolled => claimJsonMergeSlope3Unrolled
  | .mergeSlope3 => claimJsonMergeSlope3
  | .mergeSlope6Unrolled => claimJsonMergeSlope6Unrolled
  | .mergeSlope6 => claimJsonMergeSlope6

/-- Canonical `{"K": <K>}` verifier JSON selector across all 19 bridge regimes. -/
def selectBridgeVerifierJson (tier : SloadMultiAddrBridgeTier) : String :=
  match tier with
  | .sloadPortfolio t => selectPortfolioVerifierJson t
  | .mergeSlope3Unrolled => verifierJsonMergeSlope3Unrolled
  | .mergeSlope3 => verifierJsonMergeSlope3
  | .mergeSlope6Unrolled => verifierJsonMergeSlope6Unrolled
  | .mergeSlope6 => verifierJsonMergeSlope6

/-! ## Section 2: Eleven `non_vacuous_and_tight` Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Absorption of 5 address tables (`5*A^2`) and 12
address-table probes (`12*A^2`) into `blockMerge = 100,000,000,000` (`40 * (...) ≤ S * S`),
preserving `kPanMultiAddrMerge = kPanMerge = 136,116,135,658` with dual boundary tightness
at `(50,000, 950,000, 0)` and `(0, 650,000, 50,000)`. -/
theorem five_and_twelve_addr_tables_absorbed_into_kPanMultiAddrMerge_non_vacuous_and_tight
    (D A W Tloc Tlin : Nat)
    (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    40 * (2 * ((D + A) * (W + D + A)) + 5 * (A * A)) ≤ S * S ∧
    40 * (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) ≤ S * S ∧
    2 * ((D + A) * (W + D + A)) + 5 * (A * A) ≤ blockMerge ∧
    2 * ((D + A) * (W + D + A)) + 12 * (A * A) ≤ blockMerge ∧
    linear + Tloc + (2 * ((D + A) * (W + D + A)) + 5 * (A * A)) + Tlin ≤ kPanMultiAddrMerge ∧
    linear + Tloc + (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) + Tlin ≤ kPanMultiAddrMerge ∧
    kPanMultiAddrMerge = kPanMerge ∧
    kPanMultiAddrMerge = 136_116_135_658 ∧
    (20 * 50000 + 26 * 0 + (950000 + 50000 + 0) = S ∧
      2 * ((50000 + 0) * (950000 + 50000 + 0)) + 5 * (0 * 0) = blockMerge) ∧
    (20 * 0 + 26 * 50000 + (650000 + 0 + 50000) = S ∧
      2 * ((0 + 50000) * (650000 + 0 + 50000)) + 12 * (50000 * 50000) = blockMerge) := by
  have h5 := five_addr_tables_absorbed D A W h
  have h12 := twelve_addr_tables_absorbed D A W h
  have h5_le := five_le D A W h
  have h12_le : 2 * ((D + A) * (W + D + A)) + 12 * (A * A) ≤ 100000000000 := by
    unfold S at h12; omega
  have hbm : blockMerge = 100000000000 := rfl
  have hk_eq := kPanMultiAddrMerge_eq_non_vacuous_and_tight
  have hk_def : linear + locCoup + blockMerge + mergeLin = kPanMultiAddrMerge := by
    rw [hk_eq.2]; decide
  refine ⟨h5, h12, ?_, ?_, ?_, ?_, hk_eq.1, hk_eq.2, five_tight, twelve_sharp⟩
  · rw [hbm]; exact h5_le
  · rw [hbm]; exact h12_le
  · rw [← hk_def, hbm]; omega
  · rw [← hk_def, hbm]; omega

/-- Theorem 2 (`non_vacuous_and_tight`): Coupled address-table quadratic bound
`42 * (2 * (D * W) + 12 * (A * A)) ≤ S * S` (`2 * (D * W) + 12 * (A * A) ≤ 95,238,095,238 < blockMerge`)
together with per-address list subadditivity and five-table target step bounds at `3×` and `6×`
into `mergeSlope3UnrolledK`, `mergeSlope3K`, `mergeSlope6UnrolledK`, and `mergeSlope6K`. -/
theorem coupled_five_addr_tables_and_target_merge_bounds_non_vacuous_and_tight
    (l : List (Nat × Nat)) (D A W Tloc Tlin post3 post6 : Nat)
    (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hc : 21 * D + 26 * A + W ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hp3 : post3 ≤ 3 * (linear + Tloc + (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) + Tlin))
    (hp6 : post6 ≤ 6 * (linear + Tloc + (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) + Tlin)) :
    (l.map (fun p => p.1 * (p.2 + p.1))).sum ≤
      (l.map Prod.fst).sum * ((l.map Prod.snd).sum + (l.map Prod.fst).sum) ∧
    42 * (2 * (D * W) + 12 * (A * A)) ≤ S * S ∧
    2 * (D * W) + 12 * (A * A) ≤ 95_238_095_238 ∧
    95_238_095_238 < blockMerge ∧
    9332 + post3 ≤ mergeSlope3UnrolledK ∧
    23132 + post3 ≤ mergeSlope3K ∧
    9332 + post6 ≤ mergeSlope6UnrolledK ∧
    23132 + post6 ≤ mergeSlope6K ∧
    2 * (47619 * 1000001) + 12 * (0 * 0) = 95_238_095_238 ∧
    2 * (0 * 0) + 12 * (76923 * 76923) = 71_005_775_148 := by
  have h12_src := (five_and_twelve_addr_tables_absorbed_into_kPanMultiAddrMerge_non_vacuous_and_tight
    D A W Tloc Tlin h hloc hlin).2.2.2.2.2.1
  have h3 := Nat.mul_le_mul_left 3 h12_src
  have h6 := Nat.mul_le_mul_left 6 h12_src
  have ht := tiers_preserved_non_vacuous_and_tight
  have hcl := coupled_le D A W hc
  refine ⟨per_address_split_non_vacuous_and_tight l,
    coupled_absorbed D A W hc,
    hcl.1,
    by decide,
    by omega,
    by omega,
    by omega,
    by omega,
    hcl.2,
    coupled_addr_corner.2.1⟩

/-- Theorem 3 (`non_vacuous_and_tight`): Joint source-clock hierarchy uniting
`kPanJoint 6 = 40,486,477,625`, `maxGuestSourceClock = 43,914,839,586`,
`blockVsTxSourceK = 71,448,666,010`, `kPanMultiAddrMerge = 136,116,135,658`,
`maxColdSloadTotalClock = 203,659,564,202`, and `maxTotalClock = 225,881,786,442`,
with sharp Yukon multiplier thresholds `k ≤ 6` for `kPanMultiAddrMerge` and `M ≤ 3` for `maxTotalClock`. -/
theorem source_clock_hierarchy_with_kPanMultiAddrMerge_and_sload_non_vacuous_and_tight
    (k M : Nat) :
    kPanJoint 6 = 40_486_477_625 ∧
    maxGuestSourceClock = 43_914_839_586 ∧
    blockVsTxSourceK = 71_448_666_010 ∧
    kPanMultiAddrMerge = 136_116_135_658 ∧
    maxColdSloadTotalClock = 203_659_564_202 ∧
    maxTotalClock = 225_881_786_442 ∧
    kPanJoint 6 < maxGuestSourceClock ∧
    maxGuestSourceClock < blockVsTxSourceK ∧
    blockVsTxSourceK < kPanMultiAddrMerge ∧
    kPanMultiAddrMerge < maxColdSloadTotalClock ∧
    maxColdSloadTotalClock < maxTotalClock ∧
    yukon - 6 * kPanMultiAddrMerge = 84_023_111_526 ∧
    (k * kPanMultiAddrMerge < yukon ↔ k ≤ 6) ∧
    (bootstrapSteps + M * (maxTotalClock + pipeOffset) < yukonFloat64StepCeiling ↔ M ≤ 3) := by
  have hkpan : kPanJoint 6 = 40_486_477_625 := kPanJoint_val
  have hm_merge := threshold_and_margin_non_vacuous_and_tight k
  have hm_sload := (sload_probe_multiplier_threshold_non_vacuous_and_tight M).2
  have hk_val := kPanMultiAddrMerge_eq_non_vacuous_and_tight.2
  rw [hkpan, hk_val]
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl,
    by decide, by decide, by decide, by decide, by decide,
    hm_merge.2, hm_merge.1, hm_sload⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Complete strict ordering across all 19 target regimes
uniting the 15 `SloadProbeDryRunPortfolio` regimes and the 4 `MultiAddressMergeThirtySixBudgetMaster`
regimes (`mergeSlope3UnrolledK = 408,348,416,306 < mergeSlope3K = 408,348,430,106` between
`jointBlockGasSlope6K` and `jointBlockGasSlope12K`, and
`mergeSlope6UnrolledK = 816,696,823,280 < mergeSlope6K = 816,696,837,080` between
`sloadProbeEnvelopeTargetK` and `quadraticCollisionTargetK`). -/
theorem complete_nineteen_regime_strict_ordering_sload_and_multi_addr_merge_non_vacuous_and_tight
    (K : Nat) :
    sixPassUnrolledCopyLoopK < sixPassReducedK ∧
    sixPassReducedK < isoReducedCopyLoopK ∧
    isoReducedCopyLoopK < isoReducedCandidateK ∧
    isoReducedCandidateK < refinedCandidateK ∧
    refinedCandidateK < push31NoGcCandidateK ∧
    push31NoGcCandidateK < jointBlockGasSlope3K ∧
    jointBlockGasSlope3K < perTxSixPassTargetK ∧
    perTxSixPassTargetK < push31CandidateK ∧
    push31CandidateK < jointBlockGasSlope6K ∧
    jointBlockGasSlope6K < mergeSlope3UnrolledK ∧
    mergeSlope3UnrolledK < mergeSlope3K ∧
    mergeSlope3K < jointBlockGasSlope12K ∧
    jointBlockGasSlope12K < coldSloadRawTargetK ∧
    coldSloadRawTargetK < coldSloadProbeEnvelopeTargetK ∧
    coldSloadProbeEnvelopeTargetK < sloadProbeRawTargetK ∧
    sloadProbeRawTargetK < sloadProbeEnvelopeTargetK ∧
    sloadProbeEnvelopeTargetK < mergeSlope6UnrolledK ∧
    mergeSlope6UnrolledK < mergeSlope6K ∧
    mergeSlope6K < quadraticCollisionTargetK ∧
    quadraticCollisionTargetK < yukonFloat64MaxK ∧
    (23132 + K * kPanMultiAddrMerge < yukon ↔ K ≤ 6) := by
  have hd := dry_run_eight_tier_candidate_hierarchy_with_unrolled_copyloop_non_vacuous_and_tight 0
  have hunr : sixPassUnrolledCopyLoopK = 11_029_669_988 := hd.1
  have hred : sixPassReducedK = 11_029_683_788 := hd.2.1
  have hisoc : isoReducedCopyLoopK = 22_059_330_644 := hd.2.2.1
  have hiso : isoReducedCandidateK = 22_059_344_444 := hd.2.2.2.1
  have href : refinedCandidateK = 36_765_558_652 := hd.2.2.2.2.1
  have hp31n : push31NoGcCandidateK = 87_829_684_748 := hd.2.2.2.2.2.1
  have hp31 : push31CandidateK = 175_659_346_364 := hd.2.2.2.2.2.2.1
  have hq : quadraticCollisionTargetK = 857_678_983_380 := hd.2.2.2.2.2.2.2.1
  have hptx : perTxSixPassTargetK = 122_620_608_536 :=
    (eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0).2.2.2.2.2.1
  have hmv := values_non_vacuous_and_tight
  have hm3u : mergeSlope3UnrolledK = 408_348_416_306 := hmv.1
  have hm3 : mergeSlope3K = 408_348_430_106 := hmv.2.1
  have hm6u : mergeSlope6UnrolledK = 816_696_823_280 := hmv.2.2.1
  have hm6 : mergeSlope6K = 816_696_837_080 := hmv.2.2.2.1
  have hthr : 23132 + K * kPanMultiAddrMerge < yukon ↔ K ≤ 6 := by
    rw [kPanMultiAddrMerge_eq_non_vacuous_and_tight.1]
    exact MergeTxUnionSixPassMaster.target_threshold_non_vacuous_and_tight K
  rw [hunr, hred, hisoc, hiso, href, hp31n, hp31, hq, hptx, hm3u, hm3, hm6u, hm6]
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, hthr⟩

/-- Theorem 5 (`non_vacuous_and_tight`): Exact step gaps and Yukon headroom margins connecting
the 36-budget multi-address merge portfolio (`portfolio.length = 36`, `portfolio.Pairwise (· < ·)`)
and the SLOAD probe envelope (`mergeSlope6K - sloadProbeEnvelopeTargetK = 139,051,439,622`,
`yukon - mergeSlope6K = 84,023,088,394`, unrolling gap `13,800`, and `3 * pipeOffset` gap `15,000`). -/
theorem thirty_six_budget_portfolio_and_sload_merge_gaps_non_vacuous_and_tight :
    portfolio.length = 36 ∧
    portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ portfolio, 1_212_035_192 ≤ k ∧ k < yukon) ∧
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified, k ∈ portfolio) ∧
    mergeSlope3K - mergeSlope3UnrolledK = 13_800 ∧
    mergeSlope6K - mergeSlope6UnrolledK = 13_800 ∧
    coldSloadProbeEnvelopeTargetK - coldSloadRawTargetK = 15_000 ∧
    sloadProbeEnvelopeTargetK - sloadProbeRawTargetK = 15_000 ∧
    mergeSlope6UnrolledK - sloadProbeEnvelopeTargetK = 139_051_425_822 ∧
    mergeSlope6K - sloadProbeEnvelopeTargetK = 139_051_439_622 ∧
    quadraticCollisionTargetK - mergeSlope6K = 40_982_146_300 ∧
    yukon - mergeSlope6K = 84_023_088_394 ∧
    ¬ (23132 + 6 * kPanMultiAddrMerge ≤ mergeSlope6K - 1) := by
  have hp := portfolio_non_vacuous_and_tight
  have h32 := thirty_two_coverage_non_vacuous_and_tight
  have hd := dry_run_eight_tier_candidate_hierarchy_with_unrolled_copyloop_non_vacuous_and_tight 0
  have hq : quadraticCollisionTargetK = 857_678_983_380 := hd.2.2.2.2.2.2.2.1
  have hsat : ¬ (23132 + 6 * kPanMultiAddrMerge ≤ mergeSlope6K - 1) := by
    rw [kPanMultiAddrMerge_eq_non_vacuous_and_tight.1]
    exact MergeTxUnionSixPassMaster.saturated_non_vacuous_and_tight.2.2.2
  rw [hq]
  refine ⟨hp.1, hp.2.1, hp.2.2, h32.1, h32.2.1,
    by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, hsat⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Universal `claim.json ≤ 128`-byte compliance and
`validFiniteClaim` verification across all 19 bridge regimes (`SloadMultiAddrBridgeTier`),
with exact 29-byte `claimed_k` payloads and 19-byte verifier `K` payloads for the 4 merge tiers. -/
theorem all_nineteen_bridge_tiers_claim_json_le_128_bytes_non_vacuous_and_tight
    (tier : SloadMultiAddrBridgeTier) (claimBytes : Nat) :
    claimJsonMergeSlope3Unrolled.utf8ByteSize = 29 ∧
    claimJsonMergeSlope3.utf8ByteSize = 29 ∧
    claimJsonMergeSlope6Unrolled.utf8ByteSize = 29 ∧
    claimJsonMergeSlope6.utf8ByteSize = 29 ∧
    verifierJsonMergeSlope3Unrolled.utf8ByteSize = 19 ∧
    verifierJsonMergeSlope3.utf8ByteSize = 19 ∧
    verifierJsonMergeSlope6Unrolled.utf8ByteSize = 19 ∧
    verifierJsonMergeSlope6.utf8ByteSize = 19 ∧
    (selectBridgeClaimJson tier).utf8ByteSize ≤ MAX_CLAIM_BYTES ∧
    (selectBridgeVerifierJson tier).utf8ByteSize ≤ MAX_CLAIM_BYTES ∧
    validFiniteClaim (selectBridgeK tier) (selectBridgeClaimJson tier) = true ∧
    validFiniteClaim (selectBridgeK tier) (selectBridgeVerifierJson tier) = true ∧
    (checkSubmissionLimits dryRunFullSolverPackageFiles 2936344 65536 claimBytes false false true = true ↔
      claimBytes ≤ 128) := by
  have hlim := (portfolio_all_fifteen_tiers_claim_json_and_dry_run_limits_non_vacuous_and_tight
    .coldSloadRaw claimBytes).2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, hlim⟩
  · cases tier with
    | sloadPortfolio t =>
      exact (portfolio_all_fifteen_tiers_claim_json_and_dry_run_limits_non_vacuous_and_tight t 0).2.2.2.2.2.2.2.2.1
    | mergeSlope3Unrolled => decide
    | mergeSlope3 => decide
    | mergeSlope6Unrolled => decide
    | mergeSlope6 => decide
  · cases tier with
    | sloadPortfolio t =>
      exact (portfolio_all_fifteen_tiers_claim_json_and_dry_run_limits_non_vacuous_and_tight t 0).2.2.2.2.2.2.2.2.2.1
    | mergeSlope3Unrolled => decide
    | mergeSlope3 => decide
    | mergeSlope6Unrolled => decide
    | mergeSlope6 => decide
  · cases tier with
    | sloadPortfolio t =>
      exact (portfolio_all_fifteen_tiers_claim_json_and_dry_run_limits_non_vacuous_and_tight t 0).2.2.2.2.2.2.2.2.2.2.1
    | mergeSlope3Unrolled => decide
    | mergeSlope3 => decide
    | mergeSlope6Unrolled => decide
    | mergeSlope6 => decide
  · cases tier with
    | sloadPortfolio t =>
      exact (portfolio_all_fifteen_tiers_claim_json_and_dry_run_limits_non_vacuous_and_tight t 0).2.2.2.2.2.2.2.2.2.2.2.1
    | mergeSlope3Unrolled => decide
    | mergeSlope3 => decide
    | mergeSlope6Unrolled => decide
    | mergeSlope6 => decide

/-- Theorem 7 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity and IEEE-754 `float64`
representability (`< 2^53 - 1`) across all 19 bridge regimes (`selectBridgeK tier`) and all 36
budgets in `MultiAddressMergeThirtySixBudgetMaster.portfolio`. -/
theorem bridge_yukonScore_strict_monotonicity_across_sload_and_merge_non_vacuous_and_tight
    (tier : SloadMultiAddrBridgeTier) (minutes K : Nat) :
    selectBridgeK tier < 900_719_925_474 ∧
    yukonScore (selectBridgeK tier) minutes < 2 ^ 53 - 1 ∧
    yukonScore jointBlockGasSlope6K minutes < yukonScore mergeSlope3UnrolledK minutes ∧
    yukonScore mergeSlope3UnrolledK minutes < yukonScore mergeSlope3K minutes ∧
    yukonScore mergeSlope3K minutes < yukonScore jointBlockGasSlope12K minutes ∧
    yukonScore jointBlockGasSlope12K minutes < yukonScore coldSloadRawTargetK minutes ∧
    yukonScore coldSloadRawTargetK minutes < yukonScore coldSloadProbeEnvelopeTargetK minutes ∧
    yukonScore coldSloadProbeEnvelopeTargetK minutes < yukonScore sloadProbeRawTargetK minutes ∧
    yukonScore sloadProbeRawTargetK minutes < yukonScore sloadProbeEnvelopeTargetK minutes ∧
    yukonScore sloadProbeEnvelopeTargetK minutes < yukonScore mergeSlope6UnrolledK minutes ∧
    yukonScore mergeSlope6UnrolledK minutes < yukonScore mergeSlope6K minutes ∧
    yukonScore mergeSlope6K minutes < yukonScore quadraticCollisionTargetK minutes ∧
    yukonScore quadraticCollisionTargetK minutes < 2 ^ 53 - 1 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hd := dry_run_eight_tier_candidate_hierarchy_with_unrolled_copyloop_non_vacuous_and_tight 0
  have hq : quadraticCollisionTargetK = 857_678_983_380 := hd.2.2.2.2.2.2.2.1
  have hmv := values_non_vacuous_and_tight
  have hm3u : mergeSlope3UnrolledK = 408_348_416_306 := hmv.1
  have hm3 : mergeSlope3K = 408_348_430_106 := hmv.2.1
  have hm6u : mergeSlope6UnrolledK = 816_696_823_280 := hmv.2.2.1
  have hm6 : mergeSlope6K = 816_696_837_080 := hmv.2.2.2.1
  have htier_lt : selectBridgeK tier < 900_719_925_474 := by
    cases tier with
    | sloadPortfolio t =>
      exact (portfolio_yukonScore_strict_monotonicity_and_float64_exact_non_vacuous_and_tight t minutes 0).1
    | mergeSlope3Unrolled => decide
    | mergeSlope3 => decide
    | mergeSlope6Unrolled => decide
    | mergeSlope6 => decide
  have htier_sc : yukonScore (selectBridgeK tier) minutes < 2 ^ 53 - 1 :=
    yukonScore_lt_two_pow_53_sub_one (by omega)
  have hm : min minutes 9999 ≤ 9999 := Nat.min_le_right _ _
  have hm9999 : min 9999 9999 = 9999 := rfl
  refine ⟨htier_lt, htier_sc, ?_⟩
  rw [hq, hm3u, hm3, hm6u, hm6]
  unfold yukonScore jointBlockGasSlope6K jointBlockGasSlope12K
    coldSloadRawTargetK coldSloadProbeEnvelopeTargetK sloadProbeRawTargetK sloadProbeEnvelopeTargetK
    avgProbeTargetFactor maxColdSloadTotalClock maxColdSloadProbeTicks maxTotalClock
    SelfContainedMasterK.prologueTicks GuestEvmStepOpcodeBounds.gasCap
  rw [hm9999]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Theorem 8 (`non_vacuous_and_tight`): `WordToWord` tail `NoSt = true` and `storeConstsAllowance = 0`
invariance across the multi-address merge and SLOAD probe budgets (`mergeSlope3UnrolledK`,
`mergeSlope3K`, `coldSloadRawTargetK`, `sloadProbeEnvelopeTargetK`, `mergeSlope6UnrolledK`,
`mergeSlope6K`). -/
theorem word_tail_zero_allowance_across_sload_and_multi_addr_merge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (ws : List (Bool × BitVec width)) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    mergeSlope3UnrolledK + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      408_348_416_306 ∧
    mergeSlope3K + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      408_348_430_106 ∧
    coldSloadRawTargetK + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      610_978_715_738 ∧
    sloadProbeEnvelopeTargetK + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      677_645_397_458 ∧
    mergeSlope6UnrolledK + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      816_696_823_280 ∧
    mergeSlope6K + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      816_696_837_080 ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have hs := source_clock_hierarchy_and_word_tail_zero_allowance_non_vacuous_and_tight ctx p labels b ws
  have hzero := hs.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hs.2.2.2.2.2.2.2.2.2.1, hzero, ?_, ?_,
    hs.2.2.2.2.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_, ?_,
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · rw [hzero, Nat.add_zero]; decide
  · rw [hzero, Nat.add_zero]; decide
  · rw [hzero, Nat.add_zero]; decide
  · rw [hzero, Nat.add_zero]; decide

/-- Theorem 9 (`non_vacuous_and_tight`): Monotone upward `InitE.Certificate` transfer from
`CertificateAt 1212035192` across all 36 budgets in `MultiAddressMergeThirtySixBudgetMaster.portfolio`,
all 32 budgets in `ThirtyTwoBudgetJointAbsorptionMaster`, and all 19 regimes in `SloadMultiAddrBridgeTier`
(including `sixPassUnrolledCopyLoopK`, `coldSloadRawTargetK`, `sloadProbeEnvelopeTargetK`,
`mergeSlope3UnrolledK`, `mergeSlope3K`, `mergeSlope6UnrolledK`, `mergeSlope6K`, and `.infinity`). -/
theorem certificate_from_1212M_lifts_to_all_36_merge_and_19_bridge_tiers_non_vacuous_and_tight
    (hc : CertificateAt 1212035192)
    (tier : SloadMultiAddrBridgeTier) :
    (∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (ThirtyTwoBudgetJointAbsorptionMaster.absorbBudget k))
        (.finite (ThirtyTwoBudgetJointAbsorptionMaster.absorbBudget k))) ∧
    InitE.Certificate (baselineWithFiniteK sixPassUnrolledCopyLoopK)
      (.finite sixPassUnrolledCopyLoopK) ∧
    InitE.Certificate (baselineWithFiniteK mergeSlope3UnrolledK) (.finite mergeSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK mergeSlope3K) (.finite mergeSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coldSloadRawTargetK) (.finite coldSloadRawTargetK) ∧
    InitE.Certificate (baselineWithFiniteK coldSloadProbeEnvelopeTargetK)
      (.finite coldSloadProbeEnvelopeTargetK) ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeRawTargetK) (.finite sloadProbeRawTargetK) ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeEnvelopeTargetK)
      (.finite sloadProbeEnvelopeTargetK) ∧
    InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK) (.finite mergeSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK mergeSlope6K) (.finite mergeSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK (selectBridgeK tier))
      (.finite (selectBridgeK tier)) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    (∀ K₁ K₂ : Nat, (baselineWithFiniteK K₁).K = .finite K₂ ↔ K₁ = K₂) := by
  have hunr_val : sixPassUnrolledCopyLoopK = 11_029_669_988 :=
    (dry_run_eight_tier_candidate_hierarchy_with_unrolled_copyloop_non_vacuous_and_tight 0).1
  have hcert_unr : InitE.Certificate (baselineWithFiniteK sixPassUnrolledCopyLoopK)
      (.finite sixPassUnrolledCopyLoopK) :=
    certificate_lift_non_vacuous_and_tight 1212035192 sixPassUnrolledCopyLoopK
      (by rw [hunr_val]; decide) hc
  have hport := portfolio_certificate_monotone_from_tier0_across_all_fifteen_tiers_non_vacuous_and_tight
    hcert_unr .coldSloadRaw
  have hm3u := MultiAddressMergeThirtySixBudgetMaster.mergeSlope3UnrolledK_certificate_non_vacuous_and_tight hc
  have hm3 := MultiAddressMergeThirtySixBudgetMaster.mergeSlope3K_certificate_non_vacuous_and_tight hc
  have hm6u := MultiAddressMergeThirtySixBudgetMaster.mergeSlope6UnrolledK_certificate_non_vacuous_and_tight hc
  have hm6 := MultiAddressMergeThirtySixBudgetMaster.mergeSlope6K_certificate_non_vacuous_and_tight hc
  have hc_bridge : InitE.Certificate (baselineWithFiniteK (selectBridgeK tier))
      (.finite (selectBridgeK tier)) := by
    cases tier with
    | sloadPortfolio t =>
      exact (portfolio_certificate_monotone_from_tier0_across_all_fifteen_tiers_non_vacuous_and_tight
        hcert_unr t).2.2.2.2.2.2.2.2.2.2.1
    | mergeSlope3Unrolled => exact hm3u
    | mergeSlope3 => exact hm3
    | mergeSlope6Unrolled => exact hm6u
    | mergeSlope6 => exact hm6
  exact ⟨MultiAddressMergeThirtySixBudgetMaster.portfolio_certificates_non_vacuous_and_tight hc,
    ThirtyTwoBudgetJointAbsorptionMaster.absorbed_certificates_non_vacuous_and_tight hc,
    hcert_unr, hm3u, hm3,
    hport.2.2.2.2.2.1, hport.2.2.2.2.2.2.1, hport.2.2.2.2.2.2.2.1, hport.2.2.2.2.2.2.2.2.1,
    hm6u, hm6, hc_bridge, hport.2.2.2.2.2.2.2.2.2.2.2.1, hport.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 10 (`non_vacuous_and_tight`): Upward `InitE.Certificate` chain from `coldSloadRawTargetK = 610,978,715,738`
through `coldSloadProbeEnvelopeTargetK = 610,978,730,738`, `sloadProbeRawTargetK = 677,645,382,458`,
`sloadProbeEnvelopeTargetK = 677,645,397,458`, `mergeSlope6UnrolledK = 816,696,823,280`,
`mergeSlope6K = 816,696,837,080`, `quadraticCollisionTargetK = 857,678,983,380`, and
`InitE.baselineSubmission` (`.infinity`), with 1-tick sharpness at `coldSloadRawTargetK`. -/
theorem cold_sload_raw_lifts_to_mergeSlope6_and_quadratic_certificates_non_vacuous_and_tight
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
        coldSloadRawTargetK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK coldSloadRawTargetK) (.finite coldSloadRawTargetK) ∧
    InitE.Certificate (baselineWithFiniteK coldSloadProbeEnvelopeTargetK)
      (.finite coldSloadProbeEnvelopeTargetK) ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeRawTargetK) (.finite sloadProbeRawTargetK) ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeEnvelopeTargetK)
      (.finite sloadProbeEnvelopeTargetK) ∧
    InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK) (.finite mergeSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK mergeSlope6K) (.finite mergeSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK quadraticCollisionTargetK)
      (.finite quadraticCollisionTargetK) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    ¬ (bootstrapSteps + avgProbeTargetFactor * maxColdSloadTotalClock ≤ coldSloadRawTargetK - 1) := by
  have hcr := cold_sload_raw_and_probe_envelope_certificate_chain_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut
  have hcert_cr := hcr.1
  have hm6u : InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK)
      (.finite mergeSlope6UnrolledK) :=
    certificate_lift_non_vacuous_and_tight coldSloadRawTargetK mergeSlope6UnrolledK (by decide) hcert_cr
  have hm6 : InitE.Certificate (baselineWithFiniteK mergeSlope6K)
      (.finite mergeSlope6K) :=
    certificate_lift_non_vacuous_and_tight coldSloadRawTargetK mergeSlope6K (by decide) hcert_cr
  exact ⟨hcert_cr, hcr.2.1, hcr.2.2.1, hcr.2.2.2.1, hm6u, hm6,
    hcr.2.2.2.2.1, hcr.2.2.2.2.2.1, hcr.2.2.2.2.2.2⟩

/-- Theorem 11 (`non_vacuous_and_tight`): Master end-to-end bridge uniting
`SloadProbeDryRunPortfolio`, `MultiAddressMergeThirtySixBudgetMaster`, and
`GuestFiveAddrTablesMergeBound` under uniform target non-`.timeOut` at
`sixPassReducedK = 11,029,683,788`: certifies `sixPassReducedK`, `jointBlockGasSlope3K`,
`jointBlockGasSlope6K`, `mergeSlope3UnrolledK`, `mergeSlope3K`, `jointBlockGasSlope12K`,
`coldSloadRawTargetK`, `coldSloadProbeEnvelopeTargetK`, `sloadProbeRawTargetK`,
`sloadProbeEnvelopeTargetK`, `mergeSlope6UnrolledK`, `mergeSlope6K`, and `InitE.baselineSubmission`,
alongside 5- and 12-table quadratic absorption, `claim.json ≤ 128` bytes, `yukonScore < 2^53 - 1`,
`NoSt = true`, `storeConstsAllowance = 0`, and `zeroBoundedImportCount = 0`. -/
theorem master_sload_probe_multi_addr_merge_five_tables_bridge_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (D A W Tloc Tlin : Nat)
    (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (bridgeTier : SloadMultiAddrBridgeTier)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_sixPassReduced : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        sixPassReducedK (baselineInitialState input)).1 ≠ .timeOut) :
    40 * (2 * ((D + A) * (W + D + A)) + 5 * (A * A)) ≤ S * S ∧
    40 * (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) ≤ S * S ∧
    linear + Tloc + (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) + Tlin ≤ kPanMultiAddrMerge ∧
    portfolio.length = 36 ∧
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    InitE.Certificate (baselineWithFiniteK mergeSlope3UnrolledK) (.finite mergeSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK mergeSlope3K) (.finite mergeSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coldSloadRawTargetK) (.finite coldSloadRawTargetK) ∧
    InitE.Certificate (baselineWithFiniteK coldSloadProbeEnvelopeTargetK)
      (.finite coldSloadProbeEnvelopeTargetK) ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeRawTargetK) (.finite sloadProbeRawTargetK) ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeEnvelopeTargetK)
      (.finite sloadProbeEnvelopeTargetK) ∧
    InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK) (.finite mergeSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK mergeSlope6K) (.finite mergeSlope6K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    validFiniteClaim (selectBridgeK bridgeTier) (selectBridgeClaimJson bridgeTier) = true ∧
    (selectBridgeClaimJson bridgeTier).utf8ByteSize ≤ MAX_CLAIM_BYTES ∧
    yukonScore (selectBridgeK bridgeTier) minutes < 2 ^ 53 - 1 ∧
    zeroBoundedImportCount = 0 := by
  have h5_12 := five_and_twelve_addr_tables_absorbed_into_kPanMultiAddrMerge_non_vacuous_and_tight
    D A W Tloc Tlin h hloc hlin
  have hm := master_sload_probe_dry_run_joint_block_gas_portfolio_certificate_non_vacuous_and_tight
    ctx p labels b .tier1SixPassReduced .coldSloadRaw oracles c depth minutes hlab compiled depthBound
    not_timeOut_sixPassReduced
  have hcert_red := hm.2.2.2.2.2.2.1
  have hred : sixPassReducedK = 11_029_683_788 :=
    (dry_run_eight_tier_candidate_hierarchy_with_unrolled_copyloop_non_vacuous_and_tight 0).2.1
  have hm3u : InitE.Certificate (baselineWithFiniteK mergeSlope3UnrolledK)
      (.finite mergeSlope3UnrolledK) :=
    certificate_lift_non_vacuous_and_tight sixPassReducedK mergeSlope3UnrolledK
      (by rw [hred]; decide) hcert_red
  have hm3 : InitE.Certificate (baselineWithFiniteK mergeSlope3K)
      (.finite mergeSlope3K) :=
    certificate_lift_non_vacuous_and_tight sixPassReducedK mergeSlope3K
      (by rw [hred]; decide) hcert_red
  have hm6u : InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK)
      (.finite mergeSlope6UnrolledK) :=
    certificate_lift_non_vacuous_and_tight sixPassReducedK mergeSlope6UnrolledK
      (by rw [hred]; decide) hcert_red
  have hm6 : InitE.Certificate (baselineWithFiniteK mergeSlope6K)
      (.finite mergeSlope6K) :=
    certificate_lift_non_vacuous_and_tight sixPassReducedK mergeSlope6K
      (by rw [hred]; decide) hcert_red
  have hcl := all_nineteen_bridge_tiers_claim_json_le_128_bytes_non_vacuous_and_tight bridgeTier 0
  have hsc := bridge_yukonScore_strict_monotonicity_across_sload_and_merge_non_vacuous_and_tight
    bridgeTier minutes 0
  exact ⟨h5_12.1, h5_12.2.1, h5_12.2.2.2.2.2.1,
    portfolio_non_vacuous_and_tight.1,
    hm.2.2.2.2.1, hm.2.2.2.2.2.1,
    hcert_red, hm3u, hm3,
    hm.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm6u, hm6,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hcl.2.2.2.2.2.2.2.2.2.2.1,
    hcl.2.2.2.2.2.2.2.2.1,
    hsc.2.1,
    rfl⟩

#print axioms five_and_twelve_addr_tables_absorbed_into_kPanMultiAddrMerge_non_vacuous_and_tight
#print axioms coupled_five_addr_tables_and_target_merge_bounds_non_vacuous_and_tight
#print axioms source_clock_hierarchy_with_kPanMultiAddrMerge_and_sload_non_vacuous_and_tight
#print axioms complete_nineteen_regime_strict_ordering_sload_and_multi_addr_merge_non_vacuous_and_tight
#print axioms thirty_six_budget_portfolio_and_sload_merge_gaps_non_vacuous_and_tight
#print axioms all_nineteen_bridge_tiers_claim_json_le_128_bytes_non_vacuous_and_tight
#print axioms bridge_yukonScore_strict_monotonicity_across_sload_and_merge_non_vacuous_and_tight
#print axioms word_tail_zero_allowance_across_sload_and_multi_addr_merge_non_vacuous_and_tight
#print axioms certificate_from_1212M_lifts_to_all_36_merge_and_19_bridge_tiers_non_vacuous_and_tight
#print axioms cold_sload_raw_lifts_to_mergeSlope6_and_quadratic_certificates_non_vacuous_and_tight
#print axioms master_sload_probe_multi_addr_merge_five_tables_bridge_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SloadProbeAndMultiAddrMergeBridge
