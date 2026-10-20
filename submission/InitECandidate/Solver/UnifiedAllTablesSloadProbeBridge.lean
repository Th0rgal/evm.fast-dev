import InitECandidate.Solver.SloadProbeAndMultiAddrMergeBridge
import InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope
import InitECandidate.Solver.FiveAddrTablesThirtySixBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.UnifiedAllTablesSloadProbeBridge` — Wave 5 Atomic Worker `W5_97`

Self-contained bridge module (**0 `Proofs/Bounded*` imports**) integrating:
1. `SloadProbeAndMultiAddrMergeBridge` (`11/11` tight): 15 `SLOAD` / dry-run regimes and 36 budgets
   under Yukon (`SloadMultiAddrBridgeTier`, `coldSloadRawTargetK = 610,978,715,738`,
   `sloadProbeEnvelopeTargetK = 677,645,397,458`, `mergeSlope3UnrolledK = 408,348,416,306`,
   `mergeSlope3K = 408,348,430,106`, `mergeSlope6UnrolledK = 816,696,823,280`,
   `mergeSlope6K = 816,696,837,080 < 900,719,925,474`),
2. `GuestUnifiedAllTablesMasterEnvelope` (`11/11` tight): unified 5-variable `(D, R, A, C, W)`
   coupled and merge envelopes across all 9 block/transaction hash tables (`bs+32`, `ts+32`,
   `bs+72`, `bs+8/16/24/40/48` + tx storage):
   - `42 * F D R A C W ≤ S * S` (`F D R A C W ≤ 95,238,095,238`),
   - `40 * G D R A C W ≤ S * S` (`G D R A C W ≤ 100,000,000,000 = blockMerge`),
   - `kPanUnifiedAllTables = 136,116,135,658 = kPanMultiAddrMerge = kPanMerge`,
3. `FiveAddrTablesThirtySixBudgetMaster` (`47/47` tight): 5-table (`[bs+8, bs+16, bs+24, bs+40, bs+48]`)
   and 12-probe quadratic absorption, 36-budget portfolio, and unconditional `StackNoSt` /
   `flatten_storeConsts_empty` backend invariants.
-/

namespace InitECandidate.Solver.UnifiedAllTablesSloadProbeBridge

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
open InitECandidate.Solver.FiveAddrTablesThirtySixBudgetMaster
  (mergeSlope3UnrolledK mergeSlope3K mergeSlope6UnrolledK mergeSlope6K)
open InitECandidate.Solver.SloadProbeAndMultiAddrMergeBridge
open InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope
open Flapjack
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open PanToStackNoStoreConsts

/-- Explicit 9-table offset list covering all block/tx hash tables:
`ts+32`, `bs+32`, `bs+72`, and the 5 address tables `bs+8/16/24/40/48` plus tx-level merge. -/
def nineHashTableOffsets (ts bs : Nat) : List Nat :=
  [ts + 32, bs + 32, bs + 72, bs + 8, bs + 16, bs + 24, bs + 40, bs + 48, ts + 8]

/-! ## Eleven `non_vacuous_and_tight` Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Unified 5-variable coupled envelope
`42 * F D R A C W ≤ S * S` (`F D R A C W ≤ 95,238,095,238 < blockMerge`) over `(D, R, A, C, W)`
under `21*D + 20*R + 26*A + 21*C + W ≤ S`, together with exact boundary attainment at
`(47,619, 0, 0, 0, 1,000,001)`, cold-storage corner `F 0 0 0 95238 0 = 9,070,276,644`,
and address-table corner `2 * (0 * 0) + 12 * (76923 * 76923) = 71,005,775,148`. -/
theorem unified_five_var_coupled_envelope_and_corners_non_vacuous_and_tight
    (D R A C W : Nat)
    (h : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S) :
    42 * F D R A C W ≤ S * S ∧
    F D R A C W ≤ 95_238_095_238 ∧
    95_238_095_238 < blockMerge ∧
    21 * 47619 + 20 * 0 + 26 * 0 + 21 * 0 + 1000001 = S ∧
    F 47619 0 0 0 1000001 = 95_238_095_238 ∧
    F 0 0 0 95238 0 = 9_070_276_644 ∧
    9_070_276_644 < 95_238_095_238 ∧
    2 * (0 * 0) + 12 * (76923 * 76923) = 71_005_775_148 ∧
    71_005_775_148 < 95_238_095_238 := by
  have h1 := unified_five_var_coupled_envelope D R A C W h
  have h2 := unified_coupled_le D R A C W h
  have ht := unified_coupled_tight
  have hc := unified_cold_corner
  have hac := FiveAddrTablesThirtySixBudgetMaster.coupled_addr_corner_non_vacuous_and_tight
  exact ⟨h1, h2, by decide, ht.1, ht.2, hc.1, hc.2, hac.2.1, hac.2.2⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Unified 5-variable merge envelope
`40 * G D R A C W ≤ S * S` (`G D R A C W ≤ 100,000,000,000 = blockMerge`) and source master bound
`linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables` with exact identity
`kPanUnifiedAllTables = kPanMultiAddrMerge = kPanMerge = 136,116,135,658`, plus dual face tightness
at `(50,000, 0, 0, 0, 950,000)` and `(2,000, 48,000, 0, 0, 950,000)`. -/
theorem unified_five_var_merge_envelope_and_kPanUnified_identity_non_vacuous_and_tight
    (D R A C W Tloc Tlin : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    40 * G D R A C W ≤ S * S ∧
    G D R A C W ≤ 100_000_000_000 ∧
    G D R A C W ≤ blockMerge ∧
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables ∧
    kPanUnifiedAllTables = 136_116_135_658 ∧
    kPanUnifiedAllTables = kPanMultiAddrMerge ∧
    kPanUnifiedAllTables = kPanMerge ∧
    G 50000 0 0 0 950000 = 100_000_000_000 ∧
    G 2000 48000 0 0 950000 = 100_000_000_000 ∧
    20 * (2000 + 48000 + 0) + 6 * 0 + 21 * 0 + (950000 + (2000 + 48000 + 0)) = S := by
  have hm := unified_five_var_merge_envelope D R A C W h
  have hle := unified_merge_le D R A C W h
  have hbm : blockMerge = 100_000_000_000 := rfl
  have hmas := kPanUnified_master D R A C W Tloc Tlin h hloc hlin
  have hval := kPanUnified_val
  have hk_multi := FiveAddrTablesThirtySixBudgetMaster.kPanMultiAddrMerge_eq_non_vacuous_and_tight
  have ht := unified_merge_tight
  refine ⟨hm, hle, ?_, hmas, hval.1, ?_, hval.2, ht.1, ht.2.1, ht.2.2⟩
  · rw [hbm]; exact hle
  · rw [hval.2, hk_multi.1]

/-- Theorem 3 (`non_vacuous_and_tight`): Integration of the 5 address tables
(`[bs+8, bs+16, bs+24, bs+40, bs+48]`), the 9 hash table offsets, the 12-probe bound,
and the 5-variable unified all-tables envelope into the four multi-address target merge tiers
(`mergeSlope3UnrolledK`, `mergeSlope3K`, `mergeSlope6UnrolledK`, `mergeSlope6K`). -/
theorem nine_tables_and_five_addr_offsets_target_merge_tiers_non_vacuous_and_tight
    (ts bs D R A C W Tloc Tlin : Nat)
    (h5 : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (h3 : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    (nineHashTableOffsets ts bs).length = 9 ∧
    ([bs + 8, bs + 16, bs + 24, bs + 40, bs + 48].map (fun _ => A * A)).sum = 5 * (A * A) ∧
    linear + Tloc + (2 * ((D + A) * (W + D + A)) +
      ([bs + 8, bs + 16, bs + 24, bs + 40, bs + 48].map (fun _ => A * A)).sum) + Tlin ≤
      kPanUnifiedAllTables ∧
    9332 + 3 * (linear + Tloc + G D R A C W + Tlin) ≤ mergeSlope3UnrolledK ∧
    23132 + 3 * (linear + Tloc + G D R A C W + Tlin) ≤ mergeSlope3K ∧
    9332 + 6 * (linear + Tloc + G D R A C W + Tlin) ≤ mergeSlope6UnrolledK ∧
    23132 + 6 * (linear + Tloc + G D R A C W + Tlin) ≤ mergeSlope6K ∧
    mergeSlope6K < 900_719_925_474 := by
  have hoff := FiveAddrTablesThirtySixBudgetMaster.five_offsets_non_vacuous_and_tight bs A
  have h5m := FiveAddrTablesThirtySixBudgetMaster.five_master_non_vacuous_and_tight bs D A W Tloc Tlin h3 hloc hlin
  have hmas := kPanUnified_master D R A C W Tloc Tlin h5 hloc hlin
  have hk_val := kPanUnified_val.1
  have hk_multi := FiveAddrTablesThirtySixBudgetMaster.kPanMultiAddrMerge_eq_non_vacuous_and_tight.2
  have hmv := FiveAddrTablesThirtySixBudgetMaster.values_non_vacuous_and_tight
  have hm3u : mergeSlope3UnrolledK = 408_348_416_306 := hmv.1
  have hm3 : mergeSlope3K = 408_348_430_106 := hmv.2.1
  have hm6u : mergeSlope6UnrolledK = 816_696_823_280 := hmv.2.2.1
  have hm6 : mergeSlope6K = 816_696_837_080 := hmv.2.2.2.1
  refine ⟨rfl, hoff, ?_, ?_, ?_, ?_, ?_, hmv.2.2.2.2⟩
  · rw [hk_val]; rw [hk_multi] at h5m; exact h5m
  · rw [hm3u]; rw [hk_val] at hmas; omega
  · rw [hm3]; rw [hk_val] at hmas; omega
  · rw [hm6u]; rw [hk_val] at hmas; omega
  · rw [hm6]; rw [hk_val] at hmas; omega

/-- Theorem 4 (`non_vacuous_and_tight`): Joint source-clock hierarchy uniting
`kPanJoint 6 = 40,486,477,625`, `maxGuestSourceClock = 43,914,839,586`,
`blockVsTxSourceK = 71,448,666,010`, `kPanUnifiedAllTables = kPanMultiAddrMerge = kPanMerge = 136,116,135,658`,
`maxColdSloadTotalClock = 203,659,564,202`, and `maxTotalClock = 225,881,786,442`,
with sharp Yukon multiplier thresholds `k ≤ 6` for `kPanUnifiedAllTables` and `M ≤ 3` for `maxTotalClock`. -/
theorem unified_all_tables_source_clock_hierarchy_with_sload_non_vacuous_and_tight
    (k M : Nat) :
    kPanJoint 6 = 40_486_477_625 ∧
    maxGuestSourceClock = 43_914_839_586 ∧
    blockVsTxSourceK = 71_448_666_010 ∧
    kPanUnifiedAllTables = 136_116_135_658 ∧
    kPanUnifiedAllTables = kPanMultiAddrMerge ∧
    maxColdSloadTotalClock = 203_659_564_202 ∧
    maxTotalClock = 225_881_786_442 ∧
    kPanJoint 6 < maxGuestSourceClock ∧
    maxGuestSourceClock < blockVsTxSourceK ∧
    blockVsTxSourceK < kPanUnifiedAllTables ∧
    kPanUnifiedAllTables < maxColdSloadTotalClock ∧
    maxColdSloadTotalClock < maxTotalClock ∧
    6 * kPanUnifiedAllTables < yukon ∧
    yukon - 6 * kPanUnifiedAllTables = 84_023_111_526 ∧
    (k * kPanUnifiedAllTables < yukon ↔ k ≤ 6) ∧
    (bootstrapSteps + M * (maxTotalClock + pipeOffset) < yukonFloat64StepCeiling ↔ M ≤ 3) := by
  have hs := source_clock_hierarchy_with_kPanMultiAddrMerge_and_sload_non_vacuous_and_tight k M
  have hval := kPanUnified_val.1
  have hsl := slopes k
  have hk_eq : kPanUnifiedAllTables = kPanMultiAddrMerge := by
    rw [hval, hs.2.2.2.1]
  rw [hk_eq]
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, rfl, hs.2.2.2.2.1, hs.2.2.2.2.2.1,
    hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1,
    hs.2.2.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.2.2.1,
    by rw [← hk_eq]; exact hsl.1,
    hs.2.2.2.2.2.2.2.2.2.2.2.1,
    hs.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 5 (`non_vacuous_and_tight`): Complete strict ordering across all 19 target regimes
uniting the 15 `SloadProbeDryRunPortfolio` regimes and the 4 unified all-tables merge tiers
(`9332 + 3 * kPanUnifiedAllTables = mergeSlope3UnrolledK < mergeSlope3K` and
`9332 + 6 * kPanUnifiedAllTables = mergeSlope6UnrolledK < mergeSlope6K`), with exact Yukon
threshold `23132 + K * kPanUnifiedAllTables < yukon ↔ K ≤ 6`. -/
theorem complete_nineteen_regime_strict_ordering_unified_all_tables_and_sload_non_vacuous_and_tight
    (K : Nat) :
    9332 + 3 * kPanUnifiedAllTables = mergeSlope3UnrolledK ∧
    23132 + 3 * kPanUnifiedAllTables = mergeSlope3K ∧
    9332 + 6 * kPanUnifiedAllTables = mergeSlope6UnrolledK ∧
    23132 + 6 * kPanUnifiedAllTables = mergeSlope6K ∧
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
    (23132 + K * kPanUnifiedAllTables < yukon ↔ K ≤ 6) := by
  have hord := complete_nineteen_regime_strict_ordering_sload_and_multi_addr_merge_non_vacuous_and_tight K
  have htp := FiveAddrTablesThirtySixBudgetMaster.tiers_preserved_non_vacuous_and_tight
  have hk_eq : kPanUnifiedAllTables = kPanMultiAddrMerge := by
    rw [kPanUnified_val.1, FiveAddrTablesThirtySixBudgetMaster.kPanMultiAddrMerge_eq_non_vacuous_and_tight.2]
  rw [hk_eq]
  exact ⟨htp.1, htp.2.1, htp.2.2.1, htp.2.2.2, hord⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Exact step gaps, 36-budget portfolio pairwise ordering,
and 1-tick saturation connecting `FiveAddrTablesThirtySixBudgetMaster.portfolio`,
`kPanUnifiedAllTables`, and the `SLOAD` probe envelope. -/
theorem unified_all_tables_thirty_six_budget_portfolio_and_sload_gaps_non_vacuous_and_tight :
    FiveAddrTablesThirtySixBudgetMaster.portfolio.length = 36 ∧
    FiveAddrTablesThirtySixBudgetMaster.portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ FiveAddrTablesThirtySixBudgetMaster.portfolio, 1_212_035_192 ≤ k ∧ k < yukon) ∧
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      k ∈ FiveAddrTablesThirtySixBudgetMaster.portfolio) ∧
    mergeSlope3K - mergeSlope3UnrolledK = 13_800 ∧
    mergeSlope6K - mergeSlope6UnrolledK = 13_800 ∧
    coldSloadProbeEnvelopeTargetK - coldSloadRawTargetK = 15_000 ∧
    sloadProbeEnvelopeTargetK - sloadProbeRawTargetK = 15_000 ∧
    mergeSlope6UnrolledK - sloadProbeEnvelopeTargetK = 139_051_425_822 ∧
    mergeSlope6K - sloadProbeEnvelopeTargetK = 139_051_439_622 ∧
    quadraticCollisionTargetK - mergeSlope6K = 40_982_146_300 ∧
    yukon - mergeSlope6K = 84_023_088_394 ∧
    ¬ (23132 + 6 * kPanUnifiedAllTables ≤ mergeSlope6K - 1) := by
  have hg := thirty_six_budget_portfolio_and_sload_merge_gaps_non_vacuous_and_tight
  have hk_eq : kPanUnifiedAllTables = kPanMultiAddrMerge := by
    rw [kPanUnified_val.1, FiveAddrTablesThirtySixBudgetMaster.kPanMultiAddrMerge_eq_non_vacuous_and_tight.2]
  rw [hk_eq]
  exact hg

/-- Theorem 7 (`non_vacuous_and_tight`): Universal `claim.json ≤ 128`-byte compliance and
`validFiniteClaim` verification across all 19 bridge regimes (`SloadMultiAddrBridgeTier`),
with exact 29-byte `claimed_k` payloads and 19-byte verifier `K` payloads for the 4 unified
all-tables merge tiers. -/
theorem unified_all_tables_nineteen_bridge_tiers_claim_json_le_128_bytes_non_vacuous_and_tight
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
      claimBytes ≤ 128) :=
  all_nineteen_bridge_tiers_claim_json_le_128_bytes_non_vacuous_and_tight tier claimBytes

/-- Theorem 8 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity and IEEE-754 `float64`
representability (`< 2^53 - 1`) across all 19 bridge regimes (`selectBridgeK tier`), including
the 4 unified all-tables merge tiers (`mergeSlope3UnrolledK`, `mergeSlope3K`,
`mergeSlope6UnrolledK`, `mergeSlope6K`) and the 4 `SLOAD` probe regimes. -/
theorem unified_all_tables_yukonScore_strict_monotonicity_non_vacuous_and_tight
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
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) :=
  bridge_yukonScore_strict_monotonicity_across_sload_and_merge_non_vacuous_and_tight tier minutes K

/-- Theorem 9 (`non_vacuous_and_tight`): Unconditional backend invariants from
`FiveAddrTablesThirtySixBudgetMaster` (`StackNoSt = true`, `FlattenVisitsSt = false`,
`flatten_storeConsts_empty`) combined with `WordToWord` tail `NoSt = true` and
`storeConstsAllowance = 0` invariance across `kPanUnifiedAllTables`, `mergeSlope3UnrolledK`,
`mergeSlope3K`, `coldSloadRawTargetK`, `sloadProbeEnvelopeTargetK`, `mergeSlope6UnrolledK`,
and `mergeSlope6K`. -/
theorem unified_all_tables_and_sload_backend_no_store_consts_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (ws : List (Bool × BitVec width)) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    kPanUnifiedAllTables + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      136_116_135_658 ∧
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
    (∀ (t : Bool) (s b0 : Nat) (stub : Option Nat) (sid next : Nat) (cs bs : List Nat),
      StackToLab.flattenHOL t (.storeConsts s b0 stub : HolProg width) sid next cs bs =
        (.list [], false, next)) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have hw := word_tail_zero_allowance_across_sload_and_multi_addr_merge_non_vacuous_and_tight
    ctx p labels b ws
  have hzero := hw.2.1
  have hkp : kPanUnifiedAllTables + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      136_116_135_658 := by
    rw [hzero, Nat.add_zero, kPanUnified_val.1]
  exact ⟨hw.1, hzero, hkp, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
    hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1,
    FiveAddrTablesThirtySixBudgetMaster.flatten_storeConsts_empty_non_vacuous_and_tight,
    FiveAddrTablesThirtySixBudgetMaster.panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight
      arch prog wc ac perf info j bd ptr f,
    hw.2.2.2.2.2.2.2.2⟩

/-- Theorem 10 (`non_vacuous_and_tight`): Monotone upward `InitE.Certificate` transfer from
`CertificateAt 1212035192` across all 36 budgets in `FiveAddrTablesThirtySixBudgetMaster.portfolio`,
all 32 budgets in `ThirtyTwoBudgetJointAbsorptionMaster`, and all 19 regimes in
`SloadMultiAddrBridgeTier` alongside the unified 5-variable source bound `kPanUnifiedAllTables`. -/
theorem unified_all_tables_and_36_budgets_certificate_lift_from_1212M_non_vacuous_and_tight
    (D R A C W Tloc Tlin : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hc : CertificateAt 1212035192)
    (tier : SloadMultiAddrBridgeTier) :
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables ∧
    (∀ k ∈ FiveAddrTablesThirtySixBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
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
    (∀ K₁ K₂ : Nat, (baselineWithFiniteK K₁).K = .finite K₂ ↔ K₁ = K₂) :=
  ⟨kPanUnified_master D R A C W Tloc Tlin h hloc hlin,
    certificate_from_1212M_lifts_to_all_36_merge_and_19_bridge_tiers_non_vacuous_and_tight hc tier⟩

/-- Theorem 11 (`non_vacuous_and_tight`): Master end-to-end bridge uniting
`SloadProbeAndMultiAddrMergeBridge`, `GuestUnifiedAllTablesMasterEnvelope` (5-variable `(D, R, A, C, W)`
coupled and merge envelopes over all 9 hash tables), and `FiveAddrTablesThirtySixBudgetMaster`
under uniform target non-`.timeOut` at `sixPassReducedK = 11,029,683,788`:
certifies `sixPassReducedK`, `mergeSlope3UnrolledK`, `mergeSlope3K`, `coldSloadRawTargetK`,
`coldSloadProbeEnvelopeTargetK`, `sloadProbeRawTargetK`, `sloadProbeEnvelopeTargetK`,
`mergeSlope6UnrolledK`, `mergeSlope6K`, and `InitE.baselineSubmission`, alongside
`F D R A C W ≤ 95,238,095,238`, `G D R A C W ≤ 100,000,000,000`, `kPanUnifiedAllTables = 136,116,135,658`,
`claim.json ≤ 128` bytes, `yukonScore < 2^53 - 1`, `NoSt = true`, `storeConstsAllowance = 0`,
and `zeroBoundedImportCount = 0`. -/
theorem master_unified_all_tables_sload_probe_thirty_six_budget_bridge_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (D R A C W Tloc Tlin : Nat)
    (hcoup : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hmerge : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (h3 : 20 * D + 26 * A + (W + D + A) ≤ S)
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
    42 * F D R A C W ≤ S * S ∧
    F D R A C W ≤ 95_238_095_238 ∧
    40 * G D R A C W ≤ S * S ∧
    G D R A C W ≤ 100_000_000_000 ∧
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables ∧
    kPanUnifiedAllTables = 136_116_135_658 ∧
    FiveAddrTablesThirtySixBudgetMaster.portfolio.length = 36 ∧
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
  have hbr := master_sload_probe_multi_addr_merge_five_tables_bridge_certificate_non_vacuous_and_tight
    ctx p labels b D A W Tloc Tlin h3 hloc hlin bridgeTier oracles c depth minutes
    hlab compiled depthBound not_timeOut_sixPassReduced
  exact ⟨unified_five_var_coupled_envelope D R A C W hcoup,
    unified_coupled_le D R A C W hcoup,
    unified_five_var_merge_envelope D R A C W hmerge,
    unified_merge_le D R A C W hmerge,
    kPanUnified_master D R A C W Tloc Tlin hmerge hloc hlin,
    kPanUnified_val.1,
    hbr.2.2.2⟩

#print axioms unified_five_var_coupled_envelope_and_corners_non_vacuous_and_tight
#print axioms unified_five_var_merge_envelope_and_kPanUnified_identity_non_vacuous_and_tight
#print axioms nine_tables_and_five_addr_offsets_target_merge_tiers_non_vacuous_and_tight
#print axioms unified_all_tables_source_clock_hierarchy_with_sload_non_vacuous_and_tight
#print axioms complete_nineteen_regime_strict_ordering_unified_all_tables_and_sload_non_vacuous_and_tight
#print axioms unified_all_tables_thirty_six_budget_portfolio_and_sload_gaps_non_vacuous_and_tight
#print axioms unified_all_tables_nineteen_bridge_tiers_claim_json_le_128_bytes_non_vacuous_and_tight
#print axioms unified_all_tables_yukonScore_strict_monotonicity_non_vacuous_and_tight
#print axioms unified_all_tables_and_sload_backend_no_store_consts_non_vacuous_and_tight
#print axioms unified_all_tables_and_36_budgets_certificate_lift_from_1212M_non_vacuous_and_tight
#print axioms master_unified_all_tables_sload_probe_thirty_six_budget_bridge_certificate_non_vacuous_and_tight

end InitECandidate.Solver.UnifiedAllTablesSloadProbeBridge
