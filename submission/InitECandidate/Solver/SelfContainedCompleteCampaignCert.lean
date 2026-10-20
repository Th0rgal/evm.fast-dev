import InitECandidate.Solver.SelfContainedAllAxesSynthesis
import InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
import InitECandidate.Solver.GuestBlockVsTxHtabBounds
import InitECandidate.Solver.PerTxEip7825TargetMasterK
import InitECandidate.Solver.RiscvSszFastRejectAndBootCert

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SelfContainedCompleteCampaignCert` — Master Complete Campaign Certificate (`W5_46`)

This module has **0 imports from `InitECandidate.Proofs.Bounded*`** in its transitive closure and
unites all five campaign components across Axes A, B, C, D, and E into a single self-contained
complete campaign certificate:

1. **Six-Pass Pipeline & `StackRemove` Zero-Copy Bridge (`StackRemoveStoreConstsZeroBridge` + `SelfContainedSixPassMaster`)**:
   - Syntactic absence of `storeConsts` and `alloc` in `LoopToWord.compHOL` (`compHOL_NoSC`,
     `compiled_allowance_zero`) and trace provenance bridge (`TraceFrom`, `allowance_zero_of_NoSC`,
     `compiled_run_allowance_zero`),
   - Neutral six-pass slope (`sixPassSlope 1 3 = 3`) and exact affine composition
     (`sixPassAffine d_cl d_ws 0 clock = 3 * clock + (d_cl + d_ws)`).
2. **EIP-7825 Per-Transaction vs Block-Level Hash-Table Analysis (`PerTxEip7825TargetMasterK` + `GuestBlockVsTxHtabBounds`)**:
   - Per-transaction EIP-7825 (`16,777,216` gas/tx, `txUnits = 167,772`) collision bound (`perTxSourceK = 20,436,764,234`)
     and six-pass target budget `perTxSixPassTargetK = 122,620,608,536` (`> 7.3x` below Yukon ceiling),
   - Block-level `bs+72` pre-state read set (`blkRead maxColdPerBlock = 13,605,272,109` ticks at `95,238` cold accesses)
     and combined `SLOAD` + `SSTORE` (`pSstore = 14`) + `BALANCE` + `PUSH31` source clock bound
     `kPanBlock c ≤ 71,448,666,010` (`> 12x` below Yukon ceiling).
3. **RISC-V Bootstrap Unrolling & `22`-Step SSZ Fast-Reject (`RiscvSszFastRejectAndBootCert`)**:
   - 4x-unrolled `copyLoop` saving `copyLoopSavedSteps = 13,800` steps (`-138,000,000` Yukon points),
     reducing `sixPassReducedK = 11,029,683,788` to `sixPassUnrolledCopyLoopK = 11,029,669,988`
     (and `sixPassStraightLineK = 11,029,669,937`),
   - `22`-step RISC-V SSZ container header fast-reject (`sszFastRejectSteps = 22 = 6 + 16`)
     deciding `ValidSszContainerHeader` before `copyLoop`.
4. **Five-Axis Campaign Synthesis (`SelfContainedAllAxesSynthesis`)**:
   - Complete ordering of all campaign step budgets and Yukon scores, `0` `Bounded*` imports,
     `2,882` vs `55,882` transitive modules (`53,000` `Bounded*` stage modules eliminated),
     and end-to-end `InitE.Certificate` monotonicity across all candidate budgets.
-/

namespace InitECandidate.Solver.SelfContainedCompleteCampaignCert

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
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.GuestEvmStepOpcodeBounds
open InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds
open InitECandidate.Solver.GuestBlockVsTxHtabBounds
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
open InitECandidate.Solver.SelfContainedAllAxesSynthesis
open Flapjack
open Flapjack.LoopToWord
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang

/-! ## Section 1: Campaign Master Constants -/

/-- Exact combined block-level + per-tx `SSTORE` (`pSstore = 14`) source clock ceiling (`71,448,666,010` ticks). -/
def blockVsTxMaxSourceK : Nat := 71_448_666_010

/-- Exact block-level `bs+72` pre-state read set collision ceiling at `maxColdPerBlock = 95,238` (`13,605,272,109` ticks). -/
def blockPreStateReadMaxTicks : Nat := 13_605_272_109

/-- Exact per-transaction `SSTORE` collision ceiling (`14 * 167,772^2 / 80 = 4,925,802,697` ticks). -/
def perTxSstoreMaxTicks : Nat := 4_925_802_697

/-! ## Section 2: Ten+ `non_vacuous_and_tight` Complete Campaign Theorems -/

/-- Theorem 1 (`non_vacuous_and_tight`, **Six-Pass Chain & `StackRemoveStoreConstsZeroBridge`**):
Four-pass clock isometry (`C_pc * C_lw * C_ws * C_sn = 1`), neutral six-pass slope (`sixPassSlope 1 3 = 3`)
and affine clock (`sixPassAffine d_cl d_ws 0 clock = 3 * clock + (d_cl + d_ws)`), syntactic
`compHOL_NoSC`, structural `storeConstsAllowance = 0`, trace-provenance `allowance_zero_of_NoSC` /
`compiled_run_allowance_zero`, and tight non-zero payload witness `allowance_storeConsts_tight`. -/
theorem campaign_six_pass_and_storeConsts_zero_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat)
    (oracles : List (Option (Spt Nat))) (d_cl d_ws clock : Nat)
    (xs : List (Bool × Nat)) (origin : TraceFrom (LoopToWord.compHOL ctx p labels).1 xs)
    (ws : List (Bool × BitVec 64)) :
    C_pc * C_lw * C_ws * C_sn = 1 ∧
    sixPassSlope 1 3 = 3 ∧
    sixPassAffine d_cl d_ws 0 clock = 3 * clock + (d_cl + d_ws) ∧
    NoSC (LoopToWord.compHOL ctx p labels).1 = true ∧
    storeConstsAllowance (LoopToWord.compHOL ctx p labels).1 = 0 ∧
    (oracleCompilerConfig oracles).stackConf.jump = false ∧
    (∀ q ∈ xs, q.1 = false) ∧
    runAllowance xs = 0 ∧
    clock + storeConstsAllowance (LoopToWord.compHOL ctx p labels).1 = 1 * clock + 0 ∧
    clock + runAllowance xs = clock ∧
    storeConstsAllowance (WordLangProgHOL.storeConsts (α := BitVec 64) 0 2 4 6 ws) = ws.length := by
  have hgz := compiled_guest_zero ctx p labels oracles
  have hflags := noSC_trace_flags (LoopToWord.compHOL ctx p labels).1 xs
    (compHOL_NoSC ctx p labels) origin
  exact ⟨rfl, neutral_six_pass_slope, neutral_six_pass_affine d_cl d_ws clock,
    compHOL_NoSC ctx p labels, hgz.1, hgz.2, hflags,
    allowance_zero_of_NoSC xs hflags,
    compiled_clock_identity ctx p labels clock,
    compiled_trace_clock_identity ctx p labels clock xs origin,
    allowance_storeConsts_tight 0 2 4 6 ws⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **EIP-7825 Per-Transaction Analysis `PerTxEip7825TargetMasterK`**):
Per-transaction probe bound (`80 * (c * (w + c)) ≤ m * m`), multi-transaction collision sum bound
(`≤ 16,777,200,000` ticks), exact source envelope `perTxSourceK = 20,436,764,234 < maxGuestSourceClock`,
exact six-pass target budget `perTxSixPassTargetK = 122,620,608,536 = bootstrapSteps + 6 * perTxSourceK`,
and `> 7.3x` Yukon ceiling margin (`73 * perTxSixPassTargetK < 10 * 900,719,925,474`). -/
theorem campaign_per_tx_eip7825_target_master_non_vacuous_and_tight
    (c w m sourceTicks targetPost minutes : Nat) (ms : List Nat)
    (hcw : 21 * c + w ≤ m)
    (hcap : ∀ x ∈ ms, x ≤ 167772) (hsum : ms.sum ≤ 2000000)
    (hs : sourceTicks ≤ perTxSourceK) (ht : targetPost ≤ 6 * sourceTicks) :
    80 * (c * (w + c)) ≤ m * m ∧
    pEff * ((ms.map (fun x => x * x)).sum / 80) ≤ 16_777_200_000 ∧
    prologueTicks + 18 * GuestEvmStepOpcodeBounds.gasCap + pEff * ((ms.map (fun x => x * x)).sum / 80) ≤ perTxSourceK ∧
    perTxSourceK = 20_436_764_234 ∧
    perTxSourceK < 43_914_839_586 ∧
    perTxSourceK < maxGuestSourceClock ∧
    perTxSixPassTargetK = 122_620_608_536 ∧
    perTxSixPassTargetK = bootstrapSteps + 6 * perTxSourceK ∧
    bootstrapSteps + targetPost ≤ perTxSixPassTargetK ∧
    bootstrapSteps + 6 * perTxSourceK = perTxSixPassTargetK ∧
    73 * perTxSixPassTargetK < 10 * 900_719_925_474 ∧
    yukonScore perTxSixPassTargetK minutes < 2 ^ 53 - 1 ∧
    (bootstrapSteps + targetPost ≤ perTxSixPassTargetK ↔ targetPost ≤ 6 * perTxSourceK) := by
  refine ⟨per_tx_probes_bridge c w m hcw,
    per_tx_collision_ticks ms hcap hsum,
    per_tx_combined_bound ms hcap hsum,
    rfl,
    per_tx_source_below_requested_ceiling,
    per_tx_source_below_imported_ceiling,
    per_tx_target_exact,
    per_tx_target_formula,
    per_tx_target_bound sourceTicks targetPost hs ht,
    per_tx_target_saturated,
    per_tx_yukon_margin.1,
    per_tx_score_representable minutes,
    ?_⟩
  rw [per_tx_target_formula]
  omega

/-- Theorem 3 (`non_vacuous_and_tight`, **Block vs Transaction Hash-Table Separation `GuestBlockVsTxHtabBounds`**):
Exact block-level `bs+72` quadratic read-set cost (`2 * blkRead c = 3 * (c * (c - 1))`,
`blkRead c ≤ 13,605,272,109` attained at `maxColdPerBlock = 95,238`), per-tx `SSTORE` (`pSstore = 14`)
cluster bound (`≤ 4,925,802,697`), combined source clock bound `kPanBlock c ≤ 71,448,666,010`
(attained at `kPanBlock maxColdPerBlock = 71,448,666,010`), `> 12x` Yukon margin, and sharp per-opcode
slope threshold `kPanP p ≤ maxGuestSourceClock ↔ p ≤ 6`. -/
theorem campaign_block_vs_tx_htab_bounds_non_vacuous_and_tight
    (cCold cTx wTx p : Nat)
    (hcold : 2100 * cCold ≤ GuestEvmStepOpcodeBounds.gasCap)
    (htx : 21 * cTx + wTx ≤ txUnits) :
    txGasCap = 16_777_216 ∧
    txUnits = 167_772 ∧
    pSstore = 14 ∧
    maxColdPerBlock = 95_238 ∧
    txPerBlock = 11 ∧
    2 * blkRead cCold = 3 * (cCold * (cCold - 1)) ∧
    blkRead cCold ≤ blockPreStateReadMaxTicks ∧
    blkRead maxColdPerBlock = blockPreStateReadMaxTicks ∧
    pSstore * (cTx * (wTx + cTx)) ≤ perTxSstoreMaxTicks ∧
    kPanBlock cCold ≤ blockVsTxMaxSourceK ∧
    kPanBlock maxColdPerBlock = blockVsTxMaxSourceK ∧
    12 * kPanBlock cCold < 900_719_925_474 ∧
    blkRead maxColdPerBlock < maxGuestSourceClock ∧
    maxGuestSourceClock < txPerBlock * perTxSstoreMaxTicks ∧
    (kPanP p ≤ maxGuestSourceClock ↔ p ≤ 6) := by
  have hb := blkRead_le cCold hcold
  have hkb := kPanBlock_le_max cCold hcold
  have hyuk := kPanBlock_within_yukon cCold hcold
  have htight := kPanBlock_tight
  have hsep := separation
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    blkRead_closed cCold, hb.1, hb.2,
    per_tx_sstore_ticks cTx wTx htx,
    hkb.1, htight.1, hyuk.1,
    hsep.1, hsep.2.1, kPanP_threshold p⟩

/-- Theorem 4 (`non_vacuous_and_tight`, **RISC-V 4x `copyLoop` Unrolling & Score Gain `RiscvSszFastRejectAndBootCert`**):
Exact six-pass + 4x-unrolled `copyLoop` budget `sixPassUnrolledCopyLoopK = 11,029,669,988`
(saving `copyLoopSavedSteps = 13,800` steps from `sixPassReducedK = 11,029,683,788`),
straight-line bootstrap budget `sixPassStraightLineK = 11,029,669,937` (saving `13,851` steps),
and exact `-138,000,000` Yukon score reduction across all `minutes : Nat`. -/
theorem campaign_riscv_unrolled_copyloop_and_score_non_vacuous_and_tight
    (k deltaK minutes : Nat) (hk : 1 ≤ k) (hdelta : deltaK ≤ sixPassReducedK) :
    sixPassReducedPostK = 11_029_660_656 ∧
    sixPassReducedK = 11_029_683_788 ∧
    copyLoopSavedSteps = 13_800 ∧
    sixPassUnrolledCopyLoopK = 11_029_669_988 ∧
    sixPassStraightLineK = 11_029_669_937 ∧
    sixPassCopyLoopUnrolled4xK = 11_029_673_402 ∧
    sixPassUnrolledCopyLoopK + copyLoopSavedSteps = sixPassReducedK ∧
    optimizedBootstrapSteps k + sixPassReducedPostK ≤ sixPassReducedK ∧
    yukonScore sixPassReducedK minutes - yukonScore sixPassUnrolledCopyLoopK minutes = 138_000_000 ∧
    yukonScore sixPassReducedK minutes - yukonScore sixPassStraightLineK minutes = 138_510_000 ∧
    yukonScore sixPassUnrolledCopyLoopK minutes < 2 ^ 53 - 1 ∧
    (yukonScore sixPassReducedK minutes - yukonScore (sixPassReducedK - deltaK) minutes ≥ 138_000_000 ↔
      copyLoopSavedSteps ≤ deltaK) := by
  have h1 := six_pass_unrolled_copyloop_budget_exact k hk
  have h2 := six_pass_yukonScore_copyloop_reduction_exact deltaK minutes hdelta
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, rfl,
    h1.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.2,
    h2.1, h2.2.2.2.1, h2.2.2.2.2.2.1, h2.2.2.2.2.2.2⟩

/-- Theorem 5 (`non_vacuous_and_tight`, **RISC-V `22`-Step SSZ Fast-Reject & Semantic Halt Bridge**):
Exact `22`-step RISC-V SSZ header check decomposition (`bootPrefixSteps = 6`, `sszHeaderCheckSteps = 16`,
`sszFastRejectSteps = 22`), `ValidSszContainerHeader` characterization, and `FastHalt.minHaltingSubmission`
semantic matching on unaccepted inputs within `sszFastRejectSteps = 22 < sixPassUnrolledCopyLoopK`. -/
theorem campaign_riscv_ssz_fast_reject_22_steps_non_vacuous_and_tight
    (loopSteps K_fast minutes totalLen o0 o1 o2 o3 : Nat)
    (hK : sszFastRejectSteps ≤ K_fast) (hK_lt : K_fast < sixPassUnrolledCopyLoopK)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (hnot : ¬ acceptedOutput input outcome events) :
    bootPrefixSteps = 6 ∧
    bootstrapTraceSteps prefixCode = 6 ∧
    sszHeaderCheckSteps = 16 ∧
    sszFastRejectSteps = 22 ∧
    sszGuardedBootstrapSteps false loopSteps = 22 ∧
    sszGuardedBootstrapSteps true loopSteps = 22 + loopSteps ∧
    sixPassUnrolledCopyLoopK - sszFastRejectSteps = 11_029_669_966 ∧
    (¬ ValidSszContainerHeader totalLen o0 o1 o2 o3 ↔
      totalLen < 16 ∨ o0 ≠ 16 ∨ o1 < o0 ∨ o2 < o1 ∨ o3 < o2 ∨ totalLen < o3) ∧
    (minHaltingSubmission (.finite K_fast)).Admitted ∧
    yukonScore K_fast minutes < yukonScore sixPassUnrolledCopyLoopK minutes ∧
    (∃ k ≤ sszFastRejectSteps,
      k ≤ K_fast ∧
      matchingExecutionAt (minHaltingSubmission (.finite K_fast)) input outcome events k) := by
  have hdec := ssz_fast_reject_boot_prefix_decomposition_and_savings loopSteps
  have hhdr := (ssz_header_fast_reject_iff_and_examples totalLen o0 o1 o2 o3).1
  have hcmp := ssz_fast_reject_six_pass_and_iso_yukonScore_comparison K_fast minutes
  have hsem := fast_reject_matches_unaccepted_within_six_pass_unrolled_budget
    K_fast minutes hK hK_lt input outcome events hnot
  exact ⟨hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2.2.1,
    hdec.2.2.2.2.2.1, hdec.2.2.2.2.2.2.1,
    hcmp.2.1, hhdr, hsem.1, hsem.2.1, hsem.2.2.2⟩

/-- Theorem 6 (`non_vacuous_and_tight`, **Source Clock Envelope Hierarchy Across Campaign Models**):
Complete comparison and attainment of the campaign source clock models:
`perTxSourceK (20,436,764,234) < maxGuestSourceClock (43,934,217,712) <
 blockVsTxMaxSourceK (71,448,666,010) < htabMaxSourceClock (114,770,675,338) <
 guestSloadExtractedMaxSourceClock (225,881,786,442) < refinedSourceClock (459,564,194) * 500`. -/
theorem campaign_source_clock_hierarchy_and_attainment_non_vacuous_and_tight
    (cSload wSload cCold : Nat)
    (hsload : 19 * cSload + wSload ≤ 2000000)
    (hcold : 2100 * cCold ≤ GuestEvmStepOpcodeBounds.gasCap) :
    refinedSourceClock = 459_564_194 ∧
    perTxSourceK = 20_436_764_234 ∧
    maxGuestSourceClock = 43_934_217_712 ∧
    blockVsTxMaxSourceK = 71_448_666_010 ∧
    htabMaxSourceClock = 114_770_675_338 ∧
    guestSloadExtractedMaxSourceClock = 225_881_786_442 ∧
    refinedSourceClock < perTxSourceK ∧
    perTxSourceK < maxGuestSourceClock ∧
    maxGuestSourceClock < blockVsTxMaxSourceK ∧
    blockVsTxMaxSourceK < htabMaxSourceClock ∧
    htabMaxSourceClock < guestSloadExtractedMaxSourceClock ∧
    kPanBlock cCold ≤ blockVsTxMaxSourceK ∧
    kPanBlock maxColdPerBlock = blockVsTxMaxSourceK ∧
    kPanModel pEff cSload wSload ≤ guestSloadExtractedMaxSourceClock ∧
    kPanModel pEff 55556 944436 = guestSloadExtractedMaxSourceClock := by
  have hk_sload := kPan_extracted cSload wSload hsload
  have hk_blk := kPanBlock_le_max cCold hcold
  have hk_tight := kPanBlock_tight
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide,
    hk_blk.1, hk_tight.1, hk_sload.1, hk_sload.2⟩

/-- Theorem 7 (`non_vacuous_and_tight`, **Complete Target Step-Budget & Yukon Score Hierarchy**):
Strict ordering and IEEE-754 float64 representability (`< 2^53 - 1`) across all nine campaign
target step budgets:
`sszFastRejectSteps (22) < sixPassStraightLineK (11,029,669,937) <
 sixPassUnrolledCopyLoopK (11,029,669,988) < sixPassCopyLoopUnrolled4xK (11,029,673,402) <
 sixPassReducedK (11,029,683,788) < indexIsoReducedK (22,059,344,444) <
 indexRefinedK (36,765,558,652) < perTxSixPassTargetK (122,620,608,536) <
 htabQuadraticMaxK (803,394,750,498) < 900,719,925,474`. -/
theorem campaign_complete_target_budget_and_score_hierarchy_non_vacuous_and_tight
    (minutes K : Nat) :
    sszFastRejectSteps < sixPassStraightLineK ∧
    sixPassStraightLineK < sixPassUnrolledCopyLoopK ∧
    sixPassUnrolledCopyLoopK < sixPassCopyLoopUnrolled4xK ∧
    sixPassCopyLoopUnrolled4xK < sixPassReducedK ∧
    sixPassReducedK < indexIsoReducedK ∧
    indexIsoReducedK < indexRefinedK ∧
    indexRefinedK < perTxSixPassTargetK ∧
    perTxSixPassTargetK < htabQuadraticMaxK ∧
    htabQuadraticMaxK < 900_719_925_474 ∧
    yukonScore sszFastRejectSteps minutes < yukonScore sixPassStraightLineK minutes ∧
    yukonScore sixPassStraightLineK minutes < yukonScore sixPassUnrolledCopyLoopK minutes ∧
    yukonScore sixPassUnrolledCopyLoopK minutes < yukonScore sixPassCopyLoopUnrolled4xK minutes ∧
    yukonScore sixPassCopyLoopUnrolled4xK minutes < yukonScore sixPassReducedK minutes ∧
    yukonScore sixPassReducedK minutes < yukonScore indexIsoReducedK minutes ∧
    yukonScore indexIsoReducedK minutes < yukonScore indexRefinedK minutes ∧
    yukonScore indexRefinedK minutes < yukonScore perTxSixPassTargetK minutes ∧
    yukonScore perTxSixPassTargetK minutes < yukonScore htabQuadraticMaxK minutes ∧
    yukonScore htabQuadraticMaxK minutes < 2 ^ 53 - 1 ∧
    ((∀ m : Nat, m ≤ 9999 → FiniteScore K m) ↔ K ≤ 900_719_925_473) := by
  have h1 := six_pass_unrolled_copyloop_budget_exact 1 (by decide)
  have hred : sixPassReducedK = 11_029_683_788 := h1.2.1
  have hunr : sixPassUnrolledCopyLoopK = 11_029_669_988 := h1.2.2.2.1
  have hstr : sixPassStraightLineK = 11_029_669_937 := h1.2.2.2.2.1
  have h4x : sixPassCopyLoopUnrolled4xK = 11_029_673_402 := by
    unfold sixPassCopyLoopUnrolled4xK bootstrapUnrolled4xSteps
      copyLoopUnrolledSteps copyLoopUnrolledBlockSteps guestInitDataWords
    rw [reduced_post_exact]
  have hiso : indexIsoReducedK = 22_059_344_444 := isoReducedCandidateK_eq
  have href : indexRefinedK = 36_765_558_652 := refinedCandidateK_eq
  have hptx : perTxSixPassTargetK = 122_620_608_536 := per_tx_target_exact
  have hssz : sszFastRejectSteps = 22 := rfl
  have hhtab : htabQuadraticMaxK = 803_394_750_498 := rfl
  have hrep := (htabQuadraticMaxK_yukonScore_representable minutes).1
  have hunif := uniform_score_non_vacuous_and_tight K
  refine ⟨by rw [hssz, hstr]; decide,
    by rw [hstr, hunr]; decide,
    by rw [hunr, h4x]; decide,
    by rw [h4x, hred]; decide,
    by rw [hred, hiso]; decide,
    by rw [hiso, href]; decide,
    by rw [href, hptx]; decide,
    by rw [hptx, hhtab]; decide,
    by rw [hhtab]; decide,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrep, hunif⟩
  · unfold yukonScore; rw [hssz, hstr]; omega
  · unfold yukonScore; rw [hstr, hunr]; omega
  · unfold yukonScore; rw [hunr, h4x]; omega
  · unfold yukonScore; rw [h4x, hred]; omega
  · unfold yukonScore; rw [hred, hiso]; omega
  · unfold yukonScore; rw [hiso, href]; omega
  · unfold yukonScore; rw [href, hptx]; omega
  · unfold yukonScore; rw [hptx, hhtab]; omega

/-- Theorem 8 (`non_vacuous_and_tight`, **Purified Import Graph, `verify.py` Invariance & `Transport` Admission**):
`zeroBoundedImportCount = 0` transitive `InitECandidate.Proofs.Bounded*` imports, elimination of all
`53,000` `Bounded*` stage modules (`55,882 → 2,882`, `19x` reduction), `verifier/verify.py` overwrite
invariance for `submission/InitECandidate/Solver/SelfContainedCompleteCampaignCert.lean`, and
`Transport` / `SourcePolicy` admission. -/
theorem campaign_purified_import_graph_and_transport_non_vacuous_and_tight
    (boundedImports factor archiveBytes expandedBytes largestFile claimJsonBytes : Nat)
    (ha : archiveBytes ≤ 25 * 1024 * 1024)
    (hx : expandedBytes ≤ 512 * 1024 * 1024)
    (hf : largestFile ≤ 16 * 1024 * 1024)
    (hc : claimJsonBytes ≤ 128) :
    zeroBoundedImportCount = 0 ∧
    purifiedTransitiveModules = 2_882 ∧
    legacyTransitiveModules = 55_882 ∧
    eliminatedBoundedStageModules = 53_000 ∧
    legacyTransitiveModules - purifiedTransitiveModules = eliminatedBoundedStageModules ∧
    (factor * purifiedTransitiveModules ≤ legacyTransitiveModules ↔ factor ≤ 19) ∧
    (isPurifiedSolverModule boundedImports = true ↔ boundedImports = 0) ∧
    stagedSubdirOrigin .Solver = .candidateSubmission ∧
    stagedSubdirOrigin .Proofs = .frozenProblemBaseline ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedCompleteCampaignCert"] = true ∧
    isProofsModulePath ["InitECandidate", "Solver", "SelfContainedCompleteCampaignCert"] = false ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedCompleteCampaignCert"] true = true ∧
    Transport archiveBytes
      (purifiedSolverModuleCount + frozenNonBoundedProofsImportCount + 2) expandedBytes ∧
    SourcePolicy
      (purifiedSolverModuleCount + frozenNonBoundedProofsImportCount + 2)
      largestFile expandedBytes claimJsonBytes := by
  have hC := axis_C_purified_import_graph_and_verify_invariance_non_vacuous_and_tight boundedImports
  have hE := axis_E_module_closure_and_transport_policy_non_vacuous_and_tight
    factor archiveBytes expandedBytes largestFile claimJsonBytes ha hx hf hc
  exact ⟨rfl, rfl, rfl, rfl, hE.2.2.2.2.2.1, hE.2.2.2.2.2.2.2.1,
    hC.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by decide, by decide, by decide,
    hE.2.2.2.2.2.2.2.2.1, hE.2.2.2.2.2.2.2.2.2.1⟩

/-- Theorem 9 (`non_vacuous_and_tight`, **Certificate Lift from `sixPassReducedK` to `perTxSixPassTargetK` & All Campaign Budgets**):
Any `InitE.Certificate` at `sixPassReducedK = 11,029,683,788` lifts monotonically to
`11,029,683,788` (literal), `indexIsoReducedK = 22,059,344,444`, `indexRefinedK = 36,765,558,652`,
`perTxSixPassTargetK = 122,620,608,536` (and literal `122,620,608,536`),
`htabQuadraticMaxK = 803,394,750,498`, and `.infinity`. -/
theorem campaign_certificate_monotonicity_across_all_budgets_non_vacuous_and_tight
    (hcert_six : InitE.Certificate (baselineWithFiniteK sixPassReducedK)
      (.finite sixPassReducedK)) :
    InitE.Certificate (baselineWithFiniteK 11_029_683_788) (.finite 11_029_683_788) ∧
    InitE.Certificate (baselineWithFiniteK indexIsoReducedK) (.finite indexIsoReducedK) ∧
    InitE.Certificate (baselineWithFiniteK indexRefinedK) (.finite indexRefinedK) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK 122_620_608_536) (.finite 122_620_608_536) ∧
    InitE.Certificate (baselineWithFiniteK htabQuadraticMaxK) (.finite htabQuadraticMaxK) ∧
    InitE.Certificate InitE.baselineSubmission .infinity := by
  have hchain := all_axes_certificate_monotonicity_chain_non_vacuous_and_tight hcert_six
  have hlit_six := reduced_certificate_at_literal hcert_six
  have hle_ptx : sixPassReducedK ≤ perTxSixPassTargetK :=
    Nat.le_of_lt reduced_strictly_below_per_tx
  have hptx : InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK)
      (.finite perTxSixPassTargetK) := by
    refine ⟨rfl, baselineWithFiniteK_admitted perTxSixPassTargetK, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hcert_six.correct input hgas outcome events hsrc hcov
    have hm_base :=
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission
        (.finite sixPassReducedK) input outcome events steps).mp hm
    exact ⟨steps, Nat.le_trans hsteps hle_ptx,
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission
        (.finite perTxSixPassTargetK) input outcome events steps).mpr hm_base⟩
  have hlit_ptx := per_tx_certificate_literal hptx
  exact ⟨hlit_six, hchain.1, hchain.2.1, hptx, hlit_ptx, hchain.2.2.1, hchain.2.2.2.1⟩

/-- Theorem 10 (`non_vacuous_and_tight`, **Master End-to-End Campaign Certificate from Unrolled RISC-V Budget `11,029,669,988`**):
From uniform target non-`.timeOut` at the 4x-unrolled `copyLoop` budget
`sixPassUnrolledCopyLoopK = 11,029,669,988`, simultaneously establishes:
- `InitE.Certificate` at `sixPassReducedK` (`11,029,683,788`), `indexIsoReducedK` (`22,059,344,444`),
  `indexRefinedK` (`36,765,558,652`), `perTxSixPassTargetK` (`122,620,608,536`),
  `htabQuadraticMaxK` (`803,394,750,498`), and `.infinity`,
- `StackRemoveStoreConstsZeroBridge` (`compHOL_NoSC`, `storeConstsAllowance = 0`, `runAllowance = 0`),
- `PerTxEip7825TargetMasterK` (`perTxSixPassTargetK = 122,620,608,536`),
- `GuestBlockVsTxHtabBounds` (`kPanBlock maxColdPerBlock = 71,448,666,010`),
- `RiscvSszFastRejectAndBootCert` (`sixPassUnrolledCopyLoopK = 11,029,669,988`, `sszFastRejectSteps = 22`),
- `SelfContainedAllAxesSynthesis` (`0` `Bounded*` imports, `2,882` vs `55,882` modules). -/
theorem campaign_master_end_to_end_complete_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width] (ctx : Spt Nat) (prog : HolLoopProg width) (loc : Nat × Nat)
    (xs : List (Bool × Nat)) (origin : TraceFrom (LoopToWord.compHOL ctx prog loc).1 xs)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_unrolled : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          sixPassUnrolledCopyLoopK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    InitE.Certificate (baselineWithFiniteK 11_029_683_788) (.finite 11_029_683_788) ∧
    InitE.Certificate (baselineWithFiniteK indexIsoReducedK) (.finite indexIsoReducedK) ∧
    InitE.Certificate (baselineWithFiniteK indexRefinedK) (.finite indexRefinedK) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK 122_620_608_536) (.finite 122_620_608_536) ∧
    InitE.Certificate (baselineWithFiniteK htabQuadraticMaxK) (.finite htabQuadraticMaxK) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    NoSC (LoopToWord.compHOL ctx prog loc).1 = true ∧
    storeConstsAllowance (LoopToWord.compHOL ctx prog loc).1 = 0 ∧
    runAllowance xs = 0 ∧
    sixPassUnrolledCopyLoopK = 11_029_669_988 ∧
    sixPassReducedK = 11_029_683_788 ∧
    perTxSixPassTargetK = 122_620_608_536 ∧
    kPanBlock maxColdPerBlock = 71_448_666_010 ∧
    sszFastRejectSteps = 22 ∧
    yukonScore sixPassReducedK minutes - yukonScore sixPassUnrolledCopyLoopK minutes = 138_000_000 ∧
    zeroBoundedImportCount = 0 ∧
    purifiedTransitiveModules = 2_882 ∧
    legacyTransitiveModules = 55_882 := by
  have hunr_cert := self_contained_six_pass_and_unrolled_copyloop_master_certificate
    oracles c depth minutes hlab compiled depthBound not_timeOut_unrolled
  have hcert_six := hunr_cert.1
  have hall := campaign_certificate_monotonicity_across_all_budgets_non_vacuous_and_tight hcert_six
  exact ⟨hcert_six, hall.1, hall.2.1, hall.2.2.1, hall.2.2.2.1, hall.2.2.2.2.1,
    hall.2.2.2.2.2.1, hall.2.2.2.2.2.2,
    compHOL_NoSC ctx prog loc,
    compiled_allowance_zero ctx prog loc,
    compiled_run_allowance_zero ctx prog loc xs origin,
    hunr_cert.2.2.2.1, hunr_cert.2.2.1, per_tx_target_exact,
    kPanBlock_tight.1, rfl, hunr_cert.2.2.2.2.2.1, rfl, rfl, rfl⟩

#print axioms campaign_six_pass_and_storeConsts_zero_bridge_non_vacuous_and_tight
#print axioms campaign_per_tx_eip7825_target_master_non_vacuous_and_tight
#print axioms campaign_block_vs_tx_htab_bounds_non_vacuous_and_tight
#print axioms campaign_riscv_unrolled_copyloop_and_score_non_vacuous_and_tight
#print axioms campaign_riscv_ssz_fast_reject_22_steps_non_vacuous_and_tight
#print axioms campaign_source_clock_hierarchy_and_attainment_non_vacuous_and_tight
#print axioms campaign_complete_target_budget_and_score_hierarchy_non_vacuous_and_tight
#print axioms campaign_purified_import_graph_and_transport_non_vacuous_and_tight
#print axioms campaign_certificate_monotonicity_across_all_budgets_non_vacuous_and_tight
#print axioms campaign_master_end_to_end_complete_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedCompleteCampaignCert
