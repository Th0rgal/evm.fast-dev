import InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts
import InitECandidate.Solver.GuestBs32BlockStorageEnvelope
import InitECandidate.Solver.SelfContainedTwelveTierSynthesis

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SelfContainedSsaCseAndBs32Synth` — Self-Contained 14-Tier SSA/CSE & `bs+32` Synthesis (`W5_65`)

This module has **0 imports from `InitECandidate.Proofs.Bounded*`** in its transitive closure and
unifies:
1. The 8-pass `WordToWord` `NoSt` preservation chain (`t_ssa_cse_mid_tail_chain`,
   `storeConstsAllowance_chain_zero`, `storeConstsAllowance_tight`) from `WordSsaCsePreserveNoStoreConsts`:
   `instSelect → fullSsaCcTrans → removeDeadProg → wordCommonSubexpElim → copyProp → threeToTwoRegProg → removeUnreach → removeDeadProg`.
2. The joint block storage envelope `GuestBs32BlockStorageEnvelope` (`kPanBs32Joint = 153_081_489_139`,
   `kPanBs32Sum = 166_686_761_248`, `k * kPanBs32Joint < yukon ↔ k ≤ 5`).
3. The unrolled and non-unrolled `3x`-slope target tiers for `kPanBs32Joint`:
   - `bs32JointSlope3UnrolledK = 9_332 + 3 * 153_081_489_139 = 459_244_476_749`
   - `bs32JointSlope3K = 23_132 + 3 * 153_081_489_139 = 459_244_490_549`
   (`459_244_476_749 < 459_244_490_549 < 900_719_925_474`).
4. The complete 14-tier candidate hierarchy (`exactKeccak128UnrolledK = 1_212_035_192` through
   `bs32JointSlope3K = 459_244_490_549`, plus `blockVsTxSlope12K = 857_384_015_252 < 900_719_925_474`),
   `claim.json ≤ 128`-byte compliance, and `InitE.Certificate` theorems (`0 sorryAx`).
-/

namespace InitECandidate.Solver.SelfContainedSsaCseAndBs32Synth

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
open InitECandidate.Solver.GuestJointBlockGasHtabBound
open InitECandidate.Solver.GuestDirtyWriteHtabDominance
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts
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
open Flapjack
open Flapjack.LoopToWord
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang

/-! ## Section 1: Unrolled & Non-Unrolled `kPanBs32Joint` Slope-3 Tiers (Tiers 13 & 14) -/

/-- Post-bootstrap target steps for `kPanBs32Joint = 153_081_489_139` under 6-pass `3x` target slope:
`3 * 153_081_489_139 = 459_244_467_417`. -/
def bs32JointSlope3PostK : Nat := 3 * kPanBs32Joint

/-- Tier 13: Unrolled-`copyLoop` (`bootstrapSteps - copyLoopSavedSteps = 9_332`) target ceiling for
`kPanBs32Joint` at `3x` slope: `9_332 + 3 * 153_081_489_139 = 459_244_476_749`. -/
def bs32JointSlope3UnrolledK : Nat :=
  (bootstrapSteps - copyLoopSavedSteps) + bs32JointSlope3PostK

/-- Tier 14: Baseline-bootstrap (`bootstrapSteps = 23_132`) target ceiling for `kPanBs32Joint` at
`3x` slope: `23_132 + 3 * 153_081_489_139 = 459_244_490_549`. -/
def bs32JointSlope3K : Nat :=
  bootstrapSteps + bs32JointSlope3PostK

/-- Canonical `{"claimed_k": "<K>"}` JSON strings (`≤ 128` bytes) for Tiers 13 & 14. -/
def claimJsonBs32Slope3Unrolled : String := claimedKJson "459244476749"
def claimJsonBs32Slope3 : String := claimedKJson "459244490549"

/-- Canonical `{"K": <K>}` JSON strings (`verifier/check_submission.py`) for Tiers 13 & 14. -/
def verifierJsonBs32Slope3Unrolled : String := verifierClaimJson "459244476749"
def verifierJsonBs32Slope3 : String := verifierClaimJson "459244490549"

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`, **8-Pass `WordToWord` SSA/CSE `NoSt` Chain & Zero `storeConstsAllowance`**):
Unites `t_ssa_cse_mid_tail_chain`, `storeConstsAllowance_chain_zero`, and `storeConstsAllowance_tight`
from `WordSsaCsePreserveNoStoreConsts` with `loopToWord_NoSt` from `WordPassesPreserveNoStoreConsts`:
any `LoopToWord.compHOL ctx prog loc` output preserves `NoSt = true` and `storeConstsAllowance = 0`
across all 8 `WordToWord` passes (`instSelect → fullSsaCcTrans → removeDeadProg → wordCommonSubexpElim →
copyProp → threeToTwoRegProg → removeUnreach → removeDeadProg`), whereas an explicit `.storeConsts` node
evaluates to `storeConstsAllowance = 1`. -/
theorem word_ssa_cse_eight_pass_chain_no_store_consts_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp argc : Nat) (b : Bool)
    (ctx : Spt Nat) (prog : HolLoopProg width) (loc : Nat × Nat)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true) :
    NoSt (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
      (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
        (fullSsaCcTrans argc (WordInst.instSelect c temp p)))))))) = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
        (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
          (fullSsaCcTrans argc (WordInst.instSelect c temp p)))))))) = 0 ∧
    NoSt (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
      (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
        (fullSsaCcTrans argc (WordInst.instSelect c temp (LoopToWord.compHOL ctx prog loc).1)))))))) = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
        (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
          (fullSsaCcTrans argc (WordInst.instSelect c temp (LoopToWord.compHOL ctx prog loc).1)))))))) = 0 ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordLangProgHOL.storeConsts (α := BitVec width) 0 2 4 6 []) = 1 ∧
    NoSt (WordLangProgHOL.storeConsts (α := BitVec width) 0 2 4 6 []) = false := by
  have hcomp : NoSt (LoopToWord.compHOL ctx prog loc).1 = true := loopToWord_NoSt ctx prog loc
  exact ⟨t_ssa_cse_mid_tail_chain c temp argc b p hp,
    storeConstsAllowance_chain_zero c temp argc b p hp,
    t_ssa_cse_mid_tail_chain c temp argc b (LoopToWord.compHOL ctx prog loc).1 hcomp,
    storeConstsAllowance_chain_zero c temp argc b (LoopToWord.compHOL ctx prog loc).1 hcomp,
    storeConstsAllowance_tight,
    rfl⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **Joint `bs+32` + `bs+72` Block Storage Envelope & `k ≤ 5` Slope Threshold**):
Unifies `GuestBs32BlockStorageEnvelope` (`kPanBs32Joint = 153_081_489_139`, `kPanBs32Sum = 166_686_761_248`,
`bs32_bs72_joint`, `joint_vertex_tight`, `kPan_master`, `slope3_ok`, `slope_6_9_12_fail`, `slope_threshold`,
and `slope_threshold_sum`). -/
theorem guest_bs32_block_storage_joint_envelope_and_slope_threshold_non_vacuous_and_tight
    (D W C T2 k : Nat)
    (hbud : 21 * D + W + 21 * C ≤ S)
    (htx : T2 ≤ perTx) :
    linear = 3_659_564_234 ∧
    perTx = 54_183_829_667 ∧
    blockJoint = 95_238_095_238 ∧
    kPanBs32Joint = 153_081_489_139 ∧
    kPanBs32Sum = 166_686_761_248 ∧
    42 * (2 * (D * W) + blkRead C) ≤ S * S ∧
    2 * (D * W) + blkRead C ≤ blockJoint ∧
    linear + T2 + (2 * (D * W) + blkRead C) ≤ kPanBs32Joint ∧
    (21 * 47619 + 1000001 + 21 * 0 = S ∧ 2 * (47619 * 1000001) + blkRead 0 = blockJoint) ∧
    (blkRead 95238 = 13_605_272_109 ∧ 13_605_272_109 < blockJoint) ∧
    3 * kPanBs32Joint < yukon ∧
    3 * kPanBs32Sum < yukon ∧
    yukon < 6 * kPanBs32Joint ∧
    yukon < 9 * kPanBs32Joint ∧
    yukon < 12 * kPanBs32Joint ∧
    (k * kPanBs32Joint < yukon ↔ k ≤ 5) ∧
    (k * kPanBs32Sum < yukon ↔ k ≤ 5) := by
  have hc := GuestBs32BlockStorageEnvelope.constants
  have hk := kPan_values
  have hs3 := slope3_ok
  have hsfail := slope_6_9_12_fail
  exact ⟨hc.1, hc.2.1, rfl, hk.1, hk.2,
    bs32_bs72_joint D W C hbud,
    block_terms_le D W C hbud,
    kPan_master D W C T2 hbud htx,
    joint_vertex_tight,
    joint_other_vertex,
    hs3.1, hs3.2,
    hsfail.1, hsfail.2.1, hsfail.2.2,
    slope_threshold k,
    slope_threshold_sum k⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Exact Values & Bounds of the `kPanBs32Joint` Slope-3 Tiers**):
Certifies the unrolled and non-unrolled `3x`-slope tiers for `kPanBs32Joint`:
`bs32JointSlope3PostK = 459_244_467_417`, `bs32JointSlope3UnrolledK = 459_244_476_749`, and
`bs32JointSlope3K = 459_244_490_549`, proving `459_244_476_749 < 459_244_490_549 < 900_719_925_474`,
their `13_800`-step `copyLoop` difference, and `138_000_000`-point `yukonScore` gain. -/
theorem bs32_joint_slope3_unrolled_and_baseline_tiers_non_vacuous_and_tight
    (k minutes : Nat) :
    bs32JointSlope3PostK = 459_244_467_417 ∧
    bs32JointSlope3UnrolledK = 459_244_476_749 ∧
    bs32JointSlope3K = 459_244_490_549 ∧
    459_244_476_749 < 459_244_490_549 ∧
    459_244_490_549 < 900_719_925_474 ∧
    bs32JointSlope3UnrolledK < bs32JointSlope3K ∧
    bs32JointSlope3K < yukonFloat64MaxK ∧
    bs32JointSlope3K - bs32JointSlope3UnrolledK = 13_800 ∧
    bs32JointSlope3UnrolledK + copyLoopSavedSteps = bs32JointSlope3K ∧
    (bs32JointSlope3K ≤ k + copyLoopSavedSteps ↔ bs32JointSlope3UnrolledK ≤ k) ∧
    yukonScore bs32JointSlope3K minutes - yukonScore bs32JointSlope3UnrolledK minutes = 138_000_000 := by
  have h12 := twelve_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
  have hbs : bootstrapSteps = 23_132 := h12.2.1
  have hsave : copyLoopSavedSteps = 13_800 := copy_loop_saved_exact
  have hk : kPanBs32Joint = 153_081_489_139 := kPan_values.1
  have hpost : bs32JointSlope3PostK = 459_244_467_417 := by
    unfold bs32JointSlope3PostK; rw [hk]
  have hunr : bs32JointSlope3UnrolledK = 459_244_476_749 := by
    unfold bs32JointSlope3UnrolledK; rw [hbs, hsave, hpost]
  have hbase : bs32JointSlope3K = 459_244_490_549 := by
    unfold bs32JointSlope3K; rw [hbs, hpost]
  have hy : yukonFloat64MaxK = 900_719_925_474 := rfl
  rw [hpost, hunr, hbase, hsave, hy]
  unfold yukonScore
  omega

/-- Theorem 4 (`non_vacuous_and_tight`, **Strict Total Ordering of All 14 Candidate Tiers**):
Establishes the exact numerical values and strict total ordering across all 14 candidate tiers
from Tier 1 (`exactKeccak128UnrolledK = 1_212_035_192`) through Tier 14 (`bs32JointSlope3K = 459_244_490_549`),
plus `blockVsTxSlope12K = 857_384_015_252 < 900_719_925_474`, and exact `13_800`-step `copyLoop`
reductions across all five unrolled/baseline pairs. -/
theorem fourteen_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight :
    exactKeccak128UnrolledK = 1_212_035_192 ∧
    exactKeccak128NoGcK = 1_212_048_992 ∧
    exactKeccak0UnrolledK = 2_038_701_869 ∧
    exactKeccakNoGcK = 2_038_715_669 ∧
    sixPassUnrolledCopyLoopK = 11_029_669_988 ∧
    sixPassReducedK = 11_029_683_788 ∧
    exactKeccak128CandidateK = 19_392_692_330 ∧
    isoReducedCopyLoopK = 22_059_330_644 ∧
    isoReducedCandidateK = 22_059_344_444 ∧
    exactKeccakCandidateK = 32_791_963_724 ∧
    push31NoGcCandidateK = 87_829_684_748 ∧
    perTxSixPassTargetK = 122_620_608_536 ∧
    blockVsTxSlope3K = 214_346_021_162 ∧
    blockVsTxSlope6K = 428_692_019_192 ∧
    bs32JointSlope3UnrolledK = 459_244_476_749 ∧
    bs32JointSlope3K = 459_244_490_549 ∧
    blockVsTxSlope12K = 857_384_015_252 ∧
    yukonFloat64MaxK = 900_719_925_474 ∧
    exactKeccak128UnrolledK < exactKeccak128NoGcK ∧
    exactKeccak128NoGcK < exactKeccak0UnrolledK ∧
    exactKeccak0UnrolledK < exactKeccakNoGcK ∧
    exactKeccakNoGcK < sixPassUnrolledCopyLoopK ∧
    sixPassUnrolledCopyLoopK < sixPassReducedK ∧
    sixPassReducedK < exactKeccak128CandidateK ∧
    exactKeccak128CandidateK < isoReducedCopyLoopK ∧
    isoReducedCopyLoopK < isoReducedCandidateK ∧
    isoReducedCandidateK < exactKeccakCandidateK ∧
    exactKeccakCandidateK < push31NoGcCandidateK ∧
    push31NoGcCandidateK < perTxSixPassTargetK ∧
    perTxSixPassTargetK < blockVsTxSlope3K ∧
    blockVsTxSlope3K < blockVsTxSlope6K ∧
    blockVsTxSlope6K < bs32JointSlope3UnrolledK ∧
    bs32JointSlope3UnrolledK < bs32JointSlope3K ∧
    bs32JointSlope3K < blockVsTxSlope12K ∧
    blockVsTxSlope12K < 900_719_925_474 ∧
    exactKeccak128NoGcK - exactKeccak128UnrolledK = 13_800 ∧
    exactKeccakNoGcK - exactKeccak0UnrolledK = 13_800 ∧
    sixPassReducedK - sixPassUnrolledCopyLoopK = 13_800 ∧
    isoReducedCandidateK - isoReducedCopyLoopK = 13_800 ∧
    bs32JointSlope3K - bs32JointSlope3UnrolledK = 13_800 ∧
    bs32JointSlope3UnrolledK - blockVsTxSlope6K = 30_552_457_557 := by
  have h12 := twelve_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hu128 : exactKeccak128UnrolledK = 1_212_035_192 := h12.1
  have hb128 : exactKeccak128NoGcK = 1_212_048_992 := h12.2.1
  have hu0 : exactKeccak0UnrolledK = 2_038_701_869 := h12.2.2.1
  have hb0 : exactKeccakNoGcK = 2_038_715_669 := h12.2.2.2.1
  have h1 : sixPassUnrolledCopyLoopK = 11_029_669_988 := h12.2.2.2.2.1
  have h2 : sixPassReducedK = 11_029_683_788 := h12.2.2.2.2.2.1
  have h3 : exactKeccak128CandidateK = 19_392_692_330 := h12.2.2.2.2.2.2.1
  have h4 : isoReducedCopyLoopK = 22_059_330_644 := h12.2.2.2.2.2.2.2.1
  have h5 : isoReducedCandidateK = 22_059_344_444 := h12.2.2.2.2.2.2.2.2.1
  have h6 : exactKeccakCandidateK = 32_791_963_724 := h12.2.2.2.2.2.2.2.2.2.1
  have h7 : push31NoGcCandidateK = 87_829_684_748 := h12.2.2.2.2.2.2.2.2.2.2.1
  have h8 : perTxSixPassTargetK = 122_620_608_536 := h12.2.2.2.2.2.2.2.2.2.2.2.1
  have h9 : blockVsTxSlope3K = 214_346_021_162 := h12.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h10 : blockVsTxSlope6K = 428_692_019_192 := h12.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h11 : blockVsTxSlope12K = 857_384_015_252 := h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbs32 := bs32_joint_slope3_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 0
  have h13 : bs32JointSlope3UnrolledK = 459_244_476_749 := hbs32.2.1
  have h14 : bs32JointSlope3K = 459_244_490_549 := hbs32.2.2.1
  have hy : yukonFloat64MaxK = 900_719_925_474 := rfl
  rw [hu128, hb128, hu0, hb0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h13, h14, h11, hy]
  decide

/-- Theorem 5 (`non_vacuous_and_tight`, **Bootstrap Decompositions & 1-Tick Tightness Across All 14 Tiers**):
Establishes exact `(bootstrapSteps - copyLoopSavedSteps) = 9_332` and `bootstrapSteps = 23_132`
decompositions across all 14 tiers, with sharp 1-tick tightness boundaries (`¬ K ≤ K - 1`). -/
theorem fourteen_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight :
    bootstrapSteps - copyLoopSavedSteps = 9_332 ∧
    bootstrapSteps = 23_132 ∧
    exactKeccak128UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 3 * SelfContainedExactKeccakMasterK.exactKeccak128SourceClock ∧
    exactKeccak0UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 3 * SelfContainedExactKeccakMasterK.exactKeccakSourceClock ∧
    sixPassUnrolledCopyLoopK = (bootstrapSteps - copyLoopSavedSteps) + sixPassReducedPostK ∧
    sixPassReducedK = bootstrapSteps + sixPassReducedPostK ∧
    exactKeccak128CandidateK = bootstrapSteps + exactKeccak128PostSteps ∧
    isoReducedCopyLoopK = bootstrapSteps + isoReducedCopyloopPostK ∧
    isoReducedCandidateK = bootstrapSteps + isoReducedPostK ∧
    exactKeccakCandidateK = bootstrapSteps + exactKeccakPostSteps ∧
    push31NoGcCandidateK = bootstrapSteps + push31NoGcPostK ∧
    perTxSixPassTargetK = bootstrapSteps + 6 * perTxSourceK ∧
    blockVsTxSlope3K = bootstrapSteps + 3 * blockVsTxSourceK ∧
    blockVsTxSlope6K = bootstrapSteps + 6 * blockVsTxSourceK ∧
    bs32JointSlope3UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanBs32Joint ∧
    bs32JointSlope3K = bootstrapSteps + 3 * kPanBs32Joint ∧
    blockVsTxSlope12K = bootstrapSteps + 12 * blockVsTxSourceK ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanBs32Joint ≤ bs32JointSlope3UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 3 * kPanBs32Joint ≤ bs32JointSlope3K - 1) ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 3 * SelfContainedExactKeccakMasterK.exactKeccak128SourceClock ≤ exactKeccak128UnrolledK - 1) ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 3 * SelfContainedExactKeccakMasterK.exactKeccakSourceClock ≤ exactKeccak0UnrolledK - 1) ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + sixPassReducedPostK ≤ sixPassUnrolledCopyLoopK - 1) ∧
    ¬ (bootstrapSteps + sixPassReducedPostK ≤ sixPassReducedK - 1) ∧
    ¬ (bootstrapSteps + exactKeccak128PostSteps ≤ exactKeccak128CandidateK - 1) ∧
    ¬ (bootstrapSteps + isoReducedCopyloopPostK ≤ isoReducedCopyLoopK - 1) ∧
    ¬ (bootstrapSteps + isoReducedPostK ≤ isoReducedCandidateK - 1) ∧
    ¬ (bootstrapSteps + exactKeccakPostSteps ≤ exactKeccakCandidateK - 1) ∧
    ¬ (bootstrapSteps + push31NoGcPostK ≤ push31NoGcCandidateK - 1) ∧
    ¬ (bootstrapSteps + 6 * perTxSourceK ≤ perTxSixPassTargetK - 1) ∧
    ¬ (bootstrapSteps + 3 * blockVsTxSourceK ≤ blockVsTxSlope3K - 1) ∧
    ¬ (bootstrapSteps + 6 * blockVsTxSourceK ≤ blockVsTxSlope6K - 1) ∧
    ¬ (bootstrapSteps + 12 * blockVsTxSourceK ≤ blockVsTxSlope12K - 1) := by
  have h12 := twelve_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
  have hbs : bootstrapSteps = 23_132 := h12.2.1
  have hsave : copyLoopSavedSteps = 13_800 := copy_loop_saved_exact
  have hk : kPanBs32Joint = 153_081_489_139 := kPan_values.1
  have hbs32 := bs32_joint_slope3_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 0
  have h13 : bs32JointSlope3UnrolledK = 459_244_476_749 := hbs32.2.1
  have h14 : bs32JointSlope3K = 459_244_490_549 := hbs32.2.2.1
  refine ⟨h12.1, hbs, h12.2.2.1, h12.2.2.2.1, h12.2.2.2.2.1, h12.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_, ?_, h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    ?_, ?_, h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · rfl
  · rfl
  · rw [h13, hbs, hsave, hk]; decide
  · rw [h14, hbs, hk]; decide

/-- Theorem 6 (`non_vacuous_and_tight`, **IEEE-754 Float64 Representability & Strict `yukonScore` Order Across All 14 Tiers**):
Strict `yukonScore` ordering and exact IEEE-754 double-precision integer representability
(`yukonScore K minutes < 2^53 - 1`) across all 14 candidate tiers and `blockVsTxSlope12K` for every
`minutes : Nat`, plus the sharp uniform ceiling equivalence `yukonScore K 9999 < 2^53 - 1 ↔ K < 900_719_925_474`. -/
theorem fourteen_tier_yukonScore_strict_order_and_float64_exact_non_vacuous_and_tight
    (minutes K : Nat) :
    yukonScore exactKeccak128UnrolledK minutes < yukonScore exactKeccak0UnrolledK minutes ∧
    yukonScore exactKeccak0UnrolledK minutes < yukonScore sixPassUnrolledCopyLoopK minutes ∧
    yukonScore sixPassUnrolledCopyLoopK minutes < yukonScore sixPassReducedK minutes ∧
    yukonScore sixPassReducedK minutes < yukonScore exactKeccak128CandidateK minutes ∧
    yukonScore exactKeccak128CandidateK minutes < yukonScore isoReducedCopyLoopK minutes ∧
    yukonScore isoReducedCopyLoopK minutes < yukonScore isoReducedCandidateK minutes ∧
    yukonScore isoReducedCandidateK minutes < yukonScore exactKeccakCandidateK minutes ∧
    yukonScore exactKeccakCandidateK minutes < yukonScore push31NoGcCandidateK minutes ∧
    yukonScore push31NoGcCandidateK minutes < yukonScore perTxSixPassTargetK minutes ∧
    yukonScore perTxSixPassTargetK minutes < yukonScore blockVsTxSlope3K minutes ∧
    yukonScore blockVsTxSlope3K minutes < yukonScore blockVsTxSlope6K minutes ∧
    yukonScore blockVsTxSlope6K minutes < yukonScore bs32JointSlope3UnrolledK minutes ∧
    yukonScore bs32JointSlope3UnrolledK minutes < yukonScore bs32JointSlope3K minutes ∧
    yukonScore bs32JointSlope3K minutes < yukonScore blockVsTxSlope12K minutes ∧
    yukonScore blockVsTxSlope12K minutes < 2 ^ 53 - 1 ∧
    yukonScore exactKeccak128UnrolledK minutes < 2 ^ 53 - 1 ∧
    yukonScore exactKeccak0UnrolledK minutes < 2 ^ 53 - 1 ∧
    yukonScore sixPassUnrolledCopyLoopK minutes < 2 ^ 53 - 1 ∧
    yukonScore sixPassReducedK minutes < 2 ^ 53 - 1 ∧
    yukonScore exactKeccak128CandidateK minutes < 2 ^ 53 - 1 ∧
    yukonScore isoReducedCopyLoopK minutes < 2 ^ 53 - 1 ∧
    yukonScore isoReducedCandidateK minutes < 2 ^ 53 - 1 ∧
    yukonScore exactKeccakCandidateK minutes < 2 ^ 53 - 1 ∧
    yukonScore push31NoGcCandidateK minutes < 2 ^ 53 - 1 ∧
    yukonScore perTxSixPassTargetK minutes < 2 ^ 53 - 1 ∧
    yukonScore blockVsTxSlope3K minutes < 2 ^ 53 - 1 ∧
    yukonScore blockVsTxSlope6K minutes < 2 ^ 53 - 1 ∧
    yukonScore bs32JointSlope3UnrolledK minutes < 2 ^ 53 - 1 ∧
    yukonScore bs32JointSlope3K minutes < 2 ^ 53 - 1 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have h14 := fourteen_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hu128 : exactKeccak128UnrolledK = 1_212_035_192 := h14.1
  have hu0 : exactKeccak0UnrolledK = 2_038_701_869 := h14.2.2.1
  have h1 : sixPassUnrolledCopyLoopK = 11_029_669_988 := h14.2.2.2.2.1
  have h2 : sixPassReducedK = 11_029_683_788 := h14.2.2.2.2.2.1
  have h3 : exactKeccak128CandidateK = 19_392_692_330 := h14.2.2.2.2.2.2.1
  have h4 : isoReducedCopyLoopK = 22_059_330_644 := h14.2.2.2.2.2.2.2.1
  have h5 : isoReducedCandidateK = 22_059_344_444 := h14.2.2.2.2.2.2.2.2.1
  have h6 : exactKeccakCandidateK = 32_791_963_724 := h14.2.2.2.2.2.2.2.2.2.1
  have h7 : push31NoGcCandidateK = 87_829_684_748 := h14.2.2.2.2.2.2.2.2.2.2.1
  have h8 : perTxSixPassTargetK = 122_620_608_536 := h14.2.2.2.2.2.2.2.2.2.2.2.1
  have h9 : blockVsTxSlope3K = 214_346_021_162 := h14.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h10 : blockVsTxSlope6K = 428_692_019_192 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h13 : bs32JointSlope3UnrolledK = 459_244_476_749 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h14v : bs32JointSlope3K = 459_244_490_549 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h11 : blockVsTxSlope12K = 857_384_015_252 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hm : min minutes 9999 ≤ 9999 := Nat.min_le_right _ _
  have hm9999 : min 9999 9999 = 9999 := rfl
  rw [hu128, hu0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h13, h14v, h11]
  unfold yukonScore
  rw [hm9999]
  omega

/-- Theorem 7 (`non_vacuous_and_tight`, **`claim.json ≤ 128`-Byte Audit Across All 14 Tiers**):
Exact UTF-8 byte sizes (`27`, `28`, or `29` bytes for `{"claimed_k": "..."}` and `17`, `18`, or `19`
bytes for `{"K": ...}`), `validFiniteClaim` conformance across all 14 tiers and `blockVsTxSlope12K`,
and sharp `128`-byte vs `129`-byte `checkSubmissionLimits` boundary. -/
theorem fourteen_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight :
    claimJsonBs32Slope3Unrolled.utf8ByteSize = 29 ∧
    claimJsonBs32Slope3.utf8ByteSize = 29 ∧
    verifierJsonBs32Slope3Unrolled.utf8ByteSize = 19 ∧
    verifierJsonBs32Slope3.utf8ByteSize = 19 ∧
    claimJsonUnrolled128.utf8ByteSize = 27 ∧
    claimJsonUnrolled0.utf8ByteSize = 27 ∧
    claimJsonTier1.utf8ByteSize = 28 ∧
    claimJsonTier2.utf8ByteSize = 28 ∧
    claimJsonTier3.utf8ByteSize = 28 ∧
    claimJsonTier4.utf8ByteSize = 28 ∧
    claimJsonTier5.utf8ByteSize = 28 ∧
    claimJsonTier6.utf8ByteSize = 28 ∧
    claimJsonTier7.utf8ByteSize = 28 ∧
    claimJsonTier8.utf8ByteSize = 29 ∧
    claimJsonTier9.utf8ByteSize = 29 ∧
    claimJsonTier10.utf8ByteSize = 29 ∧
    claimJsonSlope12.utf8ByteSize = 29 ∧
    validFiniteClaim bs32JointSlope3UnrolledK claimJsonBs32Slope3Unrolled = true ∧
    validFiniteClaim bs32JointSlope3K claimJsonBs32Slope3 = true ∧
    validFiniteClaim bs32JointSlope3UnrolledK verifierJsonBs32Slope3Unrolled = true ∧
    validFiniteClaim bs32JointSlope3K verifierJsonBs32Slope3 = true ∧
    validFiniteClaim exactKeccak128UnrolledK claimJsonUnrolled128 = true ∧
    validFiniteClaim exactKeccak0UnrolledK claimJsonUnrolled0 = true ∧
    validFiniteClaim sixPassUnrolledCopyLoopK claimJsonTier1 = true ∧
    validFiniteClaim sixPassReducedK claimJsonTier2 = true ∧
    validFiniteClaim exactKeccak128CandidateK claimJsonTier3 = true ∧
    validFiniteClaim isoReducedCopyLoopK claimJsonTier4 = true ∧
    validFiniteClaim isoReducedCandidateK claimJsonTier5 = true ∧
    validFiniteClaim exactKeccakCandidateK claimJsonTier6 = true ∧
    validFiniteClaim push31NoGcCandidateK claimJsonTier7 = true ∧
    validFiniteClaim perTxSixPassTargetK claimJsonTier8 = true ∧
    validFiniteClaim blockVsTxSlope3K claimJsonTier9 = true ∧
    validFiniteClaim blockVsTxSlope6K claimJsonTier10 = true ∧
    validFiniteClaim blockVsTxSlope12K claimJsonSlope12 = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonBs32Slope3Unrolled.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonBs32Slope3.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 (MAX_CLAIM_BYTES + 1) false false true = false := by
  have h14 := fourteen_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have h13 : bs32JointSlope3UnrolledK = 459_244_476_749 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h14v : bs32JointSlope3K = 459_244_490_549 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h12 := twelve_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
  refine ⟨by decide, by decide, by decide, by decide,
    h12.1, h12.2.1, h12.2.2.1, h12.2.2.2.1, h12.2.2.2.2.1, h12.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.2.1,
    ?_, ?_, ?_, ?_,
    h12.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by decide, by decide, by decide⟩
  · rw [h13]; decide
  · rw [h14v]; decide
  · rw [h13]; decide
  · rw [h14v]; decide

/-- Theorem 8 (`non_vacuous_and_tight`, **Direct `InitE.Certificate` Bridges for `bs32JointSlope3UnrolledK` & `bs32JointSlope3K`**):
Proves that uniform target non-`.timeOut` at `bs32JointSlope3UnrolledK = 459_244_476_749` (or
`bs32JointSlope3K = 459_244_490_549`) yields `InitE.Certificate` at that budget and lifts
monotonically across `bs32JointSlope3K`, `blockVsTxSlope12K`, and `.infinity`, with valid `claim.json`
payloads (`29` bytes) and `138_000_000`-point `yukonScore` gain. -/
theorem bs32_joint_slope3_certificates_and_margins_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
       sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_bs32_unrolled : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          bs32JointSlope3UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3UnrolledK) (.finite bs32JointSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope12K) (.finite blockVsTxSlope12K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    validFiniteClaim bs32JointSlope3UnrolledK claimJsonBs32Slope3Unrolled = true ∧
    validFiniteClaim bs32JointSlope3K claimJsonBs32Slope3 = true ∧
    yukonScore bs32JointSlope3K minutes - yukonScore bs32JointSlope3UnrolledK minutes = 138_000_000 ∧
    bs32JointSlope3UnrolledK < bs32JointSlope3K ∧
    bs32JointSlope3K < 900_719_925_474 := by
  have h14 := fourteen_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have h13 : bs32JointSlope3UnrolledK = 459_244_476_749 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h14v : bs32JointSlope3K = 459_244_490_549 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert13 : InitE.Certificate (baselineWithFiniteK bs32JointSlope3UnrolledK)
      (.finite bs32JointSlope3UnrolledK) := by
    have h := finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth (459244476749 - 23132) hlab compiled depthBound
      (by simpa only [bootstrapSteps_eq, h13] using not_timeOut_bs32_unrolled)
    simpa only [bootstrapSteps_eq, h13] using h
  have hmono : ∀ {A B : Nat}, A ≤ B →
      InitE.Certificate (baselineWithFiniteK A) (.finite A) →
      InitE.Certificate (baselineWithFiniteK B) (.finite B) := by
    intro A B hab hA
    refine ⟨rfl, baselineWithFiniteK_admitted B, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hA.correct input hgas outcome events hsrc hcov
    have hm_base : matchingExecutionAt InitE.baselineSubmission input outcome events steps :=
      (matchingExecutionAt_with_score InitE.baselineSubmission (.finite A)
        input outcome events steps).mp hm
    exact ⟨steps, Nat.le_trans hsteps hab,
      (matchingExecutionAt_with_score InitE.baselineSubmission (.finite B)
        input outcome events steps).mpr hm_base⟩
  have hlt13_14 : bs32JointSlope3UnrolledK < bs32JointSlope3K := by rw [h13, h14v]; decide
  have hlt14_12 : bs32JointSlope3K < blockVsTxSlope12K :=
    h14.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert14 := hmono (Nat.le_of_lt hlt13_14) hcert13
  have hcert12 := hmono (Nat.le_of_lt hlt14_12) hcert14
  have hinf : InitE.Certificate InitE.baselineSubmission .infinity := by
    refine ⟨rfl, InitE.baselineSubmission_admitted, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, _, hm⟩ := hcert13.correct input hgas outcome events hsrc hcov
    exact ⟨steps, trivial,
      (matchingExecutionAt_with_score InitE.baselineSubmission (.finite bs32JointSlope3UnrolledK)
        input outcome events steps).mp hm⟩
  have hclaims := fourteen_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
  have hbs32 := bs32_joint_slope3_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 minutes
  exact ⟨hcert13, hcert14, hcert12, hinf,
    hclaims.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hclaims.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hbs32.2.2.2.2.2.2.2.2.2.2,
    hlt13_14,
    by rw [h14v]; decide⟩

/-- Theorem 9 (`non_vacuous_and_tight`, **Monotone `InitE.Certificate` Chain Across All 14 Tiers**):
From `InitE.Certificate` at Tier 1 (`exactKeccak128UnrolledK = 1_212_035_192`), lifts monotonically
across all 14 candidate tiers (`exactKeccak128UnrolledK` through `bs32JointSlope3K = 459_244_490_549`),
`blockVsTxSlope12K = 857_384_015_252`, and `.infinity`. -/
theorem fourteen_tier_certificate_monotonicity_chain_non_vacuous_and_tight
    {K₁ K₂ : Nat} (hle : K₁ ≤ K₂)
    (hcert₁ : InitE.Certificate (baselineWithFiniteK K₁) (.finite K₁))
    (hcert_u128 : InitE.Certificate (baselineWithFiniteK exactKeccak128UnrolledK)
      (.finite exactKeccak128UnrolledK)) :
    InitE.Certificate (baselineWithFiniteK K₂) (.finite K₂) ∧
    InitE.Certificate (baselineWithFiniteK exactKeccak128UnrolledK) (.finite exactKeccak128UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK exactKeccak0UnrolledK) (.finite exactKeccak0UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK sixPassUnrolledCopyLoopK) (.finite sixPassUnrolledCopyLoopK) ∧
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    InitE.Certificate (baselineWithFiniteK exactKeccak128CandidateK) (.finite exactKeccak128CandidateK) ∧
    InitE.Certificate (baselineWithFiniteK isoReducedCopyLoopK) (.finite isoReducedCopyLoopK) ∧
    InitE.Certificate (baselineWithFiniteK isoReducedCandidateK) (.finite isoReducedCandidateK) ∧
    InitE.Certificate (baselineWithFiniteK exactKeccakCandidateK) (.finite exactKeccakCandidateK) ∧
    InitE.Certificate (baselineWithFiniteK push31NoGcCandidateK) (.finite push31NoGcCandidateK) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope3K) (.finite blockVsTxSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope6K) (.finite blockVsTxSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3UnrolledK) (.finite bs32JointSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope12K) (.finite blockVsTxSlope12K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity := by
  have h12 := twelve_tier_certificate_monotonicity_chain_non_vacuous_and_tight hle hcert₁ hcert_u128
  have hmono : ∀ {A B : Nat}, A ≤ B →
      InitE.Certificate (baselineWithFiniteK A) (.finite A) →
      InitE.Certificate (baselineWithFiniteK B) (.finite B) := by
    intro A B hab hA
    refine ⟨rfl, baselineWithFiniteK_admitted B, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hA.correct input hgas outcome events hsrc hcov
    have hm_base : matchingExecutionAt InitE.baselineSubmission input outcome events steps :=
      (matchingExecutionAt_with_score InitE.baselineSubmission (.finite A)
        input outcome events steps).mp hm
    exact ⟨steps, Nat.le_trans hsteps hab,
      (matchingExecutionAt_with_score InitE.baselineSubmission (.finite B)
        input outcome events steps).mpr hm_base⟩
  have h14 := fourteen_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have h10 : blockVsTxSlope6K = 428_692_019_192 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h13 : bs32JointSlope3UnrolledK = 459_244_476_749 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h14v : bs32JointSlope3K = 459_244_490_549 := h14.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt10_13 : blockVsTxSlope6K < bs32JointSlope3UnrolledK := by rw [h10, h13]; decide
  have hlt13_14 : bs32JointSlope3UnrolledK < bs32JointSlope3K := by rw [h13, h14v]; decide
  have hc10 := h12.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc13 := hmono (Nat.le_of_lt hlt10_13) hc10
  have hc14 := hmono (Nat.le_of_lt hlt13_14) hc13
  exact ⟨h12.1, h12.2.1, h12.2.2.1, h12.2.2.2.1, h12.2.2.2.2.1, h12.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.1,
    h12.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.1,
    hc10, hc13, hc14, h12.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h12.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 10 (`non_vacuous_and_tight`, **Master 14-Tier SSA/CSE & `bs+32` Campaign Synthesis Certificate**):
Simultaneously unites:
- All 14 `InitE.Certificate (baselineWithFiniteK K) (.finite K)` tiers (`exactKeccak128UnrolledK` through
  `bs32JointSlope3K`), `blockVsTxSlope12K`, and `.infinity`,
- The 8-pass `WordToWord` `NoSt` & `storeConstsAllowance = 0` chain (`t_ssa_cse_mid_tail_chain`,
  `storeConstsAllowance_chain_zero`),
- The `StackRemoveStoreConstsZeroBridge` (`NoSC`, `storeConstsAllowance = 0`, `runAllowance = 0`),
- The `GuestBs32BlockStorageEnvelope` master bound (`linear + T2 + (2DW + blkRead C) ≤ kPanBs32Joint = 153_081_489_139`
  and `k * kPanBs32Joint < yukon ↔ k ≤ 5`), and
- Purified `.Solver` path admission (`0` `Bounded*` imports). -/
theorem master_fourteen_tier_ssa_cse_and_bs32_campaign_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width] (cAsm : AsmConfigExact width) (temp argc : Nat) (b : Bool)
    (ctx : Spt Nat) (prog : HolLoopProg width) (loc : Nat × Nat)
    (xs : List (Bool × Nat)) (origin : TraceFrom (LoopToWord.compHOL ctx prog loc).1 xs)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes D W C T2 k : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (hbud : 21 * D + W + 21 * C ≤ S)
    (htx : T2 ≤ perTx)
    (not_timeOut_u128 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccak128UnrolledK) (.finite exactKeccak128UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK exactKeccak0UnrolledK) (.finite exactKeccak0UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK sixPassUnrolledCopyLoopK) (.finite sixPassUnrolledCopyLoopK) ∧
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    InitE.Certificate (baselineWithFiniteK exactKeccak128CandidateK) (.finite exactKeccak128CandidateK) ∧
    InitE.Certificate (baselineWithFiniteK isoReducedCopyLoopK) (.finite isoReducedCopyLoopK) ∧
    InitE.Certificate (baselineWithFiniteK isoReducedCandidateK) (.finite isoReducedCandidateK) ∧
    InitE.Certificate (baselineWithFiniteK exactKeccakCandidateK) (.finite exactKeccakCandidateK) ∧
    InitE.Certificate (baselineWithFiniteK push31NoGcCandidateK) (.finite push31NoGcCandidateK) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope3K) (.finite blockVsTxSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope6K) (.finite blockVsTxSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3UnrolledK) (.finite bs32JointSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope12K) (.finite blockVsTxSlope12K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    NoSt (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
      (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
        (fullSsaCcTrans argc (WordInst.instSelect cAsm temp (LoopToWord.compHOL ctx prog loc).1)))))))) = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
        (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
          (fullSsaCcTrans argc (WordInst.instSelect cAsm temp (LoopToWord.compHOL ctx prog loc).1)))))))) = 0 ∧
    NoSC (LoopToWord.compHOL ctx prog loc).1 = true ∧
    StackRemoveStoreConstsZeroBridge.storeConstsAllowance (LoopToWord.compHOL ctx prog loc).1 = 0 ∧
    runAllowance xs = 0 ∧
    linear + T2 + (2 * (D * W) + blkRead C) ≤ kPanBs32Joint ∧
    (k * kPanBs32Joint < yukon ↔ k ≤ 5) ∧
    yukonScore bs32JointSlope3K minutes - yukonScore bs32JointSlope3UnrolledK minutes = 138_000_000 ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedSsaCseAndBs32Synth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedSsaCseAndBs32Synth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hcert_u128 := exact_keccak_128_unrolled_certificate
    oracles c depth hlab compiled depthBound not_timeOut_u128
  have hchain := fourteen_tier_certificate_monotonicity_chain_non_vacuous_and_tight
    (Nat.le_refl exactKeccak128UnrolledK) hcert_u128 hcert_u128
  have hcomp : NoSt (LoopToWord.compHOL ctx prog loc).1 = true := loopToWord_NoSt ctx prog loc
  have hbs32 := bs32_joint_slope3_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 minutes
  exact ⟨hchain.2.1, hchain.2.2.1, hchain.2.2.2.1, hchain.2.2.2.2.1, hchain.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.1, hchain.2.2.2.2.2.2.2.1, hchain.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.1, hchain.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.1, hchain.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    t_ssa_cse_mid_tail_chain cAsm temp argc b (LoopToWord.compHOL ctx prog loc).1 hcomp,
    storeConstsAllowance_chain_zero cAsm temp argc b (LoopToWord.compHOL ctx prog loc).1 hcomp,
    compHOL_NoSC ctx prog loc,
    StackRemoveStoreConstsZeroBridge.compiled_allowance_zero ctx prog loc,
    compiled_run_allowance_zero ctx prog loc xs origin,
    kPan_master D W C T2 hbud htx,
    slope_threshold k,
    hbs32.2.2.2.2.2.2.2.2.2.2,
    by decide,
    by decide,
    rfl⟩

#print axioms word_ssa_cse_eight_pass_chain_no_store_consts_non_vacuous_and_tight
#print axioms guest_bs32_block_storage_joint_envelope_and_slope_threshold_non_vacuous_and_tight
#print axioms bs32_joint_slope3_unrolled_and_baseline_tiers_non_vacuous_and_tight
#print axioms fourteen_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
#print axioms fourteen_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
#print axioms fourteen_tier_yukonScore_strict_order_and_float64_exact_non_vacuous_and_tight
#print axioms fourteen_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
#print axioms bs32_joint_slope3_certificates_and_margins_non_vacuous_and_tight
#print axioms fourteen_tier_certificate_monotonicity_chain_non_vacuous_and_tight
#print axioms master_fourteen_tier_ssa_cse_and_bs32_campaign_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedSsaCseAndBs32Synth
