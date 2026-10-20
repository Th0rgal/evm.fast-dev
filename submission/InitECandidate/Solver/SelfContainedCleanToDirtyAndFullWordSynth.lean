import InitECandidate.Solver.GuestSstoreCleanToDirtyTransition
import InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
import InitECandidate.Solver.SelfContainedWordSimpAndCoupledSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SelfContainedCleanToDirtyAndFullWordSynth` — Self-Contained 22-Tier `WordToWord.fullCompileSingle` (10 Passes) & Clean→Dirty `SSTORE` Transition Synthesis (`W5_75`)

This module has **0 imports from `InitECandidate.Proofs.Bounded*`** in its transitive closure and
unifies:
1. The complete 10-pass `WordToWord.fullCompileSingle` + `LoopToWord.compHOL` `NoSt` preservation chain
   (`WordToWordFullCompileNoStoreConsts`: `applyColour_NoSt_iff`, `t_applyColour`, `t_oracleColourOk`,
   `t_wordAlloc`, `t_fullCompileSingle`, `fullCompileSingle_preserves_meta`,
   `loopToWord_fullCompileSingle_NoSt`, `loopToWord_fullCompileSingle_allowance_zero`,
   `t_fullCompile_list`, `applyColour_keeps_storeConsts`, `fullCompileSingle_needs_hyp_counterexample`).
2. The clean-to-dirty `SSTORE` (`sstoreWarm false -> true`) transition envelope
   `GuestSstoreCleanToDirtyTransition` (`kPanTransition = 135_048_530_896`,
   `kPanTransition - kPanCoupled = 4_194_300_000`, `slopes_ok`,
   `slope_threshold : k * kPanTransition < yukon ↔ k ≤ 6`, `margin6 : yukon - 6 * kPanTransition = 90_428_740_098`).
3. The unrolled and non-unrolled target tiers for `kPanTransition` at slopes `3x` and `6x`:
   - `transitionSlope3UnrolledK = 9_332 + 3 * 135_048_530_896 = 405_145_602_020`
   - `transitionSlope3K = 23_132 + 3 * 135_048_530_896 = 405_145_615_820`
     (`405_145_602_020 < 405_145_615_820 < 900_719_925_474`)
   - `transitionSlope6UnrolledK = 9_332 + 6 * 135_048_530_896 = 810_291_194_708`
   - `transitionSlope6K = 23_132 + 6 * 135_048_530_896 = 810_291_208_508`
     (`810_291_194_708 < 810_291_208_508 < 900_719_925_474`).
4. The certified 22-tier candidate hierarchy (`twentyTwoTierHierarchy`), `claim.json ≤ 128`-byte
   compliance, `yukonScore` monotonicity, and `InitE.Certificate` theorems (`0 sorryAx`).
-/

namespace InitECandidate.Solver.SelfContainedCleanToDirtyAndFullWordSynth

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
open InitECandidate.Solver.GuestCoupledTxBlockStorageBound
open InitECandidate.Solver.GuestSstoreWarmCoeffAudit
open InitECandidate.Solver.GuestSstoreCleanToDirtyTransition
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

/-! ## Section 1: Unrolled & Non-Unrolled `kPanTransition` Slope-3 & Slope-6 Tiers and `twentyTwoTierHierarchy` -/

/-- Post-bootstrap target steps for `kPanTransition = 135_048_530_896` at `3x` target slope:
`3 * 135_048_530_896 = 405_145_592_688`. -/
def transitionSlope3PostK : Nat := 3 * kPanTransition

/-- Unrolled-`copyLoop` (`bootstrapSteps - copyLoopSavedSteps = 9_332`) target ceiling for
`kPanTransition` at `3x` slope: `9_332 + 3 * 135_048_530_896 = 405_145_602_020`. -/
def transitionSlope3UnrolledK : Nat :=
  (bootstrapSteps - copyLoopSavedSteps) + transitionSlope3PostK

/-- Baseline-bootstrap (`bootstrapSteps = 23_132`) target ceiling for `kPanTransition` at
`3x` slope: `23_132 + 3 * 135_048_530_896 = 405_145_615_820`. -/
def transitionSlope3K : Nat :=
  bootstrapSteps + transitionSlope3PostK

/-- Post-bootstrap target steps for `kPanTransition = 135_048_530_896` at `6x` target slope:
`6 * 135_048_530_896 = 810_291_185_376`. -/
def transitionSlope6PostK : Nat := 6 * kPanTransition

/-- Unrolled-`copyLoop` (`bootstrapSteps - copyLoopSavedSteps = 9_332`) target ceiling for
`kPanTransition` at `6x` slope: `9_332 + 6 * 135_048_530_896 = 810_291_194_708`. -/
def transitionSlope6UnrolledK : Nat :=
  (bootstrapSteps - copyLoopSavedSteps) + transitionSlope6PostK

/-- Baseline-bootstrap (`bootstrapSteps = 23_132`) target ceiling for `kPanTransition` at
`6x` slope: `23_132 + 6 * 135_048_530_896 = 810_291_208_508`. -/
def transitionSlope6K : Nat :=
  bootstrapSteps + transitionSlope6PostK

/-- The certified 22-tier candidate hierarchy (`twentyTwoTierHierarchy`), formed by inserting
`transitionSlope3UnrolledK`, `transitionSlope3K`, `transitionSlope6UnrolledK`, and
`transitionSlope6K` into the 18-tier hierarchy of `SelfContainedWordSimpAndCoupledSynth`. -/
def twentyTwoTierHierarchy : List Nat :=
  [ exactKeccak128UnrolledK,
    exactKeccak0UnrolledK,
    sixPassUnrolledCopyLoopK,
    sixPassReducedK,
    exactKeccak128CandidateK,
    isoReducedCopyLoopK,
    isoReducedCandidateK,
    exactKeccakCandidateK,
    push31NoGcCandidateK,
    perTxSixPassTargetK,
    blockVsTxSlope3K,
    coupledSlope3UnrolledK,
    coupledSlope3K,
    transitionSlope3UnrolledK,
    transitionSlope3K,
    blockVsTxSlope6K,
    bs32JointSlope3UnrolledK,
    bs32JointSlope3K,
    coupledSlope6UnrolledK,
    coupledSlope6K,
    transitionSlope6UnrolledK,
    transitionSlope6K ]

/-- Canonical `{"claimed_k": "<K>"}` JSON strings (`≤ 128` bytes) for the 4 transition tiers. -/
def claimJsonTransitionSlope3Unrolled : String := claimedKJson "405145602020"
def claimJsonTransitionSlope3 : String := claimedKJson "405145615820"
def claimJsonTransitionSlope6Unrolled : String := claimedKJson "810291194708"
def claimJsonTransitionSlope6 : String := claimedKJson "810291208508"

/-- Canonical `{"K": <K>}` JSON strings (`verifier/check_submission.py`) for the 4 transition tiers. -/
def verifierJsonTransitionSlope3Unrolled : String := verifierClaimJson "405145602020"
def verifierJsonTransitionSlope3 : String := verifierClaimJson "405145615820"
def verifierJsonTransitionSlope6Unrolled : String := verifierClaimJson "810291194708"
def verifierJsonTransitionSlope6 : String := verifierClaimJson "810291208508"

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`, **Complete 10-Pass `WordToWord.fullCompileSingle` + `LoopToWord.compHOL` `NoSt` Chain & Zero `storeConstsAllowance`**):
Unites `applyColour_NoSt_iff`, `t_wordAlloc`, `t_fullCompileSingle`, `fullCompileSingle_preserves_meta`,
`loopToWord_fullCompileSingle_NoSt`, `loopToWord_fullCompileSingle_allowance_zero`, `t_fullCompile_list`,
`applyColour_keeps_storeConsts`, and `fullCompileSingle_needs_hyp_counterexample` from
`WordToWordFullCompileNoStoreConsts`:
every `LoopToWord.compHOL ctx q l` output preserves `NoSt = true` and `storeConstsAllowance = 0`
through 100% of `WordToWord.fullCompileSingle` (`WordSimp.compileExp → instSelect → fullSsaCcTrans →
removeDeadProg → wordCommonSubexpElim → copyProp → threeToTwoRegProg → removeUnreach → removeDeadProg →
wordAlloc → removeMustTerminate`), whereas an explicit `.storeConsts` node evaluates to `NoSt = false`
and `storeConstsAllowance = 1`. -/
theorem word_to_word_full_compile_single_no_store_consts_non_vacuous_and_tight
    {width : Nat} [NeZero width] (b : Bool) (rc alg fc k : Nat) (c : AsmConfigExact width)
    (nm ac : Nat) (f : Nat → Nat)
    (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat))
    (ps : List ((Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)))
    (hp : NoSt p = true)
    (hps : ∀ x ∈ ps, NoSt x.1.2.2 = true) :
    NoSt (Flapjack.WordAlloc.applyColour f p) = true ∧
    NoSt (Flapjack.WordAlloc.wordAlloc fc c alg k p co) = true ∧
    NoSt (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.2 = true ∧
    (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).1 = nm ∧
    (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.1 = ac ∧
    NoSt (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordToWord.fullCompileSingle b rc alg c
        ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 ∧
    (∀ y ∈ ps.map (WordToWord.fullCompileSingle b rc alg c), NoSt y.2.2 = true) ∧
    NoSt (Flapjack.WordAlloc.applyColour f
      (WordLangProgHOL.storeConsts (α := BitVec width) 0 2 4 6 [])) = false ∧
    NoSt (WordLangProgHOL.mustTerminate (α := BitVec width)
      (.storeConsts 0 2 4 6 [])) = false ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordLangProgHOL.storeConsts (α := BitVec width) 0 2 4 6 []) = 1 := by
  have hm := fullCompileSingle_preserves_meta b rc alg c nm ac p co
  exact ⟨t_applyColour f p hp,
    t_wordAlloc fc c alg k p co hp,
    t_fullCompileSingle b rc alg c nm ac p co hp,
    hm.1, hm.2,
    loopToWord_fullCompileSingle_NoSt ctx q l b rc alg c nm ac co,
    loopToWord_fullCompileSingle_allowance_zero ctx q l b rc alg c nm ac co,
    t_fullCompile_list b rc alg c ps hps,
    applyColour_keeps_storeConsts f,
    fullCompileSingle_needs_hyp_counterexample,
    storeConstsAllowance_tight⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **Clean→Dirty `SSTORE` Transition `kPanTransition = 135_048_530_896`, Insertion Envelope & `k ≤ 6` Slope Threshold**):
Unifies `GuestSstoreCleanToDirtyTransition`:
- `afterSet d = true` and `seqBlock false (n + 1) = n + 2 ∧ seqBlock true n = n`,
- `cleanUnits = 20 ∧ 4 ≤ 2 * cleanUnits`,
- `D * (2 * W + 4 * R) ≤ 95_238_095_238` (tight at `(47619, 1000001, 0)`),
- `(rs.map (fun r => 5 * (r * (r - 1)))).sum ≤ 4_194_300_000` (with single-tx tightness at `r = 8388`),
- `kPanTransition = 135_048_530_896`, `kPanTransition - kPanCoupled = 4_194_300_000`,
- `slopes_ok` (`3x, 4x, 5x, 6x < yukon`), `k * kPanTransition < yukon ↔ k ≤ 6`, and
  `yukon - 6 * kPanTransition = 90_428_740_098`. -/
theorem guest_sstore_clean_to_dirty_transition_and_slope_threshold_non_vacuous_and_tight
    (d : Bool) (n D W R k : Nat) (rs : List Nat)
    (hDWR : 21 * D + W + 20 * R ≤ S)
    (hrs : ∀ r ∈ rs, 20 * r ≤ GuestCoupledTxBlockStorageBound.M)
    (hrsS : 20 * rs.sum ≤ S) :
    afterSet d = true ∧
    cnt .blockStor (sstoreWarm (afterSet d)) = 1 ∧
    cnt .blockStor (sstoreWarm false) = 2 ∧
    seqBlock false (n + 1) = n + 2 ∧
    seqBlock true n = n ∧
    cleanUnits = 20 ∧
    4 ≤ 2 * cleanUnits ∧
    42 * (D * (2 * W + 4 * R)) ≤ S * S ∧
    D * (2 * W + 4 * R) ≤ 95_238_095_238 ∧
    47619 * (2 * 1000001 + 4 * 0) = 95_238_095_238 ∧
    (rs.map (fun r => 5 * (r * (r - 1)))).sum ≤ 4_194_300_000 ∧
    (20 * 8388 ≤ GuestCoupledTxBlockStorageBound.M ∧
      GuestCoupledTxBlockStorageBound.M < 20 * 8389 ∧
      5 * (8388 * (8388 - 1)) = 351_750_780) ∧
    kPanTransition = 135_048_530_896 ∧
    kPanTransition - kPanCoupled = 4_194_300_000 ∧
    kPanBs32Joint - kPanTransition = 18_032_958_243 ∧
    3 * kPanTransition < yukon ∧
    4 * kPanTransition < yukon ∧
    5 * kPanTransition < yukon ∧
    6 * kPanTransition < yukon ∧
    yukon < 7 * kPanTransition ∧
    (k * kPanTransition < yukon ↔ k ≤ 6) ∧
    yukon - 6 * kPanTransition = 90_428_740_098 := by
  have htr := transition d
  have hseq := seqBlock_eq n
  have hcc := clean_cost
  have hbu := block_unchanged D W R hDWR
  have hval := kPanTransition_val
  have hsl := slopes_ok
  have hbs32 : kPanBs32Joint - kPanTransition = 18_032_958_243 := by decide
  have h7 : yukon < 7 * kPanTransition := by decide
  exact ⟨htr.1, htr.2.1, htr.2.2,
    hseq.1, hseq.2,
    hcc.1, hcc.2,
    block_with_clean D W R hDWR,
    hbu.1, hbu.2,
    insert_le rs hrs hrsS,
    insert_tight,
    hval.1, hval.2,
    hbs32,
    hsl.1, hsl.2.1, hsl.2.2.1, hsl.2.2.2,
    h7,
    GuestSstoreCleanToDirtyTransition.slope_threshold k,
    margin6⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Exact Values & Bounds of the `kPanTransition` Slope-3 and Slope-6 Tiers**):
Certifies the unrolled and non-unrolled `3x`-slope and `6x`-slope tiers for `kPanTransition`:
- `3x`: `transitionSlope3UnrolledK = 405_145_602_020 < transitionSlope3K = 405_145_615_820 < 900_719_925_474`,
- `6x`: `transitionSlope6UnrolledK = 810_291_194_708 < transitionSlope6K = 810_291_208_508 < 900_719_925_474`,
- Exact transition increments (`12_582_900_000` at `3x` and `25_165_800_000` at `6x` over `kPanCoupled` tiers)
  and savings (`54_098_874_729` at `3x` over `bs32JointSlope3` tiers). -/
theorem transition_slope3_and_slope6_unrolled_and_baseline_tiers_non_vacuous_and_tight
    (k minutes : Nat) :
    transitionSlope3PostK = 405_145_592_688 ∧
    transitionSlope3UnrolledK = 405_145_602_020 ∧
    transitionSlope3K = 405_145_615_820 ∧
    transitionSlope6PostK = 810_291_185_376 ∧
    transitionSlope6UnrolledK = 810_291_194_708 ∧
    transitionSlope6K = 810_291_208_508 ∧
    405_145_602_020 < 405_145_615_820 ∧
    405_145_615_820 < 900_719_925_474 ∧
    810_291_194_708 < 810_291_208_508 ∧
    810_291_208_508 < 900_719_925_474 ∧
    coupledSlope3K < transitionSlope3UnrolledK ∧
    transitionSlope3UnrolledK < transitionSlope3K ∧
    transitionSlope3K < blockVsTxSlope6K ∧
    coupledSlope6K < transitionSlope6UnrolledK ∧
    transitionSlope6UnrolledK < transitionSlope6K ∧
    transitionSlope6K < blockVsTxSlope12K ∧
    transitionSlope6K < yukonFloat64MaxK ∧
    transitionSlope3K - transitionSlope3UnrolledK = 13_800 ∧
    transitionSlope6K - transitionSlope6UnrolledK = 13_800 ∧
    transitionSlope3UnrolledK - coupledSlope3UnrolledK = 12_582_900_000 ∧
    transitionSlope3K - coupledSlope3K = 12_582_900_000 ∧
    transitionSlope6UnrolledK - coupledSlope6UnrolledK = 25_165_800_000 ∧
    transitionSlope6K - coupledSlope6K = 25_165_800_000 ∧
    bs32JointSlope3UnrolledK - transitionSlope3UnrolledK = 54_098_874_729 ∧
    bs32JointSlope3K - transitionSlope3K = 54_098_874_729 ∧
    (transitionSlope3K ≤ k + copyLoopSavedSteps ↔ transitionSlope3UnrolledK ≤ k) ∧
    (transitionSlope6K ≤ k + copyLoopSavedSteps ↔ transitionSlope6UnrolledK ≤ k) ∧
    yukonScore transitionSlope3K minutes - yukonScore transitionSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore transitionSlope6K minutes - yukonScore transitionSlope6UnrolledK minutes = 138_000_000 := by
  have h18 := eighteen_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hbs : bootstrapSteps = 23_132 :=
    eighteen_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight.2.1
  have hsave : copyLoopSavedSteps = 13_800 := copy_loop_saved_exact
  have hkt : kPanTransition = 135_048_530_896 := kPanTransition_val.1
  have hc3u : coupledSlope3UnrolledK = 392_562_702_020 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc3 : coupledSlope3K = 392_562_715_820 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h10 : blockVsTxSlope6K = 428_692_019_192 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb3u : bs32JointSlope3UnrolledK = 459_244_476_749 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb3 : bs32JointSlope3K = 459_244_490_549 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6u : coupledSlope6UnrolledK = 785_125_394_708 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6 : coupledSlope6K = 785_125_408_508 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h11 : blockVsTxSlope12K = 857_384_015_252 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hp3 : transitionSlope3PostK = 405_145_592_688 := by unfold transitionSlope3PostK; rw [hkt]
  have hu3 : transitionSlope3UnrolledK = 405_145_602_020 := by
    unfold transitionSlope3UnrolledK; rw [hbs, hsave, hp3]
  have ht3 : transitionSlope3K = 405_145_615_820 := by
    unfold transitionSlope3K; rw [hbs, hp3]
  have hp6 : transitionSlope6PostK = 810_291_185_376 := by unfold transitionSlope6PostK; rw [hkt]
  have hu6 : transitionSlope6UnrolledK = 810_291_194_708 := by
    unfold transitionSlope6UnrolledK; rw [hbs, hsave, hp6]
  have ht6 : transitionSlope6K = 810_291_208_508 := by
    unfold transitionSlope6K; rw [hbs, hp6]
  have hy : yukonFloat64MaxK = 900_719_925_474 := rfl
  rw [hp3, hu3, ht3, hp6, hu6, ht6, hc3u, hc3, h10, hb3u, hb3, hc6u, hc6, h11, hsave, hy]
  unfold yukonScore
  omega

/-- Theorem 4 (`non_vacuous_and_tight`, **Strict Total Ordering Across the 22-Tier Hierarchy (`twentyTwoTierHierarchy`)**):
Establishes `twentyTwoTierHierarchy.length = 22`, `twentyTwoTierHierarchy.Pairwise (· < ·)`,
and the exact numerical values and strict total ordering across all 22 tiers (plus
`exactKeccak128NoGcK`, `exactKeccakNoGcK`, and `blockVsTxSlope12K < 900_719_925_474`). -/
theorem twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight :
    twentyTwoTierHierarchy.length = 22 ∧
    twentyTwoTierHierarchy.Pairwise (· < ·) ∧
    (∀ K ∈ twentyTwoTierHierarchy, K < 900_719_925_474) ∧
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
    coupledSlope3UnrolledK = 392_562_702_020 ∧
    coupledSlope3K = 392_562_715_820 ∧
    transitionSlope3UnrolledK = 405_145_602_020 ∧
    transitionSlope3K = 405_145_615_820 ∧
    blockVsTxSlope6K = 428_692_019_192 ∧
    bs32JointSlope3UnrolledK = 459_244_476_749 ∧
    bs32JointSlope3K = 459_244_490_549 ∧
    coupledSlope6UnrolledK = 785_125_394_708 ∧
    coupledSlope6K = 785_125_408_508 ∧
    transitionSlope6UnrolledK = 810_291_194_708 ∧
    transitionSlope6K = 810_291_208_508 ∧
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
    blockVsTxSlope3K < coupledSlope3UnrolledK ∧
    coupledSlope3UnrolledK < coupledSlope3K ∧
    coupledSlope3K < transitionSlope3UnrolledK ∧
    transitionSlope3UnrolledK < transitionSlope3K ∧
    transitionSlope3K < blockVsTxSlope6K ∧
    blockVsTxSlope6K < bs32JointSlope3UnrolledK ∧
    bs32JointSlope3UnrolledK < bs32JointSlope3K ∧
    bs32JointSlope3K < coupledSlope6UnrolledK ∧
    coupledSlope6UnrolledK < coupledSlope6K ∧
    coupledSlope6K < transitionSlope6UnrolledK ∧
    transitionSlope6UnrolledK < transitionSlope6K ∧
    transitionSlope6K < blockVsTxSlope12K ∧
    blockVsTxSlope12K < 900_719_925_474 := by
  have h18 := eighteen_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hu128 : exactKeccak128UnrolledK = 1_212_035_192 := h18.1
  have hb128 : exactKeccak128NoGcK = 1_212_048_992 := h18.2.1
  have hu0 : exactKeccak0UnrolledK = 2_038_701_869 := h18.2.2.1
  have hb0 : exactKeccakNoGcK = 2_038_715_669 := h18.2.2.2.1
  have h1 : sixPassUnrolledCopyLoopK = 11_029_669_988 := h18.2.2.2.2.1
  have h2 : sixPassReducedK = 11_029_683_788 := h18.2.2.2.2.2.1
  have h3 : exactKeccak128CandidateK = 19_392_692_330 := h18.2.2.2.2.2.2.1
  have h4 : isoReducedCopyLoopK = 22_059_330_644 := h18.2.2.2.2.2.2.2.1
  have h5 : isoReducedCandidateK = 22_059_344_444 := h18.2.2.2.2.2.2.2.2.1
  have h6 : exactKeccakCandidateK = 32_791_963_724 := h18.2.2.2.2.2.2.2.2.2.1
  have h7 : push31NoGcCandidateK = 87_829_684_748 := h18.2.2.2.2.2.2.2.2.2.2.1
  have h8 : perTxSixPassTargetK = 122_620_608_536 := h18.2.2.2.2.2.2.2.2.2.2.2.1
  have h9 : blockVsTxSlope3K = 214_346_021_162 := h18.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc3u : coupledSlope3UnrolledK = 392_562_702_020 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc3 : coupledSlope3K = 392_562_715_820 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h10 : blockVsTxSlope6K = 428_692_019_192 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb3u : bs32JointSlope3UnrolledK = 459_244_476_749 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb3 : bs32JointSlope3K = 459_244_490_549 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6u : coupledSlope6UnrolledK = 785_125_394_708 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6 : coupledSlope6K = 785_125_408_508 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h11 : blockVsTxSlope12K = 857_384_015_252 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htr := transition_slope3_and_slope6_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 0
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := htr.2.1
  have ht3 : transitionSlope3K = 405_145_615_820 := htr.2.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := htr.2.2.2.2.1
  have ht6 : transitionSlope6K = 810_291_208_508 := htr.2.2.2.2.2.1
  have hy : yukonFloat64MaxK = 900_719_925_474 := rfl
  unfold twentyTwoTierHierarchy
  rw [hu128, hb128, hu0, hb0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hc3u, hc3, ht3u, ht3, h10, hb3u, hb3, hc6u, hc6, ht6u, ht6, h11, hy]
  decide

/-- Theorem 5 (`non_vacuous_and_tight`, **Bootstrap Decompositions & 1-Tick Tightness Across All Transition, Coupled & `bs+32` Tiers**):
Establishes exact `(bootstrapSteps - copyLoopSavedSteps) = 9_332` and `bootstrapSteps = 23_132`
decompositions for `transitionSlope3UnrolledK`, `transitionSlope3K`, `transitionSlope6UnrolledK`,
and `transitionSlope6K`, with sharp 1-tick tightness boundaries (`¬ K ≤ K - 1`). -/
theorem twenty_two_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight :
    bootstrapSteps - copyLoopSavedSteps = 9_332 ∧
    bootstrapSteps = 23_132 ∧
    transitionSlope3UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanTransition ∧
    transitionSlope3K = bootstrapSteps + 3 * kPanTransition ∧
    transitionSlope6UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 6 * kPanTransition ∧
    transitionSlope6K = bootstrapSteps + 6 * kPanTransition ∧
    coupledSlope3UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanCoupled ∧
    coupledSlope3K = bootstrapSteps + 3 * kPanCoupled ∧
    coupledSlope6UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 6 * kPanCoupled ∧
    coupledSlope6K = bootstrapSteps + 6 * kPanCoupled ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanTransition ≤ transitionSlope3UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 3 * kPanTransition ≤ transitionSlope3K - 1) ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanTransition ≤ transitionSlope6UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 6 * kPanTransition ≤ transitionSlope6K - 1) := by
  have h18b := eighteen_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
  have hbs : bootstrapSteps = 23_132 := h18b.2.1
  have hsave : copyLoopSavedSteps = 13_800 := copy_loop_saved_exact
  have hkt : kPanTransition = 135_048_530_896 := kPanTransition_val.1
  have htr := transition_slope3_and_slope6_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 0
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := htr.2.1
  have ht3 : transitionSlope3K = 405_145_615_820 := htr.2.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := htr.2.2.2.2.1
  have ht6 : transitionSlope6K = 810_291_208_508 := htr.2.2.2.2.2.1
  refine ⟨h18b.1, hbs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [ht3u, hbs, hsave, hkt]; decide
  · rw [ht3, hbs, hkt]; decide
  · rw [ht6u, hbs, hsave, hkt]; decide
  · rw [ht6, hbs, hkt]; decide

/-- Theorem 6 (`non_vacuous_and_tight`, **IEEE-754 Float64 Representability & Strict `yukonScore` Order Across All Transition & Coupled Tiers**):
Strict `yukonScore` ordering and exact IEEE-754 double-precision integer representability
(`yukonScore K minutes < 2^53 - 1`) across all transition, coupled, and `bs+32` tiers for every
`minutes : Nat`, plus the sharp uniform ceiling equivalence
`yukonScore K 9999 < 2^53 - 1 ↔ K < 900_719_925_474`. -/
theorem twenty_two_tier_yukonScore_strict_order_and_float64_exact_non_vacuous_and_tight
    (minutes K : Nat) :
    yukonScore coupledSlope3UnrolledK minutes < yukonScore coupledSlope3K minutes ∧
    yukonScore coupledSlope3K minutes < yukonScore transitionSlope3UnrolledK minutes ∧
    yukonScore transitionSlope3UnrolledK minutes < yukonScore transitionSlope3K minutes ∧
    yukonScore transitionSlope3K minutes < yukonScore blockVsTxSlope6K minutes ∧
    yukonScore blockVsTxSlope6K minutes < yukonScore bs32JointSlope3UnrolledK minutes ∧
    yukonScore bs32JointSlope3UnrolledK minutes < yukonScore bs32JointSlope3K minutes ∧
    yukonScore bs32JointSlope3K minutes < yukonScore coupledSlope6UnrolledK minutes ∧
    yukonScore coupledSlope6UnrolledK minutes < yukonScore coupledSlope6K minutes ∧
    yukonScore coupledSlope6K minutes < yukonScore transitionSlope6UnrolledK minutes ∧
    yukonScore transitionSlope6UnrolledK minutes < yukonScore transitionSlope6K minutes ∧
    yukonScore transitionSlope6K minutes < yukonScore blockVsTxSlope12K minutes ∧
    yukonScore transitionSlope3UnrolledK minutes < 2 ^ 53 - 1 ∧
    yukonScore transitionSlope3K minutes < 2 ^ 53 - 1 ∧
    yukonScore transitionSlope6UnrolledK minutes < 2 ^ 53 - 1 ∧
    yukonScore transitionSlope6K minutes < 2 ^ 53 - 1 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have h22 := twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hc3u : coupledSlope3UnrolledK = 392_562_702_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc3 : coupledSlope3K = 392_562_715_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3 : transitionSlope3K = 405_145_615_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h10 : blockVsTxSlope6K = 428_692_019_192 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb3u : bs32JointSlope3UnrolledK = 459_244_476_749 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb3 : bs32JointSlope3K = 459_244_490_549 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6u : coupledSlope6UnrolledK = 785_125_394_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6 : coupledSlope6K = 785_125_408_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6 : transitionSlope6K = 810_291_208_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h11 : blockVsTxSlope12K = 857_384_015_252 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hm : min minutes 9999 ≤ 9999 := Nat.min_le_right _ _
  have hm9999 : min 9999 9999 = 9999 := rfl
  rw [hc3u, hc3, ht3u, ht3, h10, hb3u, hb3, hc6u, hc6, ht6u, ht6, h11]
  unfold yukonScore
  rw [hm9999]
  omega

/-- Theorem 7 (`non_vacuous_and_tight`, **`claim.json ≤ 128`-Byte Audit Across All 4 `kPanTransition` Tiers**):
Exact UTF-8 byte sizes (`29` bytes for `{"claimed_k": "..."}` and `19` bytes for `{"K": ...}`),
`validFiniteClaim` conformance across all 4 transition tiers (`transitionSlope3UnrolledK`,
`transitionSlope3K`, `transitionSlope6UnrolledK`, `transitionSlope6K`) and the 4 coupled tiers,
and sharp `128`-byte vs `129`-byte `checkSubmissionLimits` boundary. -/
theorem twenty_two_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight :
    claimJsonTransitionSlope3Unrolled.utf8ByteSize = 29 ∧
    claimJsonTransitionSlope3.utf8ByteSize = 29 ∧
    claimJsonTransitionSlope6Unrolled.utf8ByteSize = 29 ∧
    claimJsonTransitionSlope6.utf8ByteSize = 29 ∧
    verifierJsonTransitionSlope3Unrolled.utf8ByteSize = 19 ∧
    verifierJsonTransitionSlope3.utf8ByteSize = 19 ∧
    verifierJsonTransitionSlope6Unrolled.utf8ByteSize = 19 ∧
    verifierJsonTransitionSlope6.utf8ByteSize = 19 ∧
    validFiniteClaim transitionSlope3UnrolledK claimJsonTransitionSlope3Unrolled = true ∧
    validFiniteClaim transitionSlope3K claimJsonTransitionSlope3 = true ∧
    validFiniteClaim transitionSlope6UnrolledK claimJsonTransitionSlope6Unrolled = true ∧
    validFiniteClaim transitionSlope6K claimJsonTransitionSlope6 = true ∧
    validFiniteClaim transitionSlope3UnrolledK verifierJsonTransitionSlope3Unrolled = true ∧
    validFiniteClaim transitionSlope3K verifierJsonTransitionSlope3 = true ∧
    validFiniteClaim transitionSlope6UnrolledK verifierJsonTransitionSlope6Unrolled = true ∧
    validFiniteClaim transitionSlope6K verifierJsonTransitionSlope6 = true ∧
    validFiniteClaim coupledSlope3UnrolledK claimJsonCoupledSlope3Unrolled = true ∧
    validFiniteClaim coupledSlope6UnrolledK claimJsonCoupledSlope6Unrolled = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonTransitionSlope3Unrolled.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonTransitionSlope3.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonTransitionSlope6Unrolled.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonTransitionSlope6.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 (MAX_CLAIM_BYTES + 1) false false true = false := by
  have htr := transition_slope3_and_slope6_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 0
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := htr.2.1
  have ht3 : transitionSlope3K = 405_145_615_820 := htr.2.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := htr.2.2.2.2.1
  have ht6 : transitionSlope6K = 810_291_208_508 := htr.2.2.2.2.2.1
  have hclaims18 := eighteen_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hclaims18.2.2.2.2.2.2.2.2.1,
    hclaims18.2.2.2.2.2.2.2.2.2.2.1,
    by decide, by decide, by decide, by decide, by decide⟩
  · rw [ht3u]; decide
  · rw [ht3]; decide
  · rw [ht6u]; decide
  · rw [ht6]; decide
  · rw [ht3u]; decide
  · rw [ht3]; decide
  · rw [ht6u]; decide
  · rw [ht6]; decide

/-- Theorem 8 (`non_vacuous_and_tight`, **Direct `InitE.Certificate` Bridges for `transitionSlope3UnrolledK`, `transitionSlope3K`, `transitionSlope6UnrolledK`, and `transitionSlope6K`**):
Proves that uniform target non-`.timeOut` at `transitionSlope3UnrolledK = 405_145_602_020` yields
`InitE.Certificate` at that budget and lifts monotonically across `transitionSlope3K = 405_145_615_820`,
`blockVsTxSlope6K = 428_692_019_192`, `bs32JointSlope3UnrolledK = 459_244_476_749`,
`bs32JointSlope3K = 459_244_490_549`, `coupledSlope6UnrolledK = 785_125_394_708`,
`coupledSlope6K = 785_125_408_508`, `transitionSlope6UnrolledK = 810_291_194_708`,
`transitionSlope6K = 810_291_208_508`, `blockVsTxSlope12K = 857_384_015_252`, and `.infinity`. -/
theorem transition_slope3_and_slope6_certificates_and_margins_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_transition_s3_unrolled : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          transitionSlope3UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK transitionSlope3UnrolledK) (.finite transitionSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope3K) (.finite transitionSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope6K) (.finite blockVsTxSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3UnrolledK) (.finite bs32JointSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coupledSlope6UnrolledK) (.finite coupledSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledSlope6K) (.finite coupledSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope6UnrolledK) (.finite transitionSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope6K) (.finite transitionSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope12K) (.finite blockVsTxSlope12K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    validFiniteClaim transitionSlope3UnrolledK claimJsonTransitionSlope3Unrolled = true ∧
    validFiniteClaim transitionSlope3K claimJsonTransitionSlope3 = true ∧
    validFiniteClaim transitionSlope6UnrolledK claimJsonTransitionSlope6Unrolled = true ∧
    validFiniteClaim transitionSlope6K claimJsonTransitionSlope6 = true ∧
    yukonScore transitionSlope3K minutes - yukonScore transitionSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore transitionSlope6K minutes - yukonScore transitionSlope6UnrolledK minutes = 138_000_000 ∧
    transitionSlope3UnrolledK < transitionSlope3K ∧
    transitionSlope6UnrolledK < transitionSlope6K ∧
    transitionSlope6K < 900_719_925_474 := by
  have h22 := twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3 : transitionSlope3K = 405_145_615_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h10 : blockVsTxSlope6K = 428_692_019_192 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb3u : bs32JointSlope3UnrolledK = 459_244_476_749 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb3 : bs32JointSlope3K = 459_244_490_549 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6u : coupledSlope6UnrolledK = 785_125_394_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6 : coupledSlope6K = 785_125_408_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6 : transitionSlope6K = 810_291_208_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h11 : blockVsTxSlope12K = 857_384_015_252 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert_t3u : InitE.Certificate (baselineWithFiniteK transitionSlope3UnrolledK)
      (.finite transitionSlope3UnrolledK) := by
    have h := finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth (405145602020 - 23132) hlab compiled depthBound
      (by simpa only [bootstrapSteps_eq, ht3u] using not_timeOut_transition_s3_unrolled)
    simpa only [bootstrapSteps_eq, ht3u] using h
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
  have hlt1 : transitionSlope3UnrolledK < transitionSlope3K := by rw [ht3u, ht3]; decide
  have hlt2 : transitionSlope3K < blockVsTxSlope6K := by rw [ht3, h10]; decide
  have hlt3 : blockVsTxSlope6K < bs32JointSlope3UnrolledK := by rw [h10, hb3u]; decide
  have hlt4 : bs32JointSlope3UnrolledK < bs32JointSlope3K := by rw [hb3u, hb3]; decide
  have hlt5 : bs32JointSlope3K < coupledSlope6UnrolledK := by rw [hb3, hc6u]; decide
  have hlt6 : coupledSlope6UnrolledK < coupledSlope6K := by rw [hc6u, hc6]; decide
  have hlt7 : coupledSlope6K < transitionSlope6UnrolledK := by rw [hc6, ht6u]; decide
  have hlt8 : transitionSlope6UnrolledK < transitionSlope6K := by rw [ht6u, ht6]; decide
  have hlt9 : transitionSlope6K < blockVsTxSlope12K := by rw [ht6, h11]; decide
  have hcert_t3 := hmono (Nat.le_of_lt hlt1) hcert_t3u
  have hcert_10 := hmono (Nat.le_of_lt hlt2) hcert_t3
  have hcert_b3u := hmono (Nat.le_of_lt hlt3) hcert_10
  have hcert_b3 := hmono (Nat.le_of_lt hlt4) hcert_b3u
  have hcert_c6u := hmono (Nat.le_of_lt hlt5) hcert_b3
  have hcert_c6 := hmono (Nat.le_of_lt hlt6) hcert_c6u
  have hcert_t6u := hmono (Nat.le_of_lt hlt7) hcert_c6
  have hcert_t6 := hmono (Nat.le_of_lt hlt8) hcert_t6u
  have hcert_12 := hmono (Nat.le_of_lt hlt9) hcert_t6
  have hinf : InitE.Certificate InitE.baselineSubmission .infinity := by
    refine ⟨rfl, InitE.baselineSubmission_admitted, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, _, hm⟩ := hcert_t3u.correct input hgas outcome events hsrc hcov
    exact ⟨steps, trivial,
      (matchingExecutionAt_with_score InitE.baselineSubmission (.finite transitionSlope3UnrolledK)
        input outcome events steps).mp hm⟩
  have hclaims := twenty_two_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
  have htr := transition_slope3_and_slope6_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 minutes
  exact ⟨hcert_t3u, hcert_t3, hcert_10, hcert_b3u, hcert_b3, hcert_c6u, hcert_c6, hcert_t6u, hcert_t6, hcert_12, hinf,
    hclaims.2.2.2.2.2.2.2.2.1,
    hclaims.2.2.2.2.2.2.2.2.2.1,
    hclaims.2.2.2.2.2.2.2.2.2.2.1,
    hclaims.2.2.2.2.2.2.2.2.2.2.2.1,
    htr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    htr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hlt1, hlt8, by rw [ht6]; decide⟩

/-- Theorem 9 (`non_vacuous_and_tight`, **Monotone `InitE.Certificate` Chain Across All 22 Tiers (`twentyTwoTierHierarchy`)**):
From `InitE.Certificate` at Tier 1 (`exactKeccak128UnrolledK = 1_212_035_192`), lifts monotonically
across all 22 tiers of `twentyTwoTierHierarchy` (plus `blockVsTxSlope12K = 857_384_015_252` and
`.infinity`). -/
theorem twenty_two_tier_certificate_monotonicity_chain_non_vacuous_and_tight
    {K₁ K₂ : Nat} (hle : K₁ ≤ K₂)
    (hcert₁ : InitE.Certificate (baselineWithFiniteK K₁) (.finite K₁))
    (hcert_u128 : InitE.Certificate (baselineWithFiniteK exactKeccak128UnrolledK)
      (.finite exactKeccak128UnrolledK)) :
    InitE.Certificate (baselineWithFiniteK K₂) (.finite K₂) ∧
    (∀ K ∈ twentyTwoTierHierarchy, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
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
    InitE.Certificate (baselineWithFiniteK coupledSlope3UnrolledK) (.finite coupledSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledSlope3K) (.finite coupledSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope3UnrolledK) (.finite transitionSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope3K) (.finite transitionSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope6K) (.finite blockVsTxSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3UnrolledK) (.finite bs32JointSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coupledSlope6UnrolledK) (.finite coupledSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledSlope6K) (.finite coupledSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope6UnrolledK) (.finite transitionSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope6K) (.finite transitionSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope12K) (.finite blockVsTxSlope12K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity := by
  have h18 := eighteen_tier_certificate_monotonicity_chain_non_vacuous_and_tight hle hcert₁ hcert_u128
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
  have h22 := twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hc3 : coupledSlope3K = 392_562_715_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3 : transitionSlope3K = 405_145_615_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6 : coupledSlope6K = 785_125_408_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6 : transitionSlope6K = 810_291_208_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hltc3_t3u : coupledSlope3K < transitionSlope3UnrolledK := by rw [hc3, ht3u]; decide
  have hltt3u_t3 : transitionSlope3UnrolledK < transitionSlope3K := by rw [ht3u, ht3]; decide
  have hltc6_t6u : coupledSlope6K < transitionSlope6UnrolledK := by rw [hc6, ht6u]; decide
  have hltt6u_t6 : transitionSlope6UnrolledK < transitionSlope6K := by rw [ht6u, ht6]; decide
  have hcc3 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert_t3u := hmono (Nat.le_of_lt hltc3_t3u) hcc3
  have hcert_t3 := hmono (Nat.le_of_lt hltt3u_t3) hcert_t3u
  have hcc6 := h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert_t6u := hmono (Nat.le_of_lt hltc6_t6u) hcc6
  have hcert_t6 := hmono (Nat.le_of_lt hltt6u_t6) hcert_t6u
  have hall : ∀ K ∈ twentyTwoTierHierarchy, InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
    intro K hK
    unfold twentyTwoTierHierarchy at hK
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
    rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h18.2.1
    · exact h18.2.2.1
    · exact h18.2.2.2.1
    · exact h18.2.2.2.2.1
    · exact h18.2.2.2.2.2.1
    · exact h18.2.2.2.2.2.2.1
    · exact h18.2.2.2.2.2.2.2.1
    · exact h18.2.2.2.2.2.2.2.2.1
    · exact h18.2.2.2.2.2.2.2.2.2.1
    · exact h18.2.2.2.2.2.2.2.2.2.2.1
    · exact h18.2.2.2.2.2.2.2.2.2.2.2.1
    · exact h18.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hcc3
    · exact hcert_t3u
    · exact hcert_t3
    · exact h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact hcc6
    · exact hcert_t6u
    · exact hcert_t6
  exact ⟨h18.1, hall, h18.2.1, h18.2.2.1, h18.2.2.2.1, h18.2.2.2.2.1, h18.2.2.2.2.2.1,
    h18.2.2.2.2.2.2.1, h18.2.2.2.2.2.2.2.1, h18.2.2.2.2.2.2.2.2.1,
    h18.2.2.2.2.2.2.2.2.2.1, h18.2.2.2.2.2.2.2.2.2.2.1, h18.2.2.2.2.2.2.2.2.2.2.2.1,
    h18.2.2.2.2.2.2.2.2.2.2.2.2.1, hcc3,
    hcert_t3u, hcert_t3,
    h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hcc6,
    hcert_t6u, hcert_t6,
    h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 10 (`non_vacuous_and_tight`, **Master 22-Tier `WordToWord.fullCompileSingle` & Clean→Dirty `SSTORE` Campaign Certificate**):
Simultaneously unites:
- All 22 `InitE.Certificate (baselineWithFiniteK K) (.finite K)` tiers in `twentyTwoTierHierarchy`
  (plus `blockVsTxSlope12K` and `.infinity`),
- The 10-pass `WordToWord.fullCompileSingle` + `LoopToWord.compHOL` `NoSt = true` and
  `storeConstsAllowance = 0` chain (`loopToWord_fullCompileSingle_NoSt`,
  `loopToWord_fullCompileSingle_allowance_zero`),
- The `StackRemoveStoreConstsZeroBridge` (`NoSC`, `storeConstsAllowance = 0`, `runAllowance = 0`),
- The `GuestSstoreCleanToDirtyTransition` master envelope (`kPanTransition = 135_048_530_896`,
  `kPanTransition - kPanCoupled = 4_194_300_000`, `slopes_ok`, `k * kPanTransition < yukon ↔ k ≤ 6`,
  and `(rs.map (fun r => 5 * (r * (r - 1)))).sum ≤ 4_194_300_000`), and
- Purified `.Solver` path admission (`0` `Bounded*` imports). -/
theorem master_twenty_two_tier_clean_to_dirty_and_full_word_campaign_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width] (cAsm : AsmConfigExact width) (rc alg nm ac : Nat) (b : Bool)
    (ctx : Spt Nat) (prog : HolLoopProg width) (loc : Nat × Nat) (co : Option (Spt Nat))
    (xs : List (Bool × Nat)) (origin : TraceFrom (LoopToWord.compHOL ctx prog loc).1 xs)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes D W R k : Nat)
    (rs : List Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (hDWR : 21 * D + W + 20 * R ≤ S)
    (hrs : ∀ r ∈ rs, 20 * r ≤ GuestCoupledTxBlockStorageBound.M)
    (hrsS : 20 * rs.sum ≤ S)
    (not_timeOut_u128 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    twentyTwoTierHierarchy.length = 22 ∧
    twentyTwoTierHierarchy.Pairwise (· < ·) ∧
    (∀ K ∈ twentyTwoTierHierarchy, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope3UnrolledK) (.finite transitionSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope3K) (.finite transitionSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope6UnrolledK) (.finite transitionSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope6K) (.finite transitionSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope12K) (.finite blockVsTxSlope12K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    NoSt (WordToWord.fullCompileSingle b rc alg cAsm
      ((nm, ac, (LoopToWord.compHOL ctx prog loc).1), co)).2.2 = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordToWord.fullCompileSingle b rc alg cAsm
        ((nm, ac, (LoopToWord.compHOL ctx prog loc).1), co)).2.2 = 0 ∧
    NoSC (LoopToWord.compHOL ctx prog loc).1 = true ∧
    StackRemoveStoreConstsZeroBridge.storeConstsAllowance (LoopToWord.compHOL ctx prog loc).1 = 0 ∧
    runAllowance xs = 0 ∧
    D * (2 * W + 4 * R) ≤ 95_238_095_238 ∧
    (rs.map (fun r => 5 * (r * (r - 1)))).sum ≤ 4_194_300_000 ∧
    kPanTransition = 135_048_530_896 ∧
    kPanTransition - kPanCoupled = 4_194_300_000 ∧
    (k * kPanTransition < yukon ↔ k ≤ 6) ∧
    yukonScore transitionSlope3K minutes - yukonScore transitionSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore transitionSlope6K minutes - yukonScore transitionSlope6UnrolledK minutes = 138_000_000 ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedCleanToDirtyAndFullWordSynth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedCleanToDirtyAndFullWordSynth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hcert_u128 := exact_keccak_128_unrolled_certificate
    oracles c depth hlab compiled depthBound not_timeOut_u128
  have hchain := twenty_two_tier_certificate_monotonicity_chain_non_vacuous_and_tight
    (Nat.le_refl exactKeccak128UnrolledK) hcert_u128 hcert_u128
  have h22 := twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have htr := transition_slope3_and_slope6_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 minutes
  have hbu := block_unchanged D W R hDWR
  have hval := kPanTransition_val
  exact ⟨h22.1, h22.2.1, hchain.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    loopToWord_fullCompileSingle_NoSt ctx prog loc b rc alg cAsm nm ac co,
    loopToWord_fullCompileSingle_allowance_zero ctx prog loc b rc alg cAsm nm ac co,
    compHOL_NoSC ctx prog loc,
    StackRemoveStoreConstsZeroBridge.compiled_allowance_zero ctx prog loc,
    compiled_run_allowance_zero ctx prog loc xs origin,
    hbu.1,
    insert_le rs hrs hrsS,
    hval.1,
    hval.2,
    GuestSstoreCleanToDirtyTransition.slope_threshold k,
    htr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    htr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    by decide,
    by decide,
    rfl⟩

#print axioms word_to_word_full_compile_single_no_store_consts_non_vacuous_and_tight
#print axioms guest_sstore_clean_to_dirty_transition_and_slope_threshold_non_vacuous_and_tight
#print axioms transition_slope3_and_slope6_unrolled_and_baseline_tiers_non_vacuous_and_tight
#print axioms twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
#print axioms twenty_two_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
#print axioms twenty_two_tier_yukonScore_strict_order_and_float64_exact_non_vacuous_and_tight
#print axioms twenty_two_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
#print axioms transition_slope3_and_slope6_certificates_and_margins_non_vacuous_and_tight
#print axioms twenty_two_tier_certificate_monotonicity_chain_non_vacuous_and_tight
#print axioms master_twenty_two_tier_clean_to_dirty_and_full_word_campaign_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedCleanToDirtyAndFullWordSynth
