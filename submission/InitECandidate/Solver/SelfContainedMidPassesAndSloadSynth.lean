import InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
import InitECandidate.Solver.SelfContainedSloadProbeEnvelope
import InitECandidate.Solver.JointBlockGasSixPassMasterCert

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedMidPassesAndSloadSynth` — Wave 5 Atomic Worker `W5_61`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`WordMidPassesPreserveNoStoreConsts`**: The 6-pass `WordToWord` middle+tail chain
   `midTailChain c temp b p`:
   `instSelect → removeDeadProg → copyProp → threeToTwoRegProg → removeUnreach → removeMustTerminate`,
   proving `NoSt p = true → NoSt (midTailChain c temp b p) = true` and
   `storeConstsAllowance (midTailChain c temp b p) = 0` (and directly on `LoopToWord.compHOL`),
   which establishes `C_sr = C_sr_probe = 1` and `k_sr = k_sn + 1` (zero `storeConsts` allowance).
2. **`SelfContainedSloadProbeEnvelope`**: The `pEff = 4` SLOAD probe envelopes with `C_sr_probe = 1`
   and unrolled `memeq` (`avgProbeTargetFactor = 3`):
   - zero-pipeOffset cold/general probe envelopes:
     `coldSloadProbeZeroOffsetK = 610_978_715_738 < sloadProbeZeroOffsetK = 677_645_382_458 < 900_719_925_474`,
   - full `+ 5000` pipeOffset probe envelopes:
     `coldSloadProbeEnvelopeTargetK = 610_978_730_738 < sloadProbeEnvelopeTargetK = 677_645_397_458 < 900_719_925_474`.
3. **`JointBlockGasSixPassMasterCert`**: The 3 joint single-budget block-gas regimes
   (`kPanJoint 6 = 40_486_477_625 < maxGuestSourceClock = 43_914_839_586`):
   `121_459_456_007 < 242_918_888_882 < 485_837_754_632`,
   together with complete strict ordering, Yukon `float64` score bounds, and `InitE.Certificate`
   theorems (`0 sorryAx`, 10 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.SelfContainedMidPassesAndSloadSynth

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedEndToEndCert
open InitECandidate.Solver.SelfContainedSixPassMaster (sixPassSlope six_pass_slope_reduction reduced_baseline_compatible)
open InitECandidate.Solver.SelfContainedSolutionCandidates
open InitECandidate.Solver.PurifiedImportGraphCert
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
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitECandidate.Solver.YukonEightTierMasterPortfolio
open InitECandidate.Solver.JointBlockGasSixPassMasterCert
open Flapjack
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target

/-! ## Section 1: 6-Pass `WordToWord` Chain & SLOAD Probe Envelope Definitions -/

/-- The 6-pass `WordToWord` middle+tail compilation pipeline from `WordMidPassesPreserveNoStoreConsts`:
`instSelect → removeDeadProg → copyProp → threeToTwoRegProg → removeUnreach → removeMustTerminate`. -/
noncomputable def midTailChain {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat)
    (b : Bool) (p : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  WordRemove.removeMustTerminate (WordUnreach.removeUnreach
    (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordAlloc.removeDeadProg
      (WordInst.instSelect c temp p)))))

/-- Pure cold-`SLOAD` target step budget at `avgProbeTargetFactor = 3` before `pipeOffset`:
`23_132 + 3 * maxColdSloadTotalClock = 610_978_715_738`. -/
def coldSloadProbeZeroOffsetK : Nat :=
  23_132 + 3 * maxColdSloadTotalClock

/-- General access-list `SLOAD` target step budget at `avgProbeTargetFactor = 3` before `pipeOffset`:
`23_132 + 3 * maxTotalClock = 677_645_382_458`. -/
def sloadProbeZeroOffsetK : Nat :=
  23_132 + 3 * maxTotalClock

/-- `StackRemove` clock transition under `NoSt` (`C_sr = 1`, `D_sr = 1`, zero `storeConstsAllowance`):
`k_sr = k_sn + 1 + storeConstsAllowance p`. -/
def stackRemoveClockWithAllowance {α : Type} (k_sn : Nat) (p : WordLangProgHOL α) : Nat :=
  k_sn + 1 + storeConstsAllowance p

/-! ## Section 2: Ten `non_vacuous_and_tight` Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Any `WordLangProgHOL` program `p` with `NoSt p = true`
traversing the 6-pass `WordToWord` chain `midTailChain c temp b p` preserves `NoSt = true` and
`storeConstsAllowance = 0`, so `stackRemoveClockWithAllowance k_sn (midTailChain c temp b p) = k_sn + 1`
(`C_sr = C_sr_probe = 1`), whereas `instSelect` preserves a `.storeConsts` node (`NoSt = false`
and positive allowance on non-empty payloads). -/
theorem mid_tail_chain_preserves_noSt_and_zero_allowance_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (hp : NoSt p = true) (k_sn : Nat)
    (ws : List (Bool × BitVec width)) :
    NoSt (midTailChain c temp b p) = true ∧
    storeConstsAllowance (midTailChain c temp b p) = 0 ∧
    stackRemoveClockWithAllowance k_sn (midTailChain c temp b p) = k_sn + 1 ∧
    C_sr_probe = 1 ∧
    NoSt (WordInst.instSelect c temp
      (WordLangProgHOL.storeConsts (α := BitVec width) 0 2 4 6 [])) = false ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have hnost : NoSt (midTailChain c temp b p) = true := by
    unfold midTailChain
    exact t_mid_tail_chain c temp b p hp
  have hzero : storeConstsAllowance (midTailChain c temp b p) = 0 :=
    noSt_allowance_zero _ hnost
  have hsr : stackRemoveClockWithAllowance k_sn (midTailChain c temp b p) = k_sn + 1 := by
    unfold stackRemoveClockWithAllowance
    rw [hzero, Nat.add_zero]
  have hkeep := instSelect_keeps_storeConsts c temp
  have htight := StackRemoveStoreConstsZeroBridge.allowance_storeConsts_tight 0 2 4 6 ws
  refine ⟨hnost, hzero, hsr, rfl, hkeep, ?_⟩
  rw [htight, List.length_eq_zero_iff]

/-- Theorem 2 (`non_vacuous_and_tight`): Composing `LoopToWord.compHOL` with the 6-pass `WordToWord`
chain `midTailChain c temp b` guarantees `NoSt = true`, `storeConstsAllowance = 0`, and
`k_sr = k_sn + 1`, formally justifying `C_sr_probe = 1` (`avgProbeTargetFactor = 3`) in
`SelfContainedSloadProbeEnvelope` and the `3x` / `6x` / `12x` slopes in
`JointBlockGasSixPassMasterCert`. -/
theorem loop_to_word_mid_tail_chain_justifies_probe_and_six_pass_slopes_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) (b : Bool)
    (ctx : Spt Nat) (lp : HolLoopProg width) (labels : Nat × Nat) (k_sn : Nat)
    (findSlots insSlots : Nat) :
    NoSt (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) = true ∧
    storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) = 0 ∧
    stackRemoveClockWithAllowance k_sn
      (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) = k_sn + 1 ∧
    C_sr_probe = 1 ∧
    fourPassSlopeProduct = 1 ∧
    avgProbeTargetFactor = 3 ∧
    sixPassSlope C_sr_probe 3 = 3 ∧
    sixPassSlope C_sr_probe 6 = 6 ∧
    sixPassSlope 2 6 = 12 ∧
    ((C_cl_loop + C_cl_memeq) * findSlots + C_cl_loop * (pIns * insSlots) =
      avgProbeTargetFactor * (pFind * findSlots + pIns * insSlots) ↔ findSlots = 0) := by
  have hlp : NoSt (LoopToWord.compHOL ctx lp labels).1 = true :=
    loopToWord_NoSt ctx lp labels
  have hmid := mid_tail_chain_preserves_noSt_and_zero_allowance_non_vacuous_and_tight
    c temp b (LoopToWord.compHOL ctx lp labels).1 hlp k_sn []
  have hprobe := unrolled_memeq_half_ticks_average_factor_le_three_non_vacuous_and_tight
    findSlots insSlots
  exact ⟨hmid.1, hmid.2.1, hmid.2.2.1, rfl, rfl, rfl,
    slope3_reduction, slope6_reduction, slope12_reduction, hprobe.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 3 (`non_vacuous_and_tight`): Exact evaluation and ordering of the `SelfContainedSloadProbeEnvelope`
regimes (`610_978_715_738 < 610_978_730_738 < 677_645_382_458 < 677_645_397_458 < 680_000_000_000 < 900_719_925_474`),
with zero `storeConstsAllowance` drift across `midTailChain` and sharp integer multiplier bound `M ≤ 3`. -/
theorem sload_probe_envelope_exact_bounds_with_mid_passes_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) (b : Bool)
    (ctx : Spt Nat) (lp : HolLoopProg width) (labels : Nat × Nat) (M : Nat) :
    coldSloadProbeZeroOffsetK = 610_978_715_738 ∧
    coldSloadProbeEnvelopeTargetK = 610_978_730_738 ∧
    sloadProbeZeroOffsetK = 677_645_382_458 ∧
    sloadProbeEnvelopeTargetK = 677_645_397_458 ∧
    coldSloadProbeZeroOffsetK < sloadProbeZeroOffsetK ∧
    sloadProbeZeroOffsetK < SelfContainedQuadraticEnvelopeCert.yukonFloat64StepCeiling ∧
    coldSloadProbeZeroOffsetK < coldSloadProbeEnvelopeTargetK ∧
    coldSloadProbeEnvelopeTargetK < sloadProbeZeroOffsetK ∧
    sloadProbeZeroOffsetK < sloadProbeEnvelopeTargetK ∧
    sloadProbeEnvelopeTargetK < 680_000_000_000 ∧
    680_000_000_000 < SelfContainedQuadraticEnvelopeCert.yukonFloat64StepCeiling ∧
    sloadProbeEnvelopeTargetK +
      storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) =
        677_645_397_458 ∧
    coldSloadProbeZeroOffsetK +
      storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) =
        610_978_715_738 ∧
    sloadProbeZeroOffsetK +
      storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) =
        677_645_382_458 ∧
    (bootstrapSteps + M * (maxTotalClock + pipeOffset) <
      SelfContainedQuadraticEnvelopeCert.yukonFloat64StepCeiling ↔ M ≤ 3) := by
  have hzero : storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) = 0 :=
    (loop_to_word_mid_tail_chain_justifies_probe_and_six_pass_slopes_non_vacuous_and_tight
      c temp b ctx lp labels 0 0 0).2.1
  have hm := (sload_probe_multiplier_threshold_non_vacuous_and_tight M).2
  have hsload : sloadProbeEnvelopeTargetK = 677_645_397_458 :=
    (sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.1
  have hcold : coldSloadProbeEnvelopeTargetK = 610_978_730_738 :=
    (sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.2.2.2.2.2.2.1
  have hcz : coldSloadProbeZeroOffsetK = 610_978_715_738 := by
    unfold coldSloadProbeZeroOffsetK maxColdSloadTotalClock maxColdSloadProbeTicks
      SelfContainedMasterK.prologueTicks GuestEvmStepOpcodeBounds.gasCap
    decide
  have hsz : sloadProbeZeroOffsetK = 677_645_382_458 := by
    unfold sloadProbeZeroOffsetK maxTotalClock
    decide
  rw [hzero, Nat.add_zero, Nat.add_zero, Nat.add_zero, hsload, hcold, hcz, hsz]
  unfold SelfContainedQuadraticEnvelopeCert.yukonFloat64StepCeiling
  exact ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, rfl, rfl, rfl, hm⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Joint block-gas 3-regime bounds (`121_459_456_007 < 242_918_888_882 < 485_837_754_632`)
preserved with zero `storeConstsAllowance` across the 6-pass `midTailChain` (extending the 3-pass `tail`
of `WordToWordTailNoStoreConstsBridge` with `instSelect`, `removeDeadProg`, and `copyProp`). -/
theorem joint_block_gas_three_regimes_with_mid_tail_chain_non_vacuous_and_tight
    {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) (b : Bool)
    (ctx : Spt Nat) (lp : HolLoopProg width) (labels : Nat × Nat) (m : Nat) :
    jointBlockGasSlope3K = 121_459_456_007 ∧
    jointBlockGasSlope6K = 242_918_888_882 ∧
    jointBlockGasSlope12K = 485_837_754_632 ∧
    jointBlockGasSlope3K < jointBlockGasSlope6K ∧
    jointBlockGasSlope6K < jointBlockGasSlope12K ∧
    jointBlockGasSlope12K < coldSloadProbeZeroOffsetK ∧
    NoSt (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) = true ∧
    storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) = 0 ∧
    jointBlockGasSlope3K +
      storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) =
        121_459_456_007 ∧
    jointBlockGasSlope6K +
      storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) =
        242_918_888_882 ∧
    jointBlockGasSlope12K +
      storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) =
        485_837_754_632 ∧
    (m * jointBlockGasSlope3K < yukon ↔ m ≤ 7) := by
  have hmid := loop_to_word_mid_tail_chain_justifies_probe_and_six_pass_slopes_non_vacuous_and_tight
    c temp b ctx lp labels 0 0 0
  have hnost : NoSt (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) = true := hmid.1
  have hzero : storeConstsAllowance (midTailChain c temp b (LoopToWord.compHOL ctx lp labels).1) = 0 :=
    hmid.2.1
  have hj := joint_block_gas_three_regimes_exact_and_yukon_margins_non_vacuous_and_tight m
  have hcz : coldSloadProbeZeroOffsetK = 610_978_715_738 :=
    (sload_probe_envelope_exact_bounds_with_mid_passes_non_vacuous_and_tight c temp b ctx lp labels 0).1
  rw [hzero, Nat.add_zero, Nat.add_zero, Nat.add_zero, hcz]
  exact ⟨rfl, rfl, rfl, by decide, by decide, by decide,
    hnost, rfl, rfl, rfl, rfl, hj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 5 (`non_vacuous_and_tight`): Complete 12-point strict ordering uniting the portfolio,
the 3 joint block-gas regimes (`121_459_456_007 < 242_918_888_882 < 485_837_754_632`), the
4 SLOAD probe envelope regimes (`610_978_715_738 < 610_978_730_738 < 677_645_382_458 < 677_645_397_458`),
`quadraticCollisionTargetK = 857_678_983_380`, and the Yukon ceiling `900_719_925_474`. -/
theorem complete_twelve_regime_strict_ordering_and_gaps_non_vacuous_and_tight (K : Nat) :
    sixPassReducedK = 11_029_683_788 ∧
    isoReducedCandidateK = 22_059_344_444 ∧
    jointBlockGasSlope3K = 121_459_456_007 ∧
    perTxSixPassTargetK = 122_620_608_536 ∧
    jointBlockGasSlope6K = 242_918_888_882 ∧
    jointBlockGasSlope12K = 485_837_754_632 ∧
    coldSloadProbeZeroOffsetK = 610_978_715_738 ∧
    coldSloadProbeEnvelopeTargetK = 610_978_730_738 ∧
    sloadProbeZeroOffsetK = 677_645_382_458 ∧
    sloadProbeEnvelopeTargetK = 677_645_397_458 ∧
    quadraticCollisionTargetK = 857_678_983_380 ∧
    yukon = 900_719_925_474 ∧
    sixPassReducedK < isoReducedCandidateK ∧
    isoReducedCandidateK < jointBlockGasSlope3K ∧
    jointBlockGasSlope3K < perTxSixPassTargetK ∧
    perTxSixPassTargetK < jointBlockGasSlope6K ∧
    jointBlockGasSlope6K < jointBlockGasSlope12K ∧
    jointBlockGasSlope12K < coldSloadProbeZeroOffsetK ∧
    coldSloadProbeZeroOffsetK < coldSloadProbeEnvelopeTargetK ∧
    coldSloadProbeEnvelopeTargetK < sloadProbeZeroOffsetK ∧
    sloadProbeZeroOffsetK < sloadProbeEnvelopeTargetK ∧
    sloadProbeEnvelopeTargetK < quadraticCollisionTargetK ∧
    quadraticCollisionTargetK < yukon ∧
    coldSloadProbeZeroOffsetK - jointBlockGasSlope12K = 125_140_961_106 ∧
    sloadProbeZeroOffsetK - coldSloadProbeZeroOffsetK = 66_666_666_720 ∧
    yukon - sloadProbeEnvelopeTargetK = 223_074_528_016 ∧
    (sloadProbeEnvelopeTargetK ≤ K ↔ 677_645_397_458 ≤ K) := by
  have hord := eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hred : sixPassReducedK = 11_029_683_788 := hord.2.1
  have hiso : isoReducedCandidateK = 22_059_344_444 := hord.2.2.2.1
  have hptx : perTxSixPassTargetK = 122_620_608_536 := hord.2.2.2.2.2.1
  have hsload := sload_probe_envelope_target_k_non_vacuous_and_tight K
  have hse : sloadProbeEnvelopeTargetK = 677_645_397_458 := hsload.2.1
  have hce : coldSloadProbeEnvelopeTargetK = 610_978_730_738 := hsload.2.2.2.2.2.2.2.1
  have hcz : coldSloadProbeZeroOffsetK = 610_978_715_738 := by
    unfold coldSloadProbeZeroOffsetK maxColdSloadTotalClock maxColdSloadProbeTicks
      SelfContainedMasterK.prologueTicks GuestEvmStepOpcodeBounds.gasCap
    decide
  have hsz : sloadProbeZeroOffsetK = 677_645_382_458 := by
    unfold sloadProbeZeroOffsetK maxTotalClock
    decide
  have hquad : quadraticCollisionTargetK = 857_678_983_380 := rfl
  rw [hred, hiso, hptx, hse, hce, hcz, hsz, hquad]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  omega

/-- Theorem 6 (`non_vacuous_and_tight`): Strict `yukonScore` hierarchy and IEEE-754 `float64`
exactness (`< 2^53 - 1`) across the joint block-gas regimes and SLOAD probe envelopes. -/
theorem mid_passes_joint_and_sload_yukon_score_ordering_non_vacuous_and_tight
    (minutes K : Nat) :
    yukonScore jointBlockGasSlope3K minutes < yukonScore jointBlockGasSlope6K minutes ∧
    yukonScore jointBlockGasSlope6K minutes < yukonScore jointBlockGasSlope12K minutes ∧
    yukonScore jointBlockGasSlope12K minutes < yukonScore coldSloadProbeZeroOffsetK minutes ∧
    yukonScore coldSloadProbeZeroOffsetK minutes < yukonScore coldSloadProbeEnvelopeTargetK minutes ∧
    yukonScore coldSloadProbeEnvelopeTargetK minutes < yukonScore sloadProbeZeroOffsetK minutes ∧
    yukonScore sloadProbeZeroOffsetK minutes < yukonScore sloadProbeEnvelopeTargetK minutes ∧
    yukonScore sloadProbeEnvelopeTargetK minutes < 2 ^ 53 - 1 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hm : min minutes 9999 ≤ 9999 := Nat.min_le_right _ _
  have hm9999 : min 9999 9999 = 9999 := rfl
  have hord := complete_twelve_regime_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hcz : coldSloadProbeZeroOffsetK = 610_978_715_738 := hord.2.2.2.2.2.2.1
  have hce : coldSloadProbeEnvelopeTargetK = 610_978_730_738 := hord.2.2.2.2.2.2.2.1
  have hsz : sloadProbeZeroOffsetK = 677_645_382_458 := hord.2.2.2.2.2.2.2.2.1
  have hse : sloadProbeEnvelopeTargetK = 677_645_397_458 := hord.2.2.2.2.2.2.2.2.2.1
  rw [hcz, hce, hsz, hse]
  unfold yukonScore jointBlockGasSlope3K jointBlockGasSlope6K jointBlockGasSlope12K
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  rw [hm9999]
  omega

/-- Theorem 7 (`non_vacuous_and_tight`): Source-clock synthesis comparing the joint single-budget
clock `kPanJoint 6 = 40_486_477_625 < maxGuestSourceClock = 43_914_839_586` against the pure cold
SLOAD clock `maxColdSloadTotalClock = 203_659_564_202` and general access-list clock
`maxTotalClock = 225_881_786_442`, showing a `> 5x` source-clock reduction from the joint
EIP-7825 block-gas invariant. -/
theorem source_clock_joint_vs_sload_probe_reduction_non_vacuous_and_tight (p : Nat) :
    kPanJoint 6 = 40_486_477_625 ∧
    maxGuestSourceClock = 43_914_839_586 ∧
    maxColdSloadTotalClock = 203_659_564_202 ∧
    maxTotalClock = 225_881_786_442 ∧
    kPanJoint 6 < maxGuestSourceClock ∧
    maxGuestSourceClock < maxColdSloadTotalClock ∧
    maxColdSloadTotalClock < maxTotalClock ∧
    5 * kPanJoint 6 < maxColdSloadTotalClock ∧
    5 * maxGuestSourceClock < maxTotalClock ∧
    maxColdSloadTotalClock - kPanJoint 6 = 163_173_086_577 ∧
    maxTotalClock - kPanJoint 6 = 185_395_308_817 ∧
    (kPanJoint p ≤ maxGuestSourceClock ↔ p ≤ 6) := by
  have hkpan : kPanJoint 6 = 40_486_477_625 := kPanJoint_val
  have hcold : maxColdSloadTotalClock = 203_659_564_202 :=
    (exact_probe_ticks_and_cold_clock_non_vacuous_and_tight 0 0).2.2.2.1
  have htot : maxTotalClock = 225_881_786_442 := rfl
  have hmax : maxGuestSourceClock = 43_914_839_586 := rfl
  have hthresh := kPanJoint_threshold p
  rw [hkpan, hcold, htot, hmax]
  exact ⟨rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, hthresh⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Finite `InitE.Certificate` at `jointBlockGasSlope3K = 121_459_456_007`
paired with the 6-pass `midTailChain` `NoSt` and `storeConstsAllowance = 0` invariant, upward
transfer to all higher joint block-gas and SLOAD probe envelope regimes (`jointBlockGasSlope6K`,
`jointBlockGasSlope12K`, `coldSloadProbeZeroOffsetK`, `coldSloadProbeEnvelopeTargetK`,
`sloadProbeZeroOffsetK`, `sloadProbeEnvelopeTargetK`), and sharp 1-tick tightness. -/
theorem joint_slope3_mid_tail_and_sload_envelope_certificate_non_vacuous_and_tight
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
        jointBlockGasSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = true ∧
    storeConstsAllowance (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K) (.finite jointBlockGasSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    InitE.Certificate (baselineWithFiniteK coldSloadProbeZeroOffsetK)
      (.finite coldSloadProbeZeroOffsetK) ∧
    InitE.Certificate (baselineWithFiniteK coldSloadProbeEnvelopeTargetK)
      (.finite coldSloadProbeEnvelopeTargetK) ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeZeroOffsetK)
      (.finite sloadProbeZeroOffsetK) ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeEnvelopeTargetK)
      (.finite sloadProbeEnvelopeTargetK) ∧
    ¬ (bootstrapSteps + jointBlockGasSlope3PostK ≤ jointBlockGasSlope3K - 1) := by
  have hmono : ∀ {A B : Nat}, A ≤ B →
      InitE.Certificate (baselineWithFiniteK A) (.finite A) →
      InitE.Certificate (baselineWithFiniteK B) (.finite B) := by
    intro A B hab hA
    refine ⟨rfl, baselineWithFiniteK_admitted B, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hA.correct input hgas outcome events hsrc hcov
    have hm_base : matchingExecutionAt InitE.baselineSubmission input outcome events steps :=
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite A)
        input outcome events steps).mp hm
    exact ⟨steps, Nat.le_trans hsteps hab,
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite B)
        input outcome events steps).mpr hm_base⟩
  have hmid := loop_to_word_mid_tail_chain_justifies_probe_and_six_pass_slopes_non_vacuous_and_tight
    asmConf temp b ctx lp labels 0 0 0
  have hj3 := joint_block_gas_slope3_tail_certificate_non_vacuous_and_tight
    ctx lp labels b oracles c depth hlab compiled depthBound not_timeOut
  have hcert3 := hj3.2.2.1
  have hord := complete_twelve_regime_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hcz : coldSloadProbeZeroOffsetK = 610_978_715_738 := hord.2.2.2.2.2.2.1
  have hce : coldSloadProbeEnvelopeTargetK = 610_978_730_738 := hord.2.2.2.2.2.2.2.1
  have hsz : sloadProbeZeroOffsetK = 677_645_382_458 := hord.2.2.2.2.2.2.2.2.1
  have hse : sloadProbeEnvelopeTargetK = 677_645_397_458 := hord.2.2.2.2.2.2.2.2.2.1
  exact ⟨hmid.1, hmid.2.1, hcert3, hj3.2.2.2.2.1, hj3.2.2.2.2.2.1,
    hmono (by rw [hcz]; decide) hcert3,
    hmono (by rw [hce]; decide) hcert3,
    hmono (by rw [hsz]; decide) hcert3,
    hmono (by rw [hse]; decide) hcert3,
    hj3.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`): Direct `InitE.Certificate` at `sloadProbeEnvelopeTargetK = 677_645_397_458`
paired with the 6-pass `midTailChain` `NoSt` and `storeConstsAllowance = 0` invariant, baseline
`.infinity` compatibility, and sharp 1-tick tightness. -/
theorem sload_probe_envelope_mid_tail_certificate_non_vacuous_and_tight
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
        sloadProbeEnvelopeTargetK (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = true ∧
    storeConstsAllowance (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeEnvelopeTargetK)
      (.finite sloadProbeEnvelopeTargetK) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    sloadProbeEnvelopeTargetK < 680_000_000_000 ∧
    sloadProbeEnvelopeTargetK < 900_719_925_474 ∧
    ¬ (bootstrapSteps + sloadProbeEnvelopePostK ≤ sloadProbeEnvelopeTargetK - 1) := by
  have hmid := loop_to_word_mid_tail_chain_justifies_probe_and_six_pass_slopes_non_vacuous_and_tight
    asmConf temp b ctx lp labels 0 0 0
  have hcert := self_contained_sload_probe_envelope_certificate
    oracles c depth hlab compiled depthBound not_timeOut
  have hcompat := sload_probe_envelope_finite_and_baseline_compatible hcert.1
  have htight : ¬ (bootstrapSteps + sloadProbeEnvelopePostK ≤ sloadProbeEnvelopeTargetK - 1) := by
    have h1 : sloadProbeEnvelopePostK = 677_645_374_326 :=
      (sload_probe_envelope_target_k_non_vacuous_and_tight 0).1
    have h2 : sloadProbeEnvelopeTargetK = 677_645_397_458 :=
      (sload_probe_envelope_target_k_non_vacuous_and_tight 0).2.1
    rw [InitE.bootstrapSteps_eq, h1, h2]
    decide
  exact ⟨hmid.1, hmid.2.1, hcert.1, hcompat.2.1, hcert.2.1, hcert.2.2.1, htight⟩

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 synthesis theorem uniting
`WordMidPassesPreserveNoStoreConsts` (`midTailChain`), `SelfContainedSloadProbeEnvelope`, and
`JointBlockGasSixPassMasterCert`: under uniform target non-`.timeOut` at `sixPassReducedK = 11_029_683_788`,
every finite certificate across the joint block-gas and SLOAD probe hierarchy holds simultaneously
with `NoSt = true`, `storeConstsAllowance = 0`, `C_sr_probe = 1`, `k_sr = k_sn + 1`, and
`zeroBoundedImportCount = 0`. -/
theorem end_to_end_mid_passes_sload_and_joint_block_gas_master_synth_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (temp : Nat) (b : Bool)
    (ctx : Spt Nat) (lp : HolLoopProg width) (labels : Nat × Nat)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes k_sn : Nat)
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
    NoSt (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = true ∧
    storeConstsAllowance (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = 0 ∧
    stackRemoveClockWithAllowance k_sn
      (midTailChain asmConf temp b (LoopToWord.compHOL ctx lp labels).1) = k_sn + 1 ∧
    C_sr_probe = 1 ∧
    kPanJoint 6 < maxGuestSourceClock ∧
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    InitE.Certificate (baselineWithFiniteK isoReducedCandidateK) (.finite isoReducedCandidateK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K) (.finite jointBlockGasSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    InitE.Certificate (baselineWithFiniteK coldSloadProbeZeroOffsetK)
      (.finite coldSloadProbeZeroOffsetK) ∧
    InitE.Certificate (baselineWithFiniteK coldSloadProbeEnvelopeTargetK)
      (.finite coldSloadProbeEnvelopeTargetK) ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeZeroOffsetK)
      (.finite sloadProbeZeroOffsetK) ∧
    InitE.Certificate (baselineWithFiniteK sloadProbeEnvelopeTargetK)
      (.finite sloadProbeEnvelopeTargetK) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    yukonScore sloadProbeEnvelopeTargetK minutes < 2 ^ 53 - 1 ∧
    zeroBoundedImportCount = 0 ∧
    ¬ (bootstrapSteps + jointBlockGasSlope3PostK ≤ jointBlockGasSlope3K - 1) := by
  have hmid := loop_to_word_mid_tail_chain_justifies_probe_and_six_pass_slopes_non_vacuous_and_tight
    asmConf temp b ctx lp labels k_sn 0 0
  have hjoint := end_to_end_joint_block_gas_six_pass_master_certificate_non_vacuous_and_tight
    ctx lp labels b oracles c depth minutes hlab compiled depthBound not_timeOut_sixPassReduced
  have hmono : ∀ {A B : Nat}, A ≤ B →
      InitE.Certificate (baselineWithFiniteK A) (.finite A) →
      InitE.Certificate (baselineWithFiniteK B) (.finite B) := by
    intro A B hab hA
    refine ⟨rfl, baselineWithFiniteK_admitted B, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hA.correct input hgas outcome events hsrc hcov
    have hm_base : matchingExecutionAt InitE.baselineSubmission input outcome events steps :=
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite A)
        input outcome events steps).mp hm
    exact ⟨steps, Nat.le_trans hsteps hab,
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite B)
        input outcome events steps).mpr hm_base⟩
  have hcert_j3 := hjoint.2.2.2.2.2.1
  have hord := complete_twelve_regime_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hcz : coldSloadProbeZeroOffsetK = 610_978_715_738 := hord.2.2.2.2.2.2.1
  have hce : coldSloadProbeEnvelopeTargetK = 610_978_730_738 := hord.2.2.2.2.2.2.2.1
  have hsz : sloadProbeZeroOffsetK = 677_645_382_458 := hord.2.2.2.2.2.2.2.2.1
  have hse : sloadProbeEnvelopeTargetK = 677_645_397_458 := hord.2.2.2.2.2.2.2.2.2.1
  have hscore := (sload_probe_envelope_yukon_score_non_vacuous_and_tight minutes).1
  have htight : ¬ (bootstrapSteps + jointBlockGasSlope3PostK ≤ jointBlockGasSlope3K - 1) := by
    rw [InitE.bootstrapSteps_eq]; decide
  exact ⟨hmid.1, hmid.2.1, hmid.2.2.1, rfl, hjoint.1,
    hjoint.2.2.2.1, hjoint.2.2.2.2.1, hcert_j3, hjoint.2.2.2.2.2.2.1,
    hjoint.2.2.2.2.2.2.2.1, hjoint.2.2.2.2.2.2.2.2.1,
    hmono (by rw [hcz]; decide) hcert_j3,
    hmono (by rw [hce]; decide) hcert_j3,
    hmono (by rw [hsz]; decide) hcert_j3,
    hmono (by rw [hse]; decide) hcert_j3,
    hjoint.2.2.2.2.2.2.2.2.2.1, hscore, rfl, htight⟩

#print axioms mid_tail_chain_preserves_noSt_and_zero_allowance_non_vacuous_and_tight
#print axioms loop_to_word_mid_tail_chain_justifies_probe_and_six_pass_slopes_non_vacuous_and_tight
#print axioms sload_probe_envelope_exact_bounds_with_mid_passes_non_vacuous_and_tight
#print axioms joint_block_gas_three_regimes_with_mid_tail_chain_non_vacuous_and_tight
#print axioms complete_twelve_regime_strict_ordering_and_gaps_non_vacuous_and_tight
#print axioms mid_passes_joint_and_sload_yukon_score_ordering_non_vacuous_and_tight
#print axioms source_clock_joint_vs_sload_probe_reduction_non_vacuous_and_tight
#print axioms joint_slope3_mid_tail_and_sload_envelope_certificate_non_vacuous_and_tight
#print axioms sload_probe_envelope_mid_tail_certificate_non_vacuous_and_tight
#print axioms end_to_end_mid_passes_sload_and_joint_block_gas_master_synth_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedMidPassesAndSloadSynth
