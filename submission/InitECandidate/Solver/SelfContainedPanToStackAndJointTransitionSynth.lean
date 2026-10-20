import InitECandidate.Solver.PanToStackNoStoreConsts
import InitECandidate.Solver.GuestJointTransitionInsertionBound
import InitECandidate.Solver.SelfContainedCleanToDirtyAndFullWordSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SelfContainedPanToStackAndJointTransitionSynth` — Self-Contained End-to-End `PanToStackNoStoreConsts` (`PanToCrep → CrepToLoop → LoopToWord → WordToWord → WordToStack → StackAlloc`) & Joint Clean→Dirty Transition Absorption Synthesis (`W5_79`)

This module has **0 imports from `InitECandidate.Proofs.Bounded*`** in its transitive closure and
unifies:
1. The complete end-to-end `panToStackAlloc_NoSt` chain from `PanToStackNoStoreConsts` (`28/28` tight:
   `loopToWordCompFunc_NoSt`, `loopToWordCompile_NoSt`, `panToWord_NoSt`, `wordToWordCompile_NoSt`,
   `panToWordToWord_NoSt`, `StackNoSt`, `s_compNative`, `s_compileProgNative`, `s_compileWordToStack`,
   `s_compileNative_bodies`, `storeConstsStub_not_StackNoSt`, `s_stackAllocComp`, `s_progComp`,
   `panToStackAlloc_NoSt`).
2. The joint clean→dirty `SSTORE` transition insertion absorption from `GuestJointTransitionInsertionBound`
   (`11/11` tight: `kIns = 41_935`, `insert_linear`, `insert_linear_tight`, `insert_sum`,
   `joint_transition_absorbed`, `joint_le`, `joint_tight`, `pure_transition_corner`,
   `kPan_with_transitions`, `improves_transition`, `margin6`, `slope_threshold`), proving that the
   `4_194_300_000` transition insertion ticks are completely absorbed into the block storage envelope
   `⌊S² / 42⌋ = 95_238_095_238`, reducing the worst-case source clock with transitions from
   `kPanTransition = 135_048_530_896` back down to `kPanCoupled = 130_854_230_896`.
3. The exact collapse of the `kPanTransition` target tiers (`transitionSlope3UnrolledK`,
   `transitionSlope3K`, `transitionSlope6UnrolledK`, `transitionSlope6K`) back to the `kPanCoupled`
   target tiers (`coupledSlope3UnrolledK`, `coupledSlope3K`, `coupledSlope6UnrolledK`,
   `coupledSlope6K`), saving `4_194_300_000` source ticks, `12_582_900_000` target steps at `3x`
   slope, and `25_165_800_000` target steps at `6x` slope (`yukonScore` gain of `125_829_000_000_000`
   at `3x` and `251_658_000_000_000` at `6x`).
4. The certified 22-tier candidate hierarchy (`twentyTwoTierHierarchy`) from
   `SelfContainedCleanToDirtyAndFullWordSynth`, `claim.json ≤ 128`-byte compliance, `yukonScore`
   monotonicity, and `InitE.Certificate` theorems (`0 sorryAx`).
-/

namespace InitECandidate.Solver.SelfContainedPanToStackAndJointTransitionSynth

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
open InitECandidate.Solver.GuestJointTransitionInsertionBound
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
open Flapjack.Compiler.Backend.StackLang

/-! ## Section 1: Exact Absorption Gains Between `kPanTransition` and `kPanCoupled` Tiers -/

/-- Exact source-tick gain from joint clean→dirty transition absorption:
`kPanTransition - kPanCoupled = 135_048_530_896 - 130_854_230_896 = 4_194_300_000`. -/
def jointTransitionSourceGain : Nat := kPanTransition - kPanCoupled

/-- Exact target-step gain at `3x` slope from joint clean→dirty transition absorption:
`3 * 4_194_300_000 = 12_582_900_000`. -/
def jointTransitionSlope3Gain : Nat := 3 * jointTransitionSourceGain

/-- Exact target-step gain at `6x` slope from joint clean→dirty transition absorption:
`6 * 4_194_300_000 = 25_165_800_000`. -/
def jointTransitionSlope6Gain : Nat := 6 * jointTransitionSourceGain

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`, **End-to-End `PanToStackNoStoreConsts` Chain (`PanToCrep → CrepToLoop → LoopToWord → WordToWord → WordToStack → StackAlloc`)**):
Unites `panToWord_NoSt`, `panToWordToWord_NoSt`, `s_compNative`, `s_compileProgNative`,
`s_compileWordToStack`, `s_compileNative_bodies`, `storeConstsStub_not_StackNoSt`,
`s_stackAllocComp`, `s_progComp`, and `panToStackAlloc_NoSt` from `PanToStackNoStoreConsts`:
every function emitted by `panToWordCompileProgHOL arch prog` satisfies `NoSt = true`, preserves
`NoSt = true` through `WordToWord.compile wc ac`, compiles under `WordToStack.compileNative ac perf`
to `StackNoSt = true` on every function body except the single prepended stub at
`storeConstsStubLocation` (for which `StackNoSt (storeConstsStubNative k) = false`), and preserves
`StackNoSt = true` through `StackAlloc.progComp`. -/
theorem pan_to_stack_alloc_end_to_end_no_store_consts_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (name : Nat) (params : List Nat) (body : HolLoopProg width)
    (pWord : WordLangProgHOL (BitVec width)) (argCount regCount k n m : Nat)
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat)
    (pStack : HolProg width)
    (hpWord : NoSt pWord = true)
    (hpStack : StackNoSt pStack = true) :
    NoSt (loopToWordCompFuncHOL name params body) = true ∧
    (∀ x ∈ panToWordCompileProgHOL arch prog, NoSt x.2.2 = true) ∧
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2, NoSt y.2.2 = true) ∧
    StackNoSt (compNative ac perf pWord bs kf).1 = true ∧
    StackNoSt (compileProgNative ac perf pWord argCount regCount bs).1 = true ∧
    StackNoSt (StackAlloc.comp n m pStack).1 = true ∧
    StackNoSt (StackAlloc.progComp (name, pStack)).2 = true ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoSt y.2 = true) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoSt (StackAlloc.progComp y).2 = true) ∧
    StackNoSt (storeConstsStubNative (width := width) k) = false ∧
    StackNoSt (.storeConsts 0 1 none : HolProg width) = false := by
  exact ⟨loopToWordCompFunc_NoSt name params body,
    panToWord_NoSt arch prog,
    panToWordToWord_NoSt arch prog wc ac,
    s_compNative ac perf pWord bs kf hpWord,
    s_compileProgNative ac perf pWord argCount regCount bs hpWord,
    s_stackAllocComp n m pStack hpStack,
    s_progComp (name, pStack) hpStack,
    s_compileNative_bodies ac perf _ (panToWordToWord_NoSt arch prog wc ac),
    panToStackAlloc_NoSt arch prog wc ac perf,
    storeConstsStub_not_StackNoSt k,
    rfl⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **Joint Clean→Dirty Transition Insertion Absorption into `kPanCoupled = 130_854_230_896`**):
Unites all 11 theorems of `GuestJointTransitionInsertionBound`:
- `kIns = 41_935` and `20 * r ≤ M → 5 * (r * (r - 1)) ≤ kIns * r` (tight at `r = 8_388`),
- `(rs.map (fun r => 5 * (r * (r - 1)))).sum ≤ kIns * rs.sum`,
- `42 * (D * (2 * W + 4 * R) + kIns * R) ≤ S * S` and `D * (2 * W + 4 * R) + kIns * R ≤ 95_238_095_238`
  under `21 * D + W + 20 * R ≤ S` (attained at `(D, W, R) = (47_619, 1_000_001, 0)`, with pure-transition
  corner `4_193_500_000` at `(0, 0, 100_000)`),
- `linear + Tloc + (D * (2 * W + 4 * R) + kIns * R) ≤ kPanCoupled = 130_854_230_896`,
- `kPanCoupled < kPanTransition` with `kPanTransition - kPanCoupled = 4_194_300_000`,
- `6 * kPanCoupled < yukon` with restored margin `yukon - 6 * kPanCoupled = 115_594_540_098`
  and exact slope threshold `k * kPanCoupled < yukon ↔ k ≤ 6`. -/
theorem guest_joint_transition_insertion_absorbed_into_kPanCoupled_non_vacuous_and_tight
    (r D W R Tloc k : Nat) (rs : List Nat)
    (hr : 20 * r ≤ GuestCoupledTxBlockStorageBound.M)
    (hrs : ∀ x ∈ rs, 20 * x ≤ GuestCoupledTxBlockStorageBound.M)
    (hDWR : 21 * D + W + 20 * R ≤ S)
    (hloc : Tloc ≤ 8 * 3994571428) :
    kIns = 41_935 ∧
    5 * (r * (r - 1)) ≤ kIns * r ∧
    (20 * 8388 ≤ GuestCoupledTxBlockStorageBound.M ∧ 5 * (8388 * (8388 - 1)) = kIns * 8388) ∧
    (rs.map (fun x => 5 * (x * (x - 1)))).sum ≤ kIns * rs.sum ∧
    42 * (D * (2 * W + 4 * R) + kIns * R) ≤ S * S ∧
    D * (2 * W + 4 * R) + kIns * R ≤ 95_238_095_238 ∧
    (21 * 47619 + 1000001 + 20 * 0 = S ∧
      47619 * (2 * 1000001 + 4 * 0) + kIns * 0 = 95_238_095_238) ∧
    (21 * 0 + 0 + 20 * 100000 = S ∧
      0 * (2 * 0 + 4 * 100000) + kIns * 100000 = 4_193_500_000) ∧
    linear + Tloc + (D * (2 * W + 4 * R) + kIns * R) ≤ kPanCoupled ∧
    kPanCoupled = 130_854_230_896 ∧
    kPanTransition = 135_048_530_896 ∧
    kPanCoupled < kPanTransition ∧
    kPanTransition - kPanCoupled = 4_194_300_000 ∧
    6 * kPanCoupled < yukon ∧
    yukon - 6 * kPanCoupled = 115_594_540_098 ∧
    (k * kPanCoupled < yukon ↔ k ≤ 6) := by
  have himp := improves_transition
  have hm6 := GuestJointTransitionInsertionBound.margin6
  have hkc : kPanCoupled = 130_854_230_896 := by decide
  have hkt : kPanTransition = 135_048_530_896 := kPanTransition_val.1
  exact ⟨rfl,
    insert_linear r hr,
    insert_linear_tight,
    insert_sum rs hrs,
    joint_transition_absorbed D W R hDWR,
    joint_le D W R hDWR,
    joint_tight,
    pure_transition_corner,
    kPan_with_transitions D W R hDWR Tloc hloc,
    hkc,
    hkt,
    himp.1,
    himp.2,
    hm6.1,
    hm6.2,
    GuestJointTransitionInsertionBound.slope_threshold k⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Reduction of `kPanTransition` Tiers to `kPanCoupled` Tiers & Exact Gains at `1x`, `3x`, and `6x`**):
Proves that absorbing the clean→dirty insertion cost reduces the transition target tiers back to
the coupled target tiers:
- Source gain: `jointTransitionSourceGain = kPanTransition - kPanCoupled = 4_194_300_000`,
- Slope `3x` gain: `jointTransitionSlope3Gain = 12_582_900_000`, with
  `coupledSlope3UnrolledK + 12_582_900_000 = transitionSlope3UnrolledK` (`392_562_702_020 → 405_145_602_020`) and
  `coupledSlope3K + 12_582_900_000 = transitionSlope3K` (`392_562_715_820 → 405_145_615_820`),
- Slope `6x` gain: `jointTransitionSlope6Gain = 25_165_800_000`, with
  `coupledSlope6UnrolledK + 25_165_800_000 = transitionSlope6UnrolledK` (`785_125_394_708 → 810_291_194_708`) and
  `coupledSlope6K + 25_165_800_000 = transitionSlope6K` (`785_125_408_508 → 810_291_208_508`),
- Plus the induced target-step bounds `(bootstrapSteps - copyLoopSavedSteps) + 3 * (linear + Tloc + (D * (2 * W + 4 * R) + kIns * R)) ≤ coupledSlope3UnrolledK`
  and `(bootstrapSteps - copyLoopSavedSteps) + 6 * (linear + Tloc + (D * (2 * W + 4 * R) + kIns * R)) ≤ coupledSlope6UnrolledK`. -/
theorem joint_transition_tier_reduction_to_coupled_tiers_non_vacuous_and_tight
    (D W R Tloc minutes : Nat)
    (hDWR : 21 * D + W + 20 * R ≤ S)
    (hloc : Tloc ≤ 8 * 3994571428) :
    jointTransitionSourceGain = 4_194_300_000 ∧
    jointTransitionSlope3Gain = 12_582_900_000 ∧
    jointTransitionSlope6Gain = 25_165_800_000 ∧
    transitionSlope3PostK - coupledSlope3PostK = 12_582_900_000 ∧
    transitionSlope3UnrolledK - coupledSlope3UnrolledK = 12_582_900_000 ∧
    transitionSlope3K - coupledSlope3K = 12_582_900_000 ∧
    transitionSlope6PostK - coupledSlope6PostK = 25_165_800_000 ∧
    transitionSlope6UnrolledK - coupledSlope6UnrolledK = 25_165_800_000 ∧
    transitionSlope6K - coupledSlope6K = 25_165_800_000 ∧
    coupledSlope3UnrolledK + jointTransitionSlope3Gain = transitionSlope3UnrolledK ∧
    coupledSlope3K + jointTransitionSlope3Gain = transitionSlope3K ∧
    coupledSlope6UnrolledK + jointTransitionSlope6Gain = transitionSlope6UnrolledK ∧
    coupledSlope6K + jointTransitionSlope6Gain = transitionSlope6K ∧
    (bootstrapSteps - copyLoopSavedSteps) + 3 * (linear + Tloc + (D * (2 * W + 4 * R) + kIns * R)) ≤
      coupledSlope3UnrolledK ∧
    bootstrapSteps + 3 * (linear + Tloc + (D * (2 * W + 4 * R) + kIns * R)) ≤
      coupledSlope3K ∧
    (bootstrapSteps - copyLoopSavedSteps) + 6 * (linear + Tloc + (D * (2 * W + 4 * R) + kIns * R)) ≤
      coupledSlope6UnrolledK ∧
    bootstrapSteps + 6 * (linear + Tloc + (D * (2 * W + 4 * R) + kIns * R)) ≤
      coupledSlope6K ∧
    yukonScore transitionSlope3UnrolledK minutes - yukonScore coupledSlope3UnrolledK minutes =
      125_829_000_000_000 ∧
    yukonScore transitionSlope6UnrolledK minutes - yukonScore coupledSlope6UnrolledK minutes =
      251_658_000_000_000 := by
  have hkpan := kPan_with_transitions D W R hDWR Tloc hloc
  have h22 := twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hc3u : coupledSlope3UnrolledK = 392_562_702_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc3 : coupledSlope3K = 392_562_715_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3 : transitionSlope3K = 405_145_615_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6u : coupledSlope6UnrolledK = 785_125_394_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6 : coupledSlope6K = 785_125_408_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6 : transitionSlope6K = 810_291_208_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htr := transition_slope3_and_slope6_unrolled_and_baseline_tiers_non_vacuous_and_tight 0 minutes
  have htp3 : transitionSlope3PostK = 405_145_592_688 := htr.1
  have htp6 : transitionSlope6PostK = 810_291_185_376 := htr.2.2.2.1
  have hcp3 : coupledSlope3PostK = 392_562_692_688 := by decide
  have hcp6 : coupledSlope6PostK = 785_125_385_376 := by decide
  have hj1 : jointTransitionSourceGain = 4_194_300_000 := by decide
  have hj3 : jointTransitionSlope3Gain = 12_582_900_000 := by decide
  have hj6 : jointTransitionSlope6Gain = 25_165_800_000 := by decide
  have hbs : bootstrapSteps = 23_132 :=
    twenty_two_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight.2.1
  have hsave : copyLoopSavedSteps = 13_800 := copy_loop_saved_exact
  have hkc : kPanCoupled = 130_854_230_896 := by decide
  rw [hkc] at hkpan
  rw [hj1, hj3, hj6, htp3, hcp3, ht3u, hc3u, ht3, hc3, htp6, hcp6, ht6u, hc6u, ht6, hc6, hbs, hsave]
  unfold yukonScore
  omega

/-- Theorem 4 (`non_vacuous_and_tight`, **Complete 22-Tier Hierarchy Strict Ordering & Gaps (`twentyTwoTierHierarchy`)**):
Re-exports and extends `twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight`
with the exact joint transition absorption relations between the coupled and transition tiers. -/
theorem twenty_two_tier_hierarchy_with_joint_transition_absorption_non_vacuous_and_tight :
    twentyTwoTierHierarchy.length = 22 ∧
    twentyTwoTierHierarchy.Pairwise (· < ·) ∧
    (∀ K ∈ twentyTwoTierHierarchy, K < 900_719_925_474) ∧
    exactKeccak128UnrolledK = 1_212_035_192 ∧
    exactKeccak0UnrolledK = 2_038_701_869 ∧
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
    coupledSlope3UnrolledK < transitionSlope3UnrolledK ∧
    coupledSlope3K < transitionSlope3K ∧
    coupledSlope6UnrolledK < transitionSlope6UnrolledK ∧
    coupledSlope6K < transitionSlope6K ∧
    transitionSlope6K < 900_719_925_474 := by
  have h22 := twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hc3u : coupledSlope3UnrolledK = 392_562_702_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc3 : coupledSlope3K = 392_562_715_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3 : transitionSlope3K = 405_145_615_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6u : coupledSlope6UnrolledK = 785_125_394_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6 : coupledSlope6K = 785_125_408_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6 : transitionSlope6K = 810_291_208_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨h22.1, h22.2.1, h22.2.2.1,
    h22.2.2.2.1,
    h22.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc3u, hc3, ht3u, ht3,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc6u, hc6, ht6u, ht6,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by rw [hc3u, ht3u]; decide,
    by rw [hc3, ht3]; decide,
    by rw [hc6u, ht6u]; decide,
    by rw [hc6, ht6]; decide,
    by rw [ht6]; decide⟩

/-- Theorem 5 (`non_vacuous_and_tight`, **Bootstrap Decompositions & 1-Tick Tightness Across Coupled & Absorbed Transition Tiers**):
Establishes exact `(bootstrapSteps - copyLoopSavedSteps) = 9_332` and `bootstrapSteps = 23_132`
decompositions for both the absorbed `kPanCoupled` tiers and the unabsorbed `kPanTransition` tiers,
with sharp 1-tick tightness boundaries (`¬ K ≤ K - 1`). -/
theorem coupled_and_transition_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight :
    bootstrapSteps - copyLoopSavedSteps = 9_332 ∧
    bootstrapSteps = 23_132 ∧
    coupledSlope3UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanCoupled ∧
    coupledSlope3K = bootstrapSteps + 3 * kPanCoupled ∧
    coupledSlope6UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 6 * kPanCoupled ∧
    coupledSlope6K = bootstrapSteps + 6 * kPanCoupled ∧
    transitionSlope3UnrolledK =
      (bootstrapSteps - copyLoopSavedSteps) + 3 * (kPanCoupled + jointTransitionSourceGain) ∧
    transitionSlope3K =
      bootstrapSteps + 3 * (kPanCoupled + jointTransitionSourceGain) ∧
    transitionSlope6UnrolledK =
      (bootstrapSteps - copyLoopSavedSteps) + 6 * (kPanCoupled + jointTransitionSourceGain) ∧
    transitionSlope6K =
      bootstrapSteps + 6 * (kPanCoupled + jointTransitionSourceGain) ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanCoupled ≤ coupledSlope3UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 3 * kPanCoupled ≤ coupledSlope3K - 1) ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanCoupled ≤ coupledSlope6UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 6 * kPanCoupled ≤ coupledSlope6K - 1) := by
  have h18b := eighteen_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
  have h22b := twenty_two_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
  have hsum : kPanCoupled + jointTransitionSourceGain = kPanTransition := by decide
  refine ⟨h22b.1, h22b.2.1,
    h22b.2.2.2.2.2.2.1,
    h22b.2.2.2.2.2.2.2.1,
    h22b.2.2.2.2.2.2.2.2.1,
    h22b.2.2.2.2.2.2.2.2.2.1,
    by rw [hsum]; exact h22b.2.2.1,
    by rw [hsum]; exact h22b.2.2.2.1,
    by rw [hsum]; exact h22b.2.2.2.2.1,
    by rw [hsum]; exact h22b.2.2.2.2.2.1,
    h18b.2.2.2.2.2.2.2.2.1,
    h18b.2.2.2.2.2.2.2.2.2.1,
    h18b.2.2.2.2.2.2.2.2.2.2.1,
    h18b.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Theorem 6 (`non_vacuous_and_tight`, **IEEE-754 Float64 Representability & Strict `yukonScore` Monotonicity Across Absorbed and Transition Tiers**):
Establishes strict `yukonScore` monotonicity, exact `yukonScore` gains from joint transition
absorption (`125_829_000_000_000` at `3x` and `251_658_000_000_000` at `6x`), and IEEE-754 double-precision
integer representability (`yukonScore K minutes < 2^53 - 1`) for all `minutes : Nat`. -/
theorem coupled_and_transition_yukonScore_order_and_float64_exact_non_vacuous_and_tight
    (minutes K : Nat) :
    yukonScore coupledSlope3UnrolledK minutes < yukonScore coupledSlope3K minutes ∧
    yukonScore coupledSlope3K minutes < yukonScore transitionSlope3UnrolledK minutes ∧
    yukonScore transitionSlope3UnrolledK minutes < yukonScore transitionSlope3K minutes ∧
    yukonScore coupledSlope6UnrolledK minutes < yukonScore coupledSlope6K minutes ∧
    yukonScore coupledSlope6K minutes < yukonScore transitionSlope6UnrolledK minutes ∧
    yukonScore transitionSlope6UnrolledK minutes < yukonScore transitionSlope6K minutes ∧
    yukonScore transitionSlope3UnrolledK minutes - yukonScore coupledSlope3UnrolledK minutes =
      125_829_000_000_000 ∧
    yukonScore transitionSlope3K minutes - yukonScore coupledSlope3K minutes =
      125_829_000_000_000 ∧
    yukonScore transitionSlope6UnrolledK minutes - yukonScore coupledSlope6UnrolledK minutes =
      251_658_000_000_000 ∧
    yukonScore transitionSlope6K minutes - yukonScore coupledSlope6K minutes =
      251_658_000_000_000 ∧
    yukonScore coupledSlope3UnrolledK minutes < 2 ^ 53 - 1 ∧
    yukonScore coupledSlope6UnrolledK minutes < 2 ^ 53 - 1 ∧
    yukonScore transitionSlope3UnrolledK minutes < 2 ^ 53 - 1 ∧
    yukonScore transitionSlope6K minutes < 2 ^ 53 - 1 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have h22 := twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hc3u : coupledSlope3UnrolledK = 392_562_702_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc3 : coupledSlope3K = 392_562_715_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3 : transitionSlope3K = 405_145_615_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6u : coupledSlope6UnrolledK = 785_125_394_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6 : coupledSlope6K = 785_125_408_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6 : transitionSlope6K = 810_291_208_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hm : min minutes 9999 ≤ 9999 := Nat.min_le_right _ _
  have hm9999 : min 9999 9999 = 9999 := rfl
  rw [hc3u, hc3, ht3u, ht3, hc6u, hc6, ht6u, ht6]
  unfold yukonScore
  rw [hm9999]
  omega

/-- Theorem 7 (`non_vacuous_and_tight`, **`claim.json ≤ 128`-Byte Audit Across All Absorbed `kPanCoupled` & `kPanTransition` Tiers**):
Certifies `utf8ByteSize = 29` (for `{"claimed_k": "..."}`) and `utf8ByteSize = 19` (for `{"K": ...}`),
`validFiniteClaim = true`, and `checkSubmissionLimits = true` across all 4 absorbed coupled tiers
(`coupledSlope3UnrolledK`, `coupledSlope3K`, `coupledSlope6UnrolledK`, `coupledSlope6K`) and all 4
transition tiers (`transitionSlope3UnrolledK`, `transitionSlope3K`, `transitionSlope6UnrolledK`,
`transitionSlope6K`), with the sharp `128`-byte vs `129`-byte boundary. -/
theorem coupled_and_transition_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight :
    claimJsonCoupledSlope3Unrolled.utf8ByteSize = 29 ∧
    claimJsonCoupledSlope3.utf8ByteSize = 29 ∧
    claimJsonCoupledSlope6Unrolled.utf8ByteSize = 29 ∧
    claimJsonCoupledSlope6.utf8ByteSize = 29 ∧
    claimJsonTransitionSlope3Unrolled.utf8ByteSize = 29 ∧
    claimJsonTransitionSlope3.utf8ByteSize = 29 ∧
    claimJsonTransitionSlope6Unrolled.utf8ByteSize = 29 ∧
    claimJsonTransitionSlope6.utf8ByteSize = 29 ∧
    validFiniteClaim coupledSlope3UnrolledK claimJsonCoupledSlope3Unrolled = true ∧
    validFiniteClaim coupledSlope3K claimJsonCoupledSlope3 = true ∧
    validFiniteClaim coupledSlope6UnrolledK claimJsonCoupledSlope6Unrolled = true ∧
    validFiniteClaim coupledSlope6K claimJsonCoupledSlope6 = true ∧
    validFiniteClaim transitionSlope3UnrolledK claimJsonTransitionSlope3Unrolled = true ∧
    validFiniteClaim transitionSlope3K claimJsonTransitionSlope3 = true ∧
    validFiniteClaim transitionSlope6UnrolledK claimJsonTransitionSlope6Unrolled = true ∧
    validFiniteClaim transitionSlope6K claimJsonTransitionSlope6 = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonCoupledSlope3Unrolled.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonCoupledSlope6Unrolled.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonTransitionSlope3Unrolled.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonTransitionSlope6Unrolled.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 (MAX_CLAIM_BYTES + 1) false false true = false := by
  have hc18 := eighteen_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
  have hc22 := twenty_two_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
  exact ⟨hc18.1, hc18.2.1, hc18.2.2.1, hc18.2.2.2.1,
    hc22.1, hc22.2.1, hc22.2.2.1, hc22.2.2.2.1,
    hc18.2.2.2.2.2.2.2.2.1,
    hc18.2.2.2.2.2.2.2.2.2.1,
    hc18.2.2.2.2.2.2.2.2.2.2.1,
    hc18.2.2.2.2.2.2.2.2.2.2.2.1,
    hc22.2.2.2.2.2.2.2.2.1,
    hc22.2.2.2.2.2.2.2.2.2.1,
    hc22.2.2.2.2.2.2.2.2.2.2.1,
    hc22.2.2.2.2.2.2.2.2.2.2.2.1,
    hc18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc18.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`, **Direct `InitE.Certificate` Bridge from Absorbed `coupledSlope3UnrolledK` Across All Transition & Coupled Tiers**):
Proves that because joint transition absorption reduces the worst-case source clock with transitions
to `kPanCoupled`, uniform target non-`.timeOut` at `coupledSlope3UnrolledK = 392_562_702_020` suffices
to certify `coupledSlope3UnrolledK`, `coupledSlope3K`, `transitionSlope3UnrolledK`, `transitionSlope3K`,
`blockVsTxSlope6K`, `bs32JointSlope3UnrolledK`, `bs32JointSlope3K`, `coupledSlope6UnrolledK`,
`coupledSlope6K`, `transitionSlope6UnrolledK`, `transitionSlope6K`, `blockVsTxSlope12K`, and `.infinity`. -/
theorem absorbed_coupled_to_transition_certificates_and_margins_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_coupled_s3_unrolled : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          coupledSlope3UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
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
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    transitionSlope3UnrolledK - coupledSlope3UnrolledK = 12_582_900_000 ∧
    transitionSlope6UnrolledK - coupledSlope6UnrolledK = 25_165_800_000 ∧
    yukonScore transitionSlope3UnrolledK minutes - yukonScore coupledSlope3UnrolledK minutes =
      125_829_000_000_000 ∧
    yukonScore transitionSlope6UnrolledK minutes - yukonScore coupledSlope6UnrolledK minutes =
      251_658_000_000_000 ∧
    coupledSlope3UnrolledK < transitionSlope3UnrolledK ∧
    coupledSlope6UnrolledK < transitionSlope6UnrolledK ∧
    transitionSlope6K < 900_719_925_474 := by
  have hc := coupled_slope3_and_slope6_certificates_and_margins_non_vacuous_and_tight
    oracles c depth minutes hlab compiled depthBound not_timeOut_coupled_s3_unrolled
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
  have h22 := twenty_two_tier_hierarchy_with_joint_transition_absorption_non_vacuous_and_tight
  have hc3 : coupledSlope3K = 392_562_715_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3u : transitionSlope3UnrolledK = 405_145_602_020 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht3 : transitionSlope3K = 405_145_615_820 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc6 : coupledSlope6K = 785_125_408_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6u : transitionSlope6UnrolledK = 810_291_194_708 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht6 : transitionSlope6K = 810_291_208_508 := h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt1 : coupledSlope3K < transitionSlope3UnrolledK := by rw [hc3, ht3u]; decide
  have hlt2 : transitionSlope3UnrolledK < transitionSlope3K := by rw [ht3u, ht3]; decide
  have hlt3 : coupledSlope6K < transitionSlope6UnrolledK := by rw [hc6, ht6u]; decide
  have hlt4 : transitionSlope6UnrolledK < transitionSlope6K := by rw [ht6u, ht6]; decide
  have hcert_t3u := hmono (Nat.le_of_lt hlt1) hc.2.1
  have hcert_t3 := hmono (Nat.le_of_lt hlt2) hcert_t3u
  have hcert_t6u := hmono (Nat.le_of_lt hlt3) hc.2.2.2.2.2.2.1
  have hcert_t6 := hmono (Nat.le_of_lt hlt4) hcert_t6u
  have hred := joint_transition_tier_reduction_to_coupled_tiers_non_vacuous_and_tight
    0 0 0 0 minutes (by decide) (by decide)
  exact ⟨hc.1, hc.2.1, hcert_t3u, hcert_t3, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1,
    hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hcert_t6u, hcert_t6, hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.1,
    hred.2.2.2.2.1,
    hred.2.2.2.2.2.2.2.1,
    hred.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hred.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`, **Monotone `InitE.Certificate` Chain Across All 22 Tiers (`twentyTwoTierHierarchy`)**):
Lifts `InitE.Certificate` from `exactKeccak128UnrolledK = 1_212_035_192` across all 22 tiers of
`twentyTwoTierHierarchy` (plus `blockVsTxSlope12K = 857_384_015_252` and `.infinity`). -/
theorem pan_to_stack_and_joint_transition_twenty_two_tier_monotonicity_non_vacuous_and_tight
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
    InitE.Certificate InitE.baselineSubmission .infinity :=
  twenty_two_tier_certificate_monotonicity_chain_non_vacuous_and_tight hle hcert₁ hcert_u128

/-- Theorem 10 (`non_vacuous_and_tight`, **Master End-to-End `PanToStackNoStoreConsts`, Joint Clean→Dirty Transition Absorption & 22-Tier Campaign Certificate**):
Simultaneously unites:
- All 22 `InitE.Certificate (baselineWithFiniteK K) (.finite K)` tiers in `twentyTwoTierHierarchy`
  (plus `blockVsTxSlope12K` and `.infinity`),
- The end-to-end `PanToStackNoStoreConsts` chain (`panToWord_NoSt`, `panToWordToWord_NoSt`,
  `s_compileNative_bodies`, `panToStackAlloc_NoSt`, `storeConstsStub_not_StackNoSt`),
- The 10-pass `WordToWord.fullCompileSingle` + `LoopToWord.compHOL` `NoSt = true` and
  `storeConstsAllowance = 0` chain (`loopToWord_fullCompileSingle_NoSt`,
  `loopToWord_fullCompileSingle_allowance_zero`),
- The `StackRemoveStoreConstsZeroBridge` (`NoSC`, `storeConstsAllowance = 0`, `runAllowance = 0`),
- The `GuestJointTransitionInsertionBound` absorption envelope (`42 * (D * (2 * W + 4 * R) + kIns * R) ≤ S * S`,
  `linear + Tloc + (D * (2 * W + 4 * R) + kIns * R) ≤ kPanCoupled = 130_854_230_896`,
  `kPanTransition - kPanCoupled = 4_194_300_000`, `yukon - 6 * kPanCoupled = 115_594_540_098`,
  `k * kPanCoupled < yukon ↔ k ≤ 6`),
- The exact `12_582_900_000` (`3x`) and `25_165_800_000` (`6x`) target-step reductions from
  `transitionSlope*` to `coupledSlope*`, and
- Purified `.Solver` path admission (`0` `Bounded*` imports). -/
theorem master_pan_to_stack_and_joint_transition_campaign_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture) (panProg : List (DeclHOL width))
    (wc : WordToWord.Config) (cAsm : AsmConfigExact width) (perf b : Bool)
    (rc alg nm ac kStub : Nat)
    (ctx : Spt Nat) (prog : HolLoopProg width) (loc : Nat × Nat) (co : Option (Spt Nat))
    (xs : List (Bool × Nat)) (origin : TraceFrom (LoopToWord.compHOL ctx prog loc).1 xs)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes D W R Tloc k : Nat)
    (rs : List Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (hDWR : 21 * D + W + 20 * R ≤ S)
    (hrs : ∀ r ∈ rs, 20 * r ≤ GuestCoupledTxBlockStorageBound.M)
    (hloc : Tloc ≤ 8 * 3994571428)
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
    InitE.Certificate (baselineWithFiniteK coupledSlope3UnrolledK) (.finite coupledSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledSlope3K) (.finite coupledSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope3UnrolledK) (.finite transitionSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope3K) (.finite transitionSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coupledSlope6UnrolledK) (.finite coupledSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledSlope6K) (.finite coupledSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope6UnrolledK) (.finite transitionSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope6K) (.finite transitionSlope6K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    (∀ y ∈ (compileNative cAsm perf (WordToWord.compile wc cAsm
        (panToWordCompileProgHOL arch panProg)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoSt (StackAlloc.progComp y).2 = true) ∧
    StackNoSt (storeConstsStubNative (width := width) kStub) = false ∧
    NoSt (WordToWord.fullCompileSingle b rc alg cAsm
      ((nm, ac, (LoopToWord.compHOL ctx prog loc).1), co)).2.2 = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordToWord.fullCompileSingle b rc alg cAsm
        ((nm, ac, (LoopToWord.compHOL ctx prog loc).1), co)).2.2 = 0 ∧
    NoSC (LoopToWord.compHOL ctx prog loc).1 = true ∧
    StackRemoveStoreConstsZeroBridge.storeConstsAllowance (LoopToWord.compHOL ctx prog loc).1 = 0 ∧
    runAllowance xs = 0 ∧
    (rs.map (fun r => 5 * (r * (r - 1)))).sum ≤ kIns * rs.sum ∧
    42 * (D * (2 * W + 4 * R) + kIns * R) ≤ S * S ∧
    D * (2 * W + 4 * R) + kIns * R ≤ 95_238_095_238 ∧
    linear + Tloc + (D * (2 * W + 4 * R) + kIns * R) ≤ kPanCoupled ∧
    kPanCoupled = 130_854_230_896 ∧
    kPanTransition - kPanCoupled = 4_194_300_000 ∧
    transitionSlope3UnrolledK - coupledSlope3UnrolledK = 12_582_900_000 ∧
    transitionSlope6UnrolledK - coupledSlope6UnrolledK = 25_165_800_000 ∧
    yukon - 6 * kPanCoupled = 115_594_540_098 ∧
    (k * kPanCoupled < yukon ↔ k ≤ 6) ∧
    yukonScore transitionSlope3UnrolledK minutes - yukonScore coupledSlope3UnrolledK minutes =
      125_829_000_000_000 ∧
    yukonScore transitionSlope6UnrolledK minutes - yukonScore coupledSlope6UnrolledK minutes =
      251_658_000_000_000 ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedPanToStackAndJointTransitionSynth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedPanToStackAndJointTransitionSynth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hcert_u128 := exact_keccak_128_unrolled_certificate
    oracles c depth hlab compiled depthBound not_timeOut_u128
  have hchain := twenty_two_tier_certificate_monotonicity_chain_non_vacuous_and_tight
    (Nat.le_refl exactKeccak128UnrolledK) hcert_u128 hcert_u128
  have h22 := twenty_two_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hred := joint_transition_tier_reduction_to_coupled_tiers_non_vacuous_and_tight
    D W R Tloc minutes hDWR hloc
  have hkc : kPanCoupled = 130_854_230_896 := by decide
  exact ⟨h22.1, h22.2.1, hchain.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    panToStackAlloc_NoSt arch panProg wc cAsm perf,
    storeConstsStub_not_StackNoSt kStub,
    loopToWord_fullCompileSingle_NoSt ctx prog loc b rc alg cAsm nm ac co,
    loopToWord_fullCompileSingle_allowance_zero ctx prog loc b rc alg cAsm nm ac co,
    compHOL_NoSC ctx prog loc,
    StackRemoveStoreConstsZeroBridge.compiled_allowance_zero ctx prog loc,
    compiled_run_allowance_zero ctx prog loc xs origin,
    insert_sum rs hrs,
    joint_transition_absorbed D W R hDWR,
    joint_le D W R hDWR,
    kPan_with_transitions D W R hDWR Tloc hloc,
    hkc,
    improves_transition.2,
    hred.2.2.2.2.1,
    hred.2.2.2.2.2.2.2.1,
    GuestJointTransitionInsertionBound.margin6.2,
    GuestJointTransitionInsertionBound.slope_threshold k,
    hred.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hred.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    by decide,
    by decide,
    rfl⟩

#print axioms pan_to_stack_alloc_end_to_end_no_store_consts_non_vacuous_and_tight
#print axioms guest_joint_transition_insertion_absorbed_into_kPanCoupled_non_vacuous_and_tight
#print axioms joint_transition_tier_reduction_to_coupled_tiers_non_vacuous_and_tight
#print axioms twenty_two_tier_hierarchy_with_joint_transition_absorption_non_vacuous_and_tight
#print axioms coupled_and_transition_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
#print axioms coupled_and_transition_yukonScore_order_and_float64_exact_non_vacuous_and_tight
#print axioms coupled_and_transition_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
#print axioms absorbed_coupled_to_transition_certificates_and_margins_non_vacuous_and_tight
#print axioms pan_to_stack_and_joint_transition_twenty_two_tier_monotonicity_non_vacuous_and_tight
#print axioms master_pan_to_stack_and_joint_transition_campaign_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedPanToStackAndJointTransitionSynth
