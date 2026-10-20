import InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope
import InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts
import InitECandidate.Solver.SelfContainedStackRemoveNamesAndMultiAddrSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SelfContainedUnifiedAllTablesAndStackNamesSynth` — Self-Contained Unified 5-Variable All-Tables Envelope (`kPanUnifiedAllTables = 136_116_135_658`), Unconditional `PanToStackToLab` No-`storeConsts` Chain & 26-Tier Synthesis (`W5_94`)

This module has **0 imports from `InitECandidate.Proofs.Bounded*`** in its transitive closure and
unifies:
1. The 5-variable $(D, R, A, C, W)$ master envelope over all 9 block hash tables from
   `GuestUnifiedAllTablesMasterEnvelope` (`11/11` tight):
   - `unified_five_var_coupled_envelope` (`42 * F D R A C W ≤ S * S`) and `unified_coupled_le` (`F D R A C W ≤ 95_238_095_238`),
   - `unified_coupled_tight` and `unified_cold_corner`,
   - `merge_identity`, `unified_five_var_merge_envelope` (`40 * G D R A C W ≤ S * S`) and `unified_merge_le` (`G D R A C W ≤ 100_000_000_000`),
   - `unified_merge_tight`, `kPanUnifiedAllTables = kPanMerge = kPanMultiAddrMerge = 136_116_135_658`,
   - `kPanUnified_master` and `slopes` (`6 * kPanUnifiedAllTables < yukon ∧ (k * kPanUnifiedAllTables < yukon ↔ k ≤ 6)`).
2. The unconditional stack-to-lab `StackNoSt` and `FlattenVisitsSt = false` preservation chain from
   `PanToStackToLabUnconditionalNoStoreConsts` (`20/20` tight):
   - `panToStackNames_bodies_StackNoSt_unconditional` (no `WordNoStubCall` hypothesis needed),
   - `u_body_chain`, `stackRemove_storeConsts_not_skip`, `flatten_storeConsts_empty`,
   - `not_visits_of_StackNoSt`, `visits_storeConsts_tight`, `progToSection_sectionId`, and
   - `panToLabSection_unconditional`.
3. The 26-tier synthesis from `SelfContainedStackRemoveNamesAndMultiAddrSynth` (`10/10` tight),
   showing that the unified all-tables envelope `kPanUnifiedAllTables = 136_116_135_658` matches
   `kPanMultiAddrMerge` and `kPanMerge` at slopes `3x` (`408_348_416_306` / `408_348_430_106`) and
   `6x` (`816_696_823_280` / `816_696_837_080 < 900_719_925_474`), preserving strict ordering,
   `yukonScore` monotonicity, `claim.json ≤ 128`-byte compliance, and `InitE.Certificate` lifting
   across all 26 tiers (`0 sorryAx`, `10/10 non_vacuous_and_tight`).
-/

namespace InitECandidate.Solver.SelfContainedUnifiedAllTablesAndStackNamesSynth

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
open InitECandidate.Solver.GuestMergeTxUnionEnvelope
open InitECandidate.Solver.GuestMultiAddressMergeDominance
open InitECandidate.Solver.GuestFiveAddrTablesMergeBound
open InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope
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
open InitECandidate.Solver.SelfContainedPanToStackAndJointTransitionSynth
open InitECandidate.Solver.SelfContainedStackRemoveNamesAndMultiAddrSynth
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

/-! ## Section 1: Unified All-Tables Target Tiers (`kPanUnifiedAllTables = 136_116_135_658`) -/

/-- Post-bootstrap target steps for `kPanUnifiedAllTables = 136_116_135_658` at `3x` target slope:
`3 * 136_116_135_658 = 408_348_406_974`. -/
def unifiedAllTablesSlope3PostK : Nat := 3 * kPanUnifiedAllTables

/-- Unrolled-`copyLoop` (`bootstrapSteps - copyLoopSavedSteps = 9_332`) target ceiling for
`kPanUnifiedAllTables` at `3x` slope: `9_332 + 3 * 136_116_135_658 = 408_348_416_306`. -/
def unifiedAllTablesSlope3UnrolledK : Nat :=
  (bootstrapSteps - copyLoopSavedSteps) + unifiedAllTablesSlope3PostK

/-- Baseline-bootstrap (`bootstrapSteps = 23_132`) target ceiling for `kPanUnifiedAllTables` at
`3x` slope: `23_132 + 3 * 136_116_135_658 = 408_348_430_106`. -/
def unifiedAllTablesSlope3K : Nat :=
  bootstrapSteps + unifiedAllTablesSlope3PostK

/-- Post-bootstrap target steps for `kPanUnifiedAllTables = 136_116_135_658` at `6x` target slope:
`6 * 136_116_135_658 = 816_696_813_948`. -/
def unifiedAllTablesSlope6PostK : Nat := 6 * kPanUnifiedAllTables

/-- Unrolled-`copyLoop` (`bootstrapSteps - copyLoopSavedSteps = 9_332`) target ceiling for
`kPanUnifiedAllTables` at `6x` slope: `9_332 + 6 * 136_116_135_658 = 816_696_823_280`. -/
def unifiedAllTablesSlope6UnrolledK : Nat :=
  (bootstrapSteps - copyLoopSavedSteps) + unifiedAllTablesSlope6PostK

/-- Baseline-bootstrap (`bootstrapSteps = 23_132`) target ceiling for `kPanUnifiedAllTables` at
`6x` slope: `23_132 + 6 * 136_116_135_658 = 816_696_837_080`. -/
def unifiedAllTablesSlope6K : Nat :=
  bootstrapSteps + unifiedAllTablesSlope6PostK

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`, **5-Variable Coupled Envelope (`F ≤ 95_238_095_238`) Over All 9 Block Hash Tables**):
Unites `unified_five_var_coupled_envelope`, `unified_coupled_le`, `unified_coupled_tight`, and
`unified_cold_corner` from `GuestUnifiedAllTablesMasterEnvelope`:
for all `(D, R, A, C, W)` satisfying the unified block-gas budget `21D + 20R + 26A + 21C + W ≤ S`,
`42 * F D R A C W ≤ S * S` and `F D R A C W ≤ 95_238_095_238`, attained tightly at
`(47_619, 0, 0, 0, 1_000_001)` while the pure-`bs+72` cold corner `(0, 0, 0, 95_238, 0)` evaluates
to `9_070_276_644 < 95_238_095_238`. -/
theorem unified_five_var_coupled_envelope_and_tight_vertex_non_vacuous_and_tight
    (D R A C W : Nat) (h : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S) :
    42 * F D R A C W ≤ S * S ∧
    F D R A C W ≤ 95_238_095_238 ∧
    (21 * 47619 + 20 * 0 + 26 * 0 + 21 * 0 + 1000001 = S ∧ F 47619 0 0 0 1000001 = 95238095238) ∧
    (F 0 0 0 95238 0 = 9070276644 ∧ 9070276644 < 95238095238) ∧
    ¬ (F 47619 0 0 0 1000001 ≤ 95_238_095_237) := by
  exact ⟨unified_five_var_coupled_envelope D R A C W h,
    unified_coupled_le D R A C W h,
    unified_coupled_tight,
    unified_cold_corner,
    by decide⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **5-Variable Merge Envelope (`G ≤ 100_000_000_000`), `kPanUnifiedAllTables = 136_116_135_658` & `k ≤ 6` Slope Threshold**):
Unites `merge_identity`, `unified_five_var_merge_envelope`, `unified_merge_le`, `unified_merge_tight`,
`kPanUnified_val`, `kPanUnified_master`, and `slopes` from `GuestUnifiedAllTablesMasterEnvelope`:
for all `(D, R, A, C, W)` with `20(D+R+A) + 6A + 21C + (W+D+R+A) ≤ S`,
`40 * G D R A C W ≤ S * S`, `G D R A C W ≤ 100_000_000_000`, and
`linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables = 136_116_135_658 = kPanMerge = kPanMultiAddrMerge`,
with `6 * kPanUnifiedAllTables < yukon` and `k * kPanUnifiedAllTables < yukon ↔ k ≤ 6`. -/
theorem unified_five_var_merge_envelope_and_kPanUnified_master_non_vacuous_and_tight
    (X Y A_int : Int) (D R A C W Tloc Tlin k : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    (20 * X + 6 * A_int + Y) ^ 2 - 40 * (2 * X * Y + 12 * A_int ^ 2) =
      (20 * X - Y - 6 * A_int) ^ 2 + 480 * A_int * (X - A_int) ∧
    40 * G D R A C W ≤ S * S ∧
    G D R A C W ≤ 100_000_000_000 ∧
    (G 50000 0 0 0 950000 = 100000000000 ∧ G 2000 48000 0 0 950000 = 100000000000 ∧
      20 * (2000 + 48000 + 0) + 6 * 0 + 21 * 0 + (950000 + (2000 + 48000 + 0)) = S) ∧
    kPanUnifiedAllTables = 136_116_135_658 ∧
    kPanUnifiedAllTables = kPanMerge ∧
    kPanUnifiedAllTables = kPanMultiAddrMerge ∧
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables ∧
    6 * kPanUnifiedAllTables < yukon ∧
    (k * kPanUnifiedAllTables < yukon ↔ k ≤ 6) ∧
    yukon - 6 * kPanUnifiedAllTables = 84_023_111_526 := by
  have hk := kPanUnified_val
  have hkm := kPanMultiAddrMerge_eq
  have hsl := GuestUnifiedAllTablesMasterEnvelope.slopes k
  have htm := threshold_and_margin k
  exact ⟨merge_identity X Y A_int,
    unified_five_var_merge_envelope D R A C W h,
    unified_merge_le D R A C W h,
    unified_merge_tight,
    hk.1,
    hk.2,
    by rw [hk.1, hkm.2],
    kPanUnified_master D R A C W Tloc Tlin h hloc hlin,
    hsl.1,
    hsl.2,
    by rw [hk.1, ← hkm.2]; exact htm.2⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Unconditional `PanToStackToLabUnconditionalNoStoreConsts` Chain (`panToStackNames_bodies_StackNoSt_unconditional`, `flatten_storeConsts_empty`, `panToLabSection_unconditional`)**):
Unites `u_rawCallCompTop`, `u_stackRemoveComp`, `u_stackNames`, `u_body_chain`,
`panToStackNames_bodies_StackNoSt_unconditional`, `stackRemove_storeConsts_not_skip`,
`flatten_storeConsts_empty`, `not_visits_of_StackNoSt`, `visits_storeConsts_tight`,
`progToSection_sectionId`, and `panToLabSection_unconditional` from
`PanToStackToLabUnconditionalNoStoreConsts`:
without any call-target hypothesis, every non-stub Pancake body reaches `StackNames` and
`StackToLab.progToSectionHOL` with `StackNoSt = true`, `FlattenVisitsSt = false`, and
`sectionId = y.1`, whereas an explicit `.storeConsts` node expands to non-`.skip` in `StackRemove`,
evaluates `FlattenVisitsSt = true`, and produces `(.list [], false, next)` under `StackToLab.flattenHOL`. -/
theorem unconditional_pan_to_stack_to_lab_no_store_consts_chain_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf j tail : Bool)
    (info f : Spt Nat) (bd : BitVec width × BitVec width) (ptr n s b sid next : Nat)
    (stub : Option Nat) (cs bs : List Nat)
    (p : HolProg width) (hp : StackNoSt p = true) :
    StackNoSt (StackRawCall.compTop info p) = true ∧
    StackNoSt (StackRemove.comp j bd ptr p) = true ∧
    StackNoSt (StackNames.progCompHOL f p) = true ∧
    StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
      (StackAlloc.progComp (n, StackRawCall.compTop info p)).2)) = true ∧
    FlattenVisitsSt p = false ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
    StackRemove.comp j bd ptr (.storeConsts 3 4 none : HolProg width) ≠ .skip ∧
    StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
      (.list [], false, next) ∧
    FlattenVisitsSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = true ∧
    (StackToLab.progToSectionHOL (n, p)).sectionId = n := by
  exact ⟨u_rawCallCompTop info p hp,
    u_stackRemoveComp j bd ptr p hp,
    u_stackNames f p hp,
    u_body_chain info j bd ptr f n p hp,
    not_visits_of_StackNoSt p hp,
    panToStackNames_bodies_StackNoSt_unconditional arch prog wc ac perf info j bd ptr f,
    panToLabSection_unconditional arch prog wc ac perf info j bd ptr f,
    stackRemove_storeConsts_not_skip j bd ptr,
    flatten_storeConsts_empty tail s b stub sid next cs bs,
    visits_storeConsts_tight,
    progToSection_sectionId n p⟩

/-- Theorem 4 (`non_vacuous_and_tight`, **Coincidence of Unified All-Tables & Multi-Address Merge Target Tiers at Slopes `3x` and `6x`**):
Proves that `unifiedAllTablesSlope3UnrolledK`, `unifiedAllTablesSlope3K`,
`unifiedAllTablesSlope6UnrolledK`, and `unifiedAllTablesSlope6K` coincide with
`multiAddrMergeSlope3UnrolledK = 408_348_416_306`, `multiAddrMergeSlope3K = 408_348_430_106`,
`multiAddrMergeSlope6UnrolledK = 816_696_823_280`, and `multiAddrMergeSlope6K = 816_696_837_080`,
lying strictly inside `twentySixTierHierarchy` below `yukonFloat64MaxK = 900_719_925_474`. -/
theorem unified_all_tables_and_multi_addr_tiers_coincide_and_fit_under_yukon_non_vacuous_and_tight
    (k minutes : Nat) :
    unifiedAllTablesSlope3PostK = multiAddrMergeSlope3PostK ∧
    unifiedAllTablesSlope3UnrolledK = multiAddrMergeSlope3UnrolledK ∧
    unifiedAllTablesSlope3K = multiAddrMergeSlope3K ∧
    unifiedAllTablesSlope6PostK = multiAddrMergeSlope6PostK ∧
    unifiedAllTablesSlope6UnrolledK = multiAddrMergeSlope6UnrolledK ∧
    unifiedAllTablesSlope6K = multiAddrMergeSlope6K ∧
    unifiedAllTablesSlope3UnrolledK = 408_348_416_306 ∧
    unifiedAllTablesSlope3K = 408_348_430_106 ∧
    unifiedAllTablesSlope6UnrolledK = 816_696_823_280 ∧
    unifiedAllTablesSlope6K = 816_696_837_080 ∧
    transitionSlope3K < unifiedAllTablesSlope3UnrolledK ∧
    unifiedAllTablesSlope3UnrolledK < unifiedAllTablesSlope3K ∧
    unifiedAllTablesSlope3K < blockVsTxSlope6K ∧
    transitionSlope6K < unifiedAllTablesSlope6UnrolledK ∧
    unifiedAllTablesSlope6UnrolledK < unifiedAllTablesSlope6K ∧
    unifiedAllTablesSlope6K < blockVsTxSlope12K ∧
    unifiedAllTablesSlope6K < yukonFloat64MaxK ∧
    (unifiedAllTablesSlope3K ≤ k + copyLoopSavedSteps ↔ unifiedAllTablesSlope3UnrolledK ≤ k) ∧
    (unifiedAllTablesSlope6K ≤ k + copyLoopSavedSteps ↔ unifiedAllTablesSlope6UnrolledK ≤ k) ∧
    yukonScore unifiedAllTablesSlope3K minutes - yukonScore unifiedAllTablesSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore unifiedAllTablesSlope6K minutes - yukonScore unifiedAllTablesSlope6UnrolledK minutes = 138_000_000 := by
  have hk : kPanUnifiedAllTables = kPanMultiAddrMerge := by
    rw [kPanUnified_val.1, kPanMultiAddrMerge_eq.2]
  have hp3 : unifiedAllTablesSlope3PostK = multiAddrMergeSlope3PostK := by
    unfold unifiedAllTablesSlope3PostK multiAddrMergeSlope3PostK; rw [hk]
  have hu3 : unifiedAllTablesSlope3UnrolledK = multiAddrMergeSlope3UnrolledK := by
    unfold unifiedAllTablesSlope3UnrolledK multiAddrMergeSlope3UnrolledK; rw [hp3]
  have hm3 : unifiedAllTablesSlope3K = multiAddrMergeSlope3K := by
    unfold unifiedAllTablesSlope3K multiAddrMergeSlope3K; rw [hp3]
  have hp6 : unifiedAllTablesSlope6PostK = multiAddrMergeSlope6PostK := by
    unfold unifiedAllTablesSlope6PostK multiAddrMergeSlope6PostK; rw [hk]
  have hu6 : unifiedAllTablesSlope6UnrolledK = multiAddrMergeSlope6UnrolledK := by
    unfold unifiedAllTablesSlope6UnrolledK multiAddrMergeSlope6UnrolledK; rw [hp6]
  have hm6 : unifiedAllTablesSlope6K = multiAddrMergeSlope6K := by
    unfold unifiedAllTablesSlope6K multiAddrMergeSlope6K; rw [hp6]
  have hm := multi_addr_merge_slope3_and_slope6_unrolled_and_baseline_tiers_non_vacuous_and_tight k minutes
  rw [hp3, hu3, hm3, hp6, hu6, hm6]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    hm.2.1, hm.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 5 (`non_vacuous_and_tight`, **Strict Total Ordering Across the 26-Tier Hierarchy (`twentySixTierHierarchy`) with Unified All-Tables Bounds**):
Establishes `twentySixTierHierarchy.length = 26`, `twentySixTierHierarchy.Pairwise (· < ·)`,
membership of all 4 unified all-tables tiers (`unifiedAllTablesSlope3UnrolledK`,
`unifiedAllTablesSlope3K`, `unifiedAllTablesSlope6UnrolledK`, `unifiedAllTablesSlope6K`) in
`twentySixTierHierarchy`, and the uniform Yukon ceiling `< 900_719_925_474`. -/
theorem twenty_six_tier_hierarchy_with_unified_all_tables_strict_ordering_non_vacuous_and_tight :
    twentySixTierHierarchy.length = 26 ∧
    twentySixTierHierarchy.Pairwise (· < ·) ∧
    (∀ K ∈ twentySixTierHierarchy, K < 900_719_925_474) ∧
    unifiedAllTablesSlope3UnrolledK ∈ twentySixTierHierarchy ∧
    unifiedAllTablesSlope3K ∈ twentySixTierHierarchy ∧
    unifiedAllTablesSlope6UnrolledK ∈ twentySixTierHierarchy ∧
    unifiedAllTablesSlope6K ∈ twentySixTierHierarchy ∧
    exactKeccak128UnrolledK = 1_212_035_192 ∧
    unifiedAllTablesSlope3UnrolledK = 408_348_416_306 ∧
    unifiedAllTablesSlope3K = 408_348_430_106 ∧
    unifiedAllTablesSlope6UnrolledK = 816_696_823_280 ∧
    unifiedAllTablesSlope6K = 816_696_837_080 ∧
    blockVsTxSlope12K = 857_384_015_252 ∧
    blockVsTxSlope12K < 900_719_925_474 := by
  have h26 := twenty_six_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hu := unified_all_tables_and_multi_addr_tiers_coincide_and_fit_under_yukon_non_vacuous_and_tight 0 0
  have hu3 : unifiedAllTablesSlope3UnrolledK = multiAddrMergeSlope3UnrolledK := hu.2.1
  have hm3 : unifiedAllTablesSlope3K = multiAddrMergeSlope3K := hu.2.2.1
  have hu6 : unifiedAllTablesSlope6UnrolledK = multiAddrMergeSlope6UnrolledK := hu.2.2.2.2.1
  have hm6 : unifiedAllTablesSlope6K = multiAddrMergeSlope6K := hu.2.2.2.2.2.1
  refine ⟨h26.1, h26.2.1, h26.2.2.1, ?_, ?_, ?_, ?_,
    h26.2.2.2.1, hu.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.1,
    h26.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h26.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · rw [hu3]; unfold twentySixTierHierarchy; simp
  · rw [hm3]; unfold twentySixTierHierarchy; simp
  · rw [hu6]; unfold twentySixTierHierarchy; simp
  · rw [hm6]; unfold twentySixTierHierarchy; simp

/-- Theorem 6 (`non_vacuous_and_tight`, **Bootstrap Decompositions & 1-Tick Tightness Across Unified All-Tables Tiers**):
Establishes exact `(bootstrapSteps - copyLoopSavedSteps) = 9_332` and `bootstrapSteps = 23_132`
decompositions for `unifiedAllTablesSlope3UnrolledK`, `unifiedAllTablesSlope3K`,
`unifiedAllTablesSlope6UnrolledK`, and `unifiedAllTablesSlope6K`, together with 5-variable post-bootstrap
dominance `(bootstrapSteps - copyLoopSavedSteps) + k * (linear + Tloc + G D R A C W + Tlin) ≤ unifiedAllTablesSlope*`
and sharp 1-tick tightness boundaries (`¬ K ≤ K - 1`). -/
theorem unified_all_tables_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
    (D R A C W Tloc Tlin : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    bootstrapSteps - copyLoopSavedSteps = 9_332 ∧
    bootstrapSteps = 23_132 ∧
    unifiedAllTablesSlope3UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanUnifiedAllTables ∧
    unifiedAllTablesSlope3K = bootstrapSteps + 3 * kPanUnifiedAllTables ∧
    unifiedAllTablesSlope6UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables ∧
    unifiedAllTablesSlope6K = bootstrapSteps + 6 * kPanUnifiedAllTables ∧
    (bootstrapSteps - copyLoopSavedSteps) + 3 * (linear + Tloc + G D R A C W + Tlin) ≤ unifiedAllTablesSlope3UnrolledK ∧
    bootstrapSteps + 3 * (linear + Tloc + G D R A C W + Tlin) ≤ unifiedAllTablesSlope3K ∧
    (bootstrapSteps - copyLoopSavedSteps) + 6 * (linear + Tloc + G D R A C W + Tlin) ≤ unifiedAllTablesSlope6UnrolledK ∧
    bootstrapSteps + 6 * (linear + Tloc + G D R A C W + Tlin) ≤ unifiedAllTablesSlope6K ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanUnifiedAllTables ≤ unifiedAllTablesSlope3UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 3 * kPanUnifiedAllTables ≤ unifiedAllTablesSlope3K - 1) ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables ≤ unifiedAllTablesSlope6UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 6 * kPanUnifiedAllTables ≤ unifiedAllTablesSlope6K - 1) := by
  have hb := twenty_six_tier_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
  have hm := kPanUnified_master D R A C W Tloc Tlin h hloc hlin
  have hk : kPanUnifiedAllTables = kPanMultiAddrMerge := by
    rw [kPanUnified_val.1, kPanMultiAddrMerge_eq.2]
  have hu := unified_all_tables_and_multi_addr_tiers_coincide_and_fit_under_yukon_non_vacuous_and_tight 0 0
  refine ⟨hb.1, hb.2.1, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold unifiedAllTablesSlope3UnrolledK unifiedAllTablesSlope3PostK; omega
  · unfold unifiedAllTablesSlope3K unifiedAllTablesSlope3PostK; omega
  · unfold unifiedAllTablesSlope6UnrolledK unifiedAllTablesSlope6PostK; omega
  · unfold unifiedAllTablesSlope6K unifiedAllTablesSlope6PostK; omega
  · rw [hk, hu.2.1]; exact hb.2.2.2.2.2.2.2.2.2.2.1
  · rw [hk, hu.2.2.1]; exact hb.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hk, hu.2.2.2.2.1]; exact hb.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hk, hu.2.2.2.2.2.1]; exact hb.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Theorem 7 (`non_vacuous_and_tight`, **IEEE-754 Float64 Representability & Strict `yukonScore` Order Across Unified All-Tables Tiers**):
Strict `yukonScore` ordering and exact IEEE-754 double-precision integer representability
(`yukonScore K minutes < 2^53 - 1`) across all unified all-tables, transition, and coupled tiers
for every `minutes : Nat`, plus the sharp uniform ceiling equivalence
`yukonScore K 9999 < 2^53 - 1 ↔ K < 900_719_925_474`. -/
theorem unified_all_tables_yukonScore_strict_order_and_float64_exact_non_vacuous_and_tight
    (minutes K : Nat) :
    yukonScore transitionSlope3K minutes < yukonScore unifiedAllTablesSlope3UnrolledK minutes ∧
    yukonScore unifiedAllTablesSlope3UnrolledK minutes < yukonScore unifiedAllTablesSlope3K minutes ∧
    yukonScore unifiedAllTablesSlope3K minutes < yukonScore blockVsTxSlope6K minutes ∧
    yukonScore transitionSlope6K minutes < yukonScore unifiedAllTablesSlope6UnrolledK minutes ∧
    yukonScore unifiedAllTablesSlope6UnrolledK minutes < yukonScore unifiedAllTablesSlope6K minutes ∧
    yukonScore unifiedAllTablesSlope6K minutes < yukonScore blockVsTxSlope12K minutes ∧
    yukonScore unifiedAllTablesSlope3UnrolledK minutes < 2 ^ 53 - 1 ∧
    yukonScore unifiedAllTablesSlope3K minutes < 2 ^ 53 - 1 ∧
    yukonScore unifiedAllTablesSlope6UnrolledK minutes < 2 ^ 53 - 1 ∧
    yukonScore unifiedAllTablesSlope6K minutes < 2 ^ 53 - 1 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hy := twenty_six_tier_yukonScore_strict_order_and_float64_exact_non_vacuous_and_tight minutes K
  have hu := unified_all_tables_and_multi_addr_tiers_coincide_and_fit_under_yukon_non_vacuous_and_tight 0 minutes
  rw [hu.2.1, hu.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.1]
  exact ⟨hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1,
    hy.2.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.2.2.1,
    hy.2.2.2.2.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hy.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hy.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`, **`claim.json ≤ 128`-Byte Audit Across All 4 Unified All-Tables Tiers**):
Exact UTF-8 byte sizes (`29` bytes for `{"claimed_k": "..."}` and `19` bytes for `{"K": ...}`),
`validFiniteClaim` conformance for `unifiedAllTablesSlope3UnrolledK`, `unifiedAllTablesSlope3K`,
`unifiedAllTablesSlope6UnrolledK`, and `unifiedAllTablesSlope6K`, and sharp `128`-byte vs `129`-byte
`checkSubmissionLimits` boundary. -/
theorem unified_all_tables_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight :
    claimJsonMultiAddrMergeSlope3Unrolled.utf8ByteSize = 29 ∧
    claimJsonMultiAddrMergeSlope3.utf8ByteSize = 29 ∧
    claimJsonMultiAddrMergeSlope6Unrolled.utf8ByteSize = 29 ∧
    claimJsonMultiAddrMergeSlope6.utf8ByteSize = 29 ∧
    verifierJsonMultiAddrMergeSlope3Unrolled.utf8ByteSize = 19 ∧
    verifierJsonMultiAddrMergeSlope3.utf8ByteSize = 19 ∧
    verifierJsonMultiAddrMergeSlope6Unrolled.utf8ByteSize = 19 ∧
    verifierJsonMultiAddrMergeSlope6.utf8ByteSize = 19 ∧
    validFiniteClaim unifiedAllTablesSlope3UnrolledK claimJsonMultiAddrMergeSlope3Unrolled = true ∧
    validFiniteClaim unifiedAllTablesSlope3K claimJsonMultiAddrMergeSlope3 = true ∧
    validFiniteClaim unifiedAllTablesSlope6UnrolledK claimJsonMultiAddrMergeSlope6Unrolled = true ∧
    validFiniteClaim unifiedAllTablesSlope6K claimJsonMultiAddrMergeSlope6 = true ∧
    validFiniteClaim unifiedAllTablesSlope3UnrolledK verifierJsonMultiAddrMergeSlope3Unrolled = true ∧
    validFiniteClaim unifiedAllTablesSlope3K verifierJsonMultiAddrMergeSlope3 = true ∧
    validFiniteClaim unifiedAllTablesSlope6UnrolledK verifierJsonMultiAddrMergeSlope6Unrolled = true ∧
    validFiniteClaim unifiedAllTablesSlope6K verifierJsonMultiAddrMergeSlope6 = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonMultiAddrMergeSlope3Unrolled.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 (MAX_CLAIM_BYTES + 1) false false true = false := by
  have hc := twenty_six_tier_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
  have hu := unified_all_tables_and_multi_addr_tiers_coincide_and_fit_under_yukon_non_vacuous_and_tight 0 0
  rw [hu.2.1, hu.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.1]
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
    hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`, **Direct `InitE.Certificate` Bridges for `unifiedAllTablesSlope3UnrolledK`, `unifiedAllTablesSlope3K`, `unifiedAllTablesSlope6UnrolledK`, and `unifiedAllTablesSlope6K`**):
Proves that uniform target non-`.timeOut` at `unifiedAllTablesSlope3UnrolledK = 408_348_416_306` yields
`InitE.Certificate` at that budget and lifts monotonically across `unifiedAllTablesSlope3K = 408_348_430_106`,
`blockVsTxSlope6K = 428_692_019_192`, `bs32JointSlope3UnrolledK = 459_244_476_749`,
`bs32JointSlope3K = 459_244_490_549`, `coupledSlope6UnrolledK = 785_125_394_708`,
`coupledSlope6K = 785_125_408_508`, `transitionSlope6UnrolledK = 810_291_194_708`,
`transitionSlope6K = 810_291_208_508`, `unifiedAllTablesSlope6UnrolledK = 816_696_823_280`,
`unifiedAllTablesSlope6K = 816_696_837_080`, `blockVsTxSlope12K = 857_384_015_252`, and `.infinity`. -/
theorem unified_all_tables_slope3_and_slope6_certificates_and_margins_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_unified_s3_unrolled : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          unifiedAllTablesSlope3UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope3UnrolledK) (.finite unifiedAllTablesSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope3K) (.finite unifiedAllTablesSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope6K) (.finite blockVsTxSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3UnrolledK) (.finite bs32JointSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coupledSlope6UnrolledK) (.finite coupledSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledSlope6K) (.finite coupledSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope6UnrolledK) (.finite transitionSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK transitionSlope6K) (.finite transitionSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope6UnrolledK) (.finite unifiedAllTablesSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope6K) (.finite unifiedAllTablesSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope12K) (.finite blockVsTxSlope12K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    validFiniteClaim unifiedAllTablesSlope3UnrolledK claimJsonMultiAddrMergeSlope3Unrolled = true ∧
    validFiniteClaim unifiedAllTablesSlope3K claimJsonMultiAddrMergeSlope3 = true ∧
    validFiniteClaim unifiedAllTablesSlope6UnrolledK claimJsonMultiAddrMergeSlope6Unrolled = true ∧
    validFiniteClaim unifiedAllTablesSlope6K claimJsonMultiAddrMergeSlope6 = true ∧
    yukonScore unifiedAllTablesSlope3K minutes - yukonScore unifiedAllTablesSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore unifiedAllTablesSlope6K minutes - yukonScore unifiedAllTablesSlope6UnrolledK minutes = 138_000_000 ∧
    unifiedAllTablesSlope3UnrolledK < unifiedAllTablesSlope3K ∧
    unifiedAllTablesSlope6UnrolledK < unifiedAllTablesSlope6K ∧
    unifiedAllTablesSlope6K < 900_719_925_474 := by
  have hu := unified_all_tables_and_multi_addr_tiers_coincide_and_fit_under_yukon_non_vacuous_and_tight 0 minutes
  rw [hu.2.1] at not_timeOut_unified_s3_unrolled
  rw [hu.2.1, hu.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.1]
  exact multi_addr_merge_slope3_and_slope6_certificates_and_margins_non_vacuous_and_tight
    oracles c depth minutes hlab compiled depthBound not_timeOut_unified_s3_unrolled

/-- Theorem 10 (`non_vacuous_and_tight`, **Master 26-Tier Unified 5-Variable All-Tables Envelope, Unconditional `PanToStackToLab` & `StackRemoveAndNames` Campaign Certificate**):
Simultaneously unites:
- All 26 `InitE.Certificate (baselineWithFiniteK K) (.finite K)` tiers in `twentySixTierHierarchy`
  (including `unifiedAllTablesSlope3UnrolledK`, `unifiedAllTablesSlope3K`,
  `unifiedAllTablesSlope6UnrolledK`, `unifiedAllTablesSlope6K`, plus `blockVsTxSlope12K` and `.infinity`),
- The 5-variable $(D, R, A, C, W)$ coupled and merge envelopes (`F D R A C W ≤ 95_238_095_238`,
  `G D R A C W ≤ 100_000_000_000`, `kPanUnifiedAllTables = 136_116_135_658`,
  `6 * kPanUnifiedAllTables < yukon`, `k * kPanUnifiedAllTables < yukon ↔ k ≤ 6`) from
  `GuestUnifiedAllTablesMasterEnvelope`,
- The unconditional `panToStackNames_bodies_StackNoSt_unconditional`, `panToLabSection_unconditional`,
  and `flatten_storeConsts_empty` theorems from `PanToStackToLabUnconditionalNoStoreConsts` (no
  `WordNoStubCall` assumption needed), and
- Purified `.Solver` path admission (`0` `Bounded*` imports). -/
theorem master_unified_all_tables_and_unconditional_stack_to_lab_campaign_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (panProg : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (cAsm : AsmConfigExact width) (perf j tail : Bool)
    (info f : Spt Nat) (bd : BitVec width × BitVec width) (ptr s b sid next : Nat)
    (stub : Option Nat) (cs bs : List Nat)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config)
    (depth minutes D R A C W Tloc Tlin k : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (hF : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hG : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup)
    (hlin : Tlin ≤ mergeLin)
    (not_timeOut_u128 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    twentySixTierHierarchy.length = 26 ∧
    twentySixTierHierarchy.Pairwise (· < ·) ∧
    (∀ K ∈ twentySixTierHierarchy, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope3UnrolledK) (.finite unifiedAllTablesSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope3K) (.finite unifiedAllTablesSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope6UnrolledK) (.finite unifiedAllTablesSlope6UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope6K) (.finite unifiedAllTablesSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope12K) (.finite blockVsTxSlope12K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    42 * F D R A C W ≤ S * S ∧
    F D R A C W ≤ 95_238_095_238 ∧
    40 * G D R A C W ≤ S * S ∧
    G D R A C W ≤ 100_000_000_000 ∧
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables ∧
    kPanUnifiedAllTables = 136_116_135_658 ∧
    kPanUnifiedAllTables = kPanMerge ∧
    kPanUnifiedAllTables = kPanMultiAddrMerge ∧
    6 * kPanUnifiedAllTables < yukon ∧
    (k * kPanUnifiedAllTables < yukon ↔ k ≤ 6) ∧
    yukon - 6 * kPanUnifiedAllTables = 84_023_111_526 ∧
    (∀ y ∈ (compileNative cAsm perf (WordToWord.compile wc cAsm
        (panToWordCompileProgHOL arch panProg)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) ∧
    (∀ y ∈ (compileNative cAsm perf (WordToWord.compile wc cAsm
        (panToWordCompileProgHOL arch panProg)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
    StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
      (.list [], false, next) ∧
    yukonScore unifiedAllTablesSlope3K minutes - yukonScore unifiedAllTablesSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore unifiedAllTablesSlope6K minutes - yukonScore unifiedAllTablesSlope6UnrolledK minutes = 138_000_000 ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedUnifiedAllTablesAndStackNamesSynth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedUnifiedAllTablesAndStackNamesSynth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hcert_u128 := exact_keccak_128_unrolled_certificate
    oracles c depth hlab compiled depthBound not_timeOut_u128
  have hchain := twenty_six_tier_certificate_monotonicity_chain_non_vacuous_and_tight
    (Nat.le_refl exactKeccak128UnrolledK) hcert_u128 hcert_u128
  have h26 := twenty_six_tier_hierarchy_strict_ordering_and_gaps_non_vacuous_and_tight
  have hu := unified_all_tables_and_multi_addr_tiers_coincide_and_fit_under_yukon_non_vacuous_and_tight 0 minutes
  have hgm := unified_five_var_merge_envelope_and_kPanUnified_master_non_vacuous_and_tight 0 0 0 D R A C W Tloc Tlin k hG hloc hlin
  have hcert_u3u : InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope3UnrolledK)
      (.finite unifiedAllTablesSlope3UnrolledK) := by
    rw [hu.2.1]; exact hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert_u3 : InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope3K)
      (.finite unifiedAllTablesSlope3K) := by
    rw [hu.2.2.1]; exact hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert_u6u : InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope6UnrolledK)
      (.finite unifiedAllTablesSlope6UnrolledK) := by
    rw [hu.2.2.2.2.1]; exact hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert_u6 : InitE.Certificate (baselineWithFiniteK unifiedAllTablesSlope6K)
      (.finite unifiedAllTablesSlope6K) := by
    rw [hu.2.2.2.2.2.1]; exact hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨h26.1, h26.2.1, hchain.2.1,
    hcert_u3u, hcert_u3, hcert_u6u, hcert_u6,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hchain.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    unified_five_var_coupled_envelope D R A C W hF,
    unified_coupled_le D R A C W hF,
    hgm.2.1,
    hgm.2.2.1,
    hgm.2.2.2.2.2.2.2.1,
    hgm.2.2.2.2.1,
    hgm.2.2.2.2.2.1,
    hgm.2.2.2.2.2.2.1,
    hgm.2.2.2.2.2.2.2.2.1,
    hgm.2.2.2.2.2.2.2.2.2.1,
    hgm.2.2.2.2.2.2.2.2.2.2,
    panToStackNames_bodies_StackNoSt_unconditional arch panProg wc cAsm perf info j bd ptr f,
    panToLabSection_unconditional arch panProg wc cAsm perf info j bd ptr f,
    flatten_storeConsts_empty tail s b stub sid next cs bs,
    hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    by decide,
    by decide,
    rfl⟩

#print axioms unified_five_var_coupled_envelope_and_tight_vertex_non_vacuous_and_tight
#print axioms unified_five_var_merge_envelope_and_kPanUnified_master_non_vacuous_and_tight
#print axioms unconditional_pan_to_stack_to_lab_no_store_consts_chain_non_vacuous_and_tight
#print axioms unified_all_tables_and_multi_addr_tiers_coincide_and_fit_under_yukon_non_vacuous_and_tight
#print axioms twenty_six_tier_hierarchy_with_unified_all_tables_strict_ordering_non_vacuous_and_tight
#print axioms unified_all_tables_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
#print axioms unified_all_tables_yukonScore_strict_order_and_float64_exact_non_vacuous_and_tight
#print axioms unified_all_tables_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
#print axioms unified_all_tables_slope3_and_slope6_certificates_and_margins_non_vacuous_and_tight
#print axioms master_unified_all_tables_and_unconditional_stack_to_lab_campaign_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedUnifiedAllTablesAndStackNamesSynth
