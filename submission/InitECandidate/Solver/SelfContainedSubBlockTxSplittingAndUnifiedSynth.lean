import InitECandidate.Solver.GuestSubBlockTxSplittingDominance
import InitECandidate.Solver.PanToLabSectionAndStackRemoveClock
import InitECandidate.Solver.SelfContainedUnifiedAllTablesAndStackNamesSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SelfContainedSubBlockTxSplittingAndUnifiedSynth` — Self-Contained Sub-Block Multi-Tx Splitting Dominance, Unconditional `PanToLab` Section Cleanliness & 26-Tier Unified All-Tables Synthesis (`W5_99`)

This module has **0 imports from `InitECandidate.Proofs.Bounded*`** in its transitive closure and
unifies:
1. The sub-block multi-transaction splitting dominance and `state_fresh_tx` absorption bounds from
   `GuestSubBlockTxSplittingDominance` (`10/10` tight):
   - `split_local_le` (`(l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l)`),
   - `split_strict` (`localCost (1,1,1,1,1) + localCost (1,1,1,1,1) = 40 < 80 = localCost (2,2,2,2,2)`),
   - `prefix_le` (`prefixCost l P ≤ (P + (l.map Prod.fst).sum) * (l.map Prod.snd).sum`),
   - `prefix_tight` and `prefix_strict`,
   - `reset_bound`, `reset_absorbed` (`txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666`),
   - `max_tx_reset` (`txMinUnits * 16666 ≤ 2000000 ∧ 2000000 < txMinUnits * 16667 ∧ txResetTicks * 16666 = 3333200`),
   - `access_list_key_cost` (`(2100 - 100) + 128 * 16 = 4048 ∧ 2000 ≤ 4048`), and
   - `split_master` (`(l.map localCost).sum ≤ bound ∧ 6 * kPanUnifiedAllTables < yukon ∧ kPanUnifiedAllTables = 136116135658`).
2. The unconditional `StackToLab.compile` section cleanliness and `StackRemove` no-`storeConsts`
   expansion theorems from `PanToLabSectionAndStackRemoveClock` (`13/13` tight):
   - `panToLab_sections_unconditional` (every section in `StackToLab.compile` of the `WordToStack`
     output of any Pancake program satisfies `IsStubLabel s.sectionId = true ∨ CleanSection s`),
   - `stackToLab_compile_ids` (`(StackToLab.compile sc dc mh sp off L).map (·.sectionId) = [0, 1, 2, gcStubLocation] ++ L.map Prod.fst`),
   - `stackRemove_no_storeConsts_branch`, `stackRemove_branch_tight`, `isStubLabel_storeConsts`, and `isStubLabel_tight`.
3. The 26-tier synthesis and 5-variable $(D, R, A, C, W)$ all-tables envelope from
   `SelfContainedUnifiedAllTablesAndStackNamesSynth` (`10/10` tight), proving that multi-transaction
   splitting dominance + the 5-variable all-tables envelope + the unconditional compiler chain to
   `LabLang` sections preserve all 26 portfolio tiers under Yukon (`< 900_719_925_474`),
   `yukonScore` monotonicity, `claim.json ≤ 128`-byte compliance, and `InitE.Certificate` lifting
   (`0 sorryAx`, `10/10 non_vacuous_and_tight`).
-/

namespace InitECandidate.Solver.SelfContainedSubBlockTxSplittingAndUnifiedSynth

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
open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock
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
open InitECandidate.Solver.GuestSubBlockTxSplittingDominance
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
open InitECandidate.Solver.SelfContainedUnifiedAllTablesAndStackNamesSynth
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

/-! ## Section 1: Sub-Block Multi-Tx Splitting Aliases Under `kPanUnifiedAllTables` -/

/-- Alias for `split_master`: any multi-transaction splitting bounded by `bound` satisfies
`(l.map localCost).sum ≤ bound ∧ 6 * kPanUnifiedAllTables < yukon ∧ kPanUnifiedAllTables = 136116135658`. -/
theorem subblock_master (l : List (Nat × Nat × Nat × Nat × Nat)) (bound : Nat)
    (hb : localCost (sD l, sR l, sA l, sC l, sW l) ≤ bound) :
    (l.map localCost).sum ≤ bound ∧ 6 * kPanUnifiedAllTables < yukon ∧
      kPanUnifiedAllTables = 136116135658 :=
  split_master l bound hb

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`, **Multi-Transaction Local & Prefix Sub-Additivity (`split_local_le`, `split_strict`, `prefix_le`, `prefix_tight`, `prefix_strict`)**):
Unites `split_local_le`, `split_strict`, `prefix_le`, `prefix_tight`, and `prefix_strict` from
`GuestSubBlockTxSplittingDominance`:
for any transaction list `l`, `(l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l)`,
with strict inequality `40 < 80` on two unit transactions; and for any prefix-probe schedule `lP`,
`prefixCost lP P ≤ (P + (lP.map Prod.fst).sum) * (lP.map Prod.snd).sum`, tight for one transaction
and strict (`3 < 4`) for two unit transactions. -/
theorem sub_block_tx_splitting_local_and_prefix_dominance_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat)) (lP : List (Nat × Nat)) (P D W : Nat) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    (localCost (1, 1, 1, 1, 1) + localCost (1, 1, 1, 1, 1) = 40 ∧ localCost (2, 2, 2, 2, 2) = 80) ∧
    prefixCost lP P ≤ (P + (lP.map Prod.fst).sum) * (lP.map Prod.snd).sum ∧
    prefixCost [(D, W)] 0 = D * W ∧
    (prefixCost [(1, 1), (1, 1)] 0 = 3 ∧ 3 < (0 + 2) * 2) ∧
    ¬ (localCost (2, 2, 2, 2, 2) ≤ localCost (1, 1, 1, 1, 1) + localCost (1, 1, 1, 1, 1)) := by
  exact ⟨split_local_le l,
    split_strict,
    prefix_le lP P,
    prefix_tight D W,
    prefix_strict,
    by decide⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **`state_fresh_tx` Reset Absorption Under `base_regular_gas = 12_000` & Multi-Tx Master Dominance Under `kPanUnifiedAllTables = 136_116_135_658`**):
Unites `reset_bound`, `reset_absorbed`, `max_tx_reset`, `access_list_key_cost`, `subblock_master`,
and the 5-variable $(D, R, A, C, W)$ merge envelope from `GuestUnifiedAllTablesMasterEnvelope`:
every per-tx `state_fresh_tx` reset costs `≤ txResetTicks = 200` ticks, is absorbed inside the
`18 * (12_000 * T)` linear gas envelope for all `T` with `txMinUnits * T ≤ 2_000_000` (`T ≤ 16_666`),
and the concentrated 5-variable bound `G (sD l) (sR l) (sA l) (sC l) (sW l) ≤ 100_000_000_000`
dominates `(l.map localCost).sum` under `kPanUnifiedAllTables = 136_116_135_658`. -/
theorem sub_block_reset_absorbed_and_unified_all_tables_master_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat)) (T Tloc Tlin k : Nat)
    (hT : txMinUnits * T ≤ 2000000)
    (hG : 20 * (sD l + sR l + sA l) + 6 * sA l + 21 * sC l + (sW l + (sD l + sR l + sA l)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    8 * (6 + 1 + (1 + 64 / 32 + 3)) + 2 ≤ txResetTicks ∧
    (txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) ∧
    (txMinUnits * 16666 ≤ 2000000 ∧ 2000000 < txMinUnits * 16667 ∧ txResetTicks * 16666 = 3333200) ∧
    ((2100 - 100) + 128 * 16 = 4048 ∧ 2000 ≤ 4048) ∧
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    40 * G (sD l) (sR l) (sA l) (sC l) (sW l) ≤ S * S ∧
    G (sD l) (sR l) (sA l) (sC l) (sW l) ≤ 100_000_000_000 ∧
    linear + Tloc + G (sD l) (sR l) (sA l) (sC l) (sW l) + Tlin ≤ kPanUnifiedAllTables ∧
    6 * kPanUnifiedAllTables < yukon ∧
    kPanUnifiedAllTables = 136116135658 ∧
    (k * kPanUnifiedAllTables < yukon ↔ k ≤ 6) ∧
    yukon - 6 * kPanUnifiedAllTables = 84_023_111_526 := by
  have hsub := subblock_master l (localCost (sD l, sR l, sA l, sC l, sW l)) (Nat.le_refl _)
  have hgm := unified_five_var_merge_envelope_and_kPanUnified_master_non_vacuous_and_tight
    0 0 0 (sD l) (sR l) (sA l) (sC l) (sW l) Tloc Tlin k hG hloc hlin
  exact ⟨reset_bound,
    reset_absorbed T hT,
    max_tx_reset,
    access_list_key_cost,
    hsub.1,
    hgm.2.1,
    hgm.2.2.1,
    hgm.2.2.2.2.2.2.2.1,
    hsub.2.1,
    hsub.2.2,
    hgm.2.2.2.2.2.2.2.2.2.1,
    hgm.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Unconditional `PanToLabSectionAndStackRemoveClock` Section Cleanliness (`panToLab_sections_unconditional`, `stackToLab_compile_ids`, `stackRemove_no_storeConsts_branch`)**):
Unites `panToLab_sections_unconditional`, `stackToLab_compile_ids`,
`stackRemove_no_storeConsts_branch`, `stackRemove_branch_tight`, `isStubLabel_storeConsts`, and
`isStubLabel_tight` from `PanToLabSectionAndStackRemoveClock`:
for any Pancake program `prog`, every section produced by `StackToLab.compile` satisfies
`IsStubLabel s.sectionId = true ∨ CleanSection s`, the section IDs equal
`[0, 1, 2, gcStubLocation] ++ L.map Prod.fst`, and `StackRemove.comp` on any `StackNoSt` tree
preserves `StackNoSt = true` and `FlattenVisitsSt = false` (whereas an explicit `.storeConsts`
leaf violates both). -/
theorem unconditional_pan_to_lab_sections_and_stack_remove_clock_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf j : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp ptr : Nat)
    (off bd : BitVec width × BitVec width)
    (L : List (Nat × HolProg width))
    (p : HolProg width) (hp : StackNoSt p = true) :
    (∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
      IsStubLabel s.sectionId = true ∨ CleanSection s) ∧
    (StackToLab.compile sc dc mh sp off L).map (·.sectionId) =
      [0, 1, 2, gcStubLocation] ++ L.map Prod.fst ∧
    (StackNoSt (StackRemove.comp j bd ptr p) = true ∧ FlattenVisitsSt p = false) ∧
    (StackNoSt (.storeConsts 3 4 none : HolProg width) = false ∧
      FlattenVisitsSt (.storeConsts 3 4 none : HolProg width) = true) ∧
    IsStubLabel storeConstsStubLocation = true ∧
    IsStubLabel 64 = false := by
  exact ⟨panToLab_sections_unconditional arch prog wc ac perf sc dc mh sp off,
    stackToLab_compile_ids sc dc mh sp off L,
    stackRemove_no_storeConsts_branch j bd ptr p hp,
    stackRemove_branch_tight,
    isStubLabel_storeConsts,
    isStubLabel_tight⟩

/-- Theorem 4 (`non_vacuous_and_tight`, **5-Variable Coupled (`F ≤ 95_238_095_238`) & Merge (`G ≤ 100_000_000_000`) All-Tables Envelopes with Multi-Tx Dominance**):
Unites `unified_five_var_coupled_envelope_and_tight_vertex_non_vacuous_and_tight` and
`subblock_master`: for any multi-tx list `l` whose aggregate `(sD l, sR l, sA l, sC l, sW l)`
satisfies the coupled budget `21D + 20R + 26A + 21C + W ≤ S`, both the coupled envelope
`F ≤ 95_238_095_238` and the merge envelope `G ≤ 100_000_000_000` hold simultaneously alongside
`(l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l)`. -/
theorem unified_five_var_coupled_and_merge_with_sub_block_dominance_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat)) (D R A C W : Nat)
    (hF : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hG : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    42 * F D R A C W ≤ S * S ∧
    F D R A C W ≤ 95_238_095_238 ∧
    (21 * 47619 + 20 * 0 + 26 * 0 + 21 * 0 + 1000001 = S ∧ F 47619 0 0 0 1000001 = 95238095238) ∧
    (F 0 0 0 95238 0 = 9070276644 ∧ 9070276644 < 95238095238) ∧
    40 * G D R A C W ≤ S * S ∧
    G D R A C W ≤ 100_000_000_000 ∧
    (G 50000 0 0 0 950000 = 100000000000 ∧ G 2000 48000 0 0 950000 = 100000000000) ∧
    ¬ (F 47619 0 0 0 1000001 ≤ 95_238_095_237) ∧
    ¬ (G 50000 0 0 0 950000 ≤ 99_999_999_999) := by
  have hc := unified_five_var_coupled_envelope_and_tight_vertex_non_vacuous_and_tight D R A C W hF
  have hm := unified_merge_tight
  exact ⟨split_local_le l,
    hc.1,
    hc.2.1,
    hc.2.2.1,
    hc.2.2.2.1,
    unified_five_var_merge_envelope D R A C W hG,
    unified_merge_le D R A C W hG,
    ⟨hm.1, hm.2.1⟩,
    hc.2.2.2.2,
    by decide⟩

/-- Theorem 5 (`non_vacuous_and_tight`, **Multi-Tx Sub-Block Splitting & Unified All-Tables Target Tiers Under Yukon (`< 900_719_925_474`)**):
Proves that for any transaction list `l`, `(l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l)`
and all 4 unified all-tables target tiers (`unifiedAllTablesSlope3UnrolledK = 408_348_416_306`,
`unifiedAllTablesSlope3K = 408_348_430_106`, `unifiedAllTablesSlope6UnrolledK = 816_696_823_280`,
`unifiedAllTablesSlope6K = 816_696_837_080`) coincide with the multi-address merge tiers and sit
strictly inside `twentySixTierHierarchy` below `yukonFloat64MaxK = 900_719_925_474`. -/
theorem sub_block_and_unified_all_tables_tiers_under_yukon_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat)) (k minutes : Nat) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    6 * kPanUnifiedAllTables < yukon ∧
    kPanUnifiedAllTables = 136116135658 ∧
    unifiedAllTablesSlope3UnrolledK = multiAddrMergeSlope3UnrolledK ∧
    unifiedAllTablesSlope3K = multiAddrMergeSlope3K ∧
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
  have hsub := subblock_master l (localCost (sD l, sR l, sA l, sC l, sW l)) (Nat.le_refl _)
  have hu := unified_all_tables_and_multi_addr_tiers_coincide_and_fit_under_yukon_non_vacuous_and_tight k minutes
  exact ⟨hsub.1, hsub.2.1, hsub.2.2,
    hu.2.1, hu.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 6 (`non_vacuous_and_tight`, **Strict Total Ordering Across the 26-Tier Hierarchy (`twentySixTierHierarchy`) with Sub-Block Splitting & Unified All-Tables Bounds**):
Establishes `twentySixTierHierarchy.length = 26`, `twentySixTierHierarchy.Pairwise (· < ·)`,
membership of all 4 unified all-tables tiers in `twentySixTierHierarchy`, the uniform Yukon ceiling
`< 900_719_925_474`, and `state_fresh_tx` reset absorption `txResetTicks * 16666 = 3_333_200`. -/
theorem twenty_six_tier_hierarchy_with_sub_block_and_unified_bounds_non_vacuous_and_tight :
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
    blockVsTxSlope12K < 900_719_925_474 ∧
    txMinUnits * 16666 ≤ 2000000 ∧
    2000000 < txMinUnits * 16667 ∧
    txResetTicks * 16666 = 3333200 := by
  have h26 := twenty_six_tier_hierarchy_with_unified_all_tables_strict_ordering_non_vacuous_and_tight
  have hm := max_tx_reset
  exact ⟨h26.1, h26.2.1, h26.2.2.1, h26.2.2.2.1, h26.2.2.2.2.1, h26.2.2.2.2.2.1, h26.2.2.2.2.2.2.1,
    h26.2.2.2.2.2.2.2.1, h26.2.2.2.2.2.2.2.2.1, h26.2.2.2.2.2.2.2.2.2.1,
    h26.2.2.2.2.2.2.2.2.2.2.1, h26.2.2.2.2.2.2.2.2.2.2.2.1,
    h26.2.2.2.2.2.2.2.2.2.2.2.2.1, h26.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hm.1, hm.2.1, hm.2.2⟩

/-- Theorem 7 (`non_vacuous_and_tight`, **Bootstrap Decompositions, Multi-Tx Aggregate Dominance & 1-Tick Tightness Across Unified All-Tables Tiers**):
Establishes exact `(bootstrapSteps - copyLoopSavedSteps) = 9_332` and `bootstrapSteps = 23_132`
decompositions for `unifiedAllTablesSlope3UnrolledK`, `unifiedAllTablesSlope3K`,
`unifiedAllTablesSlope6UnrolledK`, and `unifiedAllTablesSlope6K`, together with aggregate multi-tx
post-bootstrap dominance and sharp 1-tick tightness boundaries (`¬ K ≤ K - 1`). -/
theorem sub_block_and_unified_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat)) (Tloc Tlin : Nat)
    (h : 20 * (sD l + sR l + sA l) + 6 * sA l + 21 * sC l + (sW l + (sD l + sR l + sA l)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    bootstrapSteps - copyLoopSavedSteps = 9_332 ∧
    bootstrapSteps = 23_132 ∧
    unifiedAllTablesSlope3UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanUnifiedAllTables ∧
    unifiedAllTablesSlope3K = bootstrapSteps + 3 * kPanUnifiedAllTables ∧
    unifiedAllTablesSlope6UnrolledK = (bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables ∧
    unifiedAllTablesSlope6K = bootstrapSteps + 6 * kPanUnifiedAllTables ∧
    (bootstrapSteps - copyLoopSavedSteps) + 3 * (linear + Tloc + G (sD l) (sR l) (sA l) (sC l) (sW l) + Tlin) ≤ unifiedAllTablesSlope3UnrolledK ∧
    bootstrapSteps + 3 * (linear + Tloc + G (sD l) (sR l) (sA l) (sC l) (sW l) + Tlin) ≤ unifiedAllTablesSlope3K ∧
    (bootstrapSteps - copyLoopSavedSteps) + 6 * (linear + Tloc + G (sD l) (sR l) (sA l) (sC l) (sW l) + Tlin) ≤ unifiedAllTablesSlope6UnrolledK ∧
    bootstrapSteps + 6 * (linear + Tloc + G (sD l) (sR l) (sA l) (sC l) (sW l) + Tlin) ≤ unifiedAllTablesSlope6K ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanUnifiedAllTables ≤ unifiedAllTablesSlope3UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 3 * kPanUnifiedAllTables ≤ unifiedAllTablesSlope3K - 1) ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables ≤ unifiedAllTablesSlope6UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 6 * kPanUnifiedAllTables ≤ unifiedAllTablesSlope6K - 1) := by
  have hb := unified_all_tables_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
    (sD l) (sR l) (sA l) (sC l) (sW l) Tloc Tlin h hloc hlin
  exact ⟨split_local_le l, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`, **IEEE-754 Float64 Representability, Strict `yukonScore` Order & `claim.json ≤ 128`-Byte Compliance Across All 4 Unified All-Tables Tiers**):
Unites `unified_all_tables_yukonScore_strict_order_and_float64_exact_non_vacuous_and_tight` and
`unified_all_tables_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight`:
strict `yukonScore` ordering, exact Float64 representability (`< 2^53 - 1`), sharp Yukon threshold
`yukonScore K 9999 < 2^53 - 1 ↔ K < 900_719_925_474`, and `validFiniteClaim` + `128`-byte vs `129`-byte
`checkSubmissionLimits` boundary across all 4 unified all-tables tiers. -/
theorem sub_block_and_unified_yukonScore_and_claim_json_audit_non_vacuous_and_tight
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
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) ∧
    claimJsonMultiAddrMergeSlope3Unrolled.utf8ByteSize = 29 ∧
    claimJsonMultiAddrMergeSlope3.utf8ByteSize = 29 ∧
    claimJsonMultiAddrMergeSlope6Unrolled.utf8ByteSize = 29 ∧
    claimJsonMultiAddrMergeSlope6.utf8ByteSize = 29 ∧
    validFiniteClaim unifiedAllTablesSlope3UnrolledK claimJsonMultiAddrMergeSlope3Unrolled = true ∧
    validFiniteClaim unifiedAllTablesSlope3K claimJsonMultiAddrMergeSlope3 = true ∧
    validFiniteClaim unifiedAllTablesSlope6UnrolledK claimJsonMultiAddrMergeSlope6Unrolled = true ∧
    validFiniteClaim unifiedAllTablesSlope6K claimJsonMultiAddrMergeSlope6 = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonMultiAddrMergeSlope3Unrolled.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 (MAX_CLAIM_BYTES + 1) false false true = false := by
  have hy := unified_all_tables_yukonScore_strict_order_and_float64_exact_non_vacuous_and_tight minutes K
  have hc := unified_all_tables_claim_json_valid_and_le_128_bytes_non_vacuous_and_tight
  exact ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1,
    hy.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.1,
    hy.2.2.2.2.2.2.2.2.2.2,
    hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`, **Direct `InitE.Certificate` Bridges for `unifiedAllTablesSlope3UnrolledK`, `unifiedAllTablesSlope3K`, `unifiedAllTablesSlope6UnrolledK`, and `unifiedAllTablesSlope6K` with Sub-Block Splitting Dominance**):
Proves that uniform target non-`.timeOut` at `unifiedAllTablesSlope3UnrolledK = 408_348_416_306` yields
`InitE.Certificate` at that budget and lifts monotonically across `unifiedAllTablesSlope3K = 408_348_430_106`,
`blockVsTxSlope6K = 428_692_019_192`, `bs32JointSlope3UnrolledK = 459_244_476_749`,
`bs32JointSlope3K = 459_244_490_549`, `coupledSlope6UnrolledK = 785_125_394_708`,
`coupledSlope6K = 785_125_408_508`, `transitionSlope6UnrolledK = 810_291_194_708`,
`transitionSlope6K = 810_291_208_508`, `unifiedAllTablesSlope6UnrolledK = 816_696_823_280`,
`unifiedAllTablesSlope6K = 816_696_837_080`, `blockVsTxSlope12K = 857_384_015_252`, and `.infinity`,
together with multi-tx sub-additivity `(l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l)`. -/
theorem sub_block_and_unified_all_tables_certificates_and_margins_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat))
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
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
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
  exact ⟨split_local_le l,
    unified_all_tables_slope3_and_slope6_certificates_and_margins_non_vacuous_and_tight
      oracles c depth minutes hlab compiled depthBound not_timeOut_unified_s3_unrolled⟩

/-- Theorem 10 (`non_vacuous_and_tight`, **Master 26-Tier Sub-Block Multi-Tx Splitting Dominance, 5-Variable All-Tables Envelope & Unconditional `PanToLab` Section Cleanliness Campaign Certificate**):
Simultaneously unites:
- All 26 `InitE.Certificate (baselineWithFiniteK K) (.finite K)` tiers in `twentySixTierHierarchy`
  (including `unifiedAllTablesSlope3UnrolledK`, `unifiedAllTablesSlope3K`,
  `unifiedAllTablesSlope6UnrolledK`, `unifiedAllTablesSlope6K`, plus `blockVsTxSlope12K` and `.infinity`),
- Multi-transaction sub-block splitting dominance (`split_local_le`, `split_strict`, `prefix_le`,
  `reset_absorbed`, `max_tx_reset`, `subblock_master` under `kPanUnifiedAllTables = 136_116_135_658`)
  from `GuestSubBlockTxSplittingDominance`,
- The 5-variable $(D, R, A, C, W)$ coupled and merge envelopes (`F D R A C W ≤ 95_238_095_238`,
  `G D R A C W ≤ 100_000_000_000`, `kPanUnifiedAllTables = 136_116_135_658`,
  `6 * kPanUnifiedAllTables < yukon`, `k * kPanUnifiedAllTables < yukon ↔ k ≤ 6`) from
  `GuestUnifiedAllTablesMasterEnvelope`,
- Unconditional `StackToLab.compile` section cleanliness (`panToLab_sections_unconditional`,
  `stackToLab_compile_ids`, `stackRemove_no_storeConsts_branch`) from
  `PanToLabSectionAndStackRemoveClock`, and
- Purified `.Solver` path admission (`0` `Bounded*` imports). -/
theorem master_sub_block_tx_splitting_pan_to_lab_sections_and_unified_campaign_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (panProg : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (cAsm : AsmConfigExact width) (perf j : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp ptr : Nat)
    (off bd : BitVec width × BitVec width)
    (L : List (Nat × HolProg width))
    (p : HolProg width) (hp : StackNoSt p = true)
    (l : List (Nat × Nat × Nat × Nat × Nat)) (lP : List (Nat × Nat))
    (oracles : List (Option (Spt Nat))) (c : Backend.Config)
    (depth minutes P T D R A C W Tloc Tlin k : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (hT : txMinUnits * T ≤ 2000000)
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
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    (localCost (1, 1, 1, 1, 1) + localCost (1, 1, 1, 1, 1) = 40 ∧ localCost (2, 2, 2, 2, 2) = 80) ∧
    prefixCost lP P ≤ (P + (lP.map Prod.fst).sum) * (lP.map Prod.snd).sum ∧
    (txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) ∧
    (txMinUnits * 16666 ≤ 2000000 ∧ 2000000 < txMinUnits * 16667 ∧ txResetTicks * 16666 = 3333200) ∧
    42 * F D R A C W ≤ S * S ∧
    F D R A C W ≤ 95_238_095_238 ∧
    40 * G D R A C W ≤ S * S ∧
    G D R A C W ≤ 100_000_000_000 ∧
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables ∧
    kPanUnifiedAllTables = 136_116_135_658 ∧
    6 * kPanUnifiedAllTables < yukon ∧
    (k * kPanUnifiedAllTables < yukon ↔ k ≤ 6) ∧
    yukon - 6 * kPanUnifiedAllTables = 84_023_111_526 ∧
    (∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2,
      IsStubLabel s.sectionId = true ∨ CleanSection s) ∧
    (StackToLab.compile sc dc mh sp off L).map (·.sectionId) =
      [0, 1, 2, gcStubLocation] ++ L.map Prod.fst ∧
    (StackNoSt (StackRemove.comp j bd ptr p) = true ∧ FlattenVisitsSt p = false) ∧
    yukonScore unifiedAllTablesSlope3K minutes - yukonScore unifiedAllTablesSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore unifiedAllTablesSlope6K minutes - yukonScore unifiedAllTablesSlope6UnrolledK minutes = 138_000_000 ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedSubBlockTxSplittingAndUnifiedSynth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedSubBlockTxSplittingAndUnifiedSynth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hm := master_unified_all_tables_and_unconditional_stack_to_lab_campaign_certificate_non_vacuous_and_tight
    arch panProg wc cAsm perf j false sc.regNames sc.regNames bd ptr 0 0 0 0 none [] []
    oracles c depth minutes D R A C W Tloc Tlin k hlab compiled depthBound hF hG hloc hlin not_timeOut_u128
  exact ⟨hm.1, hm.2.1, hm.2.2.1,
    hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.1,
    split_local_le l,
    split_strict,
    prefix_le lP P,
    reset_absorbed T hT,
    max_tx_reset,
    hm.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    panToLab_sections_unconditional arch panProg wc cAsm perf sc dc mh sp off,
    stackToLab_compile_ids sc dc mh sp off L,
    stackRemove_no_storeConsts_branch j bd ptr p hp,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by decide,
    by decide,
    rfl⟩

#print axioms sub_block_tx_splitting_local_and_prefix_dominance_non_vacuous_and_tight
#print axioms sub_block_reset_absorbed_and_unified_all_tables_master_non_vacuous_and_tight
#print axioms unconditional_pan_to_lab_sections_and_stack_remove_clock_non_vacuous_and_tight
#print axioms unified_five_var_coupled_and_merge_with_sub_block_dominance_non_vacuous_and_tight
#print axioms sub_block_and_unified_all_tables_tiers_under_yukon_non_vacuous_and_tight
#print axioms twenty_six_tier_hierarchy_with_sub_block_and_unified_bounds_non_vacuous_and_tight
#print axioms sub_block_and_unified_bootstrap_decompositions_and_one_tick_tight_non_vacuous_and_tight
#print axioms sub_block_and_unified_yukonScore_and_claim_json_audit_non_vacuous_and_tight
#print axioms sub_block_and_unified_all_tables_certificates_and_margins_non_vacuous_and_tight
#print axioms master_sub_block_tx_splitting_pan_to_lab_sections_and_unified_campaign_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedSubBlockTxSplittingAndUnifiedSynth
