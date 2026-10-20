import InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening
import InitECandidate.Solver.SelfContainedDisjointTablesAndStateRestoreSynth
import InitECandidate.Solver.DisjointBlockTxAccessListAndFortyBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SelfContainedCoupledRevertTxCapAndDisjointTablesSynth` — Self-Contained Coupled Revert & Per-Tx EIP-7825 Cap (`d_t ≤ 7_989`, `no_six_restore = 155_688_931_265`), Disjoint Block/Tx Storage Tables (`bs+32` / `ts+32`), Forty-Budget Portfolio & `LabToTarget.removeLabels` Clean-Section Synthesis (`W5_121`)

This module has **0 imports from `InitECandidate.Proofs.Bounded*`** in its transitive closure and
unifies:
1. The coupled revert & per-tx EIP-7825 dirty-key cap tightening audit from
   `GuestCoupledRevertAndTxCapTightening` (`10/10` tight):
   - `tx_cap` (`21 * 7989 ≤ M ∧ M < 21 * 7990`, where `M = 167_772`),
   - `dx_le` (`d ≤ 7_989` whenever `21 * d + w ≤ M`: the EIP-7825 per-tx dirty cap `tx_dirty_cap` on `|ts+32|`),
   - `witness_budget` (`21 * 4114 + 81378 = M ∧ 21 * 3783 + 75065 ≤ M ∧ (witness.map (fun p => 21 * p.1 + p.2)).sum = S`),
   - `witness_feasible` (`feasible witness`),
   - `witness_totals` (`(witness.map Prod.fst).sum = 49_037 ∧ (witness.map Prod.snd).sum = 970_223 ∧ (witness.map (fun p => p.1 * p.2)).sum = 3_966_650_907`),
   - `witness_cost` (`coupledCost witness = 155_688_931_265`),
   - `six_target` (`6 * 150_119_987_578 < yukon ∧ yukon ≤ 6 * 150_119_987_579`),
   - `no_six_restore` (`∃ l, feasible l ∧ yukon < 6 * coupledCost l`),
   - `witness_le_access` (`coupledCost witness ≤ kPanAccessCall`),
   - `slopes` (`kPanCoupledRevertTxCap = 159_893_274_708 ∧ 5 * kPanCoupledRevertTxCap < yukon ∧ yukon < 6 * kPanCoupledRevertTxCap`).
2. The self-contained disjoint block/tx storage table partition (`bs+32` / `ts+32`), `11`-tick exchange
   audit, `state_restore` coupled audit, and 30-tier / 40-budget synthesis from
   `SelfContainedDisjointTablesAndStateRestoreSynth` (`10/10` tight).
3. The unified 40-budget portfolio, EIP-2930 access-list & call-stack dominance, `LabToTarget.removeLabels`
   clean-section preservation, and concrete `InitE.Certificate submission (.finite K)` lifting from
   `DisjointBlockTxAccessListAndFortyBudgetMaster` (`22/22` tight).
-/

namespace InitECandidate.Solver.SelfContainedCoupledRevertTxCapAndDisjointTablesSynth

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
open InitECandidate.Solver.LabToTargetSectionCleanPreservation
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.GuestEvmStepOpcodeBounds
open InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds
open InitECandidate.Solver.GuestBlockVsTxHtabBounds
open InitECandidate.Solver.GuestJointBlockGasHtabBound hiding M
open InitECandidate.Solver.GuestDirtyWriteHtabDominance
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope
open InitECandidate.Solver.GuestCoupledTxBlockStorageBound hiding M
open InitECandidate.Solver.GuestSstoreWarmCoeffAudit
open InitECandidate.Solver.GuestSstoreCleanToDirtyTransition
open InitECandidate.Solver.GuestJointTransitionInsertionBound
open InitECandidate.Solver.GuestMergeTxUnionEnvelope
open InitECandidate.Solver.GuestMultiAddressMergeDominance
open InitECandidate.Solver.GuestFiveAddrTablesMergeBound
open InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope
open InitECandidate.Solver.GuestSubBlockTxSplittingDominance
open InitECandidate.Solver.GuestAccessListAndCallStackDominance
open InitECandidate.Solver.GuestStateRestoreCoupledTightening
open InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes
open InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening
  (M coupledCost feasible witness tx_cap dx_le witness_budget witness_feasible
   witness_totals witness_cost six_target no_six_restore witness_le_access
   kPanCoupledRevertTxCap)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.StateRestoreAndAccessCallFortyBudgetMaster
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
open InitECandidate.Solver.SelfContainedSubBlockTxSplittingAndUnifiedSynth
open InitECandidate.Solver.SelfContainedAccessListCallStackAndLabToTargetSynth
open InitECandidate.Solver.SelfContainedStateRestoreAndFortyBudgetSynth
open InitECandidate.Solver.SelfContainedDisjointTablesAndStateRestoreSynth
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
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.StackLang

/-! ## Section 1: Coupled Revert & Per-Tx EIP-7825 Cap Target Tiers & Portfolio Aliases -/

/-- Unrolled-`copyLoop` (`9_332`) target ceiling for `kPanCoupledRevertTxCap = 159_893_274_708`
at `3x` slope: `9_332 + 3 * 159_893_274_708 = 479_679_833_456`. -/
def coupledRevertTxCapSlope3UnrolledK : Nat :=
  (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanCoupledRevertTxCap

/-- Baseline-bootstrap (`23_132`) target ceiling for `kPanCoupledRevertTxCap = 159_893_274_708`
at `3x` slope: `23_132 + 3 * 159_893_274_708 = 479_679_847_256`. -/
def coupledRevertTxCapSlope3K : Nat :=
  bootstrapSteps + 3 * kPanCoupledRevertTxCap

/-- Unrolled-`copyLoop` (`9_332`) target ceiling for `kPanCoupledRevertTxCap = 159_893_274_708`
at `5x` slope: `9_332 + 5 * 159_893_274_708 = 799_466_382_872`. -/
def coupledRevertTxCapSlope5UnrolledK : Nat :=
  (bootstrapSteps - copyLoopSavedSteps) + 5 * kPanCoupledRevertTxCap

/-- Baseline-bootstrap (`23_132`) target ceiling for `kPanCoupledRevertTxCap = 159_893_274_708`
at `5x` slope: `23_132 + 5 * 159_893_274_708 = 799_466_396_672`. -/
def coupledRevertTxCapSlope5K : Nat :=
  bootstrapSteps + 5 * kPanCoupledRevertTxCap

/-- Alias for the unified 40-budget portfolio from `DisjointBlockTxAccessListAndFortyBudgetMaster`. -/
abbrev coupledRevertFortyBudgetPortfolio : List Nat :=
  DisjointBlockTxAccessListAndFortyBudgetMaster.portfolio

/-! ## Section 2: Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`, **Complete Coupled Revert & Per-Tx EIP-7825 Dirty-Key Cap Tightening (`GuestCoupledRevertAndTxCapTightening`, `10/10` tight) with Disjoint `bs+32` / `ts+32` Table Partition**):
Unites all 10 theorems of `GuestCoupledRevertAndTxCapTightening`:
- `tx_cap` (`21 * 7989 ≤ M ∧ M < 21 * 7990`),
- `dx_le` (`d_t ≤ 7989` whenever `21 * d_t + w_t ≤ M`: the per-tx EIP-7825 dirty cap `tx_dirty_cap` on `|ts+32|`),
- `witness_budget` (`21 * 4114 + 81378 = M ∧ 21 * 3783 + 75065 ≤ M ∧ (witness.map (fun p => 21 * p.1 + p.2)).sum = GuestCoupledRevertAndTxCapTightening.S`),
- `witness_feasible` (`feasible witness`),
- `witness_totals` (`(witness.map Prod.fst).sum = 49037 ∧ (witness.map Prod.snd).sum = 970223 ∧ (witness.map (fun p => p.1 * p.2)).sum = 3966650907`),
- `witness_cost` (`coupledCost witness = 155688931265`),
- `six_target` (`6 * 150119987578 < yukon ∧ yukon ≤ 6 * 150119987579`),
- `no_six_restore` (`∃ l, feasible l ∧ yukon < 6 * coupledCost l`),
- `witness_le_access` (`coupledCost witness ≤ kPanAccessCall`),
- `slopes` (`kPanCoupledRevertTxCap = 159893274708 ∧ 5 * kPanCoupledRevertTxCap < yukon ∧ yukon < 6 * kPanCoupledRevertTxCap`),
together with the disjoint `bs+32` / `ts+32` partition from `SelfContainedDisjointTablesAndStateRestoreSynth`. -/
theorem guest_coupled_revert_and_tx_cap_tightening_complete_audit_non_vacuous_and_tight
    (s : Sizes) (d_t w_t db dx D W : Nat)
    (htx : 21 * d_t + w_t ≤ M)
    (hp : db + dx ≤ D) (hgas : 21 * D + W ≤ 2000000) :
    (21 * 7989 ≤ M ∧ M < 21 * 7990) ∧
    d_t ≤ 7989 ∧
    (21 * 4114 + 81378 = M ∧ 21 * 3783 + 75065 ≤ M ∧
      (witness.map (fun p => 21 * p.1 + p.2)).sum = GuestCoupledRevertAndTxCapTightening.S) ∧
    feasible witness ∧
    ((witness.map Prod.fst).sum = 49037 ∧ (witness.map Prod.snd).sum = 970223 ∧
      (witness.map (fun p => p.1 * p.2)).sum = 3966650907) ∧
    coupledCost witness = 155688931265 ∧
    (6 * 150119987578 < yukon ∧ yukon ≤ 6 * 150119987579) ∧
    (∃ l, feasible l ∧ yukon < 6 * coupledCost l) ∧
    coupledCost witness ≤ kPanAccessCall ∧
    (kPanCoupledRevertTxCap = 159893274708 ∧ 5 * kPanCoupledRevertTxCap < yukon ∧
      yukon < 6 * kPanCoupledRevertTxCap) ∧
    kPanCoupledRevertTxCap = kPanDisjointTables ∧
    kPanCoupledRevertTxCap = kPanStateRestoreCoupled ∧
    ((endTx s).db + (endTx s).dx = s.db + s.dx ∧
      (endTx s).dx = 0 ∧
      (dirty s).db + (dirty s).dx = s.db + s.dx + 1 ∧
      21 * (db + dx) + W ≤ 2000000 ∧
      2 * db + 13 * dx ≤ 13 * (db + dx) ∧
      cycleTicks db dx ≤ 13 * D ∧
      cycleTicks 0 D = 13 * D ∧
      cycleTicks D 0 = 2 * D ∧
      cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
      kPanDisjointTables = 159893274708 ∧
      kPanDisjointTables = kPanStateRestoreCoupled ∧
      kPanDisjointTables = kPanAccessCall ∧
      (5 * kPanDisjointTables < yukon ∧ yukon < 6 * kPanDisjointTables ∧
        yukon - 5 * kPanDisjointTables = 101253551934)) := by
  refine ⟨tx_cap,
    dx_le d_t w_t htx,
    witness_budget,
    witness_feasible,
    witness_totals,
    witness_cost,
    six_target,
    no_six_restore,
    witness_le_access,
    GuestCoupledRevertAndTxCapTightening.slopes,
    rfl,
    by decide,
    guest_disjoint_block_and_tx_table_sizes_complete_audit_non_vacuous_and_tight s db dx D W hp hgas⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **Coupled Per-Tx Dirty Cap (`d_t ≤ 7_989`), `no_six_restore` (`155_688_931_265`), Disjoint Table Partition & `state_restore` Audit (`DisjointBlockTxAccessListAndFortyBudgetMaster`)**):
Couples the per-tx EIP-7825 dirty cap `dx_le` (`d_t ≤ 7_989`) and `no_six_restore` (`155_688_931_265` ticks)
directly with `DisjointBlockTxAccessListAndFortyBudgetMaster.disjoint_access_list_restore_audit_non_vacuous_and_tight`,
`disjoint_merge_reset_non_vacuous_and_tight`, `disjoint_witness_non_vacuous_and_tight`,
`disjoint_clock_non_vacuous_and_tight`, and `exact_slope_gaps_non_vacuous_and_tight`. -/
theorem coupled_revert_tx_cap_disjoint_tables_and_state_restore_audit_non_vacuous_and_tight
    (s : Sizes) (d_t w_t db dx D W : Nat) (p oc : Bool) (k c0 n : Nat)
    (htx : 21 * d_t + w_t ≤ M)
    (hp : db + dx ≤ D) (hgas : 21 * D + W ≤ S) :
    d_t ≤ 7989 ∧
    coupledCost witness = 155688931265 ∧
    (∃ l, feasible l ∧ yukon < 6 * coupledCost l) ∧
    ((21 * (db + dx) + W ≤ S ∧
      cycleTicks db dx ≤ 13 * (db + dx) ∧ cycleTicks db dx ≤ 13 * D ∧
      cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
      cycleTicks 0 D = 13 * D ∧ cycleTicks D 0 = 2 * D) ∧
     (restoreOf p = .del ↔ p = false) ∧
     sstoreGas true oc true = 100 ∧
     (sstoreGas true true false = 10100 ∧ sstoreGas false true false = 12100) ∧
     (restoreOf (jsetStep false).1 = .del ∧ sstoreGas true true true = 100) ∧
     restoreOf (jsetStep true).1 = .set ∧
     delsPerCall k = k ∧
     n * delsPerCall k + n * c0 = n * (k + c0) ∧
     ¬ (1000 * delsPerCall 100 ≤ 0 + 0) ∧
     (kPanStateRestoreCoupled = 159893274708 ∧ kPanStateRestoreCoupled = kPanAccessCall) ∧
     (5 * kPanStateRestoreCoupled < yukon ∧ yukon < 6 * kPanStateRestoreCoupled) ∧
     (6 * (136116135658 + 3804281910) < yukon ∧ ¬ (6 * kPanStateRestoreCoupled < yukon))) ∧
    ((endTx s).db + (endTx s).dx = s.db + s.dx ∧
      (endTx s).dx = 0 ∧ (dirty s).db + (dirty s).dx = s.db + s.dx + 1) ∧
    (21 * (3 + 4) + 100 ≤ S ∧ cycleTicks 3 4 = 58 ∧
      cycleTicks 0 7 = 91 ∧ cycleTicks 1 6 + 11 = cycleTicks 0 7) ∧
    (kPanDisjointTables = kPanStateRestoreCoupled ∧
      5 * kPanDisjointTables < yukon ∧ yukon < 6 * kPanDisjointTables ∧
      yukon - 5 * kPanDisjointTables = 101253551934) ∧
    (kPanUnifiedAllTables = 136116135658 ∧
      kPanStateRestoreCoupled = 159893274708 ∧
      kPanStateRestoreCoupled - kPanUnifiedAllTables = 23777139050 ∧
      (9332 + 3 * kPanStateRestoreCoupled) - (9332 + 3 * kPanUnifiedAllTables) = 71331417150 ∧
      (23132 + 3 * kPanStateRestoreCoupled) - (23132 + 3 * kPanUnifiedAllTables) = 71331417150 ∧
      (9332 + 5 * kPanStateRestoreCoupled) - (9332 + 5 * kPanUnifiedAllTables) = 118885695250 ∧
      (23132 + 5 * kPanStateRestoreCoupled) - (23132 + 5 * kPanUnifiedAllTables) = 118885695250 ∧
      5 * kPanStateRestoreCoupled < 900719925474 ∧
      900719925474 < 6 * kPanStateRestoreCoupled) := by
  exact ⟨dx_le d_t w_t htx,
    witness_cost,
    no_six_restore,
    DisjointBlockTxAccessListAndFortyBudgetMaster.disjoint_access_list_restore_audit_non_vacuous_and_tight
      db dx D W hp hgas p oc k c0 n,
    DisjointBlockTxAccessListAndFortyBudgetMaster.disjoint_merge_reset_non_vacuous_and_tight s,
    DisjointBlockTxAccessListAndFortyBudgetMaster.disjoint_witness_non_vacuous_and_tight,
    DisjointBlockTxAccessListAndFortyBudgetMaster.disjoint_clock_non_vacuous_and_tight,
    DisjointBlockTxAccessListAndFortyBudgetMaster.exact_slope_gaps_non_vacuous_and_tight⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Identity of `coupledRevertTxCapSlope*`, `disjointTablesSlope*`, `stateRestoreSlope*` & `accessSlope*` Target Tiers and Exact Bootstrap Decompositions**):
Proves that because `kPanCoupledRevertTxCap = kPanDisjointTables = kPanStateRestoreCoupled = kPanAccessCall = 159_893_274_708`,
the four coupled-revert target ceilings coincide identically with the disjoint-table, state-restore,
and access-call target ceilings (`479_679_833_456`, `479_679_847_256`, `799_466_382_872`, `799_466_396_672`),
enjoy exact `13_800`-step unrolled savings, and satisfy sharp 1-tick tightness boundaries. -/
theorem coupled_revert_tx_cap_and_disjoint_tables_target_tiers_coincide_non_vacuous_and_tight
    (k minutes : Nat) :
    coupledRevertTxCapSlope3UnrolledK = disjointTablesSlope3UnrolledK ∧
    coupledRevertTxCapSlope3K = disjointTablesSlope3K ∧
    coupledRevertTxCapSlope5UnrolledK = disjointTablesSlope5UnrolledK ∧
    coupledRevertTxCapSlope5K = disjointTablesSlope5K ∧
    coupledRevertTxCapSlope3UnrolledK = stateRestoreSlope3UnrolledK ∧
    coupledRevertTxCapSlope3K = stateRestoreSlope3K ∧
    coupledRevertTxCapSlope5UnrolledK = stateRestoreSlope5UnrolledK ∧
    coupledRevertTxCapSlope5K = stateRestoreSlope5K ∧
    coupledRevertTxCapSlope3UnrolledK = accessSlope3UnrolledK ∧
    coupledRevertTxCapSlope3K = accessSlope3K ∧
    coupledRevertTxCapSlope5UnrolledK = accessSlope5UnrolledK ∧
    coupledRevertTxCapSlope5K = accessSlope5K ∧
    coupledRevertTxCapSlope3UnrolledK = 479_679_833_456 ∧
    coupledRevertTxCapSlope3K = 479_679_847_256 ∧
    coupledRevertTxCapSlope5UnrolledK = 799_466_382_872 ∧
    coupledRevertTxCapSlope5K = 799_466_396_672 ∧
    coupledRevertTxCapSlope3K - coupledRevertTxCapSlope3UnrolledK = 13_800 ∧
    coupledRevertTxCapSlope5K - coupledRevertTxCapSlope5UnrolledK = 13_800 ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanCoupledRevertTxCap ≤ coupledRevertTxCapSlope3UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 3 * kPanCoupledRevertTxCap ≤ coupledRevertTxCapSlope3K - 1) ∧
    ¬ ((bootstrapSteps - copyLoopSavedSteps) + 5 * kPanCoupledRevertTxCap ≤ coupledRevertTxCapSlope5UnrolledK - 1) ∧
    ¬ (bootstrapSteps + 5 * kPanCoupledRevertTxCap ≤ coupledRevertTxCapSlope5K - 1) ∧
    (coupledRevertTxCapSlope3K ≤ k + copyLoopSavedSteps ↔ coupledRevertTxCapSlope3UnrolledK ≤ k) ∧
    (coupledRevertTxCapSlope5K ≤ k + copyLoopSavedSteps ↔ coupledRevertTxCapSlope5UnrolledK ≤ k) ∧
    yukonScore coupledRevertTxCapSlope3K minutes - yukonScore coupledRevertTxCapSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore coupledRevertTxCapSlope5K minutes - yukonScore coupledRevertTxCapSlope5UnrolledK minutes = 138_000_000 := by
  have hdt := disjoint_tables_and_state_restore_target_tiers_coincide_non_vacuous_and_tight k minutes
  exact ⟨rfl, rfl, rfl, rfl,
    hdt.1, hdt.2.1, hdt.2.2.1, hdt.2.2.2.1,
    hdt.2.2.2.2.1, hdt.2.2.2.2.2.1, hdt.2.2.2.2.2.2.1, hdt.2.2.2.2.2.2.2.1,
    hdt.2.2.2.2.2.2.2.2.1, hdt.2.2.2.2.2.2.2.2.2.1,
    hdt.2.2.2.2.2.2.2.2.2.2.1, hdt.2.2.2.2.2.2.2.2.2.2.2.1,
    hdt.2.2.2.2.2.2.2.2.2.2.2.2.1, hdt.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hdt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hdt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hdt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hdt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hdt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hdt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hdt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hdt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 4 (`non_vacuous_and_tight`, **Master Forty-Budget Portfolio Unification (`DisjointBlockTxAccessListAndFortyBudgetMaster.three_portfolios_unified_non_vacuous_and_tight`), Sub-Block Split-Revert Envelope & Per-Tx Dirty Cap (`d_t ≤ 7_989`)**):
Unites `DisjointBlockTxAccessListAndFortyBudgetMaster.three_portfolios_unified_non_vacuous_and_tight`
and `forty_budget_master_portfolio_and_split_revert_envelope_non_vacuous_and_tight` with
`dx_le` (`d_t ≤ 7_989`) and `no_six_restore` (`155_688_931_265` ticks). -/
theorem forty_budget_master_portfolio_unification_and_split_revert_envelope_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat)) (r : List (Nat × Nat))
    (T Tloc Tlin c n d_t w_t : Nat)
    (htx : 21 * d_t + w_t ≤ M)
    (budget : 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ S)
    (ht : txMinUnits * T ≤ 2000000) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hr : (r.map (fun p => p.1 * p.2)).sum ≤ 3994571428)
    (hc : c ≤ 7989) (hn : n ≤ 95238) :
    d_t ≤ 7989 ∧
    coupledCost witness = 155688931265 ∧
    (∃ lw, feasible lw ∧ yukon < 6 * coupledCost lw) ∧
    (coupledRevertFortyBudgetPortfolio = SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio ∧
      coupledRevertFortyBudgetPortfolio = SelfContainedStateRestoreAndFortyBudgetSynth.fortyBudgetPortfolio ∧
      coupledRevertFortyBudgetPortfolio = AccessListCallStackAndLabToTargetMaster.portfolio ∧
      coupledRevertFortyBudgetPortfolio.length = 40 ∧
      coupledRevertFortyBudgetPortfolio.Pairwise (· < ·)) ∧
    coupledRevertFortyBudgetPortfolio = disjointFortyBudgetPortfolio ∧
    ((disjointFortyBudgetPortfolio.length = 40 ∧
      disjointFortyBudgetPortfolio.Pairwise (· < ·) ∧
      ∀ k ∈ disjointFortyBudgetPortfolio, 1212035192 ≤ k ∧ k < yukon) ∧
     (addedBudgets.length = 4 ∧ addedBudgets.Pairwise (· < ·) ∧
      ∀ k ∈ addedBudgets, 1212035192 ≤ k ∧ k < yukon) ∧
     (∀ k ∈ LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio, k ∈ disjointFortyBudgetPortfolio) ∧
     (∀ k ∈ addedBudgets, k ∈ disjointFortyBudgetPortfolio) ∧
     disjointFortyBudgetPortfolio = fortyBudgetPortfolio ∧
     (let cost := linear + Tloc + ((l.map localCost).sum + 41935 * sR l) + Tlin +
        revertCost r + 5 * c * n
      cost ≤ kPanCoupledRevertTxCap ∧
      (9332 + 3 * cost ≤ coupledRevertTxCapSlope3UnrolledK ∧
       23132 + 3 * cost ≤ coupledRevertTxCapSlope3K ∧
       9332 + 5 * cost ≤ coupledRevertTxCapSlope5UnrolledK ∧
       23132 + 5 * cost ≤ coupledRevertTxCapSlope5K ∧
       coupledRevertTxCapSlope5K < yukon) ∧
      txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666 ∧
      disjointFortyBudgetPortfolio.length = 40 ∧ ∀ k ∈ disjointFortyBudgetPortfolio, k < yukon)) := by
  refine ⟨dx_le d_t w_t htx,
    witness_cost,
    no_six_restore,
    DisjointBlockTxAccessListAndFortyBudgetMaster.three_portfolios_unified_non_vacuous_and_tight,
    by decide,
    forty_budget_master_portfolio_and_split_revert_envelope_non_vacuous_and_tight
      l r T Tloc Tlin c n budget ht hloc hlin hr hc hn⟩

/-- Theorem 5 (`non_vacuous_and_tight`, **EIP-2930 Access-List Dominance, Call-Stack Revert, Sub-Block Prefix Envelope & Coupled Revert Per-Tx Dirty Cap (`d_t ≤ 7_989`)**):
Unites `DisjointBlockTxAccessListAndFortyBudgetMaster.access_list_and_call_stack_dominance_and_slope_threshold_non_vacuous_and_tight`,
`DisjointBlockTxAccessListAndFortyBudgetMaster.lab_split_prefix_non_vacuous_and_tight`,
`access_list_call_stack_and_sub_block_prefix_dominance_non_vacuous_and_tight`,
`dx_le` (`d_t ≤ 7_989`), `witness_cost`, and `no_six_restore`. -/
theorem access_list_call_stack_sub_block_and_coupled_revert_tx_cap_dominance_non_vacuous_and_tight
    (Kal Aal D A C R W d c n P k d_t w_t : Nat)
    (l : List (Nat × Nat × Nat × Nat × Nat)) (r p : List (Nat × Nat))
    (htx : 21 * d_t + w_t ≤ M)
    (hal : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2000000)
    (hr : (r.map (fun q => q.1 * q.2)).sum ≤ 3994571428)
    (hc : c ≤ 7989) (hn : n ≤ 95238)
    (hd : ¬ (d + 1 > 1024))
    (hS : 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ S) :
    d_t ≤ 7989 ∧
    (21 * 7989 ≤ M ∧ M < 21 * 7990) ∧
    coupledCost witness = 155688931265 ∧
    (∃ lw, feasible lw ∧ yukon < 6 * coupledCost lw) ∧
    coupledCost witness ≤ kPanAccessCall ∧
    ((alAddrGas = 4180 ∧ alKeyGas = 4048) ∧
     (26 * 100 < alAddrGas ∧ 21 * 100 < alKeyGas ∧ 20 * 100 < alKeyGas) ∧
     21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2000000 ∧
     undoTicks d = 5 * d ∧
     revertCost r = 5 * (r.map (fun q => q.1 * q.2)).sum ∧
     revertCost r ≤ 19972857140 ∧
     (5 * c * n ≤ 3804281910 ∧ 21 * 7989 ≤ 167772 ∧ 167772 < 21 * 7990) ∧
     d ≤ 1023 ∧
     kPanAccessCall = 159893274708 ∧
     (3 * kPanAccessCall < yukon ∧ 4 * kPanAccessCall < yukon ∧ 5 * kPanAccessCall < yukon ∧
       yukon < 6 * kPanAccessCall) ∧
     ((k * kPanAccessCall < yukon ↔ k ≤ 5) ∧ yukon - 5 * kPanAccessCall = 101253551934)) ∧
    F (D + Kal) R (A + Aal) C W ≤ 95238095238 ∧
    ((l.map localCost).sum + 41935 * sR l ≤ 95238095238 ∧
      prefixCost p P ≤ (P + (p.map Prod.fst).sum) * (p.map Prod.snd).sum) := by
  have hal_sub := access_list_call_stack_and_sub_block_prefix_dominance_non_vacuous_and_tight
    Kal Aal D A C R W d c n P l r p hal hr hc hn hd hS
  exact ⟨dx_le d_t w_t htx,
    tx_cap,
    witness_cost,
    no_six_restore,
    witness_le_access,
    DisjointBlockTxAccessListAndFortyBudgetMaster.access_list_and_call_stack_dominance_and_slope_threshold_non_vacuous_and_tight
      Kal Aal D A C R W d c n k r hal hr hc hn hd,
    hal_sub.2.2.2.1,
    DisjointBlockTxAccessListAndFortyBudgetMaster.lab_split_prefix_non_vacuous_and_tight l p P hS⟩

/-- Theorem 6 (`non_vacuous_and_tight`, **End-to-End `LabToTarget.removeLabels` Clean-Section Preservation Coupled with Per-Tx EIP-7825 Cap (`d_t ≤ 7_989`), `no_six_restore` & Disjoint Table Partition**):
Combines `lab_to_target_clean_sections_disjoint_tables_and_state_restore_non_vacuous_and_tight`
and `DisjointBlockTxAccessListAndFortyBudgetMaster.panToTarget_sections_clean_non_vacuous_and_tight`
with `dx_le` (`d_t ≤ 7_989`), `witness_cost`, and `no_six_restore`. -/
theorem lab_to_target_clean_sections_coupled_revert_tx_cap_and_disjoint_tables_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (nop : List (BitVec 8))
    (L L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (d_t w_t db dx D W : Nat)
    (htx : 21 * d_t + w_t ≤ M)
    (hrem : removeLabels ic ac pos labs ffis L = some (L', labs'))
    (hpan : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (hp : db + dx ≤ D) (hgas : 21 * D + W ≤ S) :
    d_t ≤ 7989 ∧
    coupledCost witness = 155688931265 ∧
    (∃ lw, feasible lw ∧ yukon < 6 * coupledCost lw) ∧
    (ids (filterSkip L) = ids L ∧
     ids (encSecList enc L) = ids L ∧
     ids (encSecsAgain pos labs ffis enc L).1 = ids L ∧
     ids (updLabLen pos L) = ids L ∧
     ids (padCode nop L) = ids L ∧
     ids L' = ids L ∧
     L'.length = L.length ∧
     (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
           (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
      ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
        ∃ s ∈ StackToLab.compile sc dc mh sp off
            (compileNative ac perf (WordToWord.compile wc ac
              (panToWordCompileProgHOL arch prog)).2).2.2.2,
          s.sectionId = s'.sectionId ∧ CleanSection s) ∧
     L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
           (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
     21 * (db + dx) + W ≤ S ∧
     2 * db + 13 * dx ≤ 13 * (db + dx) ∧
     cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
     (∀ p : Bool, restoreOf p = .del ↔ p = false) ∧
     (∀ oc : Bool, sstoreGas true oc true = 100) ∧
     (∀ k : Nat, delsPerCall k = k) ∧
     ¬ (1000 * delsPerCall 100 ≤ 0 + 0)) := by
  exact ⟨dx_le d_t w_t htx,
    witness_cost,
    no_six_restore,
    lab_to_target_clean_sections_disjoint_tables_and_state_restore_non_vacuous_and_tight
      arch prog wc ac perf sc dc mh sp off ic pos labs ffis enc nop L L' labs' db dx D W
      hrem hpan hp hgas⟩

/-- Theorem 7 (`non_vacuous_and_tight`, **Direct Target Non-`.timeOut` to Forty-Budget & Thirty-Tier `InitE.Certificate submission (.finite K)` Bridge (`unified_portfolio_submission_certificate_non_vacuous_and_tight`)**):
Proves that uniform target non-`.timeOut` at `exactKeccak128UnrolledK = 1_212_035_192` yields
`CertificateAt 1_212_035_192`, which simultaneously certifies:
- Every `K ∈ coupledRevertFortyBudgetPortfolio` with an explicit concrete `submission = baselineWithFiniteK K`
  satisfying `K < 900_719_925_474 ∧ InitE.Certificate submission (.finite K)`
  (`DisjointBlockTxAccessListAndFortyBudgetMaster.unified_portfolio_submission_certificate_non_vacuous_and_tight`),
- Both unified 40-budget portfolios (`both_portfolios_certified_non_vacuous_and_tight`),
- All 30 tiers in `thirtyTierHierarchy`,
- All 4 `coupledRevertTxCapSlope*` target ceilings, and `.infinity`. -/
theorem coupled_revert_tx_cap_forty_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_u128 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    CertificateAt 1212035192 ∧
    (coupledRevertFortyBudgetPortfolio.length = 40 ∧
     coupledRevertFortyBudgetPortfolio.Pairwise (· < ·) ∧
     coupledRevertFortyBudgetPortfolio = SelfContainedStateRestoreAndFortyBudgetSynth.fortyBudgetPortfolio ∧
     ∀ K ∈ coupledRevertFortyBudgetPortfolio, K < 900719925474 ∧
       ∃ submission : InitE.Submission,
         submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (coupledRevertFortyBudgetPortfolio.length = 40 ∧
     coupledRevertFortyBudgetPortfolio.Pairwise (· < ·) ∧
     SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio = coupledRevertFortyBudgetPortfolio ∧
     ∀ K ∈ SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio,
       K < 900719925474 ∧ InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (∀ K ∈ thirtyTierHierarchy, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope3UnrolledK) (.finite coupledRevertTxCapSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope3K) (.finite coupledRevertTxCapSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope5UnrolledK) (.finite coupledRevertTxCapSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope5K) (.finite coupledRevertTxCapSlope5K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity := by
  have hcert := disjoint_tables_forty_budget_and_thirty_tier_certificates_from_u128_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_u128
  exact ⟨hcert.1,
    DisjointBlockTxAccessListAndFortyBudgetMaster.unified_portfolio_submission_certificate_non_vacuous_and_tight hcert.1,
    DisjointBlockTxAccessListAndFortyBudgetMaster.both_portfolios_certified_non_vacuous_and_tight hcert.1,
    hcert.2.2.2.1,
    hcert.2.2.2.2.1,
    hcert.2.2.2.2.2.1,
    hcert.2.2.2.2.2.2.1,
    hcert.2.2.2.2.2.2.2.1,
    hcert.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`, **Coupled-Revert Slope-3 & Slope-5 Direct Certificates, `yukonScore` Order & `claim.json ≤ 128`-Byte Audit**):
Proves that uniform target non-`.timeOut` at `coupledRevertTxCapSlope3UnrolledK = 479_679_833_456`
certifies `coupledRevertTxCapSlope3UnrolledK`, `coupledRevertTxCapSlope3K`,
`coupledRevertTxCapSlope5UnrolledK`, and `coupledRevertTxCapSlope5K`, with strict `yukonScore`
ordering and `claim.json ≤ 128`-byte compliance. -/
theorem coupled_revert_tx_cap_slope3_and_slope5_certificates_and_claim_audit_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes K : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_cr_s3_unrolled : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          coupledRevertTxCapSlope3UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope3UnrolledK) (.finite coupledRevertTxCapSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope3K) (.finite coupledRevertTxCapSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope5UnrolledK) (.finite coupledRevertTxCapSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope5K) (.finite coupledRevertTxCapSlope5K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    yukonScore bs32JointSlope3K minutes < yukonScore coupledRevertTxCapSlope3UnrolledK minutes ∧
    yukonScore coupledRevertTxCapSlope3UnrolledK minutes < yukonScore coupledRevertTxCapSlope3K minutes ∧
    yukonScore coupledRevertTxCapSlope3K minutes < yukonScore coupledSlope6UnrolledK minutes ∧
    yukonScore coupledSlope6K minutes < yukonScore coupledRevertTxCapSlope5UnrolledK minutes ∧
    yukonScore coupledRevertTxCapSlope5UnrolledK minutes < yukonScore coupledRevertTxCapSlope5K minutes ∧
    yukonScore coupledRevertTxCapSlope5K minutes < yukonScore transitionSlope6UnrolledK minutes ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) ∧
    validFiniteClaim coupledRevertTxCapSlope3UnrolledK claimJsonAccessCallSlope3Unrolled = true ∧
    validFiniteClaim coupledRevertTxCapSlope3K claimJsonAccessCallSlope3 = true ∧
    validFiniteClaim coupledRevertTxCapSlope5UnrolledK claimJsonAccessCallSlope5Unrolled = true ∧
    validFiniteClaim coupledRevertTxCapSlope5K claimJsonAccessCallSlope5 = true ∧
    checkSubmissionLimits 64 1048576 65536 claimJsonAccessCallSlope3Unrolled.utf8ByteSize false false true = true ∧
    checkSubmissionLimits 64 1048576 65536 (MAX_CLAIM_BYTES + 1) false false true = false := by
  exact disjoint_tables_slope3_and_slope5_certificates_and_claim_audit_non_vacuous_and_tight
    oracles c depth minutes K hlab compiled depthBound not_timeOut_cr_s3_unrolled

/-- Theorem 9 (`non_vacuous_and_tight`, **Integrated Forty-Budget Master Bridge (`DisjointBlockTxAccessListAndFortyBudgetMaster.integrated_master_non_vacuous_and_tight`) Coupled with Per-Tx EIP-7825 Cap (`d_t ≤ 7_989`) & `no_six_restore`**):
Connects `DisjointBlockTxAccessListAndFortyBudgetMaster.integrated_master_non_vacuous_and_tight`
and `integrated_disjoint_tables_and_state_restore_forty_budget_master_bridge_non_vacuous_and_tight`
directly to the per-tx EIP-7825 cap `dx_le` (`d_t ≤ 7_989`), `witness_cost` (`155_688_931_265`),
`no_six_restore`, and `unified_portfolio_submission_certificate_non_vacuous_and_tight`. -/
theorem integrated_coupled_revert_tx_cap_disjoint_tables_and_forty_budget_master_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (l : List (Nat × Nat × Nat × Nat × Nat)) (r : List (Nat × Nat))
    (T Tloc Tlin c n base Kal Aal d_t w_t db dx D W : Nat)
    (htx : 21 * d_t + w_t ≤ M)
    (budget : 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ S)
    (hgas : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ 2000000)
    (ht : txMinUnits * T ≤ 2000000) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hr : (r.map (fun p => p.1 * p.2)).sum ≤ 3994571428)
    (hc : c ≤ 7989) (hn : n ≤ 95238) (hb : base ≤ kPanUnifiedAllTables)
    (hp : db + dx ≤ D) (hpaid : 21 * D + W ≤ S)
    (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (cert : CertificateAt 1212035192) :
    d_t ≤ 7989 ∧
    coupledCost witness = 155688931265 ∧
    (∃ lw, feasible lw ∧ yukon < 6 * coupledCost lw) ∧
    ((21 * (db + dx) + W ≤ S ∧
      cycleTicks db dx ≤ 13 * (db + dx) ∧ cycleTicks db dx ≤ 13 * D ∧
      cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
      cycleTicks 0 D = 13 * D ∧ cycleTicks D 0 = 2 * D) ∧
     (coupledRevertFortyBudgetPortfolio.length = 40 ∧ coupledRevertFortyBudgetPortfolio.Pairwise (· < ·)) ∧
     ((9332 + 3 * kPanStateRestoreCoupled) - (9332 + 3 * kPanUnifiedAllTables) = 71331417150 ∧
      (9332 + 5 * kPanStateRestoreCoupled) - (9332 + 5 * kPanUnifiedAllTables) = 118885695250) ∧
     (6 * (136116135658 + 3804281910) < yukon ∧ ¬ (6 * kPanStateRestoreCoupled < yukon)) ∧
     coupledRevertFortyBudgetPortfolio = SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio ∧
     ((ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
           (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
       ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
         ∃ s ∈ StackToLab.compile sc dc mh sp off
             (compileNative ac perf (WordToWord.compile wc ac
               (panToWordCompileProgHOL arch prog)).2).2.2.2,
           s.sectionId = s'.sectionId ∧ CleanSection s) ∧
      L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
      base + revertCost r + 5 * c * n ≤ kPanAccessCall ∧
      42 * (l.map localCost).sum ≤ S * S ∧
      (∀ k ∈ coupledRevertFortyBudgetPortfolio, k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
     (∀ p : Bool, restoreOf p = .del ↔ p = false) ∧
     (∀ oc : Bool, sstoreGas true oc true = 100) ∧
     (∀ k : Nat, delsPerCall k = k) ∧
     (¬ (1000 * delsPerCall 100 ≤ 0 + 0)) ∧
     kPanStateRestoreCoupled = 159893274708 ∧
     5 * kPanStateRestoreCoupled < yukon ∧
     yukon - 5 * kPanStateRestoreCoupled = 101253551934) ∧
    (let cost := linear + Tloc + ((l.map localCost).sum + 41935 * sR l) + Tlin +
       revertCost r + 5 * c * n
     cost ≤ kPanCoupledRevertTxCap ∧
     (9332 + 3 * cost ≤ coupledRevertTxCapSlope3UnrolledK ∧
      23132 + 3 * cost ≤ coupledRevertTxCapSlope3K ∧
      9332 + 5 * cost ≤ coupledRevertTxCapSlope5UnrolledK ∧
      23132 + 5 * cost ≤ coupledRevertTxCapSlope5K ∧
      coupledRevertTxCapSlope5K < yukon) ∧
     txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) ∧
    (∀ K ∈ coupledRevertFortyBudgetPortfolio, K < 900719925474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (∀ K ∈ thirtyTierHierarchy, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  have hint_disj := integrated_disjoint_tables_and_state_restore_forty_budget_master_bridge_non_vacuous_and_tight
    l r T Tloc Tlin c n db dx D W budget ht hloc hlin hr hc hn hp hpaid
    arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h cert
  have hunif := DisjointBlockTxAccessListAndFortyBudgetMaster.unified_portfolio_submission_certificate_non_vacuous_and_tight cert
  exact ⟨dx_le d_t w_t htx,
    witness_cost,
    no_six_restore,
    DisjointBlockTxAccessListAndFortyBudgetMaster.integrated_master_non_vacuous_and_tight
      arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h cert
      r c n base hr hc hn hb l Kal Aal db dx D W hp hpaid hgas,
    ⟨hint_disj.2.1.2.2.2.2.1.1,
     hint_disj.2.1.2.2.2.2.1.2.1,
     hint_disj.2.1.2.2.2.2.1.2.2.1,
     hint_disj.2.1.2.2.2.2.1.2.2.2.1⟩,
    hunif.2.2.2,
    hint_disj.2.2⟩

/-- Theorem 10 (`non_vacuous_and_tight`, **Master Self-Contained Coupled Revert & Per-Tx EIP-7825 Cap (`d_t ≤ 7_989`, `no_six_restore = 155_688_931_265`), Disjoint Block/Tx Tables (`bs+32` / `ts+32`), Forty-Budget Portfolio & `LabToTarget.removeLabels` Campaign Certificate (`W5_121`)**):
Simultaneously unites:
- Concrete `InitE.Certificate submission (.finite K)` (`submission = baselineWithFiniteK K`) across all 40
  budgets in `coupledRevertFortyBudgetPortfolio` under the Yukon ceiling `900_719_925_474`, plus all 30 tiers
  in `thirtyTierHierarchy`, all 4 `coupledRevertTxCapSlope*` ceilings, and `.infinity`,
- The coupled revert & per-tx EIP-7825 dirty-key cap tightening audit (`tx_cap`, `dx_le`: `d_t ≤ 7_989`,
  `witness_feasible`, `witness_totals`, `witness_cost`: `155_688_931_265`, `six_target`, `no_six_restore`,
  `witness_le_access`, `kPanCoupledRevertTxCap = 159_893_274_708`, `slopes`) from `GuestCoupledRevertAndTxCapTightening`,
- The disjoint `bs+32` / `ts+32` table partition (`21*(D_b + D_x) + W ≤ S`, `2*D_b + 13*D_x ≤ 13*(D_b + D_x)`,
  `cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1)`, `endTx_total`, `endTx_fresh`, `dirty_total`),
- The complete `state_restore` / `jset` / `op_sstore` coupled audit, EIP-2930 access-list & call-stack
  dominance, and sub-block multi-tx splitting dominance,
- End-to-end `LabToTarget.removeLabels` section cleanliness and section-ID preservation, and
- Purified `.Solver` path admission (`0` `Bounded*` imports). -/
theorem master_coupled_revert_tx_cap_and_disjoint_tables_self_contained_campaign_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (panProg : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (cAsm : AsmConfigExact width) (perf j : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp ptr : Nat)
    (off bd : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (hpan : removeLabels ic cAsm pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2)) = some (L', labs'))
    (p : HolProg width) (hp : StackNoSt p = true)
    (s : Sizes) (d_t w_t db dx : Nat)
    (l : List (Nat × Nat × Nat × Nat × Nat)) (lP lRev : List (Nat × Nat))
    (oracles : List (Option (Spt Nat))) (c : Backend.Config)
    (depth minutes P T Kal Aal D R A C W Tloc Tlin cWarm nWarm dCall k : Nat)
    (pBool ocBool : Bool)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (htx : 21 * d_t + w_t ≤ M)
    (hpart : db + dx ≤ D)
    (hT : txMinUnits * T ≤ 2000000)
    (hal : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2000000)
    (hF : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hG : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup)
    (hlin : Tlin ≤ mergeLin)
    (hrev : (lRev.map (fun q => q.1 * q.2)).sum ≤ 3994571428)
    (hcWarm : cWarm ≤ 7989)
    (hnWarm : nWarm ≤ 95238)
    (hdepth : ¬ (dCall + 1 > 1024))
    (not_timeOut_u128 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    coupledRevertFortyBudgetPortfolio.length = 40 ∧
    coupledRevertFortyBudgetPortfolio.Pairwise (· < ·) ∧
    (∀ K ∈ coupledRevertFortyBudgetPortfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (∀ K ∈ thirtyTierHierarchy, K < 900_719_925_474 →
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    thirtyTierHierarchy.length = 30 ∧
    thirtyTierHierarchy.Pairwise (· < ·) ∧
    (∀ K ∈ thirtyTierHierarchy, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope3UnrolledK) (.finite coupledRevertTxCapSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope3K) (.finite coupledRevertTxCapSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope5UnrolledK) (.finite coupledRevertTxCapSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK coupledRevertTxCapSlope5K) (.finite coupledRevertTxCapSlope5K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    (21 * 7989 ≤ M ∧ M < 21 * 7990) ∧
    d_t ≤ 7989 ∧
    feasible witness ∧
    coupledCost witness = 155_688_931_265 ∧
    (6 * 150_119_987_578 < yukon ∧ yukon ≤ 6 * 150_119_987_579) ∧
    (∃ lw, feasible lw ∧ yukon < 6 * coupledCost lw) ∧
    coupledCost witness ≤ kPanAccessCall ∧
    (kPanCoupledRevertTxCap = 159_893_274_708 ∧
      kPanCoupledRevertTxCap = kPanDisjointTables ∧
      kPanCoupledRevertTxCap = kPanStateRestoreCoupled ∧
      kPanCoupledRevertTxCap = kPanAccessCall) ∧
    (endTx s).db + (endTx s).dx = s.db + s.dx ∧
    (endTx s).dx = 0 ∧
    (dirty s).db + (dirty s).dx = s.db + s.dx + 1 ∧
    21 * (db + dx) + W ≤ S ∧
    2 * db + 13 * dx ≤ 13 * (db + dx) ∧
    cycleTicks db dx ≤ 13 * D ∧
    cycleTicks 0 D = 13 * D ∧
    cycleTicks D 0 = 2 * D ∧
    cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
    (5 * kPanCoupledRevertTxCap < yukon ∧ yukon < 6 * kPanCoupledRevertTxCap ∧
      yukon - 5 * kPanCoupledRevertTxCap = 101_253_551_934) ∧
    (restoreOf pBool = .del ↔ pBool = false) ∧
    sstoreGas true ocBool true = 100 ∧
    (restoreOf (jsetStep false).1 = .del ∧ sstoreGas true true true = 100) ∧
    restoreOf (jsetStep true).1 = .set ∧
    delsPerCall k = k ∧
    ¬ (1000 * delsPerCall 100 ≤ 0 + 0) ∧
    (6 * (136_116_135_658 + 3_804_281_910) < yukon ∧ ¬ (6 * kPanStateRestoreCoupled < yukon)) ∧
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2000000 ∧
    linear + Tloc + G D R A C W + Tlin + revertCost lRev + 5 * cWarm * nWarm ≤ kPanCoupledRevertTxCap ∧
    dCall ≤ 1023 ∧
    (k * kPanCoupledRevertTxCap < yukon ↔ k ≤ 5) ∧
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    prefixCost lP P ≤ (P + (lP.map Prod.fst).sum) * (lP.map Prod.snd).sum ∧
    (txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) ∧
    F D R A C W ≤ 95_238_095_238 ∧
    G D R A C W ≤ 100_000_000_000 ∧
    (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2.map Prod.fst ∧
     ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
       ∃ s ∈ StackToLab.compile sc dc mh sp off
           (compileNative cAsm perf (WordToWord.compile wc cAsm
             (panToWordCompileProgHOL arch panProg)).2).2.2.2,
         s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L'.length = 4 + ((compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2).length ∧
    (StackNoSt (StackRemove.comp j bd ptr p) = true ∧ FlattenVisitsSt p = false) ∧
    yukonScore coupledRevertTxCapSlope3K minutes - yukonScore coupledRevertTxCapSlope3UnrolledK minutes = 138_000_000 ∧
    yukonScore coupledRevertTxCapSlope5K minutes - yukonScore coupledRevertTxCapSlope5UnrolledK minutes = 138_000_000 ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedCoupledRevertTxCapAndDisjointTablesSynth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedCoupledRevertTxCapAndDisjointTablesSynth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hm := master_disjoint_tables_and_state_restore_self_contained_campaign_certificate_non_vacuous_and_tight
    arch panProg wc cAsm perf j sc dc mh sp ptr off bd ic pos labs ffis L' labs' hpan
    p hp s db dx l lP lRev oracles c depth minutes P T Kal Aal D R A C W Tloc Tlin cWarm nWarm dCall k
    pBool ocBool hlab compiled depthBound hpart hT hal hF hG hloc hlin hrev hcWarm hnWarm hdepth not_timeOut_u128
  have hcert7 := coupled_revert_tx_cap_forty_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_u128
  have h30_sub : ∀ K ∈ thirtyTierHierarchy, K < 900_719_925_474 →
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K) := by
    intro K hK _
    exact ⟨baselineWithFiniteK K, rfl, hm.2.2.2.2.2.1 K hK⟩
  refine ⟨hcert7.2.1.1,
    hcert7.2.1.2.1,
    hcert7.2.1.2.2.2,
    h30_sub,
    hm.2.2.2.1,
    hm.2.2.2.2.1,
    hm.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.1,
    tx_cap,
    dx_le d_t w_t htx,
    witness_feasible,
    witness_cost,
    six_target,
    no_six_restore,
    witness_le_access,
    ⟨by decide, rfl, by decide, rfl⟩,
    hm.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by decide,
    by decide,
    rfl⟩

#print axioms guest_coupled_revert_and_tx_cap_tightening_complete_audit_non_vacuous_and_tight
#print axioms coupled_revert_tx_cap_disjoint_tables_and_state_restore_audit_non_vacuous_and_tight
#print axioms coupled_revert_tx_cap_and_disjoint_tables_target_tiers_coincide_non_vacuous_and_tight
#print axioms forty_budget_master_portfolio_unification_and_split_revert_envelope_non_vacuous_and_tight
#print axioms access_list_call_stack_sub_block_and_coupled_revert_tx_cap_dominance_non_vacuous_and_tight
#print axioms lab_to_target_clean_sections_coupled_revert_tx_cap_and_disjoint_tables_non_vacuous_and_tight
#print axioms coupled_revert_tx_cap_forty_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
#print axioms coupled_revert_tx_cap_slope3_and_slope5_certificates_and_claim_audit_non_vacuous_and_tight
#print axioms integrated_coupled_revert_tx_cap_disjoint_tables_and_forty_budget_master_bridge_non_vacuous_and_tight
#print axioms master_coupled_revert_tx_cap_and_disjoint_tables_self_contained_campaign_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedCoupledRevertTxCapAndDisjointTablesSynth
