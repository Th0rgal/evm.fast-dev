import InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption
import InitECandidate.Solver.WordToWordNoStubCallAndFortyEightBudgetMaster
import InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedExhaustiveHtabInventoryAndNoStubCallSynth` — Wave 5 Atomic Worker `W5_135`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`GuestExhaustiveHtabInventoryAndSlopeAbsorption` (`10/10` tight)**:
   - Exhaustive `guest.pp.pnk` hash-table inventory (`32 htab_new + 2 htab_new_scratch` sites) and
     general side-regime absorption (`side_absorption_scalar`, `general_side_regime_absorption`,
     `slope_sum`, `absorption_tight`, `threshold_sharp`, `known_slopes`),
   - Transient storage (`ts+64`, EIP-1153 `op_tstore` / `op_tload` at 100 gas) marginal slope excess
     (`tstore_slope_exceeds`, `tstore_tx_budget`), conservative lower witness (`tstore_witness = 83_252_695_392`),
     and tick-model sensitivity (`tstore_sensitivity`: minimal 1-find 2-unit model absorbed vs `jset`
     2-find 1-unit model giving `56_214_050_904` ticks in one tx at slope `> 335_000`).
2. **`WordToWordNoStubCallAndFortyEightBudgetMaster` (`12/12` tight)**:
   - Unconditional call-target safety across all 10 `WordToWord` passes (`panToWordToWord_NoStubCall_non_vacuous_and_tight`)
     and through `WordToStack → StackRawCall → StackAlloc → StackRemove → StackNames`
     (`panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight`) with zero `hcall` premise,
   - Tight `NSC` witnesses (`NSC_rejects_stub_call_non_vacuous_and_tight`,
     `NSC_accepts_user_call_non_vacuous_and_tight`, `NSC_allows_storeConsts_non_vacuous_and_tight`)
     and `integrated_master_non_vacuous_and_tight`.
3. **`SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth` (`10/10` tight)**:
   - Frontend `PanToWordNoStubCall` closure, 11-table shared absorption (`kPanElevenTablesShared = 156_088_992_805`),
     and the strictly increasing **48-budget** (`fortyEightSharedPortfolio`, `fortyEightBaselineWarmSetsPortfolio`)
     and **52-budget** (`allFiftyTwoSharedBudgets`) portfolios under Yukon (`900_719_925_474`) with
     concrete `InitE.Certificate` lifting (`0 sorryAx`, 10 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.SelfContainedExhaustiveHtabInventoryAndNoStubCallSynth

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
open InitECandidate.Solver.PanToWordNoStubCall
open InitECandidate.Solver.WordToWordNoStubCall
open InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption
  (S side_absorption_scalar general_side_regime_absorption slope_sum absorption_tight
   threshold_sharp known_slopes tstoreTicks tstore_slope_exceeds tstore_tx_budget
   tstore_witness tstore_sensitivity)
open InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption
  (kPanElevenTablesShared side_slopes storage_loss shared_absorption
   shared_tight lower_witness bracket bracket_rel five_margin six_fails)
open InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound (kPanElevenTables)
open InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound
  (Frame enter warm truncDels warmN trunc_exact trunc_keeps_parent
   cold_addr_units addr_set_tx addr_set_tx_tight addr_dels_block
   truncTicks addr_trunc_le addr_trunc_tight storage_trunc_in_access
   kPanWarmSets kPanWarmSets_val)
open InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope
  (journalFlags dels repeat_no_delete dels_distinct cycleUnits freshUnits
   cycle_units delete_per_unit fresh_per_unit revert_le_tight revert_tight
   strict_drop kPanSixSlopeRestored kPan_val six_slope)
open InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening
  (M coupledCost feasible witness tx_cap dx_le witness_budget witness_feasible
   witness_totals witness_cost six_target no_six_restore witness_le_access
   kPanCoupledRevertTxCap)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio
  (CertificateAt certificate_lift_non_vacuous_and_tight)
open InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster
  (elevenTablesSharedSlope3UnrolledK elevenTablesSharedSlope3K
   elevenTablesSharedSlope5UnrolledK elevenTablesSharedSlope5K
   portfolio)
open InitECandidate.Solver.WordToWordNoStubCallAndFortyEightBudgetMaster
  (panToWordToWord_NoStubCall_non_vacuous_and_tight
   panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
   NSC_rejects_stub_call_non_vacuous_and_tight
   NSC_accepts_user_call_non_vacuous_and_tight
   NSC_allows_storeConsts_non_vacuous_and_tight
   shared_absorption_non_vacuous_and_tight
   bracket_non_vacuous_and_tight
   five_margin_non_vacuous_and_tight
   portfolio_shape_non_vacuous_and_tight
   forty_eight_certified_non_vacuous_and_tight
   eleven_tables_closure_non_vacuous_and_tight
   integrated_master_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth
  (fourElevenTablesSharedTiers fourElevenTablesSharedPlus100Tiers
   fortyEightSharedPortfolio fortyEightBaselineWarmSetsPortfolio
   fortyEightSharedClaims allFiftyTwoSharedBudgets
   pan_to_word_no_stub_call_and_user_names_complete_audit_non_vacuous_and_tight
   loop_to_word_and_optimiser_tgt_ok_preservation_non_vacuous_and_tight
   eleven_tables_shared_budget_absorption_and_bracket_complete_audit_non_vacuous_and_tight
   eleven_tables_shared_target_budgets_and_warm_sets_gaps_non_vacuous_and_tight
   forty_eight_budget_portfolio_exact_insertion_and_order_non_vacuous_and_tight
   eleven_tables_shared_tiers_interleaved_strict_ordering_non_vacuous_and_tight
   forty_eight_shared_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight
   forty_eight_shared_claims_valid_and_within_128_bytes_non_vacuous_and_tight
   forty_eight_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
   master_pan_to_word_no_stub_call_eleven_tables_shared_and_forty_eight_budget_campaign_certificate_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedWarmAccessSetAndFortyFourBudgetSynth
  (warmSetsSlope3UnrolledK warmSetsSlope3K warmSetsSlope5UnrolledK warmSetsSlope5K
   fourWarmSetsTiers fortyFourWarmSetsPortfolio)
open InitECandidate.Solver.SelfContainedCoupledRevertTxCapAndDisjointTablesSynth
  (coupledRevertTxCapSlope3UnrolledK coupledRevertTxCapSlope3K
   coupledRevertTxCapSlope5UnrolledK coupledRevertTxCapSlope5K)
open InitECandidate.Solver.SelfContainedDisjointTablesAndStateRestoreSynth
open InitECandidate.Solver.SelfContainedStateRestoreAndFortyBudgetSynth
open InitECandidate.Solver.SelfContainedFortyBudgetPortfolioSynth
open InitECandidate.Solver.SelfContainedCompleteCampaignCert
open InitECandidate.Solver.SelfContainedAllAxesSynthesis
open InitECandidate.Solver.SelfContainedSolutionCandidates
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
open InitECandidate.Solver.RiscvBootAndCopyLoopCert
open InitECandidate.Solver.RiscvSszFastRejectAndBootCert
open InitECandidate.Solver.SelfContainedPush31MasterK
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitECandidate.Solver.ExactKeccakSixPassReducedCert
open InitECandidate.Solver.ExactKeccakCopyLoopUnrolledCert
open InitECandidate.Solver.PerTxEip7825TargetMasterK
open InitECandidate.Solver.PurifiedSolverIndex
open InitECandidate.Solver.PurifiedSubmissionBound
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.YukonVerifyScriptAudit
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
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

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`, **General Side-Regime Absorption (`general_side_regime_absorption`, `side_absorption_scalar`, `slope_sum`), Attainable Corner (`absorption_tight`), Sharp `50_000` Threshold (`threshold_sharp`) & Absorbed Regimes (`known_slopes`)**):
Synthesizes the general slope-absorption theorems of `GuestExhaustiveHtabInventoryAndSlopeAbsorption`:
- `side_absorption_scalar B U T blk hS hblk hT`: `blk + T ≤ 100_000_000_000` whenever `B + U ≤ S`,
  `40 * blk ≤ B * B`, and `T ≤ 50_000 * U`,
- `general_side_regime_absorption l B blk hS_l hblk hslope`: `blk + (l.map Prod.fst).sum ≤ 100_000_000_000`
  for any list of side regimes `l` with `B + (l.map Prod.snd).sum ≤ S` and `(l.map Prod.fst).sum ≤ 50_000 * (l.map Prod.snd).sum`,
- `slope_sum l h_each`: pointwise slope bounds `∀ p ∈ l, p.1 ≤ 50_000 * p.2` imply the summed slope hypothesis
  and therefore `blk + (l.map Prod.fst).sum ≤ 100_000_000_000`,
- `absorption_tight`: `40 * 100_000_000_000 = S * S ∧ 100_000_000_000 + 0 = 100_000_000_000`,
- `threshold_sharp`: `¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B → T ≤ 50001 * U → blk + T ≤ 100000000000)`,
- `known_slopes`: `5 * 7989 ≤ 21 * 50000 ∧ 5 * 5611 ≤ 30 * 50000 ∧ 167772 + 2280 ≤ 60 * 50000 ∧ 2 * 6250 ≤ 320 * 50000`. -/
theorem general_side_regime_absorption_and_sharp_threshold_complete_audit_non_vacuous_and_tight
    (B U T blk : Nat) (l : List (Nat × Nat))
    (hS : B + U ≤ S) (hblk : 40 * blk ≤ B * B) (hT : T ≤ 50000 * U)
    (hS_l : B + (l.map Prod.snd).sum ≤ S)
    (h_each : ∀ p ∈ l, p.1 ≤ 50000 * p.2) :
    blk + T ≤ 100_000_000_000 ∧
    (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum ∧
    blk + (l.map Prod.fst).sum ≤ 100_000_000_000 ∧
    (40 * 100_000_000_000 = S * S ∧ 100_000_000_000 + 0 = 100_000_000_000) ∧
    ¬ (∀ B' U' T' blk' : Nat, B' + U' ≤ S → 40 * blk' ≤ B' * B' → T' ≤ 50001 * U' → blk' + T' ≤ 100000000000) ∧
    (5 * 7989 ≤ 21 * 50000 ∧ 5 * 5611 ≤ 30 * 50000 ∧
      167772 + 2280 ≤ 60 * 50000 ∧ 2 * 6250 ≤ 320 * 50000) := by
  have hsum := slope_sum l h_each
  exact ⟨side_absorption_scalar B U T blk hS hblk hT,
    hsum,
    general_side_regime_absorption l B blk hS_l hblk hsum,
    absorption_tight,
    threshold_sharp,
    known_slopes⟩

/-- Theorem 2 (`non_vacuous_and_tight`, **Transient Storage (`ts+64`, EIP-1153 `TSTORE`/`TLOAD`) Marginal Slope Excess (`tstore_slope_exceeds`), Witness (`tstore_witness = 83_252_695_392`) & Tick-Model Sensitivity (`tstore_sensitivity`)**):
Synthesizes the transient-storage (`ts+64`) theorems of `GuestExhaustiveHtabInventoryAndSlopeAbsorption`,
together with the corollary that under the minimal 1-find 2-unit model the 12-tx transient witness is absorbed
into `100_000_000_000` by `side_absorption_scalar`:
- `tstore_slope_exceeds`: `tstoreTicks 83826 - tstoreTicks 83825 = 2 * 83825 ∧ 50000 < 83825`,
- `tstore_tx_budget`: `120 + 2 * 83826 ≤ 167772 ∧ 11 * 167772 + 120 + 2 * 77194 ≤ S`,
- `tstore_witness`: `11 * tstoreTicks 83826 + tstoreTicks 77194 = 83_252_695_392`,
- `tstore_sensitivity`:
  `83_252_695_392 ≤ 50000 * (11 * 2 * 83826 + 2 * 77194) ∧ 2 * tstoreTicks 167652 = 56_214_050_904 ∧ 50000 * 167772 < 2 * tstoreTicks 167652`,
- Minimal-model block absorption: for any `B` and `blk` with `B + (11 * 2 * 83826 + 2 * 77194) ≤ S` and `40 * blk ≤ B * B`,
  `blk + (11 * tstoreTicks 83826 + tstoreTicks 77194) ≤ 100_000_000_000`,
- Multi-tx `jset` lower witness: `11 * (2 * tstoreTicks 167652) = 618_354_559_944`. -/
theorem transient_storage_ts64_slope_witness_and_sensitivity_audit_non_vacuous_and_tight
    (B blk : Nat)
    (hS : B + (11 * 2 * 83826 + 2 * 77194) ≤ S)
    (hblk : 40 * blk ≤ B * B) :
    (tstoreTicks 83826 - tstoreTicks 83825 = 2 * 83825 ∧ 50000 < 83825) ∧
    (120 + 2 * 83826 ≤ 167772 ∧ 11 * 167772 + 120 + 2 * 77194 ≤ S) ∧
    11 * tstoreTicks 83826 + tstoreTicks 77194 = 83_252_695_392 ∧
    (83_252_695_392 ≤ 50000 * (11 * 2 * 83826 + 2 * 77194) ∧
      2 * tstoreTicks 167652 = 56_214_050_904 ∧
      50000 * 167772 < 2 * tstoreTicks 167652) ∧
    blk + (11 * tstoreTicks 83826 + tstoreTicks 77194) ≤ 100_000_000_000 ∧
    11 * (2 * tstoreTicks 167652) = 618_354_559_944 ∧
    ¬ (2 * tstoreTicks 167652 ≤ 50000 * 167772) := by
  have hw := tstore_witness
  have hsens := tstore_sensitivity
  have hT : 11 * tstoreTicks 83826 + tstoreTicks 77194 ≤ 50000 * (11 * 2 * 83826 + 2 * 77194) := by
    rw [hw]; exact hsens.1
  exact ⟨tstore_slope_exceeds,
    tstore_tx_budget,
    hw,
    hsens,
    side_absorption_scalar B (11 * 2 * 83826 + 2 * 77194)
      (11 * tstoreTicks 83826 + tstoreTicks 77194) blk hS hblk hT,
    by decide,
    by decide⟩

/-- Theorem 3 (`non_vacuous_and_tight`, **Unconditional `WordToWord` & `StackNames` No-Stub-Call Synthesis (`panToWordToWord_NoStubCall` & `panToStackNames_NoSt_and_NoStubCall_unconditional`)**):
Synthesizes the compiler call-safety theorems of `WordToWordNoStubCallAndFortyEightBudgetMaster`:
- `panToWordToWord_NoStubCall_non_vacuous_and_tight arch prog wc ac`: every function emitted by
  `WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)` satisfies `WordNoStubCall y.2.2 = true`,
- `panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f`:
  every section emitted by `WordToStack.Native.compileNative` is either `storeConstsStubLocation` or satisfies both
  `StackNoSt` and `NoStubCall` after `StackRawCall.compTop`, `StackAlloc.progComp`, `StackRemove.comp`, and `StackNames.progCompHOL`,
- Non-stub corollary (`y.1 ≠ storeConstsStubLocation → StackNoSt ... = true ∧ NoStubCall ... = true`),
- Tight `NSC` witnesses (`NSC_rejects_stub_call_non_vacuous_and_tight`, `NSC_accepts_user_call_non_vacuous_and_tight`,
  `NSC_allows_storeConsts_non_vacuous_and_tight`). -/
theorem word_to_word_and_stack_names_unconditional_no_stub_call_complete_audit_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (PanToStackNoStoreConsts.StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       StackRemoveAndNamesNoStoreConsts.NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 ≠ storeConstsStubLocation →
      PanToStackNoStoreConsts.StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
      StackRemoveAndNamesNoStoreConsts.NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) ∧
    NSC (WordLangProgHOL.seq (α := BitVec width) .skip
      (.call none (some storeConstsStubLocation) [] none)) = false ∧
    NSC (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true ∧
    NSC (WordLangProgHOL.storeConsts (α := BitVec width) 0 1 2 3 []) = true := by
  refine ⟨panToWordToWord_NoStubCall_non_vacuous_and_tight arch prog wc ac,
    panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f,
    ?_,
    NSC_rejects_stub_call_non_vacuous_and_tight (α := BitVec width),
    NSC_accepts_user_call_non_vacuous_and_tight (α := BitVec width),
    NSC_allows_storeConsts_non_vacuous_and_tight (α := BitVec width)⟩
  intro y hy hne
  rcases panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
    arch prog wc ac perf info j bd ptr f y hy with hstub | hsafe
  · exact False.elim (hne hstub)
  · exact hsafe

/-- Theorem 4 (`non_vacuous_and_tight`, **Full End-to-End Frontend + `WordToWord` + `StackNames` + `LabToTarget` Clean-Section & No-Stub-Call Chain**):
Unites `SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth` (frontend `panToWord_NoStubCall`,
`panToWord_names`, `loopTgtOk` preservation) with `WordToWordNoStubCallAndFortyEightBudgetMaster`
(`panToWordToWord_NoStubCall_non_vacuous_and_tight`,
`panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight`) and `LabToTarget` clean-section
preservation (`panToTarget_sections_clean`, `panToTarget_sections_length`). -/
theorem frontend_to_stack_names_and_lab_to_target_complete_safety_chain_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (panProg : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (cAsm : AsmConfigExact width) (perf j : Bool)
    (info f : Spt Nat) (bd : BitVec width × BitVec width) (ptr : Nat)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (hpan : removeLabels ic cAsm pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2)) = some (L', labs')) :
    (∀ y ∈ panToWordCompileProgHOL arch panProg,
      WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1 ∧ NoSt y.2.2 = true) ∧
    (∀ y ∈ (WordToWord.compile wc cAsm (panToWordCompileProgHOL arch panProg)).2,
      WordNoStubCall y.2.2 = true ∧ NoSt y.2.2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative cAsm perf (WordToWord.compile wc cAsm
        (panToWordCompileProgHOL arch panProg)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (PanToStackNoStoreConsts.StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       StackRemoveAndNamesNoStoreConsts.NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
    (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2.map Prod.fst ∧
     ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
       ∃ s ∈ StackToLab.compile sc dc mh sp off
           (compileNative cAsm perf (WordToWord.compile wc cAsm
             (panToWordCompileProgHOL arch panProg)).2).2.2.2,
         s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L'.length = 4 + ((compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2).length ∧
    ¬ TgtGood (some storeConstsStubLocation) ∧
    NSC (WordLangProgHOL.seq (α := BitVec width) .skip
      (.call none (some storeConstsStubLocation) [] none)) = false := by
  refine ⟨?_, ?_,
    panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight arch panProg wc cAsm perf info j bd ptr f,
    panToTarget_sections_clean arch panProg wc cAsm perf sc dc mh sp off ic pos labs ffis L' labs' hpan,
    panToTarget_sections_length arch panProg wc cAsm perf sc dc mh sp off ic pos labs ffis L' labs' hpan,
    tgtGood_rejects_stub,
    NSC_rejects_stub_call_non_vacuous_and_tight (α := BitVec width)⟩
  · intro y hy
    exact ⟨panToWord_NoStubCall arch panProg y hy,
      panToWord_names arch panProg y hy,
      panToWord_NoSt arch panProg y hy⟩
  · intro y hy
    exact ⟨panToWordToWord_NoStubCall_non_vacuous_and_tight arch panProg wc cAsm y hy,
      PanToStackNoStoreConsts.panToWordToWord_NoSt arch panProg wc cAsm y hy⟩

/-- Theorem 5 (`non_vacuous_and_tight`, **Unified Eleven-Table Shared Absorption (`151_929_428_571` & `kPanElevenTablesShared = 156_088_992_805`) + General Side-Regime Absorption (`100_000_000_000`) & 12-Tx Feasible Bracket**):
Unites `eleven_tables_closure_non_vacuous_and_tight` from `WordToWordNoStubCallAndFortyEightBudgetMaster`
with `general_side_regime_absorption`, `slope_sum`, `absorption_tight`, `threshold_sharp`, and `known_slopes`
from `GuestExhaustiveHtabInventoryAndSlopeAbsorption`. -/
theorem unified_eleven_tables_and_general_side_regime_absorption_closure_non_vacuous_and_tight
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat) (l : List (Nat × Nat))
    (hS : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4)
    (hS_l : B + (l.map Prod.snd).sum ≤ S)
    (h_each : ∀ p ∈ l, p.1 ≤ 50000 * p.2) :
    blk + (l.map Prod.fst).sum ≤ 100_000_000_000 ∧
    (40 * 100_000_000_000 = S * S ∧ 100_000_000_000 + 0 = 100_000_000_000) ∧
    ¬ (∀ B' U' T' blk' : Nat, B' + U' ≤ S → 40 * blk' ≤ B' * B' → T' ≤ 50001 * U' → blk' + T' ≤ 100000000000) ∧
    (5 * 7989 ≤ 21 * 50000 ∧ 5 * 5611 ≤ 30 * 50000 ∧
      167772 + 2280 ≤ 60 * 50000 ∧ 2 * 6250 ≤ 320 * 50000) ∧
    (5 * 7_989 ≤ 21 * 1_903 ∧ 5 * 5_611 ≤ 30 * 936 ∧ M + 2_280 ≤ 60 * 2_835) ∧
    S * (S - B) ≤ S * S - B * B ∧
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (40 * 100_000_000_000 ≤ S * S ∧ 84 * 3_994_571_428 ≤ M * S ∧
      (21 * S * S + 130 * M * S) / 840 = 151_929_428_571) ∧
    (kPanElevenTablesShared = 156_088_992_805 ∧
      kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
      400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
      400_061_540 * 10_000 < 26 * 155_688_931_265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) := by
  have h11 := eleven_tables_closure_non_vacuous_and_tight B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc h2 h3 h4
  have hsum := slope_sum l h_each
  exact ⟨general_side_regime_absorption l B blk hS_l hblk hsum,
    absorption_tight,
    threshold_sharp,
    known_slopes,
    h11.1,
    h11.2.1,
    h11.2.2.1,
    h11.2.2.2.1,
    h11.2.2.2.2.1,
    bracket_non_vacuous_and_tight,
    h11.2.2.2.2.2.2.2.2.1,
    h11.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 6 (`non_vacuous_and_tight`, **48-Budget Portfolio (`fortyEightSharedPortfolio`), 52-Budget Grand Superset (`allFiftyTwoSharedBudgets`), Target Budget Values & Interleaved Ordering**):
Synthesizes the 48-budget portfolio properties across `WordToWordNoStubCallAndFortyEightBudgetMaster`
and `SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth`:
- `fortyEightSharedPortfolio = portfolio`, `fortyEightSharedPortfolio.length = 48`, `Pairwise (· < ·)`,
- Exact insertion-sort characterization from the 44-budget portfolio and `fourElevenTablesSharedTiers`,
- Exact numerical values of `elevenTablesSharedSlope3UnrolledK` (`468_266_987_647`), `elevenTablesSharedSlope3K`
  (`468_267_001_447`), `elevenTablesSharedSlope5UnrolledK` (`780_444_973_257`), and `elevenTablesSharedSlope5K`
  (`780_444_987_057`),
- `fortyEightBaselineWarmSetsPortfolio.length = 48` and `allFiftyTwoSharedBudgets.length = 52` with strict ordering,
- All budgets lie in `[1_212_035_192, 857_384_015_252]` strictly below Yukon `900_719_925_474`. -/
theorem forty_eight_budget_portfolio_and_target_tiers_master_non_vacuous_and_tight (K : Nat) :
    fortyEightSharedPortfolio = portfolio ∧
    fortyEightSharedPortfolio.length = 48 ∧
    fortyEightSharedPortfolio.Pairwise (· < ·) ∧
    (∀ k ∈ fortyEightSharedPortfolio,
      1_212_035_192 ≤ k ∧ k ≤ 857_384_015_252 ∧ k < 900_719_925_474 ∧ ¬ k ≤ k - 1) ∧
    (K ∈ fortyEightSharedPortfolio ↔
      K ∈ WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.portfolio ∨
      K ∈ fourElevenTablesSharedTiers) ∧
    elevenTablesSharedSlope3UnrolledK = 468_266_987_647 ∧
    elevenTablesSharedSlope3K = 468_267_001_447 ∧
    elevenTablesSharedSlope5UnrolledK = 780_444_973_257 ∧
    elevenTablesSharedSlope5K = 780_444_987_057 ∧
    459_244_490_549 < elevenTablesSharedSlope3UnrolledK ∧
    elevenTablesSharedSlope3UnrolledK < elevenTablesSharedSlope3K ∧
    elevenTablesSharedSlope3K < coupledRevertTxCapSlope3UnrolledK ∧
    775_680_812_618 < elevenTablesSharedSlope5UnrolledK ∧
    elevenTablesSharedSlope5UnrolledK < elevenTablesSharedSlope5K ∧
    elevenTablesSharedSlope5K < coupledSlope6K ∧
    fortyEightBaselineWarmSetsPortfolio.length = 48 ∧
    fortyEightBaselineWarmSetsPortfolio.Pairwise (· < ·) ∧
    allFiftyTwoSharedBudgets.length = 52 ∧
    allFiftyTwoSharedBudgets.Pairwise (· < ·) ∧
    (elevenTablesSharedSlope5K ≤ K ↔ 780_444_987_057 ≤ K) := by
  have hp5 := forty_eight_budget_portfolio_exact_insertion_and_order_non_vacuous_and_tight K
  have htv := eleven_tables_shared_target_budgets_and_warm_sets_gaps_non_vacuous_and_tight 0 0 0
  have hint := eleven_tables_shared_tiers_interleaved_strict_ordering_non_vacuous_and_tight K
  exact ⟨rfl,
    hp5.1,
    hp5.2.1,
    hp5.2.2.2.2.2.2.1,
    hp5.2.2.2.1,
    htv.1,
    htv.2.1,
    htv.2.2.1,
    htv.2.2.2.1,
    hint.1,
    Nat.lt_trans hint.2.1 hint.2.2.1,
    Nat.lt_trans hint.2.2.2.1 hint.2.2.2.2.1,
    hint.2.2.2.2.2.2.2.2.2.2.2.1,
    Nat.lt_trans hint.2.2.2.2.2.2.2.2.2.2.2.2.1 hint.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    Nat.lt_trans hint.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hint.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp5.2.2.2.2.2.2.2.1,
    hp5.2.2.2.2.2.2.2.2.1,
    hp5.2.2.2.2.2.2.2.2.2.2.1,
    hp5.2.2.2.2.2.2.2.2.2.2.2.1,
    hp5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 7 (`non_vacuous_and_tight`, **48-Budget Strict `yukonScore` Monotonicity, IEEE-754 `float64` Exactness (`< 2^53 - 1`) & `claim.json ≤ 128` Byte Compliance (`fortyEightSharedClaims`)**):
Unites Theorems 7 and 8 of `SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth` into a complete
Yukon verifier audit across all 48 budgets of `fortyEightSharedPortfolio`. -/
theorem forty_eight_shared_yukon_score_and_claims_complete_audit_non_vacuous_and_tight
    (minutes K : Nat) :
    (fortyEightSharedPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ k1 ∈ fortyEightSharedPortfolio,
      ∀ k2 ∈ fortyEightSharedPortfolio,
        k1 < k2 ↔ yukonScore k1 minutes < yukonScore k2 minutes) ∧
    (∀ k ∈ fortyEightSharedPortfolio,
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    fortyEightSharedClaims.length = 48 ∧
    fortyEightSharedClaims.map Prod.fst = fortyEightSharedPortfolio ∧
    (∀ entry ∈ fortyEightSharedClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    validFiniteClaim elevenTablesSharedSlope3UnrolledK (verifierClaimJson "468266987647") = true ∧
    validFiniteClaim elevenTablesSharedSlope3K (verifierClaimJson "468267001447") = true ∧
    validFiniteClaim elevenTablesSharedSlope5UnrolledK (verifierClaimJson "780444973257") = true ∧
    validFiniteClaim elevenTablesSharedSlope5K (verifierClaimJson "780444987057") = true ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) ∧
    (validFiniteClaim K (verifierClaimJson "780444987057") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) := by
  have hsc := forty_eight_shared_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes K
  have hcl := forty_eight_shared_claims_valid_and_within_128_bytes_non_vacuous_and_tight K
  exact ⟨hsc.1,
    hsc.2.1,
    hsc.2.2.1,
    hcl.1,
    hcl.2.1,
    hcl.2.2.1,
    hcl.2.2.2.2.1,
    hcl.2.2.2.2.2.2.1,
    hcl.2.2.2.2.2.2.2.2.1,
    hcl.2.2.2.2.2.2.2.2.2.2.1,
    hsc.2.2.2.2.2.2.2.2.2,
    hcl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`, **Integrated `WordToWordNoStubCallAndFortyEightBudgetMaster` + `GuestExhaustiveHtabInventoryAndSlopeAbsorption` Master Synthesis**):
Combines `WordToWordNoStubCallAndFortyEightBudgetMaster.integrated_master_non_vacuous_and_tight`
with the full suite of `GuestExhaustiveHtabInventoryAndSlopeAbsorption` (`general_side_regime_absorption`,
`slope_sum`, `absorption_tight`, `threshold_sharp`, `known_slopes`, `tstore_slope_exceeds`,
`tstore_tx_budget`, `tstore_witness`, `tstore_sensitivity`). -/
theorem integrated_word_to_word_no_stub_call_and_exhaustive_htab_inventory_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat) (l : List (Nat × Nat))
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4)
    (hS_l : B + (l.map Prod.snd).sum ≤ S)
    (h_each : ∀ p ∈ l, p.1 ≤ 50000 * p.2) :
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 ≠ storeConstsStubLocation →
      PanToStackNoStoreConsts.StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
      StackRemoveAndNamesNoStoreConsts.NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) ∧
    blk + (l.map Prod.fst).sum ≤ 100_000_000_000 ∧
    (40 * 100_000_000_000 = S * S ∧ 100_000_000_000 + 0 = 100_000_000_000) ∧
    ¬ (∀ B' U' T' blk' : Nat, B' + U' ≤ S → 40 * blk' ≤ B' * B' → T' ≤ 50001 * U' → blk' + T' ≤ 100000000000) ∧
    (5 * 7989 ≤ 21 * 50000 ∧ 5 * 5611 ≤ 30 * 50000 ∧
      167772 + 2280 ≤ 60 * 50000 ∧ 2 * 6250 ≤ 320 * 50000) ∧
    (tstoreTicks 83826 - tstoreTicks 83825 = 2 * 83825 ∧ 50000 < 83825) ∧
    11 * tstoreTicks 83826 + tstoreTicks 77194 = 83_252_695_392 ∧
    (83_252_695_392 ≤ 50000 * (11 * 2 * 83826 + 2 * 77194) ∧
      2 * tstoreTicks 167652 = 56_214_050_904 ∧
      50000 * 167772 < 2 * tstoreTicks 167652) ∧
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    kPanElevenTablesShared = 156_088_992_805 ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
      400_061_540 * 10000 < 26 * 156_088_992_805 ∧
      400_061_540 * 10000 < 26 * 155_688_931_265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (CertificateAt 1212035192 → ∀ K ∈ portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  have him := integrated_master_non_vacuous_and_tight
    arch prog wc ac perf info j bd ptr f B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4
  have hsum := slope_sum l h_each
  exact ⟨him.1,
    him.2.1,
    general_side_regime_absorption l B blk hS_l hb hsum,
    absorption_tight,
    threshold_sharp,
    known_slopes,
    tstore_slope_exceeds,
    tstore_witness,
    tstore_sensitivity,
    him.2.2.1,
    him.2.2.2.1,
    him.2.2.2.2.1,
    him.2.2.2.2.2.1,
    him.2.2.2.2.2.2.1,
    him.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`, **Direct Target Non-`.timeOut` to 48-Budget, 52-Budget, 44-Budget & 30-Tier `InitE.Certificate submission (.finite K)` Bridge with Unconditional `WordToWord` Call Safety**):
Combines `forty_eight_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight`
with `forty_eight_certified_non_vacuous_and_tight` and `panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight`. -/
theorem forty_eight_budget_certificates_and_unconditional_stack_names_from_u128_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
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
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (PanToStackNoStoreConsts.StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       StackRemoveAndNamesNoStoreConsts.NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
    (fortyEightSharedPortfolio.length = 48 ∧
     fortyEightSharedPortfolio.Pairwise (· < ·) ∧
     ∀ K ∈ fortyEightSharedPortfolio, K < 900_719_925_474 ∧
       ∃ submission : InitE.Submission,
         submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (fortyEightBaselineWarmSetsPortfolio.length = 48 ∧
     fortyEightBaselineWarmSetsPortfolio.Pairwise (· < ·) ∧
     ∀ K ∈ fortyEightBaselineWarmSetsPortfolio, K < 900_719_925_474 ∧
       InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (allFiftyTwoSharedBudgets.length = 52 ∧
     allFiftyTwoSharedBudgets.Pairwise (· < ·) ∧
     ∀ K ∈ allFiftyTwoSharedBudgets, K < 900_719_925_474 ∧
       InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (∀ K ∈ fortyFourWarmSetsPortfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    (∀ K ∈ thirtyTierHierarchy, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3UnrolledK) (.finite elevenTablesSharedSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3K) (.finite elevenTablesSharedSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5UnrolledK) (.finite elevenTablesSharedSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5K) (.finite elevenTablesSharedSlope5K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity := by
  have hcert9 := forty_eight_budget_and_thirty_tier_submission_certificates_from_u128_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_u128
  exact ⟨hcert9.1,
    panToWordToWord_NoStubCall_non_vacuous_and_tight arch prog wc ac,
    panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f,
    hcert9.2.1,
    hcert9.2.2.1,
    hcert9.2.2.2.1,
    hcert9.2.2.2.2.1,
    hcert9.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.2.1,
    hcert9.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 10 (`non_vacuous_and_tight`, **Master Wave 5 (`W5_135`) Self-Contained Exhaustive `htab` Inventory (`general_side_regime_absorption`, `threshold_sharp`, `tstore_sensitivity`), Unconditional `WordToWord`/`StackNames` Call Safety & 48-Budget Campaign Certificate**):
Simultaneously unites:
- Exhaustive `guest.pp.pnk` hash-table slope absorption (`general_side_regime_absorption`, `slope_sum`,
  `absorption_tight`, `threshold_sharp`, `known_slopes`) and transient-storage (`ts+64`) marginal excess,
  witness, and tick-model sensitivity (`tstore_slope_exceeds`, `tstore_tx_budget`, `tstore_witness`,
  `tstore_sensitivity`) from `GuestExhaustiveHtabInventoryAndSlopeAbsorption`,
- Unconditional `WordNoStubCall` across `PanToWord` (`panToWord_NoStubCall`) and all 10 `WordToWord` passes
  (`panToWordToWord_NoStubCall_non_vacuous_and_tight`), unconditional `StackNoSt` and `NoStubCall` through
  `StackNames` (`panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight`), tight `NSC`
  witnesses (`NSC_rejects_stub_call_non_vacuous_and_tight`, `NSC_accepts_user_call_non_vacuous_and_tight`,
  `NSC_allows_storeConsts_non_vacuous_and_tight`), and `LabToTarget.removeLabels` clean-section preservation,
- Shared 11-table budget absorption (`blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571`),
  `kPanElevenTablesShared = 156_088_992_805`, 12-tx feasible bracket (`155_688_931_265 ≤ 156_088_992_805`,
  gap `400_061_540 < 0.26%`), `5×` Yukon margin (`120_274_961_449`), and `6×` impossibility,
- Concrete `InitE.Certificate submission (.finite K)` (`submission = baselineWithFiniteK K`) across
  all **48 budgets** in `fortyEightSharedPortfolio`, all **48 budgets** in `fortyEightBaselineWarmSetsPortfolio`,
  all **52 budgets** in `allFiftyTwoSharedBudgets`, `fortyEightSharedClaims` `≤ 128`-byte compliance, and
  purified `.Solver` module path admission (`0` `Bounded*` imports). -/
theorem master_exhaustive_htab_inventory_word_to_word_no_stub_call_and_forty_eight_budget_campaign_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (panProg : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (cAsm : AsmConfigExact width) (perf j : Bool)
    (info f : Spt Nat)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp ptr : Nat)
    (off bd : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (hpan : removeLabels ic cAsm pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative cAsm perf (WordToWord.compile wc cAsm
          (panToWordCompileProgHOL arch panProg)).2).2.2.2)) = some (L', labs'))
    (p : HolProg width) (hp : StackNoSt p = true)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat) (l : List (Nat × Nat))
    (hS : B + u2 + u3 + u4 ≤ S) (hblk : 40 * blk ≤ B * B) (hloc_b : 84 * loc ≤ M * B)
    (hu2 : 21 * t2 ≤ 5 * 7989 * u2) (hu3 : 30 * t3 ≤ 5 * 5611 * u3)
    (hu4 : 60 * t4 ≤ (M + 2280) * u4)
    (hS_l : B + (l.map Prod.snd).sum ≤ S)
    (h_each : ∀ pair ∈ l, pair.1 ≤ 50000 * pair.2)
    (n_f k_f a n_blk a_c n_c d_t w_t d_del p_del q_del w_del minutes : Nat)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (htx : 21 * d_t + w_t ≤ M)
    (ha_tx : 30 * a ≤ 167772) (hn_blk : 30 * n_blk ≤ 2000000)
    (ha_c : a_c ≤ 5611) (hn_c : n_c ≤ 66666)
    (H2 : p_del + cycleUnits * q_del ≤ w_del)
    (not_timeOut_u128 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    (∀ y ∈ panToWordCompileProgHOL arch panProg, WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
    (∀ y ∈ (WordToWord.compile wc cAsm (panToWordCompileProgHOL arch panProg)).2,
      WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative cAsm perf (WordToWord.compile wc cAsm
        (panToWordCompileProgHOL arch panProg)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (PanToStackNoStoreConsts.StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       StackRemoveAndNamesNoStoreConsts.NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
    (NSC (WordLangProgHOL.seq (α := BitVec width) .skip
       (.call none (some storeConstsStubLocation) [] none)) = false ∧
     NSC (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true ∧
     NSC (WordLangProgHOL.storeConsts (α := BitVec width) 0 1 2 3 []) = true) ∧
    (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum ∧
    blk + (l.map Prod.fst).sum ≤ 100_000_000_000 ∧
    (40 * 100_000_000_000 = S * S ∧ 100_000_000_000 + 0 = 100_000_000_000) ∧
    ¬ (∀ B' U' T' blk' : Nat, B' + U' ≤ S → 40 * blk' ≤ B' * B' → T' ≤ 50001 * U' → blk' + T' ≤ 100000000000) ∧
    (5 * 7989 ≤ 21 * 50000 ∧ 5 * 5611 ≤ 30 * 50000 ∧
      167772 + 2280 ≤ 60 * 50000 ∧ 2 * 6250 ≤ 320 * 50000) ∧
    (tstoreTicks 83826 - tstoreTicks 83825 = 2 * 83825 ∧ 50000 < 83825) ∧
    (120 + 2 * 83826 ≤ 167772 ∧ 11 * 167772 + 120 + 2 * 77194 ≤ S) ∧
    11 * tstoreTicks 83826 + tstoreTicks 77194 = 83_252_695_392 ∧
    (83_252_695_392 ≤ 50000 * (11 * 2 * 83826 + 2 * 77194) ∧
      2 * tstoreTicks 167652 = 56_214_050_904 ∧
      50000 * 167772 < 2 * tstoreTicks 167652) ∧
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (kPanElevenTablesShared = 156_088_992_805 ∧
      kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
      400_061_540 * 10000 < 26 * 156_088_992_805 ∧
      400_061_540 * 10000 < 26 * 155_688_931_265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) ∧
    fortyEightSharedPortfolio.length = 48 ∧
    fortyEightSharedPortfolio.Pairwise (· < ·) ∧
    (∀ K ∈ fortyEightSharedPortfolio, K < 900_719_925_474 ∧
      ∃ submission : InitE.Submission,
        submission = baselineWithFiniteK K ∧ InitE.Certificate submission (.finite K)) ∧
    allFiftyTwoSharedBudgets.length = 52 ∧
    (∀ K ∈ allFiftyTwoSharedBudgets, K < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (fortyEightSharedPortfolio.map (fun k_b => yukonScore k_b minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ fortyEightSharedClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3UnrolledK) (.finite elevenTablesSharedSlope3UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3K) (.finite elevenTablesSharedSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5UnrolledK) (.finite elevenTablesSharedSlope5UnrolledK) ∧
    InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5K) (.finite elevenTablesSharedSlope5K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    isSolverModulePath ["InitECandidate", "Solver", "SelfContainedExhaustiveHtabInventoryAndNoStubCallSynth"] = true ∧
    admittedRelativePath .regularFile
      ["InitECandidate", "Solver", "SelfContainedExhaustiveHtabInventoryAndNoStubCallSynth"] true = true ∧
    zeroBoundedImportCount = 0 := by
  have hm := master_pan_to_word_no_stub_call_eleven_tables_shared_and_forty_eight_budget_campaign_certificate_non_vacuous_and_tight
    arch panProg wc cAsm perf j sc dc mh sp ptr off bd ic pos labs ffis L' labs' hpan p hp
    B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc_b hu2 hu3 hu4
    n_f k_f a n_blk a_c n_c d_t w_t d_del p_del q_del w_del minutes
    oracles c depth hlab compiled depthBound htx ha_tx hn_blk ha_c hn_c H2 not_timeOut_u128
  have hsum := slope_sum l h_each
  refine ⟨?_,
    panToWordToWord_NoStubCall_non_vacuous_and_tight arch panProg wc cAsm,
    panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight arch panProg wc cAsm perf info j bd ptr f,
    ⟨NSC_rejects_stub_call_non_vacuous_and_tight (α := BitVec width),
     NSC_accepts_user_call_non_vacuous_and_tight (α := BitVec width),
     NSC_allows_storeConsts_non_vacuous_and_tight (α := BitVec width)⟩,
    hsum,
    general_side_regime_absorption l B blk hS_l hblk hsum,
    absorption_tight,
    threshold_sharp,
    known_slopes,
    tstore_slope_exceeds,
    tstore_tx_budget,
    tstore_witness,
    tstore_sensitivity,
    hm.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by decide,
    by decide,
    rfl⟩
  intro y hy
  exact ⟨hm.1 y hy, hm.2.1 y hy⟩

#print axioms general_side_regime_absorption_and_sharp_threshold_complete_audit_non_vacuous_and_tight
#print axioms transient_storage_ts64_slope_witness_and_sensitivity_audit_non_vacuous_and_tight
#print axioms word_to_word_and_stack_names_unconditional_no_stub_call_complete_audit_non_vacuous_and_tight
#print axioms frontend_to_stack_names_and_lab_to_target_complete_safety_chain_non_vacuous_and_tight
#print axioms unified_eleven_tables_and_general_side_regime_absorption_closure_non_vacuous_and_tight
#print axioms forty_eight_budget_portfolio_and_target_tiers_master_non_vacuous_and_tight
#print axioms forty_eight_shared_yukon_score_and_claims_complete_audit_non_vacuous_and_tight
#print axioms integrated_word_to_word_no_stub_call_and_exhaustive_htab_inventory_non_vacuous_and_tight
#print axioms forty_eight_budget_certificates_and_unconditional_stack_names_from_u128_non_vacuous_and_tight
#print axioms master_exhaustive_htab_inventory_word_to_word_no_stub_call_and_forty_eight_budget_campaign_certificate_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedExhaustiveHtabInventoryAndNoStubCallSynth
