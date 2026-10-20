import InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption
import InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster
import InitECandidate.Solver.SelfContainedUnconditionalNoStoreConstsNoStubCallAndFortyEightBudgetSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedSubcallRevertAbsorptionAndFiftyBudgetSynth` — Wave 5 Atomic Worker `W5_145`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`GuestTransientStorageSubcallRevertAndAbsorption` (`11/11` tight)**:
   - Superadditivity of `k(k-1)` and `buildTicks` (`q_super`, `build_super`, `split_le`, `split_strict`),
   - Worst-case per-tx revert and halving split (`tx_worst_revert = 125_075_300_410`, `half_split`),
   - Exact absorption thresholds (`lmax_revert`: `L ≤ 5_000`, `lmax_norevert`: `L ≤ 10_000`, `lmax_sharp`),
   - Absorption under a run cap `L ≤ 5_000` into `10^11` ticks (`absorbed_with_cap`) and the `156_088_992_805`
     storage envelope (`5× < Yukon`, `guest_vs_cap`).
2. **`TransientStorageRemainingTablesAndFiftyBudgetMaster` (`12/12` tight)**:
   - Tight EIP-1153 transaction key cap (`key_cap_non_vacuous_and_tight`), block packing and construction costs
     (`packing_and_tx_build_non_vacuous_and_tight`, `capped_build_non_vacuous_and_tight`,
     `block_and_revert_non_vacuous_and_tight`),
   - One-slope margin (`one_slope_margin_non_vacuous_and_tight`), transient obstruction
     (`transient_obstruction_non_vacuous_and_tight`), and remaining-table side-regime absorption
     (`remaining_absorption_non_vacuous_and_tight`),
   - Unconditional `PanSimp` to `StackToLab` safety (`compiler_chain_non_vacuous_and_tight`) and the
     strictly increasing 50-budget portfolio (`fifty_shape_non_vacuous_and_tight`,
     `fifty_payloads_non_vacuous_and_tight`, `fifty_certificates_non_vacuous_and_tight`,
     `integrated_master_non_vacuous_and_tight`).
3. **`SelfContainedUnconditionalNoStoreConstsNoStubCallAndFortyEightBudgetSynth` (`10/10` tight)**:
   - Unconditional `panToStackNames_NoSt_and_NoStubCall_unconditional` and `StackToLab.flattenHOL`
     `storeConsts` non-visitation (`FlattenVisitsSt = false`),
   - Shared 11-table hierarchy and side-regime slope absorption (`156_088_992_805`, `5× < Yukon`),
   - 48-budget and 50-budget portfolios below Yukon (`900_719_925_474`) with conditional finite certificates.
-/

namespace InitECandidate.Solver.SelfContainedSubcallRevertAbsorptionAndFiftyBudgetSynth

open Classical
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedIsoReducedK
open InitECandidate.Solver.SelfContainedPush31MasterK
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedEndToEndCert
open InitECandidate.Solver.SelfContainedSolutionCandidates
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.YukonVerifyScriptAudit
open InitECandidate.Solver.ExactKeccakCopyLoopUnrolledCert
open InitECandidate.Solver.ExactKeccakSixPassReducedCert
open InitECandidate.Solver.SelfContainedTenCandidateHierarchy
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (WordNoStubCall NoStubCall)
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open InitECandidate.Solver.WordToWordNoStubCall (
  NSC
  panToWordToWord_NoStubCall
  panToStackNames_NoSt_and_NoStubCall_unconditional
)
open InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts (
  panToStackNames_bodies_StackNoSt_unconditional
  stackRemove_storeConsts_not_skip
  flatten_storeConsts_empty
  FlattenVisitsSt
  not_visits_of_StackNoSt
  visits_storeConsts_tight
  progToSection_sectionId
  panToLabSection_unconditional
)
open InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit (
  intrinsic keyGas txCap blockGas buildTicks
)
open InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption (
  q_super
  build_super
  split_le
  split_strict
  tx_worst_revert
  half_split
  lmax_revert
  lmax_norevert
  lmax_sharp
  absorbed_with_cap
  guest_vs_cap
)
open InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster (
  FiftyShape
  ClaimPayloads
  KeyCap
  PackingAndBuild
  BlockCosts
  OneSlopeMargin
  TransientObstruction
  RemainingTables
  CompilerSafety
  key_cap_non_vacuous_and_tight
  packing_and_tx_build_non_vacuous_and_tight
  capped_build_non_vacuous_and_tight
  block_and_revert_non_vacuous_and_tight
  one_slope_margin_non_vacuous_and_tight
  transient_obstruction_non_vacuous_and_tight
  remaining_absorption_non_vacuous_and_tight
  fifty_shape_non_vacuous_and_tight
  fifty_payloads_non_vacuous_and_tight
  compiler_chain_non_vacuous_and_tight
  fifty_certificates_non_vacuous_and_tight
)
open InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (tstoreTicks)
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (M feasible witness coupledCost kPanCoupledRevertTxCap)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound (enter warmN truncDels truncTicks kPanWarmSets)
open InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope (journalFlags dels cycleUnits kPanSixSlopeRestored)
open InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound (txProbe kPanElevenTables)
open InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption (kPanElevenTablesShared)
open InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth (fortyEightSharedClaims)
open InitECandidate.Solver.SelfContainedElevenTablesAndSharedAbsorptionSynth (
  elevenTablesSlope3UnrolledK
  elevenTablesSlope3K
  elevenTablesSlope5UnrolledK
  elevenTablesSlope5K
  elevenTablesSharedSlope3UnrolledK
  elevenTablesSharedSlope3K
  elevenTablesSharedSlope5UnrolledK
  elevenTablesSharedSlope5K
  fortyFourSortedPortfolio
  fortyEightSharedPortfolio
  fortyEightElevenTablesPortfolio
)
open InitECandidate.Solver.GuestMergeTxUnionEnvelope (locCoup mergeLin)
open InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope (F G kPanUnifiedAllTables)
open InitECandidate.Solver.GuestSubBlockTxSplittingDominance (localCost sD sR sA sC sW prefixCost txMinUnits txResetTicks)
open InitECandidate.Solver.GuestAccessListAndCallStackDominance (revertCost kPanAccessCall)
open InitECandidate.Solver.GuestStateRestoreCoupledTightening (restoreOf sstoreGas delsPerCall)
open InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes (Sizes endTx dirty cycleTicks)
open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock (IsStubLabel CleanSection)
open InitECandidate.Solver.LabToTargetSectionCleanPreservation (Sec ids)
open InitECandidate.Solver.SelfContainedFortyBudgetPortfolioSynth (fortyAccessCallClaims)
open Flapjack.Pancake.Proofs.PanToTarget
open InitECandidate.Solver.SelfContainedUnconditionalNoStoreConstsNoStubCallAndFortyEightBudgetSynth (
  unconditional_body_flatten_and_store_consts_discrimination_synthesis_non_vacuous_and_tight
  unified_word_to_word_and_stack_to_lab_unconditional_safety_synthesis_non_vacuous_and_tight
  aggregate_and_pointwise_side_absorption_sharp_threshold_synthesis_non_vacuous_and_tight
  unconditional_safety_eleven_table_bracket_and_shared_absorption_synthesis_non_vacuous_and_tight
  eleven_tables_shared_hierarchy_and_pointwise_side_absorption_synthesis_non_vacuous_and_tight
  forty_eight_shape_certificates_claim_payloads_and_alignment_synthesis_non_vacuous_and_tight
  integrated_master_and_unconditional_forty_eight_budget_synthesis_non_vacuous_and_tight
  pan_to_target_and_integrated_forty_eight_budget_master_synthesis_non_vacuous_and_tight
  forty_eight_certificates_claims_yukon_score_and_eleven_table_bracket_master_non_vacuous_and_tight
  grand_unconditional_no_store_consts_no_stub_call_and_forty_eight_budget_synth_master_non_vacuous_and_tight
)

abbrev fiftyPortfolio : List Nat :=
  TransientStorageRemainingTablesAndFiftyBudgetMaster.portfolio

abbrev fiftyClaims : List (Nat × String) :=
  TransientStorageRemainingTablesAndFiftyBudgetMaster.fiftyClaims

abbrev fortyEightPortfolio : List Nat :=
  ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Complete synthesis of `buildTicks` superadditivity
(`q_super`, `build_super`, `split_le`, `split_strict`), worst-case per-tx revert
(`tx_worst_revert = 125_075_300_410`, `half_split`), and tight EIP-1153 transaction key cap and
block packing (`KeyCap`, `PackingAndBuild`, `capped_build_non_vacuous_and_tight`, `BlockCosts`). -/
theorem subcall_revert_superadditivity_and_tx_block_packing_synthesis_non_vacuous_and_tight
    (a b : Nat) (l : List Nat) :
    (a * (a - 1) + b * (b - 1) ≤ (a + b) * (a + b - 1) ∧
     buildTicks a + buildTicks b ≤ buildTicks (a + b) ∧
     (l.map buildTicks).sum ≤ buildTicks l.sum ∧
     (buildTicks 2 + buildTicks 2 = 10 ∧ buildTicks 4 = 30) ∧
     2 * buildTicks 158_162 = 125_075_300_410 ∧
     (2 * buildTicks 79_081 = 31_268_627_400 ∧ buildTicks 158_162 = 62_537_650_205)) ∧
    KeyCap ∧
    PackingAndBuild ∧
    ((∀ k : Nat, intrinsic + keyGas * k ≤ txCap → buildTicks k ≤ 62_537_650_205) ∧
     (intrinsic + keyGas * 158_162 ≤ txCap ∧ buildTicks 158_162 = 62_537_650_205)) ∧
    BlockCosts :=
  ⟨⟨q_super a b, build_super a b, split_le l, split_strict, tx_worst_revert, half_split⟩,
   key_cap_non_vacuous_and_tight,
   packing_and_tx_build_non_vacuous_and_tight,
   capped_build_non_vacuous_and_tight,
   block_and_revert_non_vacuous_and_tight⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Exact collision-run absorption thresholds with and without
`REVERT` (`lmax_revert`: `10 * L ≤ 50_000 ↔ L ≤ 5_000`, `lmax_norevert`: `5 * L ≤ 50_000 ↔ L ≤ 10_000`,
`lmax_sharp`), absorption under a run cap `L ≤ 5_000` into `10^11` ticks (`absorbed_with_cap`),
the `156_088_992_805` envelope (`5× < Yukon`, `guest_vs_cap`), `OneSlopeMargin`, and
`TransientObstruction`. -/
theorem exact_absorption_thresholds_run_cap_and_one_slope_margin_synthesis_non_vacuous_and_tight
    (L n u B blk : Nat) (hL : L ≤ 5_000) (hu : n ≤ u)
    (hS : B + u ≤ 2_000_000) (hblk : 40 * blk ≤ B * B) :
    ((10 * L ≤ 50_000 ↔ L ≤ 5_000) ∧
     (5 * L ≤ 50_000 ↔ L ≤ 10_000) ∧
     (10 * 5_000 = 50_000 ∧ 50_000 < 10 * 5_001 ∧ 5 * 10_000 = 50_000 ∧ 50_000 < 5 * 10_001) ∧
     blk + 10 * L * n ≤ 100_000_000_000 ∧
     (5_000 < 158_162 ∧ 5 * 156_088_992_805 < yukon)) ∧
    OneSlopeMargin ∧
    TransientObstruction :=
  ⟨⟨lmax_revert L, lmax_norevert L, lmax_sharp,
    absorbed_with_cap L n u B blk hL hu hS hblk, guest_vs_cap⟩,
   one_slope_margin_non_vacuous_and_tight,
   transient_obstruction_non_vacuous_and_tight⟩

/-- Theorem 3 (`non_vacuous_and_tight`): Synthesis of `absorbed_with_cap`, `RemainingTables`
(`remaining_absorption_non_vacuous_and_tight`), and
`aggregate_and_pointwise_side_absorption_sharp_threshold_synthesis_non_vacuous_and_tight`. -/
theorem run_cap_remaining_tables_and_side_regime_sharp_threshold_synthesis_non_vacuous_and_tight
    (L n u B_cap blk_cap : Nat) (hL : L ≤ 5_000) (hu : n ≤ u)
    (hS_cap : B_cap + u ≤ 2_000_000) (hblk_cap : 40 * blk_cap ≤ B_cap * B_cap)
    (B_sc U T blk_sc : Nat)
    (hS_sc : B_sc + U ≤ S) (hblk_sc : 40 * blk_sc ≤ B_sc * B_sc) (hT_sc : T ≤ 50_000 * U)
    (l_reg l_per : List (Nat × Nat)) (B_reg blk_reg B_per blk_per : Nat)
    (hS_reg : B_reg + (l_reg.map Prod.snd).sum ≤ S) (hblk_reg : 40 * blk_reg ≤ B_reg * B_reg)
    (hslope_reg : (l_reg.map Prod.fst).sum ≤ 50_000 * (l_reg.map Prod.snd).sum)
    (hS_per : B_per + (l_per.map Prod.snd).sum ≤ S) (hblk_per : 40 * blk_per ≤ B_per * B_per)
    (hper : ∀ p ∈ l_per, p.1 ≤ 50_000 * p.2) :
    (blk_cap + 10 * L * n ≤ 100_000_000_000 ∧
     (10 * L ≤ 50_000 ↔ L ≤ 5_000) ∧
     (5 * L ≤ 50_000 ↔ L ≤ 10_000) ∧
     (5_000 < 158_162 ∧ 5 * 156_088_992_805 < yukon)) ∧
    (RemainingTables ∧
     (blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
      ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
        T ≤ 50_001 * U → blk + T ≤ 100_000_000_000))) ∧
    ((blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
      ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
        T ≤ 50_001 * U → blk + T ≤ 100_000_000_000)) ∧
     ((l_per.map Prod.fst).sum ≤ 50_000 * (l_per.map Prod.snd).sum ∧
      blk_per + (l_per.map Prod.fst).sum ≤ 100_000_000_000) ∧
     (40 * 100_000_000_000 = S * S ∧
      0 + 2_000_000 ≤ S ∧ 100_000_000_000 = 50_000 * 2_000_000 ∧
      50_001 * 2_000_000 > 100_000_000_000) ∧
     (blk_sc + T ≤ 100_000_000_000 ∧
      blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
      (l_per.map Prod.fst).sum ≤ 50_000 * (l_per.map Prod.snd).sum ∧
      (40 * 100_000_000_000 = S * S ∧ 100_000_000_000 + 0 = 100_000_000_000) ∧
      ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B → T ≤ 50_001 * U → blk + T ≤ 100_000_000_000) ∧
      (5 * 7_989 ≤ 21 * 50_000 ∧ 5 * 5_611 ≤ 30 * 50_000 ∧
       167_772 + 2_280 ≤ 60 * 50_000 ∧ 2 * 6_250 ≤ 320 * 50_000) ∧
      (tstoreTicks 83_826 - tstoreTicks 83_825 = 2 * 83_825 ∧ 50_000 < 83_825) ∧
      (120 + 2 * 83_826 ≤ 167_772 ∧ 11 * 167_772 + 120 + 2 * 77_194 ≤ S) ∧
      11 * tstoreTicks 83_826 + tstoreTicks 77_194 = 83_252_695_392 ∧
      (83_252_695_392 ≤ 50_000 * (11 * 2 * 83_826 + 2 * 77_194) ∧
       2 * tstoreTicks 167_652 = 56_214_050_904 ∧
       50_000 * 167_772 < 2 * tstoreTicks 167_652))) :=
  ⟨⟨absorbed_with_cap L n u B_cap blk_cap hL hu hS_cap hblk_cap,
    lmax_revert L, lmax_norevert L, guest_vs_cap⟩,
   remaining_absorption_non_vacuous_and_tight l_reg B_reg blk_reg hS_reg hblk_reg hslope_reg,
   aggregate_and_pointwise_side_absorption_sharp_threshold_synthesis_non_vacuous_and_tight
     B_sc U T blk_sc hS_sc hblk_sc hT_sc l_reg l_per B_reg blk_reg B_per blk_per
     hS_reg hblk_reg hslope_reg hS_per hblk_per hper⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Unconditional compiler chain without `hcall` from
`PanSimp` to `StackToLab` (`panToStackNames_NoSt_and_NoStubCall_unconditional`,
`FlattenVisitsSt = false`, `CompilerSafety`) coupled with `storeConsts` discrimination witnesses. -/
theorem unconditional_pan_to_stack_to_lab_no_store_consts_and_no_stub_call_synthesis_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (p_w : WordLangProgHOL (BitVec width))
    (tail : Bool) (s b : Nat) (stub : Option Nat) (sid next : Nat) (cs bs : List Nat)
    (n : Nat) (p_sec : HolProg width) :
    CompilerSafety arch prog wc ac perf info j bd ptr f ∧
    ((∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false)) ∧
     (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
     (StackNoSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = false ∧
      FlattenVisitsSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = true ∧
      StackToLab.flattenHOL tail (.storeConsts 0 1 none : HolProg width) sid next cs bs =
        (.list [], false, next)) ∧
     StackRemove.comp j bd ptr (.storeConsts 3 4 none : HolProg width) ≠ .skip ∧
     StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
       (.list [], false, next) ∧
     (StackToLab.progToSectionHOL (n, p_sec)).sectionId = n) ∧
    (((∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
     (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
     (∀ y ∈ panToWordCompileProgHOL arch prog,
      WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
     NSC p_w = WordNoStubCall p_w ∧
     NSC (WordLangProgHOL.seq (α := BitVec width) .skip
       (.call none (some storeConstsStubLocation) [] none)) = false ∧
     NSC (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true ∧
     NSC (WordLangProgHOL.storeConsts (α := BitVec width) 0 1 2 3 []) = true) ∧
    (StackNoSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = false ∧
     FlattenVisitsSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = true ∧
     StackToLab.flattenHOL tail (.storeConsts 0 1 none : HolProg width) sid next cs bs =
       (.list [], false, next))) :=
  ⟨compiler_chain_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f,
   unconditional_body_flatten_and_store_consts_discrimination_synthesis_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f tail s b stub sid next cs bs n p_sec,
   unified_word_to_word_and_stack_to_lab_unconditional_safety_synthesis_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f p_w tail sid next cs bs⟩

/-- Theorem 5 (`non_vacuous_and_tight`): Joint synthesis of unconditional compiler safety
(`CompilerSafety`), the `156_088_992_805` shared 11-table envelope (`5× < Yukon` margin
`120_274_961_449`), and `absorbed_with_cap` under a run cap `L ≤ 5_000`. -/
theorem compiler_safety_eleven_table_envelope_and_run_cap_absorption_synthesis_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (L n_ts u_ts B_cap blk_cap : Nat) (hL : L ≤ 5_000) (hu_ts : n_ts ≤ u_ts)
    (hS_cap : B_cap + u_ts ≤ 2_000_000) (hblk_cap : 40 * blk_cap ≤ B_cap * B_cap)
    (l_reg : List (Nat × Nat)) (B_reg blk_reg : Nat)
    (hS_reg : B_reg + (l_reg.map Prod.snd).sum ≤ S) (hblk_reg : 40 * blk_reg ≤ B_reg * B_reg)
    (hslope_reg : (l_reg.map Prod.fst).sum ≤ 50_000 * (l_reg.map Prod.snd).sum)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4) :
    CompilerSafety arch prog wc ac perf info j bd ptr f ∧
    (blk_cap + 10 * L * n_ts ≤ 100_000_000_000 ∧
     (5_000 < 158_162 ∧ 5 * 156_088_992_805 < yukon)) ∧
    ((kPanElevenTablesShared = 156_088_992_805 ∧
      (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
       coupledCost witness ≤ kPanElevenTablesShared ∧
       kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
       400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
       400_061_540 * 10_000 < 26 * 155_688_931_265)) ∧
     (blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
      (kPanElevenTablesShared = 156_088_992_805 ∧
       kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
      (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
       coupledCost witness ≤ kPanElevenTablesShared ∧
       kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
       400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
       400_061_540 * 10_000 < 26 * 155_688_931_265) ∧
      (5 * kPanElevenTablesShared < yukon ∧
       yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
      (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) ∧
      (5 * 7_989 ≤ 21 * 1_903 ∧ 5 * 5_611 ≤ 30 * 936 ∧ M + 2_280 ≤ 60 * 2_835) ∧
      S * (S - B) ≤ S * S - B * B ∧
      (40 * 100_000_000_000 ≤ S * S ∧ 84 * 3_994_571_428 ≤ M * S ∧
       (21 * S * S + 130 * M * S) / 840 = 151_929_428_571)) ∧
     (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       y.1 = storeConstsStubLocation ∨
       (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
        NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
        FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
        (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
     (blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
      ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
        T ≤ 50_001 * U → blk + T ≤ 100_000_000_000))) :=
  ⟨compiler_chain_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f,
   ⟨absorbed_with_cap L n_ts u_ts B_cap blk_cap hL hu_ts hS_cap hblk_cap, guest_vs_cap⟩,
   unconditional_safety_eleven_table_bracket_and_shared_absorption_synthesis_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f l_reg B_reg blk_reg hS_reg hblk_reg hslope_reg
     B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc h2 h3 h4⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Synthesis of the 11-table shared hierarchy
(`kPanSixSlopeRestored < coupledCost witness < kPanElevenTablesShared < kPanAccessCall < kPanWarmSets < kPanElevenTables`),
pointwise side-regime absorption, `OneSlopeMargin`, and sub-call revert superadditivity (`split_le`). -/
theorem eleven_tables_hierarchy_pointwise_absorption_and_subcall_revert_synthesis_non_vacuous_and_tight
    (l_chunks : List Nat)
    (a w B u2 u3 u4 blk loc t2 t3 t4 slope5 : Nat)
    (l_probe l_reg : List (Nat × Nat))
    (B_reg blk_reg : Nat)
    (ha : 30 * a + w ≤ M)
    (hS_sh : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4)
    (hl_p : ∀ p ∈ l_probe, 30 * p.1 + p.2 ≤ M)
    (hS_p : (l_probe.map (fun p => 30 * p.1 + p.2)).sum ≤ S)
    (hS_reg : B_reg + (l_reg.map Prod.snd).sum ≤ S)
    (hblk_reg : 40 * blk_reg ≤ B_reg * B_reg)
    (hper_reg : ∀ p ∈ l_reg, p.1 ≤ 50_000 * p.2) :
    ((l_chunks.map buildTicks).sum ≤ buildTicks l_chunks.sum ∧
     2 * buildTicks 158_162 = 125_075_300_410 ∧
     OneSlopeMargin ∧ TransientObstruction) ∧
    (((l_reg.map Prod.fst).sum ≤ 50_000 * (l_reg.map Prod.snd).sum ∧
      blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000) ∧
     (40 * 100_000_000_000 = S * S ∧
      0 + 2_000_000 ≤ S ∧ 100_000_000_000 = 50_000 * 2_000_000 ∧
      50_001 * 2_000_000 > 100_000_000_000) ∧
     (blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
      (l_reg.map Prod.fst).sum ≤ 50_000 * (l_reg.map Prod.snd).sum ∧
      ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B → T ≤ 50_001 * U → blk + T ≤ 100_000_000_000) ∧
      (tstoreTicks 83_826 - tstoreTicks 83_825 = 2 * 83_825 ∧ 50_000 < 83_825) ∧
      (120 * (a * w) ≤ M * (30 * a + w) ∧
       txProbe (a, w) = 2 * (a * w) + 38 * w ∧
       (l_probe.map (fun p => p.1 * p.2)).sum ≤ 2_796_200_000 ∧
       (l_probe.map txProbe).sum ≤ 5_668_400_000 ∧
       kPanElevenTables = 167_431_989_338 ∧
       (5 * kPanElevenTables < yukon ∧
        yukon - 5 * kPanElevenTables = 63_559_978_784 ∧
        yukon < 6 * kPanElevenTables) ∧
       linear + 500_000_000 + (blk + 13 * loc + t2 + t3 + t4) ≤ kPanElevenTablesShared ∧
       kPanWarmSets + (l_probe.map txProbe).sum ≤ kPanElevenTables ∧
       kPanSixSlopeRestored < coupledCost witness ∧
       coupledCost witness < kPanElevenTablesShared ∧
       kPanElevenTablesShared < kPanAccessCall ∧
       kPanAccessCall < kPanWarmSets ∧
       kPanWarmSets < kPanElevenTables ∧
       kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
       400_061_540 * 10_000 < 26 * coupledCost witness ∧
       (slope5 * kPanElevenTablesShared < yukon ↔ slope5 ≤ 5) ∧
       (slope5 * kPanElevenTables < yukon ↔ slope5 ≤ 5)))) :=
  ⟨⟨split_le l_chunks, tx_worst_revert, one_slope_margin_non_vacuous_and_tight,
    transient_obstruction_non_vacuous_and_tight⟩,
   eleven_tables_shared_hierarchy_and_pointwise_side_absorption_synthesis_non_vacuous_and_tight
     a w B u2 u3 u4 blk loc t2 t3 t4 slope5 l_probe l_reg B_reg blk_reg
     ha hS_sh hblk hloc h2 h3 h4 hl_p hS_p hS_reg hblk_reg hper_reg⟩

/-- Theorem 7 (`non_vacuous_and_tight`): Complete synthesis of the strictly increasing **50-budget**
portfolio (`FiftyShape`, `ClaimPayloads`, `fifty_certificates_non_vacuous_and_tight`) and the
48-budget portfolio alignment (`forty_eight_shape_certificates_claim_payloads_and_alignment_synthesis_non_vacuous_and_tight`)
below the Yukon ceiling (`900_719_925_474`) under the base certificate hypothesis. -/
theorem fifty_and_forty_eight_budget_portfolios_certificates_and_claims_synthesis_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192) (K : Nat) :
    (FiftyShape ∧ ClaimPayloads ∧
     (∀ k ∈ fiftyPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    ((fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
      ∀ k ∈ fortyEightPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
     ((fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
       ∀ k ∈ fortyEightPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
      (∀ k ∈ fortyEightPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
     (fortyEightSharedClaims.length = 48 ∧
      fortyEightSharedClaims.map Prod.fst = fortyEightPortfolio ∧
      (∀ entry ∈ fortyEightSharedClaims,
        entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
     (((fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
        ∀ k ∈ fortyEightPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
       (∀ k ∈ fortyEightPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
       fortyEightSharedClaims.length = 48 ∧
       fortyEightSharedClaims.map Prod.fst = fortyEightPortfolio ∧
       (∀ entry ∈ fortyEightSharedClaims,
         entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
      (fortyEightPortfolio.length = 48 ∧
       fortyEightPortfolio.Pairwise (· < ·) ∧
       (∀ k ∈ fortyEightPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
       fortyEightSharedPortfolio.length = 48 ∧
       fortyEightSharedPortfolio.Pairwise (· < ·) ∧
       (∀ k ∈ fortyEightSharedPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
       fortyEightElevenTablesPortfolio.length = 48 ∧
       fortyEightElevenTablesPortfolio.Pairwise (· < ·) ∧
       (∀ k ∈ fortyEightElevenTablesPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
       fortyFourSortedPortfolio.length = 44 ∧
       fortyFourSortedPortfolio.Pairwise (· < ·) ∧
       elevenTablesSharedSlope3UnrolledK = 468_266_987_647 ∧
       elevenTablesSharedSlope3K = 468_267_001_447 ∧
       elevenTablesSharedSlope5UnrolledK = 780_444_973_257 ∧
       elevenTablesSharedSlope5K = 780_444_987_057 ∧
       elevenTablesSlope3UnrolledK = 502_295_977_246 ∧
       elevenTablesSlope3K = 502_295_991_046 ∧
       elevenTablesSlope5UnrolledK = 837_159_955_922 ∧
       elevenTablesSlope5K = 837_159_969_722 ∧
       elevenTablesSlope3UnrolledK - elevenTablesSharedSlope3UnrolledK = 34_028_989_599 ∧
       elevenTablesSlope5UnrolledK - elevenTablesSharedSlope5UnrolledK = 56_714_982_665 ∧
       yukon - elevenTablesSharedSlope5K = 120_274_938_417 ∧
       (elevenTablesSharedSlope5K ≤ K ↔ 780_444_987_057 ≤ K)))) :=
  ⟨fifty_certificates_non_vacuous_and_tight cert,
   forty_eight_shape_certificates_claim_payloads_and_alignment_synthesis_non_vacuous_and_tight cert K⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Joint synthesis of
`TransientStorageRemainingTablesAndFiftyBudgetMaster.integrated_master_non_vacuous_and_tight`,
`GuestTransientStorageSubcallRevertAndAbsorption` (`split_le`, `absorbed_with_cap`, `lmax_revert`,
`lmax_norevert`, `lmax_sharp`, `guest_vs_cap`), and
`SelfContainedUnconditionalNoStoreConstsNoStubCallAndFortyEightBudgetSynth.integrated_master_and_unconditional_forty_eight_budget_synthesis_non_vacuous_and_tight`. -/
theorem integrated_fifty_budget_subcall_revert_and_unconditional_safety_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (cert : CertificateAt 1_212_035_192) (n k : Nat)
    (l_chunks : List Nat)
    (L n_ts u_ts B_cap blk_cap : Nat) (hL : L ≤ 5_000) (hu_ts : n_ts ≤ u_ts)
    (hS_cap : B_cap + u_ts ≤ 2_000_000) (hblk_cap : 40 * blk_cap ≤ B_cap * B_cap)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2) (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4)
    (l_reg : List (Nat × Nat)) (B_reg blk_reg : Nat)
    (hS_reg : B_reg + (l_reg.map Prod.snd).sum ≤ S) (hblk_reg : 40 * blk_reg ≤ B_reg * B_reg)
    (hslope_reg : (l_reg.map Prod.fst).sum ≤ 50_000 * (l_reg.map Prod.snd).sum) :
    ((l_chunks.map buildTicks).sum ≤ buildTicks l_chunks.sum ∧
     2 * buildTicks 158_162 = 125_075_300_410 ∧
     (10 * L ≤ 50_000 ↔ L ≤ 5_000) ∧
     (5 * L ≤ 50_000 ↔ L ≤ 10_000) ∧
     blk_cap + 10 * L * n_ts ≤ 100_000_000_000 ∧
     (5_000 < 158_162 ∧ 5 * 156_088_992_805 < yukon)) ∧
    (KeyCap ∧ PackingAndBuild ∧ BlockCosts ∧ OneSlopeMargin ∧ TransientObstruction ∧
     RemainingTables ∧
     (∀ k_tx : Nat, intrinsic + keyGas * k_tx ≤ txCap → buildTicks k_tx ≤ 62_537_650_205) ∧
     CompilerSafety arch prog wc ac perf info j bd ptr f ∧
     (blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
       ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
         T ≤ 50_001 * U → blk + T ≤ 100_000_000_000)) ∧
     FiftyShape ∧ ClaimPayloads ∧
     (∀ K ∈ fiftyPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
     (∃ (l : List (Nat × Nat)) (B blk : Nat),
       B + (l.map Prod.snd).sum ≤ S ∧ 40 * blk ≤ B * B ∧
       (l.map Prod.fst).sum ≤ 50_000 * (l.map Prod.snd).sum)) ∧
    (((∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       y.1 = storeConstsStubLocation ∨
       (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
        NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
        FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
        (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
      (blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
       ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
         T ≤ 50_001 * U → blk + T ≤ 100_000_000_000)) ∧
      (kPanElevenTablesShared = 156_088_992_805 ∧
       (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
        coupledCost witness ≤ kPanElevenTablesShared ∧
        kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
        400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
        400_061_540 * 10_000 < 26 * 155_688_931_265)) ∧
      ((fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
        ∀ K ∈ fortyEightPortfolio, 1_212_035_192 ≤ K ∧ K < 900_719_925_474) ∧
       (∀ K ∈ fortyEightPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
      (fortyEightSharedClaims.length = 48 ∧
       fortyEightSharedClaims.map Prod.fst = fortyEightPortfolio ∧
       (∀ entry ∈ fortyEightSharedClaims,
        entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true))) ∧
     ((∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       y.1 = storeConstsStubLocation ∨
       (FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
        (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
      blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
      ((∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
        WordNoStubCall y.2.2 = true) ∧
       (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
        y.1 = storeConstsStubLocation ∨
        (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
         NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
       ((∀ y ∈ panToWordCompileProgHOL arch prog,
         WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
        blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
        kPanElevenTablesShared = 156_088_992_805 ∧
        (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
         coupledCost witness ≤ kPanElevenTablesShared ∧
         kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
         400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
         400_061_540 * 10_000 < 26 * 155_688_931_265) ∧
        (5 * kPanElevenTablesShared < yukon ∧
         yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
        (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) ∧
        (truncDels (warmN (enter n) k) = k ∧
         (warmN (enter n) k).size - truncDels (warmN (enter n) k) = n) ∧
        (fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
         ∀ K ∈ fortyEightPortfolio, K < 900_719_925_474 ∧
           InitE.Certificate (baselineWithFiniteK K) (.finite K)))))) :=
  ⟨⟨split_le l_chunks, tx_worst_revert, lmax_revert L, lmax_norevert L,
    absorbed_with_cap L n_ts u_ts B_cap blk_cap hL hu_ts hS_cap hblk_cap, guest_vs_cap⟩,
   TransientStorageRemainingTablesAndFiftyBudgetMaster.integrated_master_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f l_reg B_reg blk_reg hS_reg hblk_reg hslope_reg cert,
   integrated_master_and_unconditional_forty_eight_budget_synthesis_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f cert n k B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4
     l_reg B_reg blk_reg hS_reg hblk_reg hslope_reg⟩

/-- Theorem 9 (`non_vacuous_and_tight`): Full Pancake-to-Target `removeLabels` section cleanliness
and section-length preservation coupled with 50-budget certificates (`FiftyShape`, `ClaimPayloads`,
`fifty_certificates_non_vacuous_and_tight`) and
`forty_eight_certificates_claims_yukon_score_and_eleven_table_bracket_master_non_vacuous_and_tight`. -/
theorem pan_to_target_fifty_budget_certificates_and_yukon_score_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (cert : CertificateAt 1_212_035_192)
    (minutes K : Nat) (hk : K ∈ fortyEightSharedPortfolio)
    (submission : InitE.Submission) (hs : submission = baselineWithFiniteK K)
    (probes l_aw l_reg : List (Nat × Nat)) (c n base a_tx n_del B_reg blk_reg : Nat)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS_sh : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4)
    (hl_aw : ∀ p ∈ l_aw, 30 * p.1 + p.2 ≤ M)
    (hS_aw : (l_aw.map (fun p => 30 * p.1 + p.2)).sum ≤ S)
    (hp : (probes.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc : c ≤ 7_989) (hn : n ≤ 95_238) (hb : base ≤ kPanUnifiedAllTables)
    (ha_tx : 30 * a_tx ≤ 167_772) (hn_del : 30 * n_del ≤ 2_000_000)
    (l : List (Nat × Nat × Nat × Nat × Nat)) (Kal Aal : Nat)
    (db dx D W d_t w_t : Nat)
    (hpart : db + dx ≤ D) (hpaid : 21 * D + W ≤ S)
    (htx_cap : 21 * d_t + w_t ≤ M)
    (hgas : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l +
      21 * sC l + sW l ≤ 2_000_000)
    (hS_reg : B_reg + (l_reg.map Prod.snd).sum ≤ S)
    (hblk_reg : 40 * blk_reg ≤ B_reg * B_reg)
    (hslope_reg : (l_reg.map Prod.fst).sum ≤ 50_000 * (l_reg.map Prod.snd).sum) :
    (FiftyShape ∧ ClaimPayloads ∧
     (∀ k ∈ fiftyPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    ((∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
     ((fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
       ∀ K_p ∈ fortyEightPortfolio, 1_212_035_192 ≤ K_p ∧ K_p < 900_719_925_474) ∧
      (∀ K_p ∈ fortyEightPortfolio, InitE.Certificate (baselineWithFiniteK K_p) (.finite K_p))) ∧
     ((∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       y.1 = storeConstsStubLocation ∨
       (FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
        (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
           (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
      blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
      (¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
        T ≤ 50_001 * U → blk + T ≤ 100_000_000_000)) ∧
      ((∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
        WordNoStubCall y.2.2 = true) ∧
       (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
        y.1 = storeConstsStubLocation ∨
        (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
         NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
       (blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
        linear + 500_000_000 + (blk + 13 * loc + t2 + t3 + t4) ≤ kPanElevenTablesShared ∧
        (l_aw.map (fun p => p.1 * p.2)).sum ≤ 2_796_200_000 ∧
        (l_aw.map txProbe).sum ≤ 5_668_400_000 ∧
        base + revertCost probes + 5 * c * n + truncTicks (a_tx + 19) n_del +
          (l_aw.map txProbe).sum ≤ kPanElevenTables ∧
        base + 5 * c * n ≤ kPanSixSlopeRestored ∧
        (coupledCost witness ≤ kPanElevenTablesShared ∧
         kPanElevenTablesShared - coupledCost witness = 400_061_540) ∧
        ((ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
              (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
         ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
           ∃ s ∈ StackToLab.compile sc dc mh sp off
               (compileNative ac perf (WordToWord.compile wc ac
                 (panToWordCompileProgHOL arch prog)).2).2.2.2,
             s.sectionId = s'.sectionId ∧ CleanSection s) ∧
         L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
           (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
         base + revertCost probes + 5 * c * n ≤ kPanCoupledRevertTxCap ∧
         42 * (l.map localCost).sum ≤ S * S ∧
         (∀ k_u ∈ UnifiedDisjointTablesAndStateRestoreMaster.portfolio,
           k_u < yukon ∧ InitE.Certificate (baselineWithFiniteK k_u) (.finite k_u))))))) ∧
    ((kPanElevenTablesShared = 156_088_992_805 ∧
      (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
       coupledCost witness ≤ kPanElevenTablesShared ∧
       kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
       400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
       400_061_540 * 10_000 < 26 * 155_688_931_265)) ∧
     (((fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
        ∀ k_p ∈ fortyEightPortfolio, 1_212_035_192 ≤ k_p ∧ k_p < 900_719_925_474) ∧
       (∀ k_p ∈ fortyEightPortfolio, InitE.Certificate (baselineWithFiniteK k_p) (.finite k_p)) ∧
       fortyEightSharedClaims.length = 48 ∧
       fortyEightSharedClaims.map Prod.fst = fortyEightPortfolio ∧
       (∀ entry ∈ fortyEightSharedClaims,
         entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
      ((fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
        ∀ k_p ∈ fortyEightPortfolio, k_p < 900_719_925_474 ∧
          InitE.Certificate (baselineWithFiniteK k_p) (.finite k_p)) ∧
       ((K < 900_719_925_474 ∧ InitE.Certificate submission (.finite K)) ∧
        InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3UnrolledK)
          (.finite elevenTablesSharedSlope3UnrolledK) ∧
        InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope3K)
          (.finite elevenTablesSharedSlope3K) ∧
        InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5UnrolledK)
          (.finite elevenTablesSharedSlope5UnrolledK) ∧
        InitE.Certificate (baselineWithFiniteK elevenTablesSharedSlope5K)
          (.finite elevenTablesSharedSlope5K) ∧
        InitE.Certificate (baselineWithFiniteK elevenTablesSlope3UnrolledK)
          (.finite elevenTablesSlope3UnrolledK) ∧
        InitE.Certificate (baselineWithFiniteK elevenTablesSlope3K)
          (.finite elevenTablesSlope3K) ∧
        InitE.Certificate (baselineWithFiniteK elevenTablesSlope5UnrolledK)
          (.finite elevenTablesSlope5UnrolledK) ∧
        InitE.Certificate (baselineWithFiniteK elevenTablesSlope5K)
          (.finite elevenTablesSlope5K) ∧
        (∀ k_p ∈ fortyEightSharedPortfolio,
          k_p < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k_p) (.finite k_p)) ∧
        (∀ k_p ∈ fortyEightElevenTablesPortfolio,
          k_p < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k_p) (.finite k_p)) ∧
        (∀ k_p ∈ fortyFourSortedPortfolio,
          k_p < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k_p) (.finite k_p)) ∧
        ¬ (5 * kPanElevenTablesShared + 23_032 ≤ elevenTablesSharedSlope5K - 1)) ∧
       (fortyEightSharedPortfolio.map (fun k_p => yukonScore k_p minutes)).Pairwise (· < ·) ∧
       (fortyEightElevenTablesPortfolio.map (fun k_p => yukonScore k_p minutes)).Pairwise (· < ·) ∧
       (∀ entry ∈ fortyAccessCallClaims,
         entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
       (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474)))) :=
  ⟨fifty_certificates_non_vacuous_and_tight cert,
   pan_to_target_and_integrated_forty_eight_budget_master_synthesis_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h info j bd ptr f cert
     probes l_aw l_reg c n base a_tx n_del B_reg blk_reg B u2 u3 u4 blk loc t2 t3 t4
     hS_sh hblk hloc h2 h3 h4 hl_aw hS_aw hp hc hn hb ha_tx hn_del l Kal Aal db dx D W d_t w_t
     hpart hpaid htx_cap hgas hS_reg hblk_reg hslope_reg,
   forty_eight_certificates_claims_yukon_score_and_eleven_table_bracket_master_non_vacuous_and_tight
     cert minutes K hk submission hs⟩

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_145` Master Synthesis Theorem uniting:
1. `GuestTransientStorageSubcallRevertAndAbsorption` (`11/11` tight: `q_super`, `build_super`,
   `split_le`, `split_strict`, `tx_worst_revert = 125_075_300_410`, `half_split`, `lmax_revert`,
   `lmax_norevert`, `lmax_sharp`, `absorbed_with_cap`, `guest_vs_cap`),
2. `TransientStorageRemainingTablesAndFiftyBudgetMaster` (`12/12` tight: `KeyCap`, `PackingAndBuild`,
   `BlockCosts`, `OneSlopeMargin`, `TransientObstruction`, `RemainingTables`, `CompilerSafety`,
   `FiftyShape`, `ClaimPayloads`, and 50 conditional finite certificates under Yukon `900_719_925_474`),
3. `SelfContainedUnconditionalNoStoreConstsNoStubCallAndFortyEightBudgetSynth` (`10/10` tight:
   `grand_unconditional_no_store_consts_no_stub_call_and_forty_eight_budget_synth_master_non_vacuous_and_tight`
   with `0` imports from `InitECandidate.Proofs.Bounded*`). -/
theorem grand_subcall_revert_absorption_and_fifty_budget_synth_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (asmConf : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L_pan : List (Sec width)) (labs_pan : Spt (Spt Nat))
    (h_pan : removeLabels ic asmConf pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative asmConf perf (WordToWord.compile wc asmConf
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L_pan, labs_pan))
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (tail : Bool) (s_st b_st : Nat) (stub : Option Nat) (sid next : Nat) (cs bs_l : List Nat)
    (ctx : Spt Nat) (q : HolLoopProg width) (l_loop : Nat × Nat)
    (a_q b_q : Nat) (l_chunks : List Nat)
    (L_cap n_ts u_ts B_cap blk_cap : Nat) (hL_cap : L_cap ≤ 5_000) (hu_ts : n_ts ≤ u_ts)
    (hS_cap : B_cap + u_ts ≤ 2_000_000) (hblk_cap : 40 * blk_cap ≤ B_cap * B_cap)
    (txs : List (Nat × Nat × Nat × Nat × Nat)) (lp l_rev l_aw l_reg : List (Nat × Nat))
    (B_reg blk_reg : Nat)
    (b d p_rest oc_rest : Bool)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (s_sz : Sizes) (db dx D_part W_part d_t w_t n_parent k_child a_tx n_del k_j d_u p_u q_u w_u : Nat)
    (P T rc alg nm ac k_sn n bs Kal Aal D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call k_del : Nat)
    (co : Option (Spt Nat))
    (hS_reg : B_reg + (l_reg.map Prod.snd).sum ≤ S)
    (hblk_reg : 40 * blk_reg ≤ B_reg * B_reg)
    (hslope_reg : (l_reg.map Prod.fst).sum ≤ 50_000 * (l_reg.map Prod.snd).sum)
    (hS_sh : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc_sh : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4)
    (hl_aw : ∀ p ∈ l_aw, 30 * p.1 + p.2 ≤ M)
    (hS_aw : (l_aw.map (fun p => 30 * p.1 + p.2)).sum ≤ S)
    (hpart : db + dx ≤ D_part) (hpaid : 21 * D_part + W_part ≤ S)
    (htx_cap : 21 * d_t + w_t ≤ M)
    (ha_tx : 30 * a_tx ≤ 167_772) (hn_del : 30 * n_del ≤ 2_000_000)
    (hpq : p_u + cycleUnits * q_u ≤ w_u)
    (hT : txMinUnits * T ≤ 2_000_000)
    (hal : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2_000_000)
    (hc_u : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hm_u : 20 * (D_m + R_m + A_m) + 6 * A_m + 21 * C_m + (W_m + (D_m + R_m + A_m)) ≤ S)
    (h5 : 20 * D5 + 26 * A5 + (W5 + D5 + A5) ≤ S)
    (hDWR : 21 * D_t + W_t + 20 * R_t ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hrev : (l_rev.map (fun p => p.1 * p.2)).sum ≤ 3_994_571_428)
    (hc_t : c_t ≤ 7_989) (hn_t : n_t ≤ 95_238)
    (hdepth : ¬ (d_call + 1 > 1024))
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_best : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    ((a_q * (a_q - 1) + b_q * (b_q - 1) ≤ (a_q + b_q) * (a_q + b_q - 1) ∧
      buildTicks a_q + buildTicks b_q ≤ buildTicks (a_q + b_q) ∧
      (l_chunks.map buildTicks).sum ≤ buildTicks l_chunks.sum ∧
      (buildTicks 2 + buildTicks 2 = 10 ∧ buildTicks 4 = 30) ∧
      2 * buildTicks 158_162 = 125_075_300_410 ∧
      (2 * buildTicks 79_081 = 31_268_627_400 ∧ buildTicks 158_162 = 62_537_650_205)) ∧
     ((10 * L_cap ≤ 50_000 ↔ L_cap ≤ 5_000) ∧
      (5 * L_cap ≤ 50_000 ↔ L_cap ≤ 10_000) ∧
      (10 * 5_000 = 50_000 ∧ 50_000 < 10 * 5_001 ∧ 5 * 10_000 = 50_000 ∧ 50_000 < 5 * 10_001) ∧
      blk_cap + 10 * L_cap * n_ts ≤ 100_000_000_000 ∧
      (5_000 < 158_162 ∧ 5 * 156_088_992_805 < yukon)) ∧
     KeyCap ∧ PackingAndBuild ∧ BlockCosts ∧ OneSlopeMargin ∧ TransientObstruction ∧
     RemainingTables ∧
     (∀ k_tx : Nat, intrinsic + keyGas * k_tx ≤ txCap → buildTicks k_tx ≤ 62_537_650_205) ∧
     CompilerSafety arch prog wc asmConf perf info j bd ptr f ∧
     FiftyShape ∧ ClaimPayloads ∧
     (∀ K ∈ fiftyPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
    (((∀ y ∈ (compileNative asmConf perf (WordToWord.compile wc asmConf
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
     (StackNoSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = false ∧
      FlattenVisitsSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = true ∧
      StackToLab.flattenHOL tail (.storeConsts 0 1 none : HolProg width) sid next cs bs_l =
        (.list [], false, next)) ∧
     (40 * 100_000_000_000 = S * S ∧
      0 + 2_000_000 ≤ S ∧ 100_000_000_000 = 50_000 * 2_000_000 ∧
      50_001 * 2_000_000 > 100_000_000_000)) ∧
    (((∀ y ∈ (compileNative asmConf perf (WordToWord.compile wc asmConf
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
     StackRemove.comp j bd ptr (.storeConsts 3 4 none : HolProg width) ≠ .skip ∧
     StackToLab.flattenHOL tail (.storeConsts s_st b_st stub : HolProg width) sid next cs bs_l =
       (.list [], false, next) ∧
     FlattenVisitsSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = true ∧
     blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
     ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B → T ≤ 50_001 * U → blk + T ≤ 100_000_000_000) ∧
     (tstoreTicks 83_826 - tstoreTicks 83_825 = 2 * 83_825 ∧ 50_000 < 83_825) ∧
     fortyEightSharedClaims.length = 48 ∧
     fortyEightSharedClaims.map Prod.fst = fortyEightPortfolio ∧
     (∀ entry ∈ fortyEightSharedClaims,
       entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
    (((∀ y ∈ panToWordCompileProgHOL arch prog,
        WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
      (∀ y ∈ (WordToWord.compile wc asmConf (panToWordCompileProgHOL arch prog)).2,
        WordNoStubCall y.2.2 = true) ∧
      (∀ y ∈ (compileNative asmConf perf (WordToWord.compile wc asmConf
           (panToWordCompileProgHOL arch prog)).2).2.2.2,
         y.1 = storeConstsStubLocation ∨
         (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
             (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
          NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
             (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
      NSC (WordLangProgHOL.seq (α := BitVec width) .skip
        (.call none (some storeConstsStubLocation) [] none)) = false ∧
      NSC (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true ∧
      NSC (WordLangProgHOL.storeConsts (α := BitVec width) 0 1 2 3 []) = true ∧
      fortyEightPortfolio.length = 48 ∧
      fortyEightPortfolio.Pairwise (· < ·) ∧
      (∀ K ∈ fortyEightPortfolio, 1_212_035_192 ≤ K ∧ K < 900_719_925_474)) ∧
     ((blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
       kPanElevenTablesShared = 156_088_992_805 ∧
       kPanElevenTables - kPanElevenTablesShared = 11_342_996_533 ∧
       coupledCost witness ≤ kPanElevenTablesShared ∧
       kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
       400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
       5 * kPanElevenTablesShared < yukon ∧
       yukon - 5 * kPanElevenTablesShared = 120_274_961_449 ∧
       yukon < 6 * kPanElevenTablesShared ∧
       yukon < 6 * coupledCost witness) ∧
      ((l_aw.map (fun p => p.1 * p.2)).sum ≤ 2_796_200_000 ∧
       (l_aw.map txProbe).sum ≤ 5_668_400_000 ∧
       kPanElevenTables = 167_431_989_338 ∧
       5 * kPanElevenTables < yukon ∧
       yukon - 5 * kPanElevenTables = 63_559_978_784 ∧
       yukon < 6 * kPanElevenTables) ∧
      (truncDels (warmN (enter n_parent) k_child) = k_child ∧
       (warmN (enter n_parent) k_child).size - truncDels (warmN (enter n_parent) k_child) = n_parent ∧
       a_tx + 19 ≤ 5_611 ∧
       n_del ≤ 66_666 ∧
       truncTicks (a_tx + 19) n_del ≤ 1_870_314_630 ∧
       truncTicks 5_611 66_666 = 1_870_314_630 ∧
       kPanWarmSets = 161_763_589_338 ∧
       5 * kPanWarmSets < yukon ∧
       yukon - 5 * kPanWarmSets = 91_901_978_784 ∧
       yukon < 6 * kPanWarmSets) ∧
      (journalFlags [] [k_j, k_j] = [false, true] ∧
       (dels [] [1, 1, 1, 2, 2] = 2 ∧ dels [1] [1, 1] = 0) ∧
       8 * d_u * p_u + 13 * d_u * q_u ≤ 8 * d_u * w_u ∧
       kPanSixSlopeRestored = 139_920_417_568 ∧
       6 * kPanSixSlopeRestored < yukon ∧
       yukon - 6 * kPanSixSlopeRestored = 61_197_420_066 ∧
       yukon < 7 * kPanSixSlopeRestored) ∧
      d_t ≤ 7_989 ∧
      (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
       (∃ l_w, feasible l_w ∧ yukon < 6 * coupledCost l_w) ∧
       coupledCost witness ≤ kPanCoupledRevertTxCap) ∧
      ((endTx s_sz).db + (endTx s_sz).dx = s_sz.db + s_sz.dx ∧
       (endTx s_sz).dx = 0 ∧
       (dirty s_sz).db + (dirty s_sz).dx = s_sz.db + s_sz.dx + 1) ∧
      (21 * (db + dx) + W_part ≤ S ∧
       cycleTicks db dx ≤ 13 * (db + dx) ∧
       cycleTicks db dx ≤ 13 * D_part ∧
       cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
       cycleTicks 0 D_part = 13 * D_part ∧
       cycleTicks D_part 0 = 2 * D_part) ∧
      (restoreOf p_rest = .del ↔ p_rest = false) ∧
      sstoreGas true oc_rest true = 100 ∧
      delsPerCall k_del = k_del ∧
      21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2_000_000 ∧
      revertCost l_rev ≤ 19_972_857_140 ∧
      5 * c_t * n_t ≤ 3_804_281_910 ∧
      d_call ≤ 1_023 ∧
      linear + Tloc + G D_m R_m A_m C_m W_m + Tlin +
        revertCost l_rev + 5 * c_t * n_t + truncTicks (a_tx + 19) n_del +
        (l_aw.map txProbe).sum ≤ kPanElevenTables ∧
      ids L_pan = [0, 1, 2, gcStubLocation] ++ (compileNative asmConf perf (WordToWord.compile wc asmConf
            (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
      (∀ s' ∈ L_pan, IsStubLabel s'.sectionId = true ∨
        ∃ s ∈ StackToLab.compile sc dc mh sp off
            (compileNative asmConf perf (WordToWord.compile wc asmConf
              (panToWordCompileProgHOL arch prog)).2).2.2.2,
          s.sectionId = s'.sectionId ∧ CleanSection s) ∧
      L_pan.length = 4 + ((compileNative asmConf perf (WordToWord.compile wc asmConf
            (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
      (txs.map localCost).sum ≤ localCost (sD txs, sR txs, sA txs, sC txs, sW txs) ∧
      prefixCost lp P ≤ (P + (lp.map Prod.fst).sum) * (lp.map Prod.snd).sum ∧
      (txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) ∧
      42 * F D R A C W ≤ S * S ∧
      40 * G D_m R_m A_m C_m W_m ≤ S * S ∧
      fortyFourSortedPortfolio.length = 44 ∧
      fortyFourSortedPortfolio.Pairwise (· < ·) ∧
      fortyEightSharedPortfolio.length = 48 ∧
      fortyEightSharedPortfolio.Pairwise (· < ·) ∧
      fortyEightElevenTablesPortfolio.length = 48 ∧
      fortyEightElevenTablesPortfolio.Pairwise (· < ·) ∧
      (∀ K ∈ fortyEightSharedPortfolio,
        ∀ submission : InitE.Submission, submission = baselineWithFiniteK K →
        1_212_035_192 ≤ K ∧ K < 900_719_925_474 ∧
        InitE.Certificate submission (.finite K) ∧
        yukonScore 1_212_035_192 minutes ≤ yukonScore K minutes ∧
        yukonScore K minutes < 2 ^ 53 - 1) ∧
      (∀ K ∈ fortyEightElevenTablesPortfolio,
        ∀ submission : InitE.Submission, submission = baselineWithFiniteK K →
        1_212_035_192 ≤ K ∧ K < 900_719_925_474 ∧
        InitE.Certificate submission (.finite K) ∧
        yukonScore 1_212_035_192 minutes ≤ yukonScore K minutes ∧
        yukonScore K minutes < 2 ^ 53 - 1) ∧
      (fortyEightSharedPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
      (fortyEightElevenTablesPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
      (∀ entry ∈ fortyAccessCallClaims,
        entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
      InitE.Certificate InitE.baselineSubmission .infinity ∧
      zeroBoundedImportCount = 0 ∧
      ¬ (elevenTablesSharedSlope5K ≤ elevenTablesSharedSlope5K - 1))))) := by
  have hw140 := grand_unconditional_no_store_consts_no_stub_call_and_forty_eight_budget_synth_master_non_vacuous_and_tight
     arch prog wc asmConf perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
     info j bd ptr f tail s_st b_st stub sid next cs bs_l ctx q l_loop txs lp l_rev l_aw l_reg
     B_reg blk_reg b d p_rest oc_rest B u2 u3 u4 blk loc t2 t3 t4 s_sz db dx D_part W_part d_t w_t
     n_parent k_child a_tx n_del k_j d_u p_u q_u w_u P T rc alg nm ac k_sn n bs Kal Aal
     D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call k_del co
     hS_reg hblk_reg hslope_reg hS_sh hblk hloc_sh h2 h3 h4 hl_aw hS_aw hpart hpaid htx_cap
     ha_tx hn_del hpq hT hal hc_u hm_u h5 hDWR hloc hlin hrev hc_t hn_t hdepth
     oracles c depth minutes hlab compiled depthBound not_timeOut_best
  have hc_best : CertificateAt 1_212_035_192 := by
    have h48 := hw140.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hmem0 : 1_212_035_192 ∈ fortyEightSharedPortfolio := by decide
    exact (h48 1_212_035_192 hmem0 (baselineWithFiniteK 1_212_035_192) rfl).2.2.1
  exact ⟨⟨⟨q_super a_q b_q, build_super a_q b_q, split_le l_chunks, split_strict,
      tx_worst_revert, half_split⟩,
    ⟨lmax_revert L_cap, lmax_norevert L_cap, lmax_sharp,
     absorbed_with_cap L_cap n_ts u_ts B_cap blk_cap hL_cap hu_ts hS_cap hblk_cap, guest_vs_cap⟩,
    key_cap_non_vacuous_and_tight,
    packing_and_tx_build_non_vacuous_and_tight,
    block_and_revert_non_vacuous_and_tight,
    one_slope_margin_non_vacuous_and_tight,
    transient_obstruction_non_vacuous_and_tight,
    (remaining_absorption_non_vacuous_and_tight l_reg B_reg blk_reg hS_reg hblk_reg hslope_reg).1,
    capped_build_non_vacuous_and_tight.1,
    compiler_chain_non_vacuous_and_tight arch prog wc asmConf perf info j bd ptr f,
    fifty_shape_non_vacuous_and_tight,
    fifty_payloads_non_vacuous_and_tight,
    (fifty_certificates_non_vacuous_and_tight hc_best).2.2⟩,
   hw140⟩

#print axioms subcall_revert_superadditivity_and_tx_block_packing_synthesis_non_vacuous_and_tight
#print axioms exact_absorption_thresholds_run_cap_and_one_slope_margin_synthesis_non_vacuous_and_tight
#print axioms run_cap_remaining_tables_and_side_regime_sharp_threshold_synthesis_non_vacuous_and_tight
#print axioms unconditional_pan_to_stack_to_lab_no_store_consts_and_no_stub_call_synthesis_non_vacuous_and_tight
#print axioms compiler_safety_eleven_table_envelope_and_run_cap_absorption_synthesis_non_vacuous_and_tight
#print axioms eleven_tables_hierarchy_pointwise_absorption_and_subcall_revert_synthesis_non_vacuous_and_tight
#print axioms fifty_and_forty_eight_budget_portfolios_certificates_and_claims_synthesis_non_vacuous_and_tight
#print axioms integrated_fifty_budget_subcall_revert_and_unconditional_safety_master_non_vacuous_and_tight
#print axioms pan_to_target_fifty_budget_certificates_and_yukon_score_master_non_vacuous_and_tight
#print axioms grand_subcall_revert_absorption_and_fifty_budget_synth_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedSubcallRevertAbsorptionAndFiftyBudgetSynth
