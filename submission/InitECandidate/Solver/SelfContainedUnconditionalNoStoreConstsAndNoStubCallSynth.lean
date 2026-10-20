import InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts
import InitECandidate.Solver.ExhaustiveHtabInventoryAndNoStubCallMaster
import InitECandidate.Solver.SelfContainedWordToWordNoStubCallAndSharedAbsorptionSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedUnconditionalNoStoreConstsAndNoStubCallSynth` — Wave 5 Atomic Worker `W5_137`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`PanToStackToLabUnconditionalNoStoreConsts` (`12/12` tight)**:
   - Unconditional `StackNoSt` preservation through `StackRawCall`, `StackAlloc`, `StackRemove`, and
     `StackNames` (`u_body_chain`, `panToStackNames_bodies_StackNoSt_unconditional`),
   - Unconditional `StackToLab.flattenHOL` `storeConsts` non-visitation (`not_visits_of_StackNoSt`,
     `panToLabSection_unconditional`),
   - Tight witnesses (`stackRemove_storeConsts_not_skip`, `flatten_storeConsts_empty`,
     `visits_storeConsts_tight`, `progToSection_sectionId`).
2. **`ExhaustiveHtabInventoryAndNoStubCallMaster` (`12/12` tight)**:
   - General side-regime absorption (`side_absorption_scalar_non_vacuous_and_tight`,
     `general_side_regime_absorption_non_vacuous_and_tight`, `slope_sum_non_vacuous_and_tight`,
     `absorption_tight_non_vacuous_and_tight`),
   - Sharp `50_000` ticks/unit slope threshold (`threshold_sharp_non_vacuous_and_tight`) and known
     absorbed slopes (`known_slopes_non_vacuous_and_tight`),
   - Transient-storage (`ts+64`) slope and sensitivity analysis (`tstore_slope_exceeds_non_vacuous_and_tight`,
     `tstore_tx_budget_non_vacuous_and_tight`, `tstore_witness_non_vacuous_and_tight`,
     `tstore_sensitivity_non_vacuous_and_tight`),
   - Joint unconditional compiler safety & 11-table shared absorption
     (`panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight`) and 48-budget
     certificates (`forty_eight_budget_certificates_non_vacuous_and_tight`).
3. **`SelfContainedWordToWordNoStubCallAndSharedAbsorptionSynth` (`10/10` tight)**:
   - Unconditional `WordToWord` & `StackNames` stub-call absence (`panToWordToWord_NoStubCall`,
     `panToStackNames_NoSt_and_NoStubCall_unconditional`),
   - Shared 11-table budget absorption (`kPanElevenTablesShared = 156_088_992_805`, `< 0.26%` gap
     above the 12-tx witness `155_688_931_265`, `5×` Yukon margin `120_274_961_449`),
   - Strictly increasing 48-budget portfolios (`portfolio`, `fortyEightSharedPortfolio`,
     `fortyEightElevenTablesPortfolio`) below the Yukon ceiling `900_719_925_474` and their
     associated `InitE.Certificate` finite certificates (`0 sorryAx`).
-/

namespace InitECandidate.Solver.SelfContainedUnconditionalNoStoreConstsAndNoStubCallSynth

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
open InitECandidate.Solver.PanToWordNoStubCall (TgtGood)
open InitECandidate.Solver.WordToWordNoStubCall (
  NSC
  NSC_eq
  panToWordToWord_NoStubCall
  panToStackNames_NoSt_and_NoStubCall_unconditional
  NSC_rejects_stub_call
  NSC_accepts_user_call
  NSC_allows_storeConsts
)
open InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts (
  u_body_chain
  panToStackNames_bodies_StackNoSt_unconditional
  stackRemove_storeConsts_not_skip
  flatten_storeConsts_empty
  FlattenVisitsSt
  not_visits_of_StackNoSt
  visits_storeConsts_tight
  progToSection_sectionId
  panToLabSection_unconditional
)
open InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (tstoreTicks)
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (M feasible witness coupledCost kPanCoupledRevertTxCap)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound (enter warmN truncDels truncTicks kPanWarmSets)
open InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope (journalFlags dels cycleUnits kPanSixSlopeRestored)
open InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound (txProbe kPanElevenTables)
open InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption (kPanElevenTablesShared)
open InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster (portfolio)
open InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth (fortyEightSharedClaims)
open InitECandidate.Solver.ExhaustiveHtabInventoryAndNoStubCallMaster (
  side_absorption_scalar_non_vacuous_and_tight
  general_side_regime_absorption_non_vacuous_and_tight
  slope_sum_non_vacuous_and_tight
  absorption_tight_non_vacuous_and_tight
  threshold_sharp_non_vacuous_and_tight
  known_slopes_non_vacuous_and_tight
  tstore_slope_exceeds_non_vacuous_and_tight
  tstore_tx_budget_non_vacuous_and_tight
  tstore_witness_non_vacuous_and_tight
  tstore_sensitivity_non_vacuous_and_tight
  panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
  forty_eight_budget_certificates_non_vacuous_and_tight
)
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
open InitECandidate.Solver.SelfContainedWordToWordNoStubCallAndSharedAbsorptionSynth (
  word_to_word_no_stub_call_and_frontend_safety_closure_non_vacuous_and_tight
  pan_to_stack_names_unconditional_no_st_and_no_stub_call_non_vacuous_and_tight
  shared_absorption_bracket_and_five_margin_synthesis_non_vacuous_and_tight
  eleven_tables_probe_and_shared_hierarchy_synthesis_non_vacuous_and_tight
  forty_eight_portfolio_alignment_and_exact_target_budgets_non_vacuous_and_tight
  integrated_word_to_word_no_stub_call_and_forty_eight_budget_master_non_vacuous_and_tight
  pan_to_target_and_word_to_word_no_stub_call_master_non_vacuous_and_tight
  unified_eleven_table_sstore_and_nsc_witnesses_synthesis_non_vacuous_and_tight
  forty_eight_portfolio_certificates_and_yukon_score_synthesis_non_vacuous_and_tight
  grand_word_to_word_no_stub_call_and_shared_absorption_synth_master_non_vacuous_and_tight
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

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Joint synthesis of `PanToStackToLabUnconditionalNoStoreConsts`
(`panToStackNames_bodies_StackNoSt_unconditional`, `panToLabSection_unconditional`,
`stackRemove_storeConsts_not_skip`, `flatten_storeConsts_empty`, `visits_storeConsts_tight`,
`progToSection_sectionId`) and `panToStackNames_NoSt_and_NoStubCall_unconditional` (`StackNoSt = true`
and `NoStubCall = true` with **no `hcall` hypothesis**). -/
theorem pan_to_stack_to_lab_and_no_stub_call_unconditional_joint_synthesis_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (tail : Bool) (s b : Nat) (stub : Option Nat) (sid next : Nat) (cs bs : List Nat)
    (n : Nat) (p_sec : HolProg width) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
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
    (StackToLab.progToSectionHOL (n, p_sec)).sectionId = n :=
  ⟨panToStackNames_NoSt_and_NoStubCall_unconditional arch prog wc ac perf info j bd ptr f,
   panToStackNames_bodies_StackNoSt_unconditional arch prog wc ac perf info j bd ptr f,
   panToLabSection_unconditional arch prog wc ac perf info j bd ptr f,
   stackRemove_storeConsts_not_skip j bd ptr,
   flatten_storeConsts_empty tail s b stub sid next cs bs,
   visits_storeConsts_tight (width := width),
   progToSection_sectionId n p_sec⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Unified per-body unconditional characterization from
`Pancake` through `WordToWord → WordToStack → StackRawCall → StackAlloc → StackRemove → StackNames → StackToLab`:
every non-stub body simultaneously satisfies `StackNoSt = true`, `NoStubCall = true`,
`FlattenVisitsSt = false`, and `progToSectionHOL.sectionId = y.1`, coupled with `WordToWord`
`WordNoStubCall` and `NSC` discrimination witnesses. -/
theorem pan_to_lab_section_no_st_and_no_stub_call_unified_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (p_w : WordLangProgHOL (BitVec width)) :
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
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ panToWordCompileProgHOL arch prog,
      WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
    NSC p_w = WordNoStubCall p_w ∧
    NSC (WordLangProgHOL.seq (α := BitVec width) .skip
      (.call none (some storeConstsStubLocation) [] none)) = false ∧
    NSC (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true ∧
    NSC (WordLangProgHOL.storeConsts (α := BitVec width) 0 1 2 3 []) = true := by
  have hw := word_to_word_no_stub_call_and_frontend_safety_closure_non_vacuous_and_tight arch prog wc ac p_w
  refine ⟨?_, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1⟩
  intro y hy
  rcases panToStackNames_NoSt_and_NoStubCall_unconditional arch prog wc ac perf info j bd ptr f y hy
    with hstub | ⟨hnst, hnsc⟩
  · exact Or.inl hstub
  · exact Or.inr ⟨hnst, hnsc, not_visits_of_StackNoSt _ hnst, rfl⟩

/-- Theorem 3 (`non_vacuous_and_tight`): Complete synthesis of `general_side_regime_absorption`,
`side_absorption_scalar`, `slope_sum`, `absorption_tight`, `threshold_sharp` (`50_000` ticks/unit),
`known_slopes`, and the `ts+64` transient-storage slope/sensitivity theorems from
`ExhaustiveHtabInventoryAndNoStubCallMaster`. -/
theorem general_side_regime_absorption_and_threshold_sharp_complete_synthesis_non_vacuous_and_tight
    (B_sc U T blk_sc : Nat)
    (hS_sc : B_sc + U ≤ S) (hblk_sc : 40 * blk_sc ≤ B_sc * B_sc) (hT_sc : T ≤ 50_000 * U)
    (l_reg l_per : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l_reg.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l_reg.map Prod.fst).sum ≤ 50_000 * (l_reg.map Prod.snd).sum)
    (hper : ∀ p ∈ l_per, p.1 ≤ 50_000 * p.2) :
    blk_sc + T ≤ 100_000_000_000 ∧
    blk + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
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
      50_000 * 167_772 < 2 * tstoreTicks 167_652) :=
  ⟨side_absorption_scalar_non_vacuous_and_tight B_sc U T blk_sc hS_sc hblk_sc hT_sc,
   general_side_regime_absorption_non_vacuous_and_tight l_reg B blk hS hblk hslope,
   slope_sum_non_vacuous_and_tight l_per hper,
   absorption_tight_non_vacuous_and_tight,
   threshold_sharp_non_vacuous_and_tight,
   known_slopes_non_vacuous_and_tight,
   tstore_slope_exceeds_non_vacuous_and_tight,
   tstore_tx_budget_non_vacuous_and_tight,
   tstore_witness_non_vacuous_and_tight,
   tstore_sensitivity_non_vacuous_and_tight⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Joint synthesis of
`ExhaustiveHtabInventoryAndNoStubCallMaster.panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight`,
`PanToStackToLabUnconditionalNoStoreConsts.panToLabSection_unconditional`, and
`SelfContainedWordToWordNoStubCallAndSharedAbsorptionSynth.shared_absorption_bracket_and_five_margin_synthesis_non_vacuous_and_tight`,
uniting unconditional `StackNoSt + NoStubCall + FlattenVisitsSt = false`, `general_side_regime_absorption`,
`threshold_sharp` (`50_000` ticks/unit), `shared_absorption` (`≤ 151_929_428_571`), and
`kPanElevenTablesShared = 156_088_992_805` (`< 0.26%` gap above the 12-tx witness `155_688_931_265`). -/
theorem unconditional_compiler_safety_side_regime_and_shared_absorption_synthesis_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (l_reg : List (Nat × Nat)) (B_reg blk_reg : Nat)
    (hS_reg : B_reg + (l_reg.map Prod.snd).sum ≤ S) (hblk_reg : 40 * blk_reg ≤ B_reg * B_reg)
    (hslope_reg : (l_reg.map Prod.fst).sum ≤ 50_000 * (l_reg.map Prod.snd).sum)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4) :
    ((∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
     blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
     (¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
       T ≤ 50_001 * U → blk + T ≤ 100_000_000_000)) ∧
     kPanElevenTablesShared = 156_088_992_805 ∧
     (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
      400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
      400_061_540 * 10_000 < 26 * 155_688_931_265)) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
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
      (21 * S * S + 130 * M * S) / 840 = 151_929_428_571)) :=
  ⟨panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f l_reg B_reg blk_reg hS_reg hblk_reg hslope_reg,
   panToLabSection_unconditional arch prog wc ac perf info j bd ptr f,
   shared_absorption_bracket_and_five_margin_synthesis_non_vacuous_and_tight
     B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc h2 h3 h4⟩

/-- Theorem 5 (`non_vacuous_and_tight`): Synthesis of the unabsorbed 11-table probe envelope
(`kPanElevenTables = 167_431_989_338`), the shared 11-table hierarchy
(`kPanSixSlopeRestored < coupledCost witness < kPanElevenTablesShared < kPanAccessCall < kPanWarmSets < kPanElevenTables`),
and the general side-regime slope threshold (`50_000` ticks/unit vs `ts+64` marginal slope `83_825`). -/
theorem eleven_tables_shared_hierarchy_and_general_side_slope_synthesis_non_vacuous_and_tight
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
    blk_reg + (l_reg.map Prod.fst).sum ≤ 100_000_000_000 ∧
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
     (slope5 * kPanElevenTables < yukon ↔ slope5 ≤ 5)) := by
  have hsum := slope_sum_non_vacuous_and_tight l_reg hper_reg
  exact ⟨general_side_regime_absorption_non_vacuous_and_tight l_reg B_reg blk_reg hS_reg hblk_reg hsum,
    hsum,
    threshold_sharp_non_vacuous_and_tight,
    tstore_slope_exceeds_non_vacuous_and_tight,
    eleven_tables_probe_and_shared_hierarchy_synthesis_non_vacuous_and_tight
      a w B u2 u3 u4 blk loc t2 t3 t4 slope5 l_probe ha hS_sh hblk hloc h2 h3 h4 hl_p hS_p⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Complete 48-budget portfolio alignment, strict ordering
under Yukon (`900_719_925_474`), exact target budget values, and 48-claim JSON validation
(`fortyEightSharedClaims.length = 48`, `utf8ByteSize ≤ 128`, `validFiniteClaim = true`) uniting
`ExhaustiveHtabInventoryAndNoStubCallMaster.forty_eight_budget_certificates_non_vacuous_and_tight`
and `SelfContainedWordToWordNoStubCallAndSharedAbsorptionSynth.forty_eight_portfolio_alignment_and_exact_target_budgets_non_vacuous_and_tight`. -/
theorem forty_eight_portfolio_alignment_and_shared_claims_synthesis_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192) (K : Nat) :
    ((portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ k ∈ portfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
     (∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
     fortyEightSharedClaims.length = 48 ∧
     fortyEightSharedClaims.map Prod.fst = portfolio ∧
     (∀ entry ∈ fortyEightSharedClaims,
       entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
    (portfolio.length = 48 ∧
     portfolio.Pairwise (· < ·) ∧
     (∀ k ∈ portfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
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
     (elevenTablesSharedSlope5K ≤ K ↔ 780_444_987_057 ≤ K)) :=
  ⟨forty_eight_budget_certificates_non_vacuous_and_tight cert,
   forty_eight_portfolio_alignment_and_exact_target_budgets_non_vacuous_and_tight K⟩

/-- Theorem 7 (`non_vacuous_and_tight`): Integrated synthesis of unconditional `PanToStackToLab`
(`u_body_chain`, `panToLabSection_unconditional`), `integrated_word_to_word_no_stub_call_and_forty_eight_budget_master_non_vacuous_and_tight`,
and `general_side_regime_absorption_non_vacuous_and_tight`. -/
theorem integrated_unconditional_no_st_no_stub_call_and_forty_eight_budget_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (cert : CertificateAt 1_212_035_192) (n k : Nat)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2) (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4)
    (l_reg : List (Nat × Nat)) (B_reg blk_reg : Nat)
    (hS_reg : B_reg + (l_reg.map Prod.snd).sum ≤ S) (hblk_reg : 40 * blk_reg ≤ B_reg * B_reg)
    (hslope_reg : (l_reg.map Prod.fst).sum ≤ 50_000 * (l_reg.map Prod.snd).sum) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
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
      (portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
       ∀ K ∈ portfolio, K < 900_719_925_474 ∧
         InitE.Certificate (baselineWithFiniteK K) (.finite K)))) :=
  ⟨panToLabSection_unconditional arch prog wc ac perf info j bd ptr f,
   general_side_regime_absorption_non_vacuous_and_tight l_reg B_reg blk_reg hS_reg hblk_reg hslope_reg,
   integrated_word_to_word_no_stub_call_and_forty_eight_budget_master_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f cert n k B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Full Pancake-to-Target `removeLabels` section cleanliness
and section-length preservation coupled with `panToLabSection_unconditional`,
`panToStackNames_NoSt_and_NoStubCall_unconditional`, `general_side_regime_absorption`,
`threshold_sharp`, and `kPanElevenTablesShared = 156_088_992_805`. -/
theorem pan_to_target_unconditional_no_st_no_stub_call_and_side_regime_master_non_vacuous_and_tight
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
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
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
       (∀ k ∈ UnifiedDisjointTablesAndStateRestoreMaster.portfolio,
         k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k))))) :=
  ⟨panToLabSection_unconditional arch prog wc ac perf info j bd ptr f,
   general_side_regime_absorption_non_vacuous_and_tight l_reg B_reg blk_reg hS_reg hblk_reg hslope_reg,
   threshold_sharp_non_vacuous_and_tight,
   pan_to_target_and_word_to_word_no_stub_call_master_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h info j bd ptr f cert
     probes l_aw c n base a_tx n_del B u2 u3 u4 blk loc t2 t3 t4
     hS_sh hblk hloc h2 h3 h4 hl_aw hS_aw hp hc hn hb ha_tx hn_del l Kal Aal db dx D W d_t w_t
     hpart hpaid htx_cap hgas⟩

/-- Theorem 9 (`non_vacuous_and_tight`): Complete 48-budget certificate lifting, `yukonScore`
strict monotonicity, and `claim.json ≤ 128` byte conformity across `portfolio` (`48` claims in
`fortyEightSharedClaims`), `fortyEightSharedPortfolio`, and `fortyEightElevenTablesPortfolio` under
Yukon (`900_719_925_474`). -/
theorem forty_eight_portfolio_certificates_claims_and_yukon_score_master_non_vacuous_and_tight
    (hc_best : CertificateAt 1_212_035_192)
    (minutes K : Nat) (hk : K ∈ fortyEightSharedPortfolio)
    (submission : InitE.Submission) (hs : submission = baselineWithFiniteK K) :
    ((portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ k ∈ portfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
     (∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
     fortyEightSharedClaims.length = 48 ∧
     fortyEightSharedClaims.map Prod.fst = portfolio ∧
     (∀ entry ∈ fortyEightSharedClaims,
       entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
    ((portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ k ∈ portfolio, k < 900_719_925_474 ∧
        InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
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
      (∀ k ∈ fortyEightSharedPortfolio,
        k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
      (∀ k ∈ fortyEightElevenTablesPortfolio,
        k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
      (∀ k ∈ fortyFourSortedPortfolio,
        k < 900_719_925_474 ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
      ¬ (5 * kPanElevenTablesShared + 23_032 ≤ elevenTablesSharedSlope5K - 1)) ∧
     (fortyEightSharedPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
     (fortyEightElevenTablesPortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
     (∀ entry ∈ fortyAccessCallClaims,
       entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
     (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474)) :=
  ⟨forty_eight_budget_certificates_non_vacuous_and_tight hc_best,
   forty_eight_portfolio_certificates_and_yukon_score_synthesis_non_vacuous_and_tight
     hc_best minutes K hk submission hs⟩

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_137` Master Synthesis Theorem uniting:
1. `PanToStackToLabUnconditionalNoStoreConsts` (`12/12` tight: `panToStackNames_bodies_StackNoSt_unconditional`,
   `panToLabSection_unconditional`, `stackRemove_storeConsts_not_skip`, `flatten_storeConsts_empty`,
   `visits_storeConsts_tight`),
2. `ExhaustiveHtabInventoryAndNoStubCallMaster` (`12/12` tight: `general_side_regime_absorption_non_vacuous_and_tight`,
   `threshold_sharp_non_vacuous_and_tight` at `50_000` ticks/unit, `known_slopes_non_vacuous_and_tight`,
   `tstore_slope_exceeds_non_vacuous_and_tight`, `tstore_sensitivity_non_vacuous_and_tight`,
   `panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight`,
   `forty_eight_budget_certificates_non_vacuous_and_tight`),
3. `SelfContainedWordToWordNoStubCallAndSharedAbsorptionSynth` (`10/10` tight:
   `grand_word_to_word_no_stub_call_and_shared_absorption_synth_master_non_vacuous_and_tight`,
   `kPanElevenTablesShared = 156_088_992_805` with `< 0.26%` gap above the 12-tx witness `155_688_931_265`,
   and the strictly increasing 48-budget portfolios under Yukon `900_719_925_474` with `0` imports
   from `InitECandidate.Proofs.Bounded*`). -/
theorem grand_unconditional_no_store_consts_and_no_stub_call_synth_master_non_vacuous_and_tight
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
    ((∀ y ∈ (compileNative asmConf perf (WordToWord.compile wc asmConf
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
     fortyEightSharedClaims.map Prod.fst = portfolio ∧
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
      portfolio.length = 48 ∧
      portfolio.Pairwise (· < ·) ∧
      (∀ K ∈ portfolio, 1_212_035_192 ≤ K ∧ K < 900_719_925_474)) ∧
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
      ¬ (elevenTablesSharedSlope5K ≤ elevenTablesSharedSlope5K - 1))) := by
  have hj := SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth.forty_eight_shared_claims_valid_and_within_128_bytes_non_vacuous_and_tight 1
  exact ⟨⟨panToLabSection_unconditional arch prog wc asmConf perf info j bd ptr f,
    stackRemove_storeConsts_not_skip j bd ptr,
    flatten_storeConsts_empty tail s_st b_st stub sid next cs bs_l,
    visits_storeConsts_tight (width := width),
    general_side_regime_absorption_non_vacuous_and_tight l_reg B_reg blk_reg hS_reg hblk_reg hslope_reg,
    threshold_sharp_non_vacuous_and_tight,
    tstore_slope_exceeds_non_vacuous_and_tight,
    hj.1, hj.2.1, hj.2.2.1⟩,
   grand_word_to_word_no_stub_call_and_shared_absorption_synth_master_non_vacuous_and_tight
     arch prog wc asmConf perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
     info j bd ptr f tail s_st b_st stub sid next cs bs_l ctx q l_loop txs lp l_rev l_aw
     b d p_rest oc_rest B u2 u3 u4 blk loc t2 t3 t4 s_sz db dx D_part W_part d_t w_t
     n_parent k_child a_tx n_del k_j d_u p_u q_u w_u P T rc alg nm ac k_sn n bs Kal Aal
     D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin c_t n_t d_call k_del co
     hS_sh hblk hloc_sh h2 h3 h4 hl_aw hS_aw hpart hpaid htx_cap ha_tx hn_del hpq hT hal
     hc_u hm_u h5 hDWR hloc hlin hrev hc_t hn_t hdepth oracles c depth minutes hlab compiled
     depthBound not_timeOut_best⟩

#print axioms pan_to_stack_to_lab_and_no_stub_call_unconditional_joint_synthesis_non_vacuous_and_tight
#print axioms pan_to_lab_section_no_st_and_no_stub_call_unified_non_vacuous_and_tight
#print axioms general_side_regime_absorption_and_threshold_sharp_complete_synthesis_non_vacuous_and_tight
#print axioms unconditional_compiler_safety_side_regime_and_shared_absorption_synthesis_non_vacuous_and_tight
#print axioms eleven_tables_shared_hierarchy_and_general_side_slope_synthesis_non_vacuous_and_tight
#print axioms forty_eight_portfolio_alignment_and_shared_claims_synthesis_non_vacuous_and_tight
#print axioms integrated_unconditional_no_st_no_stub_call_and_forty_eight_budget_master_non_vacuous_and_tight
#print axioms pan_to_target_unconditional_no_st_no_stub_call_and_side_regime_master_non_vacuous_and_tight
#print axioms forty_eight_portfolio_certificates_claims_and_yukon_score_master_non_vacuous_and_tight
#print axioms grand_unconditional_no_store_consts_and_no_stub_call_synth_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedUnconditionalNoStoreConstsAndNoStubCallSynth
