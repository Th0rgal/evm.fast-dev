import InitECandidate.Solver.LabToTargetSectionCleanPreservation
import InitECandidate.Solver.GuestSubBlockTxSplittingDominance
import InitECandidate.Solver.SelfContainedUnifiedAllTablesThirtySixBudgetSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedLabToTargetAndSubBlockSynth` — Wave 5 Atomic Worker `W5_103`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`LabToTargetSectionCleanPreservation` (`14/14` tight)**:
   - Section ID preservation across all `LabToTarget` passes (`ids_filterSkip`, `ids_encSecList`,
     `ids_encSecsAgain`, `ids_updLabLen`, `ids_padCode`, `ids_removeLabelsLoop`, `ids_removeLabels`),
   - Unconditional full Pancake-to-Target section cleanliness and length preservation
     (`panToTarget_sections_clean`, `panToTarget_sections_length`, `filterSkip_changes_lines`,
     `ids_distinguish_stub`, `ids_not_trivial`).
2. **`GuestSubBlockTxSplittingDominance` (`10/10` tight)**:
   - Sub-block multi-transaction splitting sub-additivity (`split_local_le`, `split_strict`),
   - Block-prefix probe dominance (`prefix_le`, `prefix_tight`, `prefix_strict`),
   - Per-transaction `state_fresh_tx` reset absorption (`reset_bound`, `reset_absorbed`,
     `max_tx_reset`, `access_list_key_cost`, `split_master`).
3. **`SelfContainedUnifiedAllTablesThirtySixBudgetSynth` (`10/10` tight)**:
   - Complete 9-table unified coupled/merge envelopes (`F ≤ 95_238_095_238`, `G ≤ 100_000_000_000`,
     `kPanUnifiedAllTables = 136_116_135_658`, `6 * kPanUnifiedAllTables < yukon`),
   - All 32-budget and 36-budget portfolio tiers under Yukon (`900_719_925_474`), strict `yukonScore`
     monotonicity, `claim.json ≤ 128` byte conformity, and `InitE.Certificate` lifting (`0 sorryAx`,
     10 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.SelfContainedLabToTargetAndSubBlockSynth

open Classical
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
open InitECandidate.Solver.SelfContainedSixPassMaster (sixPassReducedK sixPassSlope)
open InitECandidate.Solver.SelfContainedSolutionCandidates
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.YukonVerifyScriptAudit
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.FourPassClockIsometryChain
open InitECandidate.Solver.SelfContainedQuadraticEnvelopeCert (C_sr_probe yukonFloat64StepCeiling)
open InitECandidate.Solver.SelfContainedSloadProbeEnvelope
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordSimpPreservesNoStoreConsts
open InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
open InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
open InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
open InitECandidate.Solver.GuestBlockVsTxHtabBounds
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon maxGuestSourceClock)
open InitECandidate.Solver.GuestDirtyWriteHtabDominance
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope
open InitECandidate.Solver.GuestCoupledTxBlockStorageBound
open InitECandidate.Solver.GuestSstoreWarmCoeffAudit
open InitECandidate.Solver.GuestSstoreCleanToDirtyTransition (kPanTransition)
open InitECandidate.Solver.GuestJointTransitionInsertionBound (kIns)
open InitECandidate.Solver.GuestMergeTxUnionEnvelope (locCoup mergeLin blockMerge union_linear merge_block_square merge_block_le merge_block_tight addr_unions_constant kPanMerge kPanMerge_val kPanMerge_master slopes_ok slope_threshold margin6 merge_overhead)
open InitECandidate.Solver.GuestMultiAddressMergeDominance (kPanMultiAddrMerge)
open InitECandidate.Solver.GuestFiveAddrTablesMergeBound (identity5 five_addr_tables_absorbed five_le five_tight identity12 twelve_addr_tables_absorbed twelve_sharp coupled_absorbed coupled_le coupled_addr_corner envelope_unchanged)
open InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope (F unified_five_var_coupled_envelope unified_coupled_le unified_coupled_tight unified_cold_corner G merge_identity unified_five_var_merge_envelope unified_merge_le unified_merge_tight kPanUnifiedAllTables kPanUnified_val kPanUnified_master slopes)
open InitECandidate.Solver.GuestSubBlockTxSplittingDominance (localCost sD sR sA sC sW split_local_le split_strict prefixCost prefix_le prefix_tight prefix_strict txResetTicks txMinUnits reset_bound reset_absorbed max_tx_reset access_list_key_cost split_master)
open InitECandidate.Solver.PerTxEip7825TargetMasterK
open InitECandidate.Solver.RiscvSszFastRejectAndBootCert
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitECandidate.Solver.YukonFinalCandidateSelector (quadraticCollisionTargetK)
open InitECandidate.Solver.JointBlockGasSixPassMasterCert
open InitECandidate.Solver.SelfContainedMidPassesAndSloadSynth
open InitECandidate.Solver.Bs32DominanceSixPassTargetCert
open InitECandidate.Solver.Bs32EnvelopeTwelveCandidateBridge
open InitECandidate.Solver.CoupledTxBlockSixPassTargetCert
open InitECandidate.Solver.ExactKeccakCopyLoopUnrolledCert
open InitECandidate.Solver.ExactKeccakSixPassReducedCert
open InitECandidate.Solver.SelfContainedTenCandidateHierarchy
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio
open InitECandidate.Solver.SelfContainedFifteenRegimePortfolio
open InitECandidate.Solver.SelfContainedFullWordToWordAndSstoreSynth
open InitECandidate.Solver.CleanToDirtyCoupledSixPassMaster
open InitECandidate.Solver.PanToStackNoStoreConsts
open InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts (u_body_chain panToStackNames_bodies_StackNoSt_unconditional stackRemove_storeConsts_not_skip flatten_storeConsts_empty FlattenVisitsSt not_visits_of_StackNoSt visits_storeConsts_tight progToSection_sectionId panToLabSection_unconditional)
open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock (IsStubLabel CleanSection stackToLab_compile_sections panToLab_sections_unconditional stackToLab_compile_ids stackRemove_no_storeConsts_branch stackRemove_branch_tight isStubLabel_storeConsts isStubLabel_tight)
open InitECandidate.Solver.LabToTargetSectionCleanPreservation (Sec ids ids_filterSkip ids_encSecList ids_encSecsAgain ids_updLabLen ids_padCode ids_removeLabelsLoop ids_removeLabels mem_of_ids_eq length_of_ids_eq panToTarget_sections_clean panToTarget_sections_length filterSkip_changes_lines ids_distinguish_stub ids_not_trivial)
open InitECandidate.Solver.SelfContainedWordSimpAndCoupledSynth
open InitECandidate.Solver.SelfContainedCleanToDirtyAndFullWordSynth
open InitECandidate.Solver.PanToStackAndJointTransitionMaster
open InitECandidate.Solver.ThirtyTwoBudgetJointAbsorptionMaster
open InitECandidate.Solver.SelfContainedThirtyTwoBudgetPortfolio
open InitECandidate.Solver.SelfContainedMergeTxAndJointAbsorptionSynth
open InitECandidate.Solver.FiveAddrTablesThirtySixBudgetMaster (five_offsets_non_vacuous_and_tight complete_five_absorption_non_vacuous_and_tight twelve_master_non_vacuous_and_tight five_master_non_vacuous_and_tight five_four_tiers_non_vacuous_and_tight twelve_four_tiers_non_vacuous_and_tight five_tables_backend_portfolio_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth
open InitECandidate.Solver.SelfContainedUnifiedAllTablesThirtySixBudgetSynth
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
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

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Complete `LabToTarget.removeLabels` section ID preservation,
cleanliness transport (`panToTarget_sections_clean`), exact section count (`panToTarget_sections_length`),
and non-triviality witnesses (`filterSkip_changes_lines`, `ids_distinguish_stub`, `ids_not_trivial`). -/
theorem lab_to_target_section_clean_and_length_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h_any : removeLabels ic ac pos labs ffis L = some (L', labs'))
    (L_pan : List (Sec width)) (labs_pan : Spt (Spt Nat))
    (h_pan : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L_pan, labs_pan)) :
    ids L' = ids L ∧
    L'.length = L.length ∧
    ids L_pan = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    (∀ s' ∈ L_pan, IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L_pan.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
    filterSkip [(⟨7, [.asm (.asmi (.inst .skip)) [] 0]⟩ : Sec width)] = [⟨7, []⟩] ∧
    (IsStubLabel (ids [(⟨64, []⟩ : Sec width)]).head! = false ∧
      IsStubLabel (ids [(⟨0, []⟩ : Sec width)]).head! = true) ∧
    ids [(⟨3, []⟩ : Sec width)] ≠ ids [(⟨4, []⟩ : Sec width)] := by
  have hid := ids_removeLabels ic ac pos labs ffis L L' labs' h_any
  have hclean := panToTarget_sections_clean arch prog wc ac perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
  refine ⟨hid,
    length_of_ids_eq hid,
    hclean.1,
    hclean.2,
    panToTarget_sections_length arch prog wc ac perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan,
    filterSkip_changes_lines,
    ids_distinguish_stub,
    ids_not_trivial⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Sub-block multi-transaction splitting dominance from
`GuestSubBlockTxSplittingDominance` (`split_local_le`, `split_strict`, `prefix_le`, `prefix_tight`,
`prefix_strict`, `reset_bound`, `reset_absorbed`, `max_tx_reset`, `access_list_key_cost`, `split_master`). -/
theorem guest_sub_block_tx_splitting_dominance_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat))
    (lp : List (Nat × Nat)) (P D W T bound : Nat)
    (hT : txMinUnits * T ≤ 2000000)
    (hb : localCost (sD l, sR l, sA l, sC l, sW l) ≤ bound) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    (l.map localCost).sum ≤ bound ∧
    (localCost (1, 1, 1, 1, 1) + localCost (1, 1, 1, 1, 1) = 40 ∧
      localCost (2, 2, 2, 2, 2) = 80) ∧
    prefixCost lp P ≤ (P + (lp.map Prod.fst).sum) * (lp.map Prod.snd).sum ∧
    prefixCost [(D, W)] 0 = D * W ∧
    (prefixCost [(1, 1), (1, 1)] 0 = 3 ∧ 3 < (0 + 2) * 2) ∧
    8 * (6 + 1 + (1 + 64 / 32 + 3)) + 2 ≤ txResetTicks ∧
    (txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) ∧
    (txMinUnits * 16666 ≤ 2000000 ∧ 2000000 < txMinUnits * 16667 ∧
      txResetTicks * 16666 = 3333200) ∧
    ((2100 - 100) + 128 * 16 = 4048 ∧ 2000 ≤ 4048) ∧
    6 * kPanUnifiedAllTables < yukon ∧
    kPanUnifiedAllTables = 136116135658 := by
  have hsm := split_master l bound hb
  refine ⟨split_local_le l,
    hsm.1,
    split_strict,
    prefix_le lp P,
    prefix_tight D W,
    prefix_strict,
    reset_bound,
    reset_absorbed T hT,
    max_tx_reset,
    access_list_key_cost,
    hsm.2.1,
    hsm.2.2⟩

/-- Theorem 3 (`non_vacuous_and_tight`): Sub-block transaction splitting coupled with the 9-table
unified coupled/merge envelopes (`F ≤ 95_238_095_238`, `G ≤ 100_000_000_000`, `kPanUnifiedAllTables = 136_116_135_658`):
for any multi-transaction trace `l` whose aggregate counts `(sD l, sR l, sA l, sC l, sW l)` satisfy
the block gas inequality, the sum of per-tx local costs is bounded by `F (sD l) (sR l) (sA l) (sC l) (sW l) ≤ 95_238_095_238`. -/
theorem sub_block_tx_splitting_under_unified_all_tables_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat))
    (D_m R_m A_m C_m W_m Tloc Tlin K : Nat)
    (hc : 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ S)
    (hm : 20 * (D_m + R_m + A_m) + 6 * A_m + 21 * C_m + (W_m + (D_m + R_m + A_m)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    (l.map localCost).sum ≤ F (sD l) (sR l) (sA l) (sC l) (sW l) ∧
    (l.map localCost).sum ≤ 95_238_095_238 ∧
    42 * F (sD l) (sR l) (sA l) (sC l) (sW l) ≤ S * S ∧
    40 * G D_m R_m A_m C_m W_m ≤ S * S ∧
    G D_m R_m A_m C_m W_m ≤ 100_000_000_000 ∧
    linear + Tloc + G D_m R_m A_m C_m W_m + Tlin ≤ kPanUnifiedAllTables ∧
    (F 47_619 0 0 0 1_000_001 ≤ K ↔ 95_238_095_238 ≤ K) ∧
    (G 50_000 0 0 0 950_000 ≤ K ↔ 100_000_000_000 ≤ K) := by
  have hsub := split_local_le l
  have hloc_le_F : localCost (sD l, sR l, sA l, sC l, sW l) ≤ F (sD l) (sR l) (sA l) (sC l) (sW l) := by
    simp only [localCost, F]; omega
  have hFle := unified_coupled_le (sD l) (sR l) (sA l) (sC l) (sW l) hc
  have h1 := unified_five_var_coupled_master_envelope_non_vacuous_and_tight
    (sD l) (sR l) (sA l) (sC l) (sW l) K hc
  have h2 := unified_five_var_merge_master_envelope_non_vacuous_and_tight
    D_m R_m A_m C_m W_m K hm
  refine ⟨le_trans hsub hloc_le_F,
    le_trans (le_trans hsub hloc_le_F) hFle,
    h1.1,
    h2.1,
    h2.2.1,
    kPanUnified_master D_m R_m A_m C_m W_m Tloc Tlin hm hloc hlin,
    h1.2.2.2.2,
    h2.2.2.2.2⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Full Pancake-to-Target compiler chain (`panToWordCompileProgHOL` →
`WordToWord.compile` → `compileNative` → `StackToLab.compile` → `filterSkip` → `LabToTarget.removeLabels`)
combined with `WordToWord.fullCompileSingle` zero-`storeConsts` allowance and all 4 unified 3-pass/6-pass
target budgets (`408_348_416_306`, `408_348_430_106`, `816_696_823_280`, `816_696_837_080`). -/
theorem full_pan_to_target_compiler_chain_and_unified_budgets_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L_pan : List (Sec width)) (labs_pan : Spt (Spt Nat))
    (h_pan : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L_pan, labs_pan))
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (ctx : Spt Nat) (q : HolLoopProg width) (l_loop : Nat × Nat)
    (b : Bool) (rc alg nm ac_n : Nat) (co : Option (Spt Nat))
    (ws : List (Bool × BitVec width))
    (bs D R A C W D5 A5 W5 Tloc Tlin : Nat)
    (hc : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hm : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (h5 : 20 * D5 + 26 * A5 + (W5 + D5 + A5) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    ids L_pan = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    (∀ s' ∈ L_pan, IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L_pan.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
    NoSt (WordToWord.fullCompileSingle b rc alg ac
      ((nm, ac_n, (LoopToWord.compHOL ctx q l_loop).1), co)).2.2 = true ∧
    ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables) +
      storeConstsAllowance (WordToWord.fullCompileSingle b rc alg ac
        ((nm, ac_n, (LoopToWord.compHOL ctx q l_loop).1), co)).2.2 = 816_696_823_280 ∧
    (bootstrapSteps + 6 * kPanUnifiedAllTables) +
      storeConstsAllowance (WordToWord.fullCompileSingle b rc alg ac
        ((nm, ac_n, (LoopToWord.compHOL ctx q l_loop).1), co)).2.2 = 816_696_837_080 ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have hclean := panToTarget_sections_clean arch prog wc ac perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
  have hlen := panToTarget_sections_length arch prog wc ac perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
  have hcomp := unified_all_tables_with_unconditional_compiler_chain_non_vacuous_and_tight
    arch prog wc ac perf info j bd ptr f ctx q l_loop b rc alg nm ac_n co ws
    bs D R A C W D5 A5 W5 Tloc Tlin hc hm h5 hloc hlin
  refine ⟨hclean.1,
    hclean.2,
    hlen,
    hcomp.2.2.2.1,
    hcomp.2.2.2.2.2.1,
    hcomp.2.2.2.2.2.2.1,
    hcomp.2.2.2.2.2.2.2.1,
    hcomp.2.2.2.2.2.2.2.2⟩

/-- Theorem 5 (`non_vacuous_and_tight`): Unified all-9-tables + sub-block transaction splitting +
5-address-table offset absorption (`bs+8/16/24/40/48`) across the four 3-pass and 6-pass target tiers
(`408_348_416_306`, `408_348_430_106`, `816_696_823_280`, `816_696_837_080 < yukon`). -/
theorem unified_all_tables_sub_block_and_five_offsets_four_tiers_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat))
    (bs D R A C W D5 A5 W5 Tloc Tlin K : Nat)
    (hc : 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ S)
    (hu : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (h5 : 20 * D5 + 26 * A5 + (W5 + D5 + A5) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    (l.map localCost).sum ≤ 95_238_095_238 ∧
    ([bs + 8, bs + 16, bs + 24, bs + 40, bs + 48].map (fun _ => A5 * A5)).sum = 5 * (A5 * A5) ∧
    linear + Tloc + (2 * ((D5 + A5) * (W5 + D5 + A5)) +
      ([bs + 8, bs + 16, bs + 24, bs + 40, bs + 48].map (fun _ => A5 * A5)).sum) + Tlin ≤ kPanUnifiedAllTables ∧
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables ∧
    9332 + 3 * (linear + Tloc + G D R A C W + Tlin) ≤ 408_348_416_306 ∧
    23132 + 3 * (linear + Tloc + G D R A C W + Tlin) ≤ 408_348_430_106 ∧
    9332 + 6 * (linear + Tloc + G D R A C W + Tlin) ≤ 816_696_823_280 ∧
    23132 + 6 * (linear + Tloc + G D R A C W + Tlin) ≤ 816_696_837_080 ∧
    (816_696_837_080 ≤ K ↔ mergeSlope6K ≤ K) := by
  have hsub := sub_block_tx_splitting_under_unified_all_tables_non_vacuous_and_tight
    l D R A C W Tloc Tlin K hc hu hloc hlin
  have h4 := unified_all_tables_and_five_offsets_four_tiers_non_vacuous_and_tight
    bs D R A C W D5 A5 W5 Tloc Tlin K hu h5 hloc hlin
  exact ⟨hsub.2.1, h4⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Preservation of all 32-budget
(`CleanToDirtyCoupledSixPassMaster.unified`, `absorbedPortfolio`) and 36-budget
(`FiveAddrTablesThirtySixBudgetMaster.portfolio`) portfolio tiers under Yukon (`900_719_925_474`)
with sub-block multi-transaction splitting and 9-table unified coupled/merge absorption. -/
theorem thirty_two_and_thirty_six_portfolios_under_sub_block_and_unified_tables_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat))
    (lp : List (Nat × Nat)) (P T D R A C W D_m R_m A_m C_m W_m D_t W_t R_t K : Nat)
    (hT : txMinUnits * T ≤ 2000000)
    (hc : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hm : 20 * (D_m + R_m + A_m) + 6 * A_m + 21 * C_m + (W_m + (D_m + R_m + A_m)) ≤ S)
    (ht : 21 * D_t + W_t + 20 * R_t ≤ S) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) ∧
    prefixCost lp P ≤ (P + (lp.map Prod.fst).sum) * (lp.map Prod.snd).sum ∧
    (txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666) ∧
    42 * F D R A C W ≤ S * S ∧
    F D R A C W ≤ 95_238_095_238 ∧
    40 * G D_m R_m A_m C_m W_m ≤ S * S ∧
    G D_m R_m A_m C_m W_m ≤ 100_000_000_000 ∧
    42 * (D_t * (2 * W_t + 4 * R_t) + kIns * R_t) ≤ S * S ∧
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    absorbedPortfolio.length = 32 ∧
    FiveAddrTablesThirtySixBudgetMaster.portfolio.length = 36 ∧
    FiveAddrTablesThirtySixBudgetMaster.portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      1_212_035_192 ≤ absorbBudget k ∧ absorbBudget k ≤ k ∧ k < 900_719_925_474) ∧
    (∀ k ∈ FiveAddrTablesThirtySixBudgetMaster.portfolio,
      1_212_035_192 ≤ k ∧ k ≤ 857_384_015_252 ∧ k < 900_719_925_474) ∧
    (mergeSlope6K ≤ K ↔ 816_696_837_080 ≤ K) := by
  have hp := thirty_two_and_thirty_six_portfolios_under_unified_all_tables_non_vacuous_and_tight
    D R A C W D_m R_m A_m C_m W_m D_t W_t R_t K hc hm ht
  refine ⟨split_local_le l,
    prefix_le lp P,
    reset_absorbed T hT,
    hp⟩

/-- Theorem 7 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity and IEEE-754 `float64`
exactness (`< 2^53 - 1`) across the 32-budget and 36-budget portfolios with unified all-9-tables
and sub-block splitting clock invariance. -/
theorem lab_to_target_and_sub_block_yukon_score_monotonicity_non_vacuous_and_tight
    (minutes K : Nat) :
    (CleanToDirtyCoupledSixPassMaster.unified.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (FiveAddrTablesThirtySixBudgetMaster.portfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ k1 ∈ FiveAddrTablesThirtySixBudgetMaster.portfolio,
      ∀ k2 ∈ FiveAddrTablesThirtySixBudgetMaster.portfolio,
        k1 < k2 ↔ yukonScore k1 minutes < yukonScore k2 minutes) ∧
    (∀ k ∈ FiveAddrTablesThirtySixBudgetMaster.portfolio,
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    yukonScore transition3K minutes < yukonScore ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanUnifiedAllTables) minutes ∧
    yukonScore ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanUnifiedAllTables) minutes <
      yukonScore (bootstrapSteps + 3 * kPanUnifiedAllTables) minutes ∧
    yukonScore transition6K minutes < yukonScore ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables) minutes ∧
    yukonScore ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables) minutes <
      yukonScore (bootstrapSteps + 6 * kPanUnifiedAllTables) minutes ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) :=
  unified_all_tables_yukon_score_monotonicity_non_vacuous_and_tight minutes K

/-- Theorem 8 (`non_vacuous_and_tight`): `claim.json ≤ 128` byte conformity across all 32 claims
of `thirtyTwoUnifiedClaims`, all 36 claims of `thirtySixMergeClaims`, and the 4 unified all-tables
target budgets. -/
theorem lab_to_target_and_sub_block_claims_128_byte_conformity_non_vacuous_and_tight (K : Nat) :
    thirtyTwoUnifiedClaims.length = 32 ∧
    thirtySixMergeClaims.length = 36 ∧
    (∀ entry ∈ thirtyTwoUnifiedClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (∀ entry ∈ thirtySixMergeClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    validFiniteClaim ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanUnifiedAllTables)
      (verifierClaimJson "408348416306") = true ∧
    validFiniteClaim (bootstrapSteps + 3 * kPanUnifiedAllTables)
      (verifierClaimJson "408348430106") = true ∧
    validFiniteClaim ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables)
      (verifierClaimJson "816696823280") = true ∧
    validFiniteClaim (bootstrapSteps + 6 * kPanUnifiedAllTables)
      (verifierClaimJson "816696837080") = true ∧
    (validFiniteClaim K (verifierClaimJson "816696837080") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) :=
  unified_all_tables_claims_128_byte_conformity_non_vacuous_and_tight K

/-- Theorem 9 (`non_vacuous_and_tight`): `InitE.Certificate` lifting across all 4 unified all-tables
tiers, all 32 budgets of `CleanToDirtyCoupledSixPassMaster.unified`, all 32 absorbed budgets of
`absorbedPortfolio`, all 36 budgets of `FiveAddrTablesThirtySixBudgetMaster.portfolio`, and all 38
budgets of `allThirtyEightMergeBudgets`. -/
theorem lab_to_target_and_sub_block_certificate_lifting_non_vacuous_and_tight
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_merge6 : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        mergeSlope6K (baselineInitialState input)).1 ≠ .timeOut)
    (hc_best : CertificateAt 1_212_035_192) :
    CertificateAt ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanUnifiedAllTables) ∧
    CertificateAt (bootstrapSteps + 3 * kPanUnifiedAllTables) ∧
    CertificateAt ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables) ∧
    CertificateAt (bootstrapSteps + 6 * kPanUnifiedAllTables) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (absorbBudget k)) (.finite (absorbBudget k))) ∧
    (∀ k ∈ FiveAddrTablesThirtySixBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ allThirtyEightMergeBudgets,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    ¬ (bootstrapSteps + 6 * kPanUnifiedAllTables ≤ mergeSlope6K - 1) :=
  unified_all_tables_certificate_lifting_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_merge6 hc_best

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_103` Master Synthesis Theorem uniting:
1. `LabToTargetSectionCleanPreservation` (`14/14` tight: `panToTarget_sections_clean`,
   `panToTarget_sections_length`, `ids_removeLabels`),
2. `GuestSubBlockTxSplittingDominance` (`10/10` tight: `split_local_le`, `split_strict`,
   `prefix_le`, `reset_absorbed`, `split_master`),
3. `SelfContainedUnifiedAllTablesThirtySixBudgetSynth` (`10/10` tight: `42·F ≤ S²`, `40·G ≤ S²`,
   `kPanUnifiedAllTables = 136_116_135_658`, 5-address-table offsets, unconditional compiler chain,
   32-budget and 36-budget Yukon compliance, `yukonScore` monotonicity, `claim.json ≤ 128` byte
   conformity, and `InitE.Certificate` lifting with `0` imports from `Proofs/Bounded*`). -/
theorem grand_lab_to_target_and_sub_block_master_non_vacuous_and_tight
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
    (txs : List (Nat × Nat × Nat × Nat × Nat)) (lp : List (Nat × Nat))
    (b d : Bool) (P T rc alg nm ac k_sn n bs D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin : Nat)
    (co : Option (Spt Nat))
    (hT : txMinUnits * T ≤ 2000000)
    (hc_u : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hm_u : 20 * (D_m + R_m + A_m) + 6 * A_m + 21 * C_m + (W_m + (D_m + R_m + A_m)) ≤ S)
    (h5 : 20 * D5 + 26 * A5 + (W5 + D5 + A5) ≤ S)
    (hDWR : 21 * D_t + W_t + 20 * R_t ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
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
    F D R A C W ≤ 95_238_095_238 ∧
    40 * G D_m R_m A_m C_m W_m ≤ S * S ∧
    G D_m R_m A_m C_m W_m ≤ 100_000_000_000 ∧
    linear + Tloc + G D_m R_m A_m C_m W_m + Tlin ≤ kPanUnifiedAllTables ∧
    linear + Tloc + (2 * ((D5 + A5) * (W5 + D5 + A5)) +
      ([bs + 8, bs + 16, bs + 24, bs + 40, bs + 48].map (fun _ => A5 * A5)).sum) + Tlin ≤ kPanUnifiedAllTables ∧
    kPanUnifiedAllTables = 136_116_135_658 ∧
    6 * kPanUnifiedAllTables < yukon ∧
    42 * (D_t * (2 * W_t + 4 * R_t) + kIns * R_t) ≤ S * S ∧
    (∀ y ∈ (compileNative asmConf perf (WordToWord.compile wc asmConf
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
    StackToLab.flattenHOL tail (.storeConsts s_st b_st stub : HolProg width) sid next cs bs_l =
      (.list [], false, next) ∧
    NoSt (WordToWord.fullCompileSingle b rc alg asmConf
      ((nm, ac, (LoopToWord.compHOL ctx q l_loop).1), co)).2.2 = true ∧
    stackRemoveClockWithAllowance k_sn (WordToWord.fullCompileSingle b rc alg asmConf
      ((nm, ac, (LoopToWord.compHOL ctx q l_loop).1), co)).2.2 = k_sn + 1 ∧
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    absorbedPortfolio.length = 32 ∧
    FiveAddrTablesThirtySixBudgetMaster.portfolio.length = 36 ∧
    FiveAddrTablesThirtySixBudgetMaster.portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ FiveAddrTablesThirtySixBudgetMaster.portfolio,
      1_212_035_192 ≤ k ∧ k < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK k) (.finite k) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    (FiveAddrTablesThirtySixBudgetMaster.portfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ thirtySixMergeClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (absorbBudget k)) (.finite (absorbBudget k))) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    zeroBoundedImportCount = 0 ∧
    ¬ (mergeSlope6K ≤ mergeSlope6K - 1) := by
  have hclean := panToTarget_sections_clean arch prog wc asmConf perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
  have hlen := panToTarget_sections_length arch prog wc asmConf perf sc dc mh sp off ic pos labs ffis L_pan labs_pan h_pan
  have hw98 := grand_unified_all_tables_thirty_six_budget_master_non_vacuous_and_tight
    arch prog wc asmConf perf info j bd ptr f tail s_st b_st stub sid next cs bs_l
    ctx q l_loop b d rc alg nm ac k_sn n bs D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin co
    hc_u hm_u h5 hDWR hloc hlin oracles c depth minutes hlab compiled depthBound not_timeOut_best
  refine ⟨hclean.1,
    hclean.2,
    hlen,
    split_local_le txs,
    prefix_le lp P,
    reset_absorbed T hT,
    hw98⟩

#print axioms lab_to_target_section_clean_and_length_non_vacuous_and_tight
#print axioms guest_sub_block_tx_splitting_dominance_non_vacuous_and_tight
#print axioms sub_block_tx_splitting_under_unified_all_tables_non_vacuous_and_tight
#print axioms full_pan_to_target_compiler_chain_and_unified_budgets_non_vacuous_and_tight
#print axioms unified_all_tables_sub_block_and_five_offsets_four_tiers_non_vacuous_and_tight
#print axioms thirty_two_and_thirty_six_portfolios_under_sub_block_and_unified_tables_non_vacuous_and_tight
#print axioms lab_to_target_and_sub_block_yukon_score_monotonicity_non_vacuous_and_tight
#print axioms lab_to_target_and_sub_block_claims_128_byte_conformity_non_vacuous_and_tight
#print axioms lab_to_target_and_sub_block_certificate_lifting_non_vacuous_and_tight
#print axioms grand_lab_to_target_and_sub_block_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedLabToTargetAndSubBlockSynth
