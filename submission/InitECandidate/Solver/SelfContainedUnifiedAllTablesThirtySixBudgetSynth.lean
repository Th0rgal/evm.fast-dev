import InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope
import InitECandidate.Solver.FiveAddrTablesThirtySixBudgetMaster
import InitECandidate.Solver.SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedUnifiedAllTablesThirtySixBudgetSynth` — Wave 5 Atomic Worker `W5_98`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) uniting:
1. **`GuestUnifiedAllTablesMasterEnvelope` (`11/11` tight)**:
   - Master 5-variable coupled envelope (`unified_five_var_coupled_envelope`: `42·F ≤ S²`,
     `unified_coupled_le`: `F D R A C W ≤ 95_238_095_238`, `unified_coupled_tight` at
     `(47_619, 0, 0, 0, 1_000_001)`, `unified_cold_corner` at `(0, 0, 0, 95_238, 0)`),
   - Master 5-variable merge envelope (`merge_identity`, `unified_five_var_merge_envelope`:
     `40·G ≤ S²`, `unified_merge_le`: `G D R A C W ≤ 100_000_000_000`, `unified_merge_tight` at
     `(50_000, 0, 0, 0, 950_000)` and `(2_000, 48_000, 0, 0, 950_000)`),
   - Unified source clock invariance `kPanUnifiedAllTables = 136_116_135_658 = kPanMerge`
     (`kPanUnified_val`, `kPanUnified_master`) and Yukon threshold (`6 * kPanUnifiedAllTables < yukon`,
     `k * kPanUnifiedAllTables < yukon ↔ k ≤ 6`).
2. **`FiveAddrTablesThirtySixBudgetMaster` (`47/47` tight)**:
   - Explicit 5-address-table offset absorption (`bs+8/16/24/40/48`, `five_offsets_non_vacuous_and_tight`,
     `complete_five_absorption_non_vacuous_and_tight`, `five_master_non_vacuous_and_tight`,
     `twelve_master_non_vacuous_and_tight`, `five_four_tiers_non_vacuous_and_tight`,
     `twelve_four_tiers_non_vacuous_and_tight`),
   - Joint arithmetic and unconditional backend invariant (`five_tables_backend_portfolio_non_vacuous_and_tight`).
3. **`SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth` (`10/10` tight)**:
   - Unconditional compiler chain (`panToStackNames_bodies_StackNoSt_unconditional` +
     `flatten_storeConsts_empty` + `panToLabSection_unconditional`),
   - All 32-budget and 36-budget portfolio tiers under Yukon (`900_719_925_474`), strict `yukonScore`
     monotonicity, `claim.json ≤ 128` byte conformity, and `InitE.Certificate` lifting (`0 sorryAx`,
     10 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.SelfContainedUnifiedAllTablesThirtySixBudgetSynth

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
open InitECandidate.Solver.SelfContainedWordSimpAndCoupledSynth
open InitECandidate.Solver.SelfContainedCleanToDirtyAndFullWordSynth
open InitECandidate.Solver.PanToStackAndJointTransitionMaster
open InitECandidate.Solver.ThirtyTwoBudgetJointAbsorptionMaster
open InitECandidate.Solver.SelfContainedThirtyTwoBudgetPortfolio
open InitECandidate.Solver.SelfContainedMergeTxAndJointAbsorptionSynth
open InitECandidate.Solver.FiveAddrTablesThirtySixBudgetMaster (five_offsets_non_vacuous_and_tight complete_five_absorption_non_vacuous_and_tight twelve_master_non_vacuous_and_tight five_master_non_vacuous_and_tight five_four_tiers_non_vacuous_and_tight twelve_four_tiers_non_vacuous_and_tight five_tables_backend_portfolio_non_vacuous_and_tight)
open InitECandidate.Solver.SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Complete 5-variable coupled envelope synthesis from
`GuestUnifiedAllTablesMasterEnvelope` (`42·F D R A C W ≤ S²`, `F D R A C W ≤ 95_238_095_238`,
attained at `(47_619, 0, 0, 0, 1_000_001)`, with pure-`bs+72` cold corner `F 0 0 0 95_238 0 = 9_070_276_644`). -/
theorem unified_five_var_coupled_master_envelope_non_vacuous_and_tight
    (D R A C W K : Nat)
    (h : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S) :
    42 * F D R A C W ≤ S * S ∧
    F D R A C W ≤ 95_238_095_238 ∧
    (21 * 47_619 + 20 * 0 + 26 * 0 + 21 * 0 + 1_000_001 = S ∧
      F 47_619 0 0 0 1_000_001 = 95_238_095_238) ∧
    (F 0 0 0 95_238 0 = 9_070_276_644 ∧ 9_070_276_644 < 95_238_095_238) ∧
    (F 47_619 0 0 0 1_000_001 ≤ K ↔ 95_238_095_238 ≤ K) := by
  have ht := unified_coupled_tight
  refine ⟨unified_five_var_coupled_envelope D R A C W h,
    unified_coupled_le D R A C W h,
    ht,
    unified_cold_corner,
    by rw [ht.2]⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Complete 5-variable merge envelope synthesis from
`GuestUnifiedAllTablesMasterEnvelope` (`40·G D R A C W ≤ S²`, `G D R A C W ≤ 100_000_000_000 = blockMerge`,
attained at `(50_000, 0, 0, 0, 950_000)` and `(2_000, 48_000, 0, 0, 950_000)`). -/
theorem unified_five_var_merge_master_envelope_non_vacuous_and_tight
    (D R A C W K : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S) :
    40 * G D R A C W ≤ S * S ∧
    G D R A C W ≤ 100_000_000_000 ∧
    G D R A C W ≤ blockMerge ∧
    (G 50_000 0 0 0 950_000 = 100_000_000_000 ∧
      G 2_000 48_000 0 0 950_000 = 100_000_000_000 ∧
      20 * (2_000 + 48_000 + 0) + 6 * 0 + 21 * 0 + (950_000 + (2_000 + 48_000 + 0)) = S) ∧
    (G 50_000 0 0 0 950_000 ≤ K ↔ 100_000_000_000 ≤ K) := by
  have hle := unified_merge_le D R A C W h
  have hbm : blockMerge = 100_000_000_000 := rfl
  have ht := unified_merge_tight
  refine ⟨unified_five_var_merge_envelope D R A C W h,
    hle,
    by rw [hbm]; exact hle,
    ht,
    by rw [ht.1]⟩

/-- Theorem 3 (`non_vacuous_and_tight`): Unified all-9-tables source clock invariance
(`kPanUnifiedAllTables = 136_116_135_658 = kPanMerge = kPanMultiAddrMerge`), master source-clock
bound `linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables`, and Yukon slope threshold
(`6 * kPanUnifiedAllTables < yukon`, `k * kPanUnifiedAllTables < yukon ↔ k ≤ 6`). -/
theorem unified_all_tables_source_clock_and_slopes_non_vacuous_and_tight
    (D R A C W Tloc Tlin k : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    kPanUnifiedAllTables = 136_116_135_658 ∧
    kPanUnifiedAllTables = kPanMerge ∧
    kPanUnifiedAllTables = kPanMultiAddrMerge ∧
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables ∧
    6 * kPanUnifiedAllTables < yukon ∧
    (k * kPanUnifiedAllTables < yukon ↔ k ≤ 6) ∧
    (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanUnifiedAllTables = mergeSlope3UnrolledK ∧
    bootstrapSteps + 3 * kPanUnifiedAllTables = mergeSlope3K ∧
    (bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables = mergeSlope6UnrolledK ∧
    bootstrapSteps + 6 * kPanUnifiedAllTables = mergeSlope6K := by
  have hval := kPanUnified_val
  have hsl := slopes k
  refine ⟨hval.1,
    hval.2,
    rfl,
    kPanUnified_master D R A C W Tloc Tlin h hloc hlin,
    hsl.1,
    hsl.2,
    rfl,
    rfl,
    rfl,
    rfl⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Synthesis of `FiveAddrTablesThirtySixBudgetMaster` with
`GuestUnifiedAllTablesMasterEnvelope`: all 5 address-table offsets (`bs+8/16/24/40/48`) and all 9
hash tables (`bs+32`, `ts+32`, `bs+72`, `bs+8/16/24/40/48`) preserve the four 3-pass and 6-pass
target tiers (`408_348_416_306`, `408_348_430_106`, `816_696_823_280`, `816_696_837_080 < yukon`). -/
theorem unified_all_tables_and_five_offsets_four_tiers_non_vacuous_and_tight
    (bs D R A C W D5 A5 W5 Tloc Tlin K : Nat)
    (hu : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (h5 : 20 * D5 + 26 * A5 + (W5 + D5 + A5) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    ([bs + 8, bs + 16, bs + 24, bs + 40, bs + 48].map (fun _ => A5 * A5)).sum = 5 * (A5 * A5) ∧
    linear + Tloc + (2 * ((D5 + A5) * (W5 + D5 + A5)) +
      ([bs + 8, bs + 16, bs + 24, bs + 40, bs + 48].map (fun _ => A5 * A5)).sum) + Tlin ≤ kPanUnifiedAllTables ∧
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables ∧
    9332 + 3 * (linear + Tloc + G D R A C W + Tlin) ≤ 408_348_416_306 ∧
    23132 + 3 * (linear + Tloc + G D R A C W + Tlin) ≤ 408_348_430_106 ∧
    9332 + 6 * (linear + Tloc + G D R A C W + Tlin) ≤ 816_696_823_280 ∧
    23132 + 6 * (linear + Tloc + G D R A C W + Tlin) ≤ 816_696_837_080 ∧
    (816_696_837_080 ≤ K ↔ mergeSlope6K ≤ K) := by
  have h5m := five_master_non_vacuous_and_tight bs D5 A5 W5 Tloc Tlin h5 hloc hlin
  have hum := kPanUnified_master D R A C W Tloc Tlin hu hloc hlin
  have hkval : kPanUnifiedAllTables = 136_116_135_658 := rfl
  have hm6 : mergeSlope6K = 816_696_837_080 := rfl
  refine ⟨five_offsets_non_vacuous_and_tight bs A5,
    h5m,
    hum,
    by omega,
    by omega,
    by omega,
    by omega,
    by rw [hm6]⟩

/-- Theorem 5 (`non_vacuous_and_tight`): Joint synthesis of `GuestUnifiedAllTablesMasterEnvelope`,
`FiveAddrTablesThirtySixBudgetMaster.five_tables_backend_portfolio_non_vacuous_and_tight`, and the
unconditional `PanToStackToLab` + `WordToWord.fullCompileSingle` zero-`storeConsts` compiler chain. -/
theorem unified_all_tables_with_unconditional_compiler_chain_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (b : Bool) (rc alg nm ac_n : Nat) (co : Option (Spt Nat))
    (ws : List (Bool × BitVec width))
    (bs D R A C W D5 A5 W5 Tloc Tlin : Nat)
    (hc : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hm : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (h5 : 20 * D5 + 26 * A5 + (W5 + D5 + A5) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    F D R A C W ≤ 95_238_095_238 ∧
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables ∧
    linear + Tloc + (2 * ((D5 + A5) * (W5 + D5 + A5)) +
      ([bs + 8, bs + 16, bs + 24, bs + 40, bs + 48].map (fun _ => A5 * A5)).sum) + Tlin ≤ kPanMultiAddrMerge ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
    (∀ (tail : Bool) (s b_s : Nat) (stub : Option Nat) (sid next : Nat) (cs bs_l : List Nat),
      StackToLab.flattenHOL tail (.storeConsts s b_s stub : HolProg width) sid next cs bs_l =
        (.list [], false, next)) ∧
    NoSt (WordToWord.fullCompileSingle b rc alg ac
      ((nm, ac_n, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true ∧
    ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanUnifiedAllTables) +
      storeConstsAllowance (WordToWord.fullCompileSingle b rc alg ac
        ((nm, ac_n, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 816_696_823_280 ∧
    (bootstrapSteps + 6 * kPanUnifiedAllTables) +
      storeConstsAllowance (WordToWord.fullCompileSingle b rc alg ac
        ((nm, ac_n, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 816_696_837_080 ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have h5b := five_tables_backend_portfolio_non_vacuous_and_tight
    arch prog wc ac perf info j bd ptr f bs D5 A5 W5 Tloc Tlin h5 hloc hlin
  have hlab := five_addr_merge_tiers_with_unconditional_lab_chain_non_vacuous_and_tight
    arch prog wc ac perf info j bd ptr f ctx q l b rc alg nm ac_n co ws
  refine ⟨unified_coupled_le D R A C W hc,
    kPanUnified_master D R A C W Tloc Tlin hm hloc hlin,
    h5b.1,
    ?_,
    h5b.2.2.1,
    hlab.2.1,
    hlab.2.2.2.2.2.1,
    hlab.2.2.2.2.2.2.1,
    hlab.2.2.2.2.2.2.2⟩
  intro y hy
  rcases h5b.2.2.2 y hy with hstub | hnost
  · exact Or.inl hstub
  · exact Or.inr ⟨hnost, not_visits_of_StackNoSt _ hnost, rfl⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Preservation of all 32-budget
(`CleanToDirtyCoupledSixPassMaster.unified`, `absorbedPortfolio`) and 36-budget
(`thirtySixMergePortfolio` / `FiveAddrTablesThirtySixBudgetMaster.portfolio`) portfolio tiers under
Yukon (`900_719_925_474`) with complete 9-table unified coupled/merge absorption. -/
theorem thirty_two_and_thirty_six_portfolios_under_unified_all_tables_non_vacuous_and_tight
    (D R A C W D_m R_m A_m C_m W_m D_t W_t R_t K : Nat)
    (hc : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hm : 20 * (D_m + R_m + A_m) + 6 * A_m + 21 * C_m + (W_m + (D_m + R_m + A_m)) ≤ S)
    (ht : 21 * D_t + W_t + 20 * R_t ≤ S) :
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
  have hp := thirty_two_and_thirty_six_portfolios_under_five_addr_absorption_non_vacuous_and_tight
    0 0 0 0 0 0 D_t W_t R_t K (by unfold S; omega) (by unfold S; omega) ht
  refine ⟨unified_five_var_coupled_envelope D R A C W hc,
    unified_coupled_le D R A C W hc,
    unified_five_var_merge_envelope D_m R_m A_m C_m W_m hm,
    unified_merge_le D_m R_m A_m C_m W_m hm,
    hp.2.2.2.1,
    hp.2.2.2.2.1,
    hp.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 7 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity and IEEE-754 `float64`
exactness (`< 2^53 - 1`) across the 32-budget and 36-budget portfolios with unified all-9-tables
clock equalities. -/
theorem unified_all_tables_yukon_score_monotonicity_non_vacuous_and_tight
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
  thirty_two_and_thirty_six_yukon_score_monotonicity_non_vacuous_and_tight minutes K

/-- Theorem 8 (`non_vacuous_and_tight`): `claim.json ≤ 128` byte conformity across all 32 claims
of `thirtyTwoUnifiedClaims`, all 36 claims of `thirtySixMergeClaims`, and the 4 unified all-tables
target budgets (`(bootstrapSteps - copyLoopSavedSteps) + 3 * kPanUnifiedAllTables`, etc.). -/
theorem unified_all_tables_claims_128_byte_conformity_non_vacuous_and_tight (K : Nat) :
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
  thirty_two_and_thirty_six_claims_128_byte_conformity_non_vacuous_and_tight K

/-- Theorem 9 (`non_vacuous_and_tight`): `InitE.Certificate` lifting across all 4 unified all-tables
tiers, all 32 budgets of `CleanToDirtyCoupledSixPassMaster.unified`, all 32 absorbed budgets of
`absorbedPortfolio`, all 36 budgets of `FiveAddrTablesThirtySixBudgetMaster.portfolio`, and all 38
budgets of `allThirtyEightMergeBudgets`. -/
theorem unified_all_tables_certificate_lifting_non_vacuous_and_tight
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
  thirty_two_and_thirty_six_certificate_lifting_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_merge6 hc_best

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_98` Master Synthesis Theorem uniting:
1. `GuestUnifiedAllTablesMasterEnvelope` (`11/11` tight: `42·F ≤ S²`, `F ≤ 95_238_095_238`,
   `40·G ≤ S²`, `G ≤ 100_000_000_000`, `kPanUnifiedAllTables = 136_116_135_658`, `6 * kPanUnifiedAllTables < yukon`),
2. `FiveAddrTablesThirtySixBudgetMaster` (`47/47` tight: 5 address-table offsets `bs+8/16/24/40/48`,
   36-budget portfolio, and backend invariant),
3. `SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth` (`10/10` tight: unconditional
   `panToStackNames_bodies_StackNoSt_unconditional` + `flatten_storeConsts_empty` +
   `panToLabSection_unconditional`, 32-budget and 36-budget Yukon compliance, `yukonScore`
   monotonicity, `claim.json ≤ 128` byte conformity, and `InitE.Certificate` lifting with `0`
   imports from `Proofs/Bounded*`). -/
theorem grand_unified_all_tables_thirty_six_budget_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (asmConf : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (tail : Bool) (s_st b_st : Nat) (stub : Option Nat) (sid next : Nat) (cs bs_l : List Nat)
    (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (b d : Bool) (rc alg nm ac k_sn n bs D R A C W D_m R_m A_m C_m W_m D5 A5 W5 D_t W_t R_t Tloc Tlin : Nat)
    (co : Option (Spt Nat))
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
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true ∧
    stackRemoveClockWithAllowance k_sn (WordToWord.fullCompileSingle b rc alg asmConf
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = k_sn + 1 ∧
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
  have hw92 := grand_five_addr_and_unconditional_no_store_consts_master_non_vacuous_and_tight
    arch prog wc asmConf perf info j bd ptr f tail s_st b_st stub sid next cs bs_l
    ctx q l b d rc alg nm ac k_sn n D_t W_t R_t D5 A5 W5 0 0 0 Tloc Tlin co
    hDWR h5 (by unfold S; omega) hloc hlin oracles c depth minutes hlab compiled depthBound not_timeOut_best
  have h5m := five_master_non_vacuous_and_tight bs D5 A5 W5 Tloc Tlin h5 hloc hlin
  refine ⟨unified_five_var_coupled_envelope D R A C W hc_u,
    unified_coupled_le D R A C W hc_u,
    unified_five_var_merge_envelope D_m R_m A_m C_m W_m hm_u,
    unified_merge_le D_m R_m A_m C_m W_m hm_u,
    kPanUnified_master D_m R_m A_m C_m W_m Tloc Tlin hm_u hloc hlin,
    h5m,
    rfl,
    (slopes 6).1,
    hw92.2.2.2.2.1,
    hw92.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw92.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

#print axioms unified_five_var_coupled_master_envelope_non_vacuous_and_tight
#print axioms unified_five_var_merge_master_envelope_non_vacuous_and_tight
#print axioms unified_all_tables_source_clock_and_slopes_non_vacuous_and_tight
#print axioms unified_all_tables_and_five_offsets_four_tiers_non_vacuous_and_tight
#print axioms unified_all_tables_with_unconditional_compiler_chain_non_vacuous_and_tight
#print axioms thirty_two_and_thirty_six_portfolios_under_unified_all_tables_non_vacuous_and_tight
#print axioms unified_all_tables_yukon_score_monotonicity_non_vacuous_and_tight
#print axioms unified_all_tables_claims_128_byte_conformity_non_vacuous_and_tight
#print axioms unified_all_tables_certificate_lifting_non_vacuous_and_tight
#print axioms grand_unified_all_tables_thirty_six_budget_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedUnifiedAllTablesThirtySixBudgetSynth
