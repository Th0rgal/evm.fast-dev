import InitECandidate.Solver.GuestFiveAddrTablesMergeBound
import InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts
import InitECandidate.Solver.SelfContainedMergeTxAndJointAbsorptionSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth` — Wave 5 Atomic Worker `W5_92`

Self-contained synthesis (`0` imports from `InitECandidate.Proofs.Bounded*`) unifying:
1. **`GuestFiveAddrTablesMergeBound` (`11/11` tight)**:
   - Sum-of-squares quadratic absorption of 5 address tables (`identity5`, `five_addr_tables_absorbed`,
     `five_le`, `five_tight` at `(50_000, 950_000, 0)`) and 12 address-table probes (`identity12`,
     `twelve_addr_tables_absorbed`, `twelve_sharp` at `(0, 650_000, 50_000)`),
   - Coupled absorption (`coupled_absorbed`: `42·(2DW + 12A²) ≤ S²`, `coupled_le`:
     `2DW + 12A² ≤ 95_238_095_238`, `coupled_addr_corner`), and invariance of the source clock
     `kPanMultiAddrMerge = 136_116_135_658 = kPanMerge` (`envelope_unchanged`).
2. **`PanToStackToLabUnconditionalNoStoreConsts` (`20/20` tight)**:
   - Unconditional `StackNoSt` preservation across `StackRawCall`, `StackAlloc`, `StackRemove`, and
     `StackNames` (`panToStackNames_bodies_StackNoSt_unconditional`),
   - Native `StackToLab.flattenHOL` emptiness on `.storeConsts` (`flatten_storeConsts_empty`),
     non-visitation of `.storeConsts` (`not_visits_of_StackNoSt`, `visits_storeConsts_tight`), and
     section-ID preservation (`panToLabSection_unconditional`).
3. **`SelfContainedMergeTxAndJointAbsorptionSynth` (`10/10` tight)**:
   - The 32-budget (`CleanToDirtyCoupledSixPassMaster.unified`, `absorbedPortfolio`) and 36-budget
     (`thirtySixMergePortfolio`) certified portfolios under Yukon (`900_719_925_474`),
   - Strict `yukonScore` monotonicity, `claim.json ≤ 128` byte conformity, and `InitE.Certificate`
     lifting (`0 sorryAx`, 10 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth

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

/-- Theorem 1 (`non_vacuous_and_tight`): Complete synthesis of `GuestFiveAddrTablesMergeBound`
for the 5-table (`five_addr_tables_absorbed`, `five_le`, `five_tight` at `(50_000, 950_000, 0)`)
and 12-table (`twelve_addr_tables_absorbed`, `twelve_sharp` at `(0, 650_000, 50_000)`) quadratic
absorptions into `S² = 4_000_000_000_000` (`100_000_000_000 = blockMerge`). -/
theorem five_and_twelve_addr_tables_quadratic_absorption_non_vacuous_and_tight
    (D A W K : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    40 * (2 * ((D + A) * (W + D + A)) + 5 * (A * A)) ≤ S * S ∧
    2 * ((D + A) * (W + D + A)) + 5 * (A * A) ≤ 100_000_000_000 ∧
    (20 * 50_000 + 26 * 0 + (950_000 + 50_000 + 0) = S ∧
      2 * ((50_000 + 0) * (950_000 + 50_000 + 0)) + 5 * (0 * 0) = 100_000_000_000) ∧
    40 * (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) ≤ S * S ∧
    2 * ((D + A) * (W + D + A)) + 12 * (A * A) ≤ blockMerge ∧
    (20 * 0 + 26 * 50_000 + (650_000 + 0 + 50_000) = S ∧
      2 * ((0 + 50_000) * (650_000 + 0 + 50_000)) + 12 * (50_000 * 50_000) = 100_000_000_000) ∧
    (blockMerge ≤ K ↔ 100_000_000_000 ≤ K) := by
  have h12 := twelve_addr_tables_absorbed D A W h
  have h12_le : 2 * ((D + A) * (W + D + A)) + 12 * (A * A) ≤ blockMerge := by
    unfold S at h12; unfold blockMerge; omega
  have hbm : blockMerge = 100_000_000_000 := rfl
  refine ⟨five_addr_tables_absorbed D A W h,
    five_le D A W h,
    five_tight,
    h12,
    h12_le,
    twelve_sharp,
    by rw [hbm]⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Coupled 12-address-table absorption
(`coupled_absorbed`: `42·(2DW + 12A²) ≤ S²`, `coupled_le`: `2DW + 12A² ≤ 95_238_095_238`,
`coupled_addr_corner` at `A = 76_923`), invariance `kPanMultiAddrMerge = kPanMerge = 136_116_135_658`,
and exact equality of the 4 multi-address merge target budgets with `fourMergeTiers`. -/
theorem coupled_five_addr_and_multi_addr_merge_clock_invariance_non_vacuous_and_tight
    (D A W D_u A_u W_u Tloc Tlin : Nat)
    (hc : 21 * D + 26 * A + W ≤ S)
    (hu : 20 * D_u + 26 * A_u + (W_u + D_u + A_u) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    42 * (2 * (D * W) + 12 * (A * A)) ≤ S * S ∧
    (2 * (D * W) + 12 * (A * A) ≤ 95_238_095_238 ∧
      2 * (47_619 * 1_000_001) + 12 * (0 * 0) = 95_238_095_238) ∧
    (21 * 0 + 26 * 76_923 + 0 ≤ S ∧
      2 * (0 * 0) + 12 * (76_923 * 76_923) = 71_005_775_148 ∧
      71_005_775_148 < 95_238_095_238) ∧
    (6 * kPanMultiAddrMerge < yukon ∧ kPanMultiAddrMerge = 136_116_135_658) ∧
    kPanMultiAddrMerge = kPanMerge ∧
    linear + Tloc + (2 * ((D_u + A_u) * (W_u + D_u + A_u)) + 12 * (A_u * A_u)) + Tlin ≤ kPanMerge ∧
    (bootstrapSteps - copyLoopSavedSteps) + 3 * kPanMultiAddrMerge = mergeSlope3UnrolledK ∧
    bootstrapSteps + 3 * kPanMultiAddrMerge = mergeSlope3K ∧
    (bootstrapSteps - copyLoopSavedSteps) + 6 * kPanMultiAddrMerge = mergeSlope6UnrolledK ∧
    bootstrapSteps + 6 * kPanMultiAddrMerge = mergeSlope6K := by
  have h12 := (five_and_twelve_addr_tables_quadratic_absorption_non_vacuous_and_tight D_u A_u W_u 0 hu).2.2.2.2.1
  have hmaster : linear + Tloc + (2 * ((D_u + A_u) * (W_u + D_u + A_u)) + 12 * (A_u * A_u)) + Tlin ≤ kPanMerge := by
    unfold kPanMerge; omega
  have heq : kPanMultiAddrMerge = kPanMerge := rfl
  refine ⟨coupled_absorbed D A W hc,
    coupled_le D A W hc,
    coupled_addr_corner,
    envelope_unchanged,
    rfl,
    hmaster,
    by rw [heq]; rfl,
    by rw [heq]; rfl,
    by rw [heq]; rfl,
    by rw [heq]; rfl⟩

/-- Theorem 3 (`non_vacuous_and_tight`): Unconditional `StackNoSt` preservation from `PanLang`
through `WordToWord.compile`, `WordToStack.compileNative`, `StackRawCall.compTop`,
`StackAlloc.progComp`, `StackRemove.comp`, and `StackNames.progCompHOL`
(`panToStackNames_bodies_StackNoSt_unconditional` and `stackRemove_storeConsts_not_skip`). -/
theorem unconditional_pan_to_stack_names_no_store_consts_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) ∧
    StackRemove.comp j bd ptr (.storeConsts 3 4 none : HolProg width) ≠ .skip ∧
    StackNoSt (.storeConsts 3 4 none : HolProg width) = false :=
  ⟨panToStackNames_bodies_StackNoSt_unconditional arch prog wc ac perf info j bd ptr f,
   stackRemove_storeConsts_not_skip j bd ptr,
   rfl⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Unconditional `StackToLab` section compilation
(`panToLabSection_unconditional`, `flatten_storeConsts_empty`, `not_visits_of_StackNoSt`,
`visits_storeConsts_tight`, `progToSection_sectionId`). -/
theorem unconditional_pan_to_lab_section_no_store_consts_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (tail : Bool) (s b : Nat) (stub : Option Nat) (sid next : Nat) (cs bs : List Nat) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
    StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
      (.list [], false, next) ∧
    FlattenVisitsSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = true :=
  ⟨panToLabSection_unconditional arch prog wc ac perf info j bd ptr f,
   flatten_storeConsts_empty tail s b stub sid next cs bs,
   visits_storeConsts_tight⟩

/-- Theorem 5 (`non_vacuous_and_tight`): Joint synthesis of the unconditional `PanToStackToLab`
chain with `WordToWord.fullCompileSingle` zero `storeConstsAllowance` drift across all 4
multi-address/storage-merge target tiers (`408_348_416_306`, `408_348_430_106`,
`816_696_823_280`, `816_696_837_080`). -/
theorem five_addr_merge_tiers_with_unconditional_lab_chain_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (c : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (b : Bool) (rc alg nm ac : Nat) (co : Option (Spt Nat))
    (ws : List (Bool × BitVec width)) :
    (∀ y ∈ (compileNative c perf (WordToWord.compile wc c
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false)) ∧
    NoSt (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true ∧
    storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 ∧
    ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanMultiAddrMerge) +
      storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
        ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 408_348_416_306 ∧
    (bootstrapSteps + 3 * kPanMultiAddrMerge) +
      storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
        ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 408_348_430_106 ∧
    ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanMultiAddrMerge) +
      storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
        ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 816_696_823_280 ∧
    (bootstrapSteps + 6 * kPanMultiAddrMerge) +
      storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
        ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 816_696_837_080 ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have hw := merge_tiers_with_pan_to_stack_and_word_no_store_consts_non_vacuous_and_tight
    arch prog wc c perf ctx q l b rc alg nm ac co ws
  have heq : kPanMultiAddrMerge = kPanMerge := rfl
  refine ⟨?_, hw.2.2.1, hw.2.2.2.1, ?_, ?_, ?_, ?_, hw.2.2.2.2.2.2.2.2⟩
  · intro y hy
    rcases panToStackNames_bodies_StackNoSt_unconditional arch prog wc c perf info j bd ptr f y hy
      with hstub | hnost
    · exact Or.inl hstub
    · exact Or.inr ⟨hnost, not_visits_of_StackNoSt _ hnost⟩
  · exact hw.2.2.2.2.1
  · exact hw.2.2.2.2.2.1
  · exact hw.2.2.2.2.2.2.1
  · exact hw.2.2.2.2.2.2.2.1

/-- Theorem 6 (`non_vacuous_and_tight`): Preservation of all 32-budget
(`CleanToDirtyCoupledSixPassMaster.unified`, `absorbedPortfolio`) and 36-budget
(`thirtySixMergePortfolio`) portfolio tiers under Yukon (`900_719_925_474`) with simultaneous
5/12-address-table absorption and transition-insertion absorption. -/
theorem thirty_two_and_thirty_six_portfolios_under_five_addr_absorption_non_vacuous_and_tight
    (D A W D_c A_c W_c D_t W_t R K : Nat)
    (h5 : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hc : 21 * D_c + 26 * A_c + W_c ≤ S)
    (ht : 21 * D_t + W_t + 20 * R ≤ S) :
    40 * (2 * ((D + A) * (W + D + A)) + 5 * (A * A)) ≤ S * S ∧
    40 * (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) ≤ S * S ∧
    2 * (D_c * W_c) + 12 * (A_c * A_c) ≤ 95_238_095_238 ∧
    42 * (D_t * (2 * W_t + 4 * R) + kIns * R) ≤ S * S ∧
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    absorbedPortfolio.length = 32 ∧
    thirtySixMergePortfolio.length = 36 ∧
    thirtySixMergePortfolio.Pairwise (· < ·) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      1_212_035_192 ≤ absorbBudget k ∧ absorbBudget k ≤ k ∧ k < 900_719_925_474) ∧
    (∀ k ∈ thirtySixMergePortfolio,
      1_212_035_192 ≤ k ∧ k ≤ 857_384_015_252 ∧ k < 900_719_925_474) ∧
    (mergeSlope6K ≤ K ↔ 816_696_837_080 ≤ K) := by
  have hj := joint_absorption_and_coupled_projection_non_vacuous_and_tight D_t W_t R K ht
  have h36 := thirty_six_merge_portfolio_exact_insertion_and_order_non_vacuous_and_tight K
  refine ⟨five_addr_tables_absorbed D A W h5,
    twelve_addr_tables_absorbed D A W h5,
    (coupled_le D_c A_c W_c hc).1,
    hj.1,
    by decide,
    hj.2.1,
    h36.1,
    h36.2.1,
    ?_,
    ?_,
    h36.2.2.2.2.2.2.2.2.2.2⟩
  · intro k hk
    have hab := hj.2.2.1 k hk
    have hk_in36 : k ∈ thirtySixMergePortfolio := h36.2.2.2.1 k hk
    have hk_lt := (h36.2.2.2.2.2.1 k hk_in36).2.2.1
    exact ⟨hab.1, hab.2, hk_lt⟩
  · intro k hk
    have hb := h36.2.2.2.2.2.1 k hk
    exact ⟨hb.1, hb.2.1, hb.2.2.1⟩

/-- Theorem 7 (`non_vacuous_and_tight`): Strict `yukonScore` monotonicity and IEEE-754 `float64`
exactness (`< 2^53 - 1`) across both the 32-budget (`CleanToDirtyCoupledSixPassMaster.unified`)
and 36-budget (`thirtySixMergePortfolio`) portfolios. -/
theorem thirty_two_and_thirty_six_yukon_score_monotonicity_non_vacuous_and_tight
    (minutes K : Nat) :
    (CleanToDirtyCoupledSixPassMaster.unified.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (thirtySixMergePortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ k1 ∈ thirtySixMergePortfolio,
      ∀ k2 ∈ thirtySixMergePortfolio,
        k1 < k2 ↔ yukonScore k1 minutes < yukonScore k2 minutes) ∧
    (∀ k ∈ thirtySixMergePortfolio,
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes ≤ yukonScore 857_384_015_252 minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    yukonScore transition3K minutes < yukonScore mergeSlope3UnrolledK minutes ∧
    yukonScore mergeSlope3UnrolledK minutes < yukonScore mergeSlope3K minutes ∧
    yukonScore transition6K minutes < yukonScore mergeSlope6UnrolledK minutes ∧
    yukonScore mergeSlope6UnrolledK minutes < yukonScore mergeSlope6K minutes ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hord32 : CleanToDirtyCoupledSixPassMaster.unified.Pairwise (· < ·) := by decide
  have hmap32 : (CleanToDirtyCoupledSixPassMaster.unified.map (fun k => yukonScore k minutes)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp (fun {a b} hab => score_monotone_non_vacuous_and_tight a b minutes hab) hord32
  have hsc36 := thirty_six_merge_yukon_score_strict_monotonicity_and_float64_non_vacuous_and_tight minutes K
  exact ⟨hmap32, hsc36.1, hsc36.2.1, hsc36.2.2.1,
    hsc36.2.2.2.1, hsc36.2.2.2.2.1,
    hsc36.2.2.2.2.2.2.1, hsc36.2.2.2.2.2.2.2.1,
    hsc36.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 8 (`non_vacuous_and_tight`): `claim.json ≤ 128` byte conformity across all 32 claims
of `thirtyTwoUnifiedClaims` and all 36 claims of `thirtySixMergeClaims`. -/
theorem thirty_two_and_thirty_six_claims_128_byte_conformity_non_vacuous_and_tight (K : Nat) :
    thirtyTwoUnifiedClaims.length = 32 ∧
    thirtySixMergeClaims.length = 36 ∧
    (∀ entry ∈ thirtyTwoUnifiedClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (∀ entry ∈ thirtySixMergeClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    validFiniteClaim ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanMultiAddrMerge)
      (verifierClaimJson "408348416306") = true ∧
    validFiniteClaim (bootstrapSteps + 3 * kPanMultiAddrMerge)
      (verifierClaimJson "408348430106") = true ∧
    validFiniteClaim ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanMultiAddrMerge)
      (verifierClaimJson "816696823280") = true ∧
    validFiniteClaim (bootstrapSteps + 6 * kPanMultiAddrMerge)
      (verifierClaimJson "816696837080") = true ∧
    (validFiniteClaim K (verifierClaimJson "816696837080") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) := by
  have hcl36 := thirty_six_merge_claims_valid_and_within_128_bytes_non_vacuous_and_tight K
  refine ⟨by decide, hcl36.1, by decide, hcl36.2.2.1,
    hcl36.2.2.2.2.1,
    hcl36.2.2.2.2.2.2.1,
    hcl36.2.2.2.2.2.2.2.2.1,
    hcl36.2.2.2.2.2.2.2.2.2.2.1,
    hcl36.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Theorem 9 (`non_vacuous_and_tight`): `InitE.Certificate` lifting across all 32 budgets of
`CleanToDirtyCoupledSixPassMaster.unified`, all 32 absorbed budgets of `absorbedPortfolio`,
all 36 budgets of `thirtySixMergePortfolio`, and all 38 budgets of `allThirtyEightMergeBudgets`. -/
theorem thirty_two_and_thirty_six_certificate_lifting_non_vacuous_and_tight
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
    CertificateAt ((bootstrapSteps - copyLoopSavedSteps) + 3 * kPanMultiAddrMerge) ∧
    CertificateAt (bootstrapSteps + 3 * kPanMultiAddrMerge) ∧
    CertificateAt ((bootstrapSteps - copyLoopSavedSteps) + 6 * kPanMultiAddrMerge) ∧
    CertificateAt (bootstrapSteps + 6 * kPanMultiAddrMerge) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (absorbBudget k)) (.finite (absorbBudget k))) ∧
    (∀ k ∈ thirtySixMergePortfolio,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ allThirtyEightMergeBudgets,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    ¬ (bootstrapSteps + 6 * kPanMultiAddrMerge ≤ mergeSlope6K - 1) := by
  have hm := merge_and_thirty_six_portfolio_certificates_non_vacuous_and_tight
    oracles c depth hlab compiled depthBound not_timeOut_merge6 hc_best
  have h36 := thirty_six_merge_portfolio_exact_insertion_and_order_non_vacuous_and_tight 0
  have hcert32 : ∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
    intro k hk
    exact hm.2.2.2.2.1 k (h36.2.2.2.1 k hk)
  refine ⟨hm.1,
    hm.2.1,
    hm.2.2.1,
    hm.2.2.2.1,
    hcert32,
    hm.2.2.2.2.2.2.1,
    hm.2.2.2.2.1,
    hm.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2⟩

/-- Theorem 10 (`non_vacuous_and_tight`): Grand Wave 5 `W5_92` Master Synthesis Theorem uniting:
1. `GuestFiveAddrTablesMergeBound` (`five_addr_tables_absorbed`, `twelve_addr_tables_absorbed` at
   `(50_000, 950_000, 0)` and `(0, 650_000, 50_000)`, `coupled_absorbed`:
   `2*D_c*W_c + 12*A_c^2 ≤ 95_238_095_238`, `kPanMultiAddrMerge = 136_116_135_658`),
2. `PanToStackToLabUnconditionalNoStoreConsts` (`panToStackNames_bodies_StackNoSt_unconditional`,
   `flatten_storeConsts_empty`, `panToLabSection_unconditional`),
3. `SelfContainedMergeTxAndJointAbsorptionSynth` (32-budget and 36-budget portfolios under Yukon
   `900_719_925_474`, `yukonScore` monotonicity, `claim.json ≤ 128` byte conformity, and
   `InitE.Certificate` lifting with `0` imports from `Proofs/Bounded*`). -/
theorem grand_five_addr_and_unconditional_no_store_consts_master_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (asmConf : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (tail : Bool) (s_st b_st : Nat) (stub : Option Nat) (sid next : Nat) (cs bs : List Nat)
    (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (b d : Bool) (rc alg nm ac k_sn n D W R D_u A_u W_u D_c A_c W_c Tloc Tlin : Nat)
    (co : Option (Spt Nat))
    (hDWR : 21 * D + W + 20 * R ≤ S)
    (h5 : 20 * D_u + 26 * A_u + (W_u + D_u + A_u) ≤ S)
    (hc : 21 * D_c + 26 * A_c + W_c ≤ S)
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
    40 * (2 * ((D_u + A_u) * (W_u + D_u + A_u)) + 5 * (A_u * A_u)) ≤ S * S ∧
    40 * (2 * ((D_u + A_u) * (W_u + D_u + A_u)) + 12 * (A_u * A_u)) ≤ S * S ∧
    2 * (D_c * W_c) + 12 * (A_c * A_c) ≤ 95_238_095_238 ∧
    linear + Tloc + (2 * ((D_u + A_u) * (W_u + D_u + A_u)) + 12 * (A_u * A_u)) + Tlin ≤ kPanMerge ∧
    42 * (D * (2 * W + 4 * R) + kIns * R) ≤ S * S ∧
    (∀ y ∈ (compileNative asmConf perf (WordToWord.compile wc asmConf
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
    StackToLab.flattenHOL tail (.storeConsts s_st b_st stub : HolProg width) sid next cs bs =
      (.list [], false, next) ∧
    NoSt (WordToWord.fullCompileSingle b rc alg asmConf
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true ∧
    stackRemoveClockWithAllowance k_sn (WordToWord.fullCompileSingle b rc alg asmConf
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = k_sn + 1 ∧
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    absorbedPortfolio.length = 32 ∧
    thirtySixMergePortfolio.length = 36 ∧
    thirtySixMergePortfolio.Pairwise (· < ·) ∧
    (∀ k ∈ thirtySixMergePortfolio,
      1_212_035_192 ≤ k ∧ k < 900_719_925_474 ∧
      InitE.Certificate (baselineWithFiniteK k) (.finite k) ∧
      yukonScore 1_212_035_192 minutes ≤ yukonScore k minutes ∧
      yukonScore k minutes < 2 ^ 53 - 1) ∧
    (thirtySixMergePortfolio.map (fun k => yukonScore k minutes)).Pairwise (· < ·) ∧
    (∀ entry ∈ thirtySixMergeClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      InitE.Certificate (baselineWithFiniteK (absorbBudget k)) (.finite (absorbBudget k))) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    zeroBoundedImportCount = 0 ∧
    ¬ (mergeSlope6K ≤ mergeSlope6K - 1) := by
  have hw84 := grand_merge_tx_joint_absorption_and_thirty_six_portfolio_master_non_vacuous_and_tight
    arch prog wc asmConf perf ctx q l b d rc alg nm ac k_sn n D W R 0 0 Tloc Tlin co
    hDWR (by unfold S; omega) hloc hlin oracles c depth minutes hlab compiled depthBound not_timeOut_best
  have hinv := coupled_five_addr_and_multi_addr_merge_clock_invariance_non_vacuous_and_tight
    D_c A_c W_c D_u A_u W_u Tloc Tlin hc h5 hloc hlin
  refine ⟨five_addr_tables_absorbed D_u A_u W_u h5,
    twelve_addr_tables_absorbed D_u A_u W_u h5,
    hinv.2.1.1,
    hinv.2.2.2.2.2.1,
    hw84.2.2.2.1,
    ?_,
    flatten_storeConsts_empty tail s_st b_st stub sid next cs bs,
    hw84.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hw84.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  intro y hy
  rcases panToStackNames_bodies_StackNoSt_unconditional arch prog wc asmConf perf info j bd ptr f y hy
    with hstub | hnost
  · exact Or.inl hstub
  · exact Or.inr ⟨hnost, not_visits_of_StackNoSt _ hnost, rfl⟩

#print axioms five_and_twelve_addr_tables_quadratic_absorption_non_vacuous_and_tight
#print axioms coupled_five_addr_and_multi_addr_merge_clock_invariance_non_vacuous_and_tight
#print axioms unconditional_pan_to_stack_names_no_store_consts_non_vacuous_and_tight
#print axioms unconditional_pan_to_lab_section_no_store_consts_non_vacuous_and_tight
#print axioms five_addr_merge_tiers_with_unconditional_lab_chain_non_vacuous_and_tight
#print axioms thirty_two_and_thirty_six_portfolios_under_five_addr_absorption_non_vacuous_and_tight
#print axioms thirty_two_and_thirty_six_yukon_score_monotonicity_non_vacuous_and_tight
#print axioms thirty_two_and_thirty_six_claims_128_byte_conformity_non_vacuous_and_tight
#print axioms thirty_two_and_thirty_six_certificate_lifting_non_vacuous_and_tight
#print axioms grand_five_addr_and_unconditional_no_store_consts_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth
