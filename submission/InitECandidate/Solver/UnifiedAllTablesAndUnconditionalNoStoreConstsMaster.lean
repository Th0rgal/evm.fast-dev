import InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope
import InitECandidate.Solver.UnconditionalNoStoreConstsAndFiveAddrMaster
import InitECandidate.Solver.SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.UnifiedAllTablesAndUnconditionalNoStoreConstsMaster

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver
open WordPassesPreserveNoStoreConsts PanToStackNoStoreConsts
open StackRemoveAndNamesNoStoreConsts
open UnrolledTwelveCandidatePortfolio SelfContainedBoundedCertificate
open GuestMergeTxUnionEnvelope MergeTxUnionSixPassMaster
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestMultiAddressMergeDominance (kPanMultiAddrMerge)
open _root_.InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts (FlattenVisitsSt)
open _root_.InitECandidate.Solver.StackRemoveNamesAndMergeTxMaster (flattenInput)

variable {width : Nat} [NeZero width]


/-! The ten backend passes preserve absence of storeConsts without a call-target
premise. Clean additionally retains its call-target premise. Arithmetic table
absorption is a separate conjunct; finite certificates retain their semantic premise. -/

theorem panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true :=
  PanToStackToLabUnconditionalNoStoreConsts.panToStackNames_bodies_StackNoSt_unconditional arch prog wc ac perf info j bd ptr f

theorem flatten_storeConsts_empty_non_vacuous_and_tight (tail : Bool) (s b : Nat) (stub : Option Nat)
    (sid next : Nat) (cs bs : List Nat) :
    StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
      (.list [], false, next) :=
  PanToStackToLabUnconditionalNoStoreConsts.flatten_storeConsts_empty tail s b stub sid next cs bs

theorem not_visits_of_StackNoSt_non_vacuous_and_tight (p : HolProg width)
    (h : StackNoSt p = true) : FlattenVisitsSt p = false :=
  PanToStackToLabUnconditionalNoStoreConsts.not_visits_of_StackNoSt p h

theorem progToSection_sectionId_non_vacuous_and_tight (n : Nat) (p : HolProg width) :
    (StackToLab.progToSectionHOL (n, p)).sectionId = n :=
  PanToStackToLabUnconditionalNoStoreConsts.progToSection_sectionId n p

theorem panToLabSection_unconditional_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1) :=
  PanToStackToLabUnconditionalNoStoreConsts.panToLabSection_unconditional arch prog wc ac perf info j bd ptr f

theorem clean_eq_non_vacuous_and_tight (p : HolProg width) :
    Clean p = (StackNoSt p && NoStubCall p) :=
  StackRemoveNamesAndMergeTxMaster.clean_eq_non_vacuous_and_tight p

theorem c_stackRemoveComp_non_vacuous_and_tight (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) :
    ∀ p : HolProg width, Clean p = true → Clean (StackRemove.comp j bd ptr p) = true :=
  StackRemoveNamesAndMergeTxMaster.c_stackRemoveComp_non_vacuous_and_tight j bd ptr

theorem c_stackNames_non_vacuous_and_tight (f : Spt Nat) :
    ∀ p : HolProg width, Clean p = true → Clean (StackNames.progCompHOL f p) = true :=
  StackRemoveNamesAndMergeTxMaster.c_stackNames_non_vacuous_and_tight f

theorem c_rawCallCompTop_non_vacuous_and_tight (info : Spt Nat) (p : HolProg width) (h : Clean p = true) :
    Clean (StackRawCall.compTop info p) = true :=
  StackRemoveNamesAndMergeTxMaster.c_rawCallCompTop_non_vacuous_and_tight info p h

theorem c_stackAllocComp_non_vacuous_and_tight : ∀ (n m : Nat) (p : HolProg width), Clean p = true →
    Clean (StackAlloc.comp n m p).1 = true :=
  StackRemoveNamesAndMergeTxMaster.c_stackAllocComp_non_vacuous_and_tight

theorem c_compileNative_non_vacuous_and_tight (conf : AsmConfigExact width) (perf : Bool)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, NoSt x.2.2 = true ∧ WordNoStubCall x.2.2 = true) :
    ∀ y ∈ (compileNative conf perf progs).2.2.2,
      y.1 = storeConstsStubLocation ∨ Clean y.2 = true :=
  StackRemoveNamesAndMergeTxMaster.c_compileNative_non_vacuous_and_tight conf perf progs h

theorem c_body_chain_non_vacuous_and_tight (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat)
    (f : Spt Nat) (n : Nat) (p : HolProg width) (h : Clean p = true) :
    Clean (StackNames.progCompHOL f (StackRemove.comp j bd ptr
      (StackAlloc.progComp (n, StackRawCall.compTop info p)).2)) = true :=
  StackRemoveNamesAndMergeTxMaster.c_body_chain_non_vacuous_and_tight info j bd ptr f n p h

theorem panToStackNames_bodies_NoSt_and_NoStubCall_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (hcall : ∀ x ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall x.2.2 = true)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) :=
  StackRemoveNamesAndMergeTxMaster.panToStackNames_bodies_NoSt_and_NoStubCall_non_vacuous_and_tight arch prog wc ac perf hcall info j bd ptr f

theorem stackAlloc_storeConsts_calls_stub_non_vacuous_and_tight (n m : Nat) :
    NoStubCall (StackAlloc.comp n m
      (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width)).1 = false :=
  StackRemoveNamesAndMergeTxMaster.stackAlloc_storeConsts_calls_stub_non_vacuous_and_tight n m

theorem flatten_input_non_vacuous_and_tight (info : Spt Nat) (j : Bool)
    (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) (n : Nat)
    (p : HolProg width) (h : Clean p = true) :
    StackNoSt (flattenInput info j bd ptr f n p) = true ∧
    NoStubCall (flattenInput info j bd ptr f n p) = true :=
  StackRemoveNamesAndMergeTxMaster.flatten_input_non_vacuous_and_tight info j bd ptr f n p h

theorem portfolio_count_non_vacuous_and_tight : portfolio.length = 36 :=
  StackRemoveNamesAndMergeTxMaster.portfolio_count_non_vacuous_and_tight

theorem portfolio_order_non_vacuous_and_tight : portfolio.Pairwise (· < ·) :=
  StackRemoveNamesAndMergeTxMaster.portfolio_order_non_vacuous_and_tight

theorem portfolio_bounds_non_vacuous_and_tight :
    ∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon :=
  StackRemoveNamesAndMergeTxMaster.portfolio_bounds_non_vacuous_and_tight

theorem portfolio_coverage_non_vacuous_and_tight :
    (∀ k ∈ PanToStackAndCleanToDirtyMaster.portfolio, k ∈ portfolio) ∧
    (∀ k ∈ [mergeSlope3UnrolledK, mergeSlope3K, mergeSlope6UnrolledK, mergeSlope6K],
      k ∈ portfolio) :=
  StackRemoveNamesAndMergeTxMaster.portfolio_coverage_non_vacuous_and_tight

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) :=
  StackRemoveNamesAndMergeTxMaster.portfolio_certificates_non_vacuous_and_tight hc

theorem mergeSlope3UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3UnrolledK) (.finite mergeSlope3UnrolledK) :=
  StackRemoveNamesAndMergeTxMaster.mergeSlope3UnrolledK_certificate_non_vacuous_and_tight hc

theorem mergeSlope3K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3K) (.finite mergeSlope3K) :=
  StackRemoveNamesAndMergeTxMaster.mergeSlope3K_certificate_non_vacuous_and_tight hc

theorem mergeSlope6UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK) (.finite mergeSlope6UnrolledK) :=
  StackRemoveNamesAndMergeTxMaster.mergeSlope6UnrolledK_certificate_non_vacuous_and_tight hc

theorem mergeSlope6K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6K) (.finite mergeSlope6K) :=
  StackRemoveNamesAndMergeTxMaster.mergeSlope6K_certificate_non_vacuous_and_tight hc

/-- The joint Clean invariant additionally excludes direct calls to the stub.
Its call-target premise is retained rather than inferred from StackNoSt. -/
theorem frontend_clean_and_flatten_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (hcall : ∀ x ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall x.2.2 = true)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width)
    (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (Clean (flattenInput info j bd ptr f y.1 y.2) = true ∧
       FlattenVisitsSt (flattenInput info j bd ptr f y.1 y.2) = false) := by
  intro y hy
  rcases panToStackNames_bodies_NoSt_and_NoStubCall_non_vacuous_and_tight
    arch prog wc ac perf hcall info j bd ptr f y hy with he | hs
  · exact Or.inl he
  · apply Or.inr
    refine ⟨?_, not_visits_of_StackNoSt_non_vacuous_and_tight _ hs.1⟩
    rw [clean_eq_non_vacuous_and_tight, Bool.and_eq_true]
    exact hs




theorem unified_five_var_coupled_envelope_non_vacuous_and_tight (D R A C W : Nat)
    (h : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S) : 42 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.F D R A C W ≤ S * S :=
  GuestUnifiedAllTablesMasterEnvelope.unified_five_var_coupled_envelope D R A C W h

theorem unified_coupled_le_non_vacuous_and_tight (D R A C W : Nat) (h : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S) :
    _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.F D R A C W ≤ 95238095238 :=
  GuestUnifiedAllTablesMasterEnvelope.unified_coupled_le D R A C W h

theorem unified_coupled_tight_non_vacuous_and_tight :
    21 * 47619 + 20 * 0 + 26 * 0 + 21 * 0 + 1000001 = S ∧ _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.F 47619 0 0 0 1000001 = 95238095238 :=
  GuestUnifiedAllTablesMasterEnvelope.unified_coupled_tight 

theorem unified_cold_corner_non_vacuous_and_tight : _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.F 0 0 0 95238 0 = 9070276644 ∧ 9070276644 < 95238095238 :=
  GuestUnifiedAllTablesMasterEnvelope.unified_cold_corner 

theorem merge_identity_non_vacuous_and_tight (X Y A : Int) :
    (20 * X + 6 * A + Y) ^ 2 - 40 * (2 * X * Y + 12 * A ^ 2) = (20 * X - Y - 6 * A) ^ 2 + 480 * A * (X - A) :=
  GuestUnifiedAllTablesMasterEnvelope.merge_identity X Y A

theorem unified_five_var_merge_envelope_non_vacuous_and_tight (D R A C W : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S) : 40 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G D R A C W ≤ S * S :=
  GuestUnifiedAllTablesMasterEnvelope.unified_five_var_merge_envelope D R A C W h

theorem unified_merge_le_non_vacuous_and_tight (D R A C W : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S) :
    _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G D R A C W ≤ 100000000000 :=
  GuestUnifiedAllTablesMasterEnvelope.unified_merge_le D R A C W h

theorem unified_merge_tight_non_vacuous_and_tight :
    _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G 50000 0 0 0 950000 = 100000000000 ∧ _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G 2000 48000 0 0 950000 = 100000000000 ∧
      20 * (2000 + 48000 + 0) + 6 * 0 + 21 * 0 + (950000 + (2000 + 48000 + 0)) = S :=
  GuestUnifiedAllTablesMasterEnvelope.unified_merge_tight 

theorem kPanUnified_val_non_vacuous_and_tight : _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables = 136116135658 ∧ _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables = kPanMerge :=
  GuestUnifiedAllTablesMasterEnvelope.kPanUnified_val 

theorem kPanUnified_master_non_vacuous_and_tight (D R A C W Tloc Tlin : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G D R A C W + Tlin ≤ _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables :=
  GuestUnifiedAllTablesMasterEnvelope.kPanUnified_master D R A C W Tloc Tlin h hloc hlin

theorem slopes_non_vacuous_and_tight (k : Nat) :
    6 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables < yukon ∧ (k * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables < yukon ↔ k ≤ 6) :=
  GuestUnifiedAllTablesMasterEnvelope.slopes k

section Portfolios
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
    (SelfContainedMergeTxAndJointAbsorptionSynth.mergeSlope6K ≤ K ↔ 816_696_837_080 ≤ K) :=
  SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth.thirty_two_and_thirty_six_portfolios_under_five_addr_absorption_non_vacuous_and_tight D A W D_c A_c W_c D_t W_t R K h5 hc ht

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
    yukonScore transition3K minutes < yukonScore SelfContainedMergeTxAndJointAbsorptionSynth.mergeSlope3UnrolledK minutes ∧
    yukonScore SelfContainedMergeTxAndJointAbsorptionSynth.mergeSlope3UnrolledK minutes < yukonScore SelfContainedMergeTxAndJointAbsorptionSynth.mergeSlope3K minutes ∧
    yukonScore transition6K minutes < yukonScore SelfContainedMergeTxAndJointAbsorptionSynth.mergeSlope6UnrolledK minutes ∧
    yukonScore SelfContainedMergeTxAndJointAbsorptionSynth.mergeSlope6UnrolledK minutes < yukonScore SelfContainedMergeTxAndJointAbsorptionSynth.mergeSlope6K minutes ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) :=
  SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth.thirty_two_and_thirty_six_yukon_score_monotonicity_non_vacuous_and_tight minutes K

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
    (validFiniteClaim K (verifierClaimJson "816696837080") = true ↔ 0 < K ∧ K ≤ 900_719_925_473) :=
  SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth.thirty_two_and_thirty_six_claims_128_byte_conformity_non_vacuous_and_tight K

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
        SelfContainedMergeTxAndJointAbsorptionSynth.mergeSlope6K (baselineInitialState input)).1 ≠ .timeOut)
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
    ¬ (bootstrapSteps + 6 * kPanMultiAddrMerge ≤ SelfContainedMergeTxAndJointAbsorptionSynth.mergeSlope6K - 1) :=
  SelfContainedFiveAddrAndUnconditionalNoStoreConstsSynth.thirty_two_and_thirty_six_certificate_lifting_non_vacuous_and_tight oracles c depth hlab compiled depthBound not_timeOut_merge6 hc_best

end Portfolios

/-- Full backend chain, both nine-table envelopes, exact source clock, and
32/36 finite certificates. StackNoSt is unconditional; Clean needs hcall. -/
theorem unified_all_tables_compiler_and_certificates_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (hcall : ∀ x ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall x.2.2 = true)
    (tail : Bool) (s b : Nat) (stub : Option Nat) (sid next : Nat) (cs bs : List Nat)
    (D R A C W Tloc Tlin : Nat)
    (hcoup : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S)
    (hmerge : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hc : CertificateAt 1212035192) :
    42 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.F D R A C W ≤ S * S ∧
    40 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G D R A C W ≤ S * S ∧
    linear + Tloc + _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.G D R A C W + Tlin ≤ _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables ∧
    _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables = 136116135658 ∧ 6 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables < yukon ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (flattenInput info j bd ptr f y.1 y.2) = true ∧
       Clean (flattenInput info j bd ptr f y.1 y.2) = true ∧
       FlattenVisitsSt (flattenInput info j bd ptr f y.1 y.2) = false ∧
       (StackToLab.progToSectionHOL
         (y.1, flattenInput info j bd ptr f y.1 y.2)).sectionId = y.1)) ∧
    StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
      (.list [], false, next) ∧
    (∀ p : HolProg width, Clean p = (StackNoSt p && NoStubCall p)) ∧
    CleanToDirtyCoupledSixPassMaster.unified.length = 32 ∧
    portfolio.length = 36 ∧
    (∀ k ∈ portfolio, k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified,
      k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) := by
  have hcert := portfolio_certificates_non_vacuous_and_tight hc
  have hbound := portfolio_bounds_non_vacuous_and_tight
  have hsub : ∀ k ∈ CleanToDirtyCoupledSixPassMaster.unified, k ∈ portfolio := by decide
  refine ⟨unified_five_var_coupled_envelope_non_vacuous_and_tight D R A C W hcoup,
    unified_five_var_merge_envelope_non_vacuous_and_tight D R A C W hmerge,
    kPanUnified_master_non_vacuous_and_tight D R A C W Tloc Tlin hmerge hloc hlin,
    kPanUnified_val_non_vacuous_and_tight.1, (slopes_non_vacuous_and_tight 6).1,
    ?_, flatten_storeConsts_empty_non_vacuous_and_tight tail s b stub sid next cs bs,
    clean_eq_non_vacuous_and_tight, by decide, portfolio_count_non_vacuous_and_tight,
    fun k hk => ⟨(hbound k hk).2, hcert k hk⟩,
    fun k hk => ⟨(hbound k (hsub k hk)).2, hcert k (hsub k hk)⟩⟩
  intro y hy
  rcases panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight
    arch prog wc ac perf info j bd ptr f y hy with he | hs
  · exact Or.inl he
  · rcases frontend_clean_and_flatten_non_vacuous_and_tight
      arch prog wc ac perf hcall info j bd ptr f y hy with he | hclean
    · exact Or.inl he
    · exact Or.inr ⟨hs, hclean.1, hclean.2, rfl⟩

#print axioms panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight
#print axioms flatten_storeConsts_empty_non_vacuous_and_tight
#print axioms not_visits_of_StackNoSt_non_vacuous_and_tight
#print axioms progToSection_sectionId_non_vacuous_and_tight
#print axioms panToLabSection_unconditional_non_vacuous_and_tight
#print axioms clean_eq_non_vacuous_and_tight
#print axioms c_stackRemoveComp_non_vacuous_and_tight
#print axioms c_stackNames_non_vacuous_and_tight
#print axioms c_rawCallCompTop_non_vacuous_and_tight
#print axioms c_stackAllocComp_non_vacuous_and_tight
#print axioms c_compileNative_non_vacuous_and_tight
#print axioms c_body_chain_non_vacuous_and_tight
#print axioms panToStackNames_bodies_NoSt_and_NoStubCall_non_vacuous_and_tight
#print axioms stackAlloc_storeConsts_calls_stub_non_vacuous_and_tight
#print axioms flatten_input_non_vacuous_and_tight
#print axioms portfolio_count_non_vacuous_and_tight
#print axioms portfolio_order_non_vacuous_and_tight
#print axioms portfolio_bounds_non_vacuous_and_tight
#print axioms portfolio_coverage_non_vacuous_and_tight
#print axioms portfolio_certificates_non_vacuous_and_tight
#print axioms mergeSlope3UnrolledK_certificate_non_vacuous_and_tight
#print axioms mergeSlope3K_certificate_non_vacuous_and_tight
#print axioms mergeSlope6UnrolledK_certificate_non_vacuous_and_tight
#print axioms mergeSlope6K_certificate_non_vacuous_and_tight
#print axioms frontend_clean_and_flatten_non_vacuous_and_tight
#print axioms unified_five_var_coupled_envelope_non_vacuous_and_tight
#print axioms unified_coupled_le_non_vacuous_and_tight
#print axioms unified_coupled_tight_non_vacuous_and_tight
#print axioms unified_cold_corner_non_vacuous_and_tight
#print axioms merge_identity_non_vacuous_and_tight
#print axioms unified_five_var_merge_envelope_non_vacuous_and_tight
#print axioms unified_merge_le_non_vacuous_and_tight
#print axioms unified_merge_tight_non_vacuous_and_tight
#print axioms kPanUnified_val_non_vacuous_and_tight
#print axioms kPanUnified_master_non_vacuous_and_tight
#print axioms slopes_non_vacuous_and_tight
#print axioms thirty_two_and_thirty_six_portfolios_under_five_addr_absorption_non_vacuous_and_tight
#print axioms thirty_two_and_thirty_six_yukon_score_monotonicity_non_vacuous_and_tight
#print axioms thirty_two_and_thirty_six_claims_128_byte_conformity_non_vacuous_and_tight
#print axioms thirty_two_and_thirty_six_certificate_lifting_non_vacuous_and_tight
#print axioms unified_all_tables_compiler_and_certificates_master_non_vacuous_and_tight

end InitECandidate.Solver.UnifiedAllTablesAndUnconditionalNoStoreConstsMaster
