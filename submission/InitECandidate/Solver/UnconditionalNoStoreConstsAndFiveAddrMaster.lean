import InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts
import InitECandidate.Solver.StackRemoveNamesAndMergeTxMaster
import InitECandidate.Solver.GuestFiveAddrTablesMergeBound

set_option autoImplicit false

namespace InitECandidate.Solver.UnconditionalNoStoreConstsAndFiveAddrMaster

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

/-!
Integration of the ten backend stages: PanToCrep, CrepToLoop, LoopToWord,
WordToWord, WordToStack, StackRawCall, StackAlloc, StackRemove, StackNames,
and StackToLab. The distinguished stub is an explicit exception.
StackNoSt needs no call-target premise; Clean additionally needs hcall.
The arithmetic bounds and syntactic invariants are independent conjuncts.
All 36 finite certificates retain their baseline semantic certificate premise.
-/

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

theorem source_master_non_vacuous_and_tight (D W Tloc Tlin : Nat)
    (h : 20 * D + (W + D) ≤ S) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + 2 * (D * (W + D)) + Tlin ≤ kPanMerge :=
  StackRemoveNamesAndMergeTxMaster.source_master_non_vacuous_and_tight D W Tloc Tlin h hloc hlin

theorem joint_absorption_non_vacuous_and_tight (D W R : Nat)
    (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤ S * S :=
  StackRemoveNamesAndMergeTxMaster.joint_absorption_non_vacuous_and_tight D W R h

theorem merge_target_threshold_non_vacuous_and_tight (k : Nat) :
    MergeTxAndJointAbsorptionMaster.mergeTarget k < yukon ↔ k ≤ 6 :=
  StackRemoveNamesAndMergeTxMaster.merge_target_threshold_non_vacuous_and_tight k

theorem identity5_non_vacuous_and_tight (D A W : Int) :
    2000000 ^ 2 - 40 * (2 * (D + A) * (W + D + A) + 5 * A ^ 2) =
      (2000000 - 40 * (D + A)) ^ 2 + 80 * (D + A) * (2000000 - 21 * D - 27 * A - W)
        + 480 * D * A + 280 * A ^ 2 :=
  GuestFiveAddrTablesMergeBound.identity5 D A W

theorem five_addr_tables_absorbed_non_vacuous_and_tight (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    40 * (2 * ((D + A) * (W + D + A)) + 5 * (A * A)) ≤ S * S :=
  GuestFiveAddrTablesMergeBound.five_addr_tables_absorbed D A W h

theorem five_le_non_vacuous_and_tight (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    2 * ((D + A) * (W + D + A)) + 5 * (A * A) ≤ 100000000000 :=
  GuestFiveAddrTablesMergeBound.five_le D A W h

theorem five_tight_non_vacuous_and_tight :
    20 * 50000 + 26 * 0 + (950000 + 50000 + 0) = S ∧
      2 * ((50000 + 0) * (950000 + 50000 + 0)) + 5 * (0 * 0) = 100000000000 :=
  GuestFiveAddrTablesMergeBound.five_tight

theorem identity12_non_vacuous_and_tight (D A W : Int) :
    2000000 ^ 2 - 40 * (2 * (D + A) * (W + D + A) + 12 * A ^ 2) =
      (2000000 - 40 * (D + A)) ^ 2 + 80 * (D + A) * (2000000 - 21 * D - 27 * A - W)
        + 480 * D * A :=
  GuestFiveAddrTablesMergeBound.identity12 D A W

theorem twelve_addr_tables_absorbed_non_vacuous_and_tight (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    40 * (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) ≤ S * S :=
  GuestFiveAddrTablesMergeBound.twelve_addr_tables_absorbed D A W h

theorem twelve_sharp_non_vacuous_and_tight :
    20 * 0 + 26 * 50000 + (650000 + 0 + 50000) = S ∧
      2 * ((0 + 50000) * (650000 + 0 + 50000)) + 12 * (50000 * 50000) = 100000000000 :=
  GuestFiveAddrTablesMergeBound.twelve_sharp

theorem coupled_absorbed_non_vacuous_and_tight (D A W : Nat) (h : 21 * D + 26 * A + W ≤ S) :
    42 * (2 * (D * W) + 12 * (A * A)) ≤ S * S :=
  GuestFiveAddrTablesMergeBound.coupled_absorbed D A W h

theorem coupled_le_non_vacuous_and_tight (D A W : Nat) (h : 21 * D + 26 * A + W ≤ S) :
    2 * (D * W) + 12 * (A * A) ≤ 95238095238 ∧
      2 * (47619 * 1000001) + 12 * (0 * 0) = 95238095238 :=
  GuestFiveAddrTablesMergeBound.coupled_le D A W h

theorem coupled_addr_corner_non_vacuous_and_tight :
    21 * 0 + 26 * 76923 + 0 ≤ S ∧ 2 * (0 * 0) + 12 * (76923 * 76923) = 71005775148 ∧
      71005775148 < 95238095238 :=
  GuestFiveAddrTablesMergeBound.coupled_addr_corner

theorem envelope_unchanged_non_vacuous_and_tight : 6 * kPanMultiAddrMerge < yukon ∧ kPanMultiAddrMerge = 136116135658 :=
  GuestFiveAddrTablesMergeBound.envelope_unchanged

/-- For every frontend body, the unconditional absence of storeConsts reaches
flattenHOL; no call-target hypothesis is used. Under the source size budget,
the same integration exposes the five-table, twelve-table and coupled bounds,
and all 36 certified budgets below Yukon. -/
theorem master_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width)
    (ptr : Nat) (f : Spt Nat)
    (D A W : Nat) (hsize : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hc : CertificateAt 1212035192) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (flattenInput info j bd ptr f y.1 y.2) = true ∧
       FlattenVisitsSt (flattenInput info j bd ptr f y.1 y.2) = false ∧
       (StackToLab.progToSectionHOL
         (y.1, flattenInput info j bd ptr f y.1 y.2)).sectionId = y.1)) ∧
    40 * (2 * ((D + A) * (W + D + A)) + 5 * (A * A)) ≤ S * S ∧
    40 * (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) ≤ S * S ∧
    42 * (2 * (D * W) + 12 * (A * A)) ≤ S * S ∧
    portfolio.length = 36 ∧ portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon) ∧
    (∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) := by
  refine ⟨?_, five_addr_tables_absorbed_non_vacuous_and_tight D A W hsize,
    twelve_addr_tables_absorbed_non_vacuous_and_tight D A W hsize,
    coupled_absorbed_non_vacuous_and_tight D A W (by omega),
    portfolio_count_non_vacuous_and_tight, portfolio_order_non_vacuous_and_tight,
    portfolio_bounds_non_vacuous_and_tight, portfolio_certificates_non_vacuous_and_tight hc⟩
  intro y hy
  rcases panToStackNames_bodies_StackNoSt_unconditional_non_vacuous_and_tight
    arch prog wc ac perf info j bd ptr f y hy with he | hs
  · exact Or.inl he
  · exact Or.inr ⟨hs, not_visits_of_StackNoSt_non_vacuous_and_tight _ hs, rfl⟩

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
#print axioms source_master_non_vacuous_and_tight
#print axioms joint_absorption_non_vacuous_and_tight
#print axioms merge_target_threshold_non_vacuous_and_tight
#print axioms identity5_non_vacuous_and_tight
#print axioms five_addr_tables_absorbed_non_vacuous_and_tight
#print axioms five_le_non_vacuous_and_tight
#print axioms five_tight_non_vacuous_and_tight
#print axioms identity12_non_vacuous_and_tight
#print axioms twelve_addr_tables_absorbed_non_vacuous_and_tight
#print axioms twelve_sharp_non_vacuous_and_tight
#print axioms coupled_absorbed_non_vacuous_and_tight
#print axioms coupled_le_non_vacuous_and_tight
#print axioms coupled_addr_corner_non_vacuous_and_tight
#print axioms envelope_unchanged_non_vacuous_and_tight
#print axioms master_non_vacuous_and_tight
#print axioms frontend_clean_and_flatten_non_vacuous_and_tight

end InitECandidate.Solver.UnconditionalNoStoreConstsAndFiveAddrMaster
