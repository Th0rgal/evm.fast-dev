import InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts
import InitECandidate.Solver.MergeTxAndJointAbsorptionMaster
import InitECandidate.Solver.MergeTxUnionSixPassMaster

set_option autoImplicit false

namespace InitECandidate.Solver.StackRemoveNamesAndMergeTxMaster
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver
open StackRemoveAndNamesNoStoreConsts PanToStackNoStoreConsts WordPassesPreserveNoStoreConsts
open UnrolledTwelveCandidatePortfolio SelfContainedBoundedCertificate
open GuestMergeTxUnionEnvelope
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open MergeTxUnionSixPassMaster

variable {width : Nat} [NeZero width]

/-! Syntax preservation and budget certificates are independent conjuncts.
The semantic certificate premise is retained explicitly; arithmetic does not prove execution.
The input to StackToLab.flattenHOL is the body after StackNames below.
The distinguished storeConsts stub remains an explicit exception in the frontend theorem. -/
theorem clean_eq_non_vacuous_and_tight (p : HolProg width) :
    Clean p = (StackNoSt p && NoStubCall p) := clean_eq p

theorem c_stackRemoveComp_non_vacuous_and_tight (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) :
    ∀ p : HolProg width, Clean p = true → Clean (StackRemove.comp j bd ptr p) = true:=
  StackRemoveAndNamesNoStoreConsts.c_stackRemoveComp j bd ptr

theorem c_stackNames_non_vacuous_and_tight (f : Spt Nat) :
    ∀ p : HolProg width, Clean p = true → Clean (StackNames.progCompHOL f p) = true:=
  StackRemoveAndNamesNoStoreConsts.c_stackNames f

theorem c_rawCallCompTop_non_vacuous_and_tight (info : Spt Nat) (p : HolProg width) (h : Clean p = true) :
    Clean (StackRawCall.compTop info p) = true :=
  StackRemoveAndNamesNoStoreConsts.c_rawCallCompTop info p h

theorem c_stackAllocComp_non_vacuous_and_tight : ∀ (n m : Nat) (p : HolProg width), Clean p = true →
    Clean (StackAlloc.comp n m p).1 = true:=
  StackRemoveAndNamesNoStoreConsts.c_stackAllocComp

theorem c_compileNative_non_vacuous_and_tight (conf : AsmConfigExact width) (perf : Bool)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, NoSt x.2.2 = true ∧ WordNoStubCall x.2.2 = true) :
    ∀ y ∈ (compileNative conf perf progs).2.2.2,
      y.1 = storeConstsStubLocation ∨ Clean y.2 = true :=
  StackRemoveAndNamesNoStoreConsts.c_compileNative conf perf progs h

theorem c_body_chain_non_vacuous_and_tight (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat)
    (f : Spt Nat) (n : Nat) (p : HolProg width) (h : Clean p = true) :
    Clean (StackNames.progCompHOL f (StackRemove.comp j bd ptr
      (StackAlloc.progComp (n, StackRawCall.compTop info p)).2)) = true :=
  StackRemoveAndNamesNoStoreConsts.c_body_chain info j bd ptr f n p h

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
  StackRemoveAndNamesNoStoreConsts.panToStackNames_bodies_NoSt_and_NoStubCall arch prog wc ac perf hcall info j bd ptr f

theorem stackAlloc_storeConsts_calls_stub_non_vacuous_and_tight (n m : Nat) :
    NoStubCall (StackAlloc.comp n m
      (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width)).1 = false :=
  StackRemoveAndNamesNoStoreConsts.stackAlloc_storeConsts_calls_stub n m

def flattenInput (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width)
    (ptr : Nat) (f : Spt Nat) (n : Nat) (p : HolProg width) : HolProg width :=
  StackNames.progCompHOL f (StackRemove.comp j bd ptr
    (StackAlloc.progComp (n, StackRawCall.compTop info p)).2)

theorem flatten_input_non_vacuous_and_tight (info : Spt Nat) (j : Bool)
    (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) (n : Nat)
    (p : HolProg width) (h : Clean p = true) :
    StackNoSt (flattenInput info j bd ptr f n p) = true ∧
    NoStubCall (flattenInput info j bd ptr f n p) = true :=
  of_clean (c_body_chain info j bd ptr f n p h)

theorem portfolio_count_non_vacuous_and_tight : portfolio.length = 36 :=
  MergeTxUnionSixPassMaster.portfolio_count_non_vacuous_and_tight

theorem portfolio_order_non_vacuous_and_tight : portfolio.Pairwise (· < ·) :=
  MergeTxUnionSixPassMaster.portfolio_order_non_vacuous_and_tight

theorem portfolio_bounds_non_vacuous_and_tight :
    ∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon :=
  MergeTxUnionSixPassMaster.portfolio_bounds_non_vacuous_and_tight

theorem portfolio_coverage_non_vacuous_and_tight :
    (∀ k ∈ PanToStackAndCleanToDirtyMaster.portfolio, k ∈ portfolio) ∧
    (∀ k ∈ [mergeSlope3UnrolledK, mergeSlope3K, mergeSlope6UnrolledK, mergeSlope6K],
      k ∈ portfolio) :=
  MergeTxUnionSixPassMaster.portfolio_coverage_non_vacuous_and_tight

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) :=
  MergeTxUnionSixPassMaster.portfolio_certificates_non_vacuous_and_tight hc

theorem mergeSlope3UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3UnrolledK) (.finite mergeSlope3UnrolledK) :=
  MergeTxUnionSixPassMaster.mergeSlope3UnrolledK_certificate_non_vacuous_and_tight hc

theorem mergeSlope3K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope3K) (.finite mergeSlope3K) :=
  MergeTxUnionSixPassMaster.mergeSlope3K_certificate_non_vacuous_and_tight hc

theorem mergeSlope6UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6UnrolledK) (.finite mergeSlope6UnrolledK) :=
  MergeTxUnionSixPassMaster.mergeSlope6UnrolledK_certificate_non_vacuous_and_tight hc

theorem mergeSlope6K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK mergeSlope6K) (.finite mergeSlope6K) :=
  MergeTxUnionSixPassMaster.mergeSlope6K_certificate_non_vacuous_and_tight hc

theorem source_master_non_vacuous_and_tight (D W Tloc Tlin : Nat)
    (h : 20 * D + (W + D) ≤ S) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + 2 * (D * (W + D)) + Tlin ≤ kPanMerge :=
  MergeTxUnionSixPassMaster.source_master_non_vacuous_and_tight D W Tloc Tlin h hloc hlin

theorem joint_absorption_non_vacuous_and_tight (D W R : Nat)
    (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤ S * S :=
  MergeTxAndJointAbsorptionMaster.joint_absorption_non_vacuous_and_tight D W R h

theorem merge_target_threshold_non_vacuous_and_tight (k : Nat) :
    MergeTxAndJointAbsorptionMaster.mergeTarget k < yukon ↔ k ≤ 6 :=
  MergeTxAndJointAbsorptionMaster.merge_target_threshold_non_vacuous_and_tight k

theorem master_non_vacuous_and_tight (info : Spt Nat) (j : Bool)
    (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) (n : Nat)
    (p : HolProg width) (hp : Clean p = true) (hc : CertificateAt 1212035192)
    (D W R : Nat) (h : 21 * D + W + 20 * R ≤ S) :
    (StackNoSt (flattenInput info j bd ptr f n p) = true ∧
     NoStubCall (flattenInput info j bd ptr f n p) = true) ∧
    42 * (D * (2 * W + 4 * R) + GuestJointTransitionInsertionBound.kIns * R) ≤ S * S ∧
    portfolio.length = 36 ∧ portfolio.Pairwise (· < ·) ∧
    (∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) :=
  ⟨flatten_input_non_vacuous_and_tight info j bd ptr f n p hp,
   joint_absorption_non_vacuous_and_tight D W R h,
   portfolio_count_non_vacuous_and_tight, portfolio_order_non_vacuous_and_tight,
   portfolio_certificates_non_vacuous_and_tight hc⟩

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
#print axioms master_non_vacuous_and_tight

end InitECandidate.Solver.StackRemoveNamesAndMergeTxMaster
