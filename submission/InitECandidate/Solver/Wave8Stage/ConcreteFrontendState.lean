import InitECandidate.Solver.Wave8Stage.ConcreteStackLayout
import InitECandidate.Solver.Wave8Stage.SourceDomainArithmetic

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteFrontendState
open Classical InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.PanLang Flapjack.Pancake.Proofs.PanToTarget
open InitECandidate.Solver.FastEnv InitECandidate.Solver.SelfContainedPipelineBridge

noncomputable abbrev word (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config) :=
  pipelinePanToWordInitState (oracleCompilerConfig oracles) baselineMachineConfig
    (sourceFfi input) t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode
    3788 ltconf sourceDeclarations wprog InitECandidate.bitmaps p 0

def heapLength : BitVec 64 := BitVec.ofNat 64 ((stackStart-sourceBase)/2)

private theorem heap_split :
    addresses (BitVec.ofNat 64 sourceBase) ((stackStart-sourceBase)/8) =
      (fun a => ordinaryDomain a ∨ addresses (BitVec.ofNat 64 heapEnd) 67 a) := by
  have split := addressesSplitGlobals (.inr rfl) (BitVec.ofNat 64 sourceBase)
    ((stackStart-sourceBase)/8) 67 (by decide)
  have top : BitVec.ofNat 64 sourceBase + bytesInWord 64 *
      BitVec.ofNat 64 ((stackStart-sourceBase)/8) - BitVec.ofNat 64 (67*64/8) =
      BitVec.ofNat 64 heapEnd := by decide
  rw [top] at split
  exact split.symm

/-- All semantic memory/store premises for the actual pre-WordToWord state.
The only state assumption is the original machine installation contract. -/
theorem fields (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (ConcreteInitMemory.dataDomain oracles t bitmapsDm) sdm) :
    let s := word oracles input t m bitmapsDm sdm wprog p ltconf
    (∀ a, ordinaryDomain a → s.memory a = wlabWlocExact (sourceMemory a)) ∧
    noLabelsHOL s.memory (fun a => s.mdomain a = true) ∧
    (fun a => s.mdomain a = true) =
      (fun a => ordinaryDomain a ∨ addresses (BitVec.ofNat 64 heapEnd) 67 a) ∧
    (fun a => s.shMdomain a = true) = sharedDomain ∧
    s.be = false ∧ s.ffi = sourceFfi input ∧
    s.store.lookup .currHeap = some (.word (BitVec.ofNat 64 sourceBase)) ∧
    s.store.lookup .heapLength = some (.word heapLength) := by
  dsimp only
  let st := ConcreteStackLayout.stack oracles input t m bitmapsDm sdm p ltconf
  obtain ⟨curr,len,dom,ffi,be,shared,mem⟩ :=
    ConcreteStackLayout.layout oracles input t m bitmapsDm sdm p ltconf initialized
  have domain : (fun a => (word oracles input t m bitmapsDm sdm wprog p ltconf).mdomain a = true) =
      addresses (BitVec.ofNat 64 sourceBase) ((stackStart-sourceBase)/8) := by
    change (fun a => st.mdomain a = true) = _
    rw [dom]
    funext a
    simp only [decide_eq_true_eq]
  refine ⟨?_,?_,domain.trans heap_split,?_,be,ffi,?_,?_⟩
  · intro a ha
    have inside : addresses (BitVec.ofNat 64 sourceBase) ((stackStart-sourceBase)/8) a := by
      rw [heap_split]
      exact .inl ha
    change st.memory a = _
    rw [mem a inside]
    have arith := SourceDomainArithmetic.ordinary_iff a |>.mp ha
    rw [ConcreteInitMemory.heap_word oracles t m bitmapsDm sdm initialized a arith.2.2
      ⟨arith.1,lt_trans arith.2.1 (by decide : heapEnd < ramEnd)⟩]
    exact SourceHeapFacts.installed_ordinary_word a ha
  · intro a ha
    have inHeap := Eq.mp (congrFun domain a) ha
    have aligned := addresses_mod (.inr rfl) (BitVec.ofNat 64 sourceBase) (by decide)
      ((stackStart-sourceBase)/8) a inHeap
    have alignEq : holByteAlign a = a := LabToTarget.holByteAlign_of_aligned (.inr rfl) a aligned
    obtain ⟨v,hv⟩ := goodInitState_wordMemory initialized a
    rw [alignEq] at hv
    exact ⟨v,(mem a inHeap).trans hv⟩
  · change (fun a => st.shMdomain a = true) = _
    rw [shared]
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,sharedEq,_,_,_,_,_⟩ := initialized
    funext a
    apply propext
    simp only [Bool.and_eq_true]
    have sd : sdm a = true ↔ machineSharedDomain a := by
      change sdm a = true ↔ baselineMachineConfig.sharedAddresses a
      rw [← sharedEq]
    change (sdm a = true ∧ holByteAligned a = true) ↔ sharedDomain a
    rw [sd]
    unfold sharedDomain
    change (_ ∧ _) ↔ (_ ∧ _)
    exact and_comm
  · change (st.store.eraseEq .handler).lookup .currHeap = _
    simpa only [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL,reduceCtorEq,if_false] using curr
  · change (st.store.eraseEq .handler).lookup .heapLength = _
    simpa only [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL,reduceCtorEq,if_false,heapLength] using len

#print axioms fields
end InitECandidate.Solver.Wave8Stage.ConcreteFrontendState
