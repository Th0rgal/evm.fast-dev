import InitECandidate.Solver.Wave8Stage.InitCodeLayout

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.PipelineInitLayout
open Classical Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Pancake.Proofs.PanToTarget

/-- Heap/store facts of successful total initialization, independently of the
register conventions or semantic correctness of the supplied program. The
memory-domain premise covers only the input heap/stack interval. -/
theorem initialized_layout {width : Nat} [NeZero width] {C F : Type}
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (stack aux : StackSemStateFiniteExact width C F)
    (p2 p3 p4 bp : BitVec width)
    (good : goodDimindex width) (sp8 : 8 ≤ sp)
    (read2 : (s2 scc dc maxHeap sp offset code lab saveRegs oracle).regs.lookup 2 =
      some (.word p2))
    (read3 : (s2 scc dc maxHeap sp offset code lab saveRegs oracle).regs.lookup 3 =
      some (.word p3))
    (read4 : (s2 scc dc maxHeap sp offset code lab saveRegs oracle).regs.lookup 4 =
      some (.word p4))
    (mem0 : lab.memory p2 = .word bp)
    (maxOk : maxStackAlloc ≤ maxHeap)
    (le : p2.toNat ≤ p4.toNat)
    (big : (1024 * bytesInWord width).toNat ≤ (p4-p2).toNat)
    (al2 : holByteAligned p2 = true) (al4 : holByteAligned p4 = true)
    (included : ∀ a,
      addresses p2 ((p4-p2).toNat / (bytesInWord width).toNat) a → lab.memDomain a = true)
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps code lab
      saveRegs dataSp oracle = (stack,some aux)) :
    let reg3 := InitCodeThm.roundedThird p2 (InitCodeThm.shrunkThird p2
      (InitCodeThm.adjustedThird p3 (InitCodeThm.middleWord p2 p4)
        (p2 + InitCodeThm.marginWord width) (p4 - InitCodeThm.marginWord width))
      (InitCodeThm.maxHeapWord width maxHeap))
    ∃ heapLength stackLength : Nat,
      reg3.toNat = p2.toNat + heapLength * (width/8) ∧
      p4.toNat = reg3.toNat + stackLength * (width/8) ∧
      heapLength % 2 = 0 ∧ heapLength ≤ maxHeap ∧ maxStackAlloc ≤ stackLength ∧
      stack.store.lookup .currHeap = some (.word p2) ∧
      stack.store.lookup .heapLength =
        some (.word (BitVec.ofNat width (heapLength/2) * bytesInWord width)) ∧
      stack.mdomain = (fun a => decide (addresses p2 heapLength a)) ∧
      stack.ffi = lab.ffi ∧ stack.be = lab.be ∧ stack.shMdomain = lab.sharedMemDomain ∧
      (∀ a, addresses p2 heapLength a → stack.memory a = lab.memory a) := by
  intro reg3
  let pre := s2 scc dc maxHeap sp offset code lab saveRegs oracle
  have entry : sptDomain pre.code 1 := by
    simp [pre,s2,StackNames.makeInit,code2,StackRemove.compileHOL,
      StackRemove.initStubs,sptDomain,sptLookup_sptFromAList,sptAListLookup]
  have bound : (width/8) * ((p4-p2).toNat / (bytesInWord width).toNat) < 2 ^ width := by
    have b : (bytesInWord width).toNat = width/8 := by
      rcases good with rfl | rfl <;> rfl
    rw [b,Nat.mul_comm]
    exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) (p4-p2).isLt
  obtain ⟨frame,heap⟩ := InitCodeLayout.framed_wordListExists good pre.memory
    (fun a => pre.mdomain a = true) p2 _ bound included
  obtain ⟨post,heapLength,stackLength,run,shape,regEq,endEq,even,heapLe,stackLow,
    t5,tk2,tk,tk1,agree⟩ :=
    InitCodeLayout.run_layout (StackToLab.isGenGc dc.gcKind) maxHeap sp pre p2 p3 p4 bp
      good sp8 read2 read3 read4 mem0 entry maxOk le big al2 al4 frame heap
  have long : 49 ≤ stackLength := by
    simp only [maxStackAlloc] at stackLow
    omega
  obtain ⟨reducedCurr,reducedLength,reducedDomain,reducedMemory,reducedFfi,
      reducedBe,reducedShared⟩ :=
    InitCodeLayout.reduced_layout (StackToLab.isGenGc dc.gcKind) scc.jump offset sp
      (sptFromAList (code1 dc code)) bitmaps dataSp (coracle1 oracle) post p2 reg3 p4
      heapLength stackLength good regEq endEq even long t5 tk2 tk tk1
  obtain ⟨auxEq,_⟩ := panToTargetFullMakeInitReduce initialized run
  obtain ⟨stackEq,_⟩ := panToTargetFullMakeInitState initialized run
  have fields : stack.store = aux.store ∧ stack.mdomain = aux.mdomain ∧
      stack.memory = aux.memory ∧ stack.ffi = aux.ffi ∧ stack.be = aux.be ∧
      stack.shMdomain = aux.shMdomain := by
    rw [stackEq]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  rw [auxEq] at fields
  have ffiEq : post.ffi = lab.ffi := (congrArg (·.ffi) shape).trans rfl
  have beEq : post.be = lab.be := (congrArg (·.be) shape).trans rfl
  have sharedEq : post.shMdomain = lab.sharedMemDomain :=
    (congrArg (·.shMdomain) shape).trans rfl
  refine ⟨heapLength,stackLength,regEq,endEq,even,heapLe,stackLow,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [fields.1]; exact reducedCurr
  · rw [fields.1]; exact reducedLength
  · exact fields.2.1.trans reducedDomain
  · exact (fields.2.2.2.1.trans reducedFfi).trans ffiEq
  · exact (fields.2.2.2.2.1.trans reducedBe).trans beEq
  · exact (fields.2.2.2.2.2.trans reducedShared).trans sharedEq
  · intro a ha
    rw [fields.2.2.1,reducedMemory]
    exact (agree a ha).symm

#print axioms initialized_layout
end InitECandidate.Solver.Wave8Stage.PipelineInitLayout
