import InitECandidate.Solver.PipelineInitialStates
import InitECandidate.Solver.Wave8Stage.ConcreteInitMemory
import InitECandidate.Solver.Wave8Stage.PipelineInitHeap
import InitECandidate.Solver.Wave8Stage.PipelineInitLayout
import InitECandidate.Bitmaps

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteInitHeap

private theorem bitmap_length : InitECandidate.bitmaps.length = 4603 := by rfl
open Classical InitE Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.FastEnv InitECandidate.Solver.SelfContainedPipelineBridge
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

noncomputable abbrev pointer : Nat := baselineMachineConfig.target.config.regCount -
  (baselineMachineConfig.target.config.avoidRegs.length + 3)

noncomputable abbrev maximumHeap (oracles : List (Option (Spt Nat))) : Nat :=
  2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1

/-- The heap initializer leaves the installed heap/stack boundary unchanged. -/
theorem heap_boundary (oracles : List (Option (Spt Nat))) :
    InitCodeThm.roundedThird (BitVec.ofNat 64 sourceBase)
      (InitCodeThm.shrunkThird (BitVec.ofNat 64 sourceBase)
        (InitCodeThm.adjustedThird (BitVec.ofNat 64 stackStart)
          (InitCodeThm.middleWord (BitVec.ofNat 64 sourceBase) (BitVec.ofNat 64 ramEnd))
          (BitVec.ofNat 64 sourceBase + InitCodeThm.marginWord 64)
          (BitVec.ofNat 64 ramEnd - InitCodeThm.marginWord 64))
        (InitCodeThm.maxHeapWord 64 (maximumHeap oracles))) =
      BitVec.ofNat 64 stackStart := by
  change InitCodeThm.roundedThird (BitVec.ofNat 64 sourceBase)
    (InitCodeThm.shrunkThird (BitVec.ofNat 64 sourceBase)
      (InitCodeThm.adjustedThird (BitVec.ofNat 64 stackStart)
        (InitCodeThm.middleWord (BitVec.ofNat 64 sourceBase) (BitVec.ofNat 64 ramEnd))
        (BitVec.ofNat 64 sourceBase + InitCodeThm.marginWord 64)
        (BitVec.ofNat 64 ramEnd - InitCodeThm.marginWord 64))
      (InitCodeThm.maxHeapWord 64
        (2 * DataToWord.maxHeapLimit 64 RiscVConfig.pancakeRiscVBackendConfig.dataConf - 1))) = _
  decide


noncomputable abbrev lab (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (p : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config) :=
  pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig (sourceFfi input)
    t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode 3788 ltconf p

noncomputable abbrev preState (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (p : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config) :=
  s2 (oracleCompilerConfig oracles).stackConf (oracleCompilerConfig oracles).dataConf
    (maximumHeap oracles) pointer baselineMachineConfig.target.config.addrOffset p
    (lab oracles input t m bitmapsDm sdm p ltconf)
    (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs))
    (fun _ => (ltconf,[],[]))

/-- Every aligned cell of the heap/stack interval belongs to the actual Lab
initializer domain, even if the supplied bitmap domain is empty. -/
theorem heap_included (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (p : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (ConcreteInitMemory.dataDomain oracles t bitmapsDm) sdm)
    (a : BitVec 64)
    (ha : addresses (BitVec.ofNat 64 sourceBase)
      (((BitVec.ofNat 64 ramEnd)-(BitVec.ofNat 64 sourceBase)).toNat /
        (bytesInWord 64).toNat) a) :
    (lab oracles input t m bitmapsDm sdm p ltconf).memDomain a = true := by
  obtain ⟨i,hi,rfl⟩ := (mem_addresses _ _ _).mp ha
  have count : (((BitVec.ofNat 64 ramEnd)-(BitVec.ofNat 64 sourceBase)).toNat /
      (bytesInWord 64).toNat) = (ramEnd-sourceBase)/8 := by decide
  rw [count] at hi
  have small : sourceBase+i*8 < 2^64 := by
    norm_num [sourceBase,ramEnd,ramStart,ramSize] at hi ⊢
    omega
  have addr : (BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 i * bytesInWord 64).toNat =
      sourceBase+i*8 := by
    change (BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 i * BitVec.ofNat 64 8).toNat = _
    rw [BitVec.ofNat_mul_ofNat,BitVec.ofNat_add_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have bounds : sourceBase ≤ sourceBase+i*8 ∧ sourceBase+i*8 < ramEnd := by
    norm_num [sourceBase,ramEnd,ramStart,ramSize] at hi ⊢
    omega
  have aligned : (sourceBase+i*8)%8 = 0 := by norm_num [sourceBase,Nat.add_mod]
  obtain ⟨r2,_,r4⟩ := ConcreteInitMemory.registers oracles t m bitmapsDm sdm initialized
  change ((ConcreteInitMemory.dataDomain oracles t bitmapsDm _) && holByteAligned _) = true
  rw [Bool.and_eq_true]
  constructor
  · simp only [ConcreteInitMemory.dataDomain,r2,r4,Bool.or_eq_true,decide_eq_true_eq]
    left
    simp only [BitVec.le_def,BitVec.lt_def,addr]
    simpa only [BitVec.toNat_ofNat, show sourceBase % 2^64 = sourceBase from by decide,
      show ramEnd % 2^64 = ramEnd from by decide] using bounds
  · exact (InitCodeThm.byteAligned_iff (.inr rfl) _).2 (addr ▸ aligned)

/-- The concrete machine installation satisfies the weaker heap initializer
contract for arbitrary supplied Stack code and lab compiler configuration. -/
theorem machine_pre (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (p : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (ConcreteInitMemory.dataDomain oracles t bitmapsDm) sdm) :
    ∃ frame, InitCodeHeap.heapPre pointer InitECandidate.bitmaps 0
      (preState oracles input t m bitmapsDm sdm p ltconf) frame := by
  let s := preState oracles input t m bitmapsDm sdm p ltconf
  obtain ⟨r2,r3,r4⟩ := ConcreteInitMemory.registers oracles t m bitmapsDm sdm initialized
  have hcfg := oracleBackendConfigOk oracles
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bij,_⟩ := hcfg
  have reg2 : s.regs.lookup 2 = some (.word (BitVec.ofNat 64 sourceBase)) := by
    rw [s2_regs_lookup bij (.inl rfl)]
    exact congrArg (fun v => some (WordLocW.word v)) r2
  have reg3 : s.regs.lookup 3 = some (.word (BitVec.ofNat 64 stackStart)) := by
    rw [s2_regs_lookup bij (.inr (.inl rfl))]
    exact congrArg (fun v => some (WordLocW.word v)) r3
  have reg4 : s.regs.lookup 4 = some (.word (BitVec.ofNat 64 ramEnd)) := by
    rw [s2_regs_lookup bij (.inr (.inr rfl))]
    exact congrArg (fun v => some (WordLocW.word v)) r4
  have entry : sptDomain s.code 1 := by
    simp [s,preState,s2,StackNames.makeInit,code2,StackRemove.compileHOL,
      StackRemove.initStubs,sptDomain,sptLookup_sptFromAList,sptAListLookup]
  have included : ∀ a, addresses (BitVec.ofNat 64 sourceBase)
      (((BitVec.ofNat 64 ramEnd)-(BitVec.ofNat 64 sourceBase)).toNat /
        (bytesInWord 64).toNat) a → s.mdomain a = true :=
    heap_included oracles input t m bitmapsDm sdm p ltconf initialized
  have bound : (64/8) * (((BitVec.ofNat 64 ramEnd)-(BitVec.ofNat 64 sourceBase)).toNat /
      (bytesInWord 64).toNat) < 2^64 := by decide
  obtain ⟨frame,heap⟩ := InitCodeLayout.framed_wordListExists (.inr rfl) s.memory
    (fun a => s.mdomain a = true) (BitVec.ofNat 64 sourceBase) _ bound included
  refine ⟨frame,BitVec.ofNat 64 sourceBase,BitVec.ofNat 64 stackStart,
    BitVec.ofNat 64 ramEnd,BitVec.ofNat 64 (initDataRam+24),.inr rfl,by decide,entry,
    reg2,reg3,reg4,?_,?_,?_,?_,?_,by decide,by decide,
    (InitCodeThm.byteAligned_iff (.inr rfl) _).2 (by decide),
    (InitCodeThm.byteAligned_iff (.inr rfl) _).2 (by decide),
    (InitCodeThm.byteAligned_iff (.inr rfl) _).2 (by decide),rfl,heap⟩
  · exact ConcreteInitMemory.headers oracles t m bitmapsDm sdm initialized ⟨0,by decide⟩
  · have h := ConcreteInitMemory.headers oracles t m bitmapsDm sdm initialized ⟨1,by decide⟩
    rw [bitmap_length]
    change m (BitVec.ofNat 64 (sourceBase+8*1)) = .word _
    exact h
  · have h := ConcreteInitMemory.headers oracles t m bitmapsDm sdm initialized ⟨2,by decide⟩
    rw [bitmap_length]
    change m (BitVec.ofNat 64 (sourceBase+8*2)) = .word _
    exact h
  · have h := ConcreteInitMemory.headers oracles t m bitmapsDm sdm initialized ⟨3,by decide⟩
    have position : s.codeBuffer.position =
        BitVec.ofNat 64 nativePc + BitVec.ofNat 64 InitECandidate.nativeCode.length := rfl
    rw [position,InitECandidate.Proofs.LiteralFacts.nativeCode_length]
    exact h
  · have h := ConcreteInitMemory.headers oracles t m bitmapsDm sdm initialized ⟨4,by decide⟩
    have position : s.codeBuffer.position =
        BitVec.ofNat 64 nativePc + BitVec.ofNat 64 InitECandidate.nativeCode.length := rfl
    rw [position,InitECandidate.Proofs.LiteralFacts.nativeCode_length]
    change m (BitVec.ofNat 64 (sourceBase+8*4)) = .word
      ((BitVec.ofNat 64 nativePc + BitVec.ofNat 64 979140) + BitVec.ofNat 64 3788)
    exact h

/-- The actual concrete machine contract rules out the failure branch of the
pipeline initializer, even for arbitrary supplied Stack code. -/
theorem fullMakeInit_success (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (p : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (ConcreteInitMemory.dataDomain oracles t bitmapsDm) sdm) :
    ∃ aux, FullMakeInit.fullMakeInit (oracleCompilerConfig oracles).stackConf
      (oracleCompilerConfig oracles).dataConf (maximumHeap oracles) pointer
      baselineMachineConfig.target.config.addrOffset InitECandidate.bitmaps p
      (lab oracles input t m bitmapsDm sdm p ltconf)
      (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0
      (fun _ => (ltconf,[],[])) =
        (pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode
          3788 ltconf InitECandidate.bitmaps p 0, some aux) := by
  obtain ⟨frame,pre⟩ := machine_pre oracles input t m bitmapsDm sdm p ltconf initialized
  obtain ⟨aux,success⟩ := PipelineInitHeap.fullMakeInit_success
    (oracleCompilerConfig oracles).stackConf (oracleCompilerConfig oracles).dataConf
    (maximumHeap oracles) pointer baselineMachineConfig.target.config.addrOffset
    InitECandidate.bitmaps p (lab oracles input t m bitmapsDm sdm p ltconf)
    (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0
    (fun _ => (ltconf,[],[])) frame pre (by rw [bitmap_length]; decide) (by
      change maxStackAlloc ≤ 2 * DataToWord.maxHeapLimit 64
        RiscVConfig.pancakeRiscVBackendConfig.dataConf - 1
      decide)
  exact ⟨aux,Prod.ext rfl success⟩


end InitECandidate.Solver.Wave8Stage.ConcreteInitHeap
