import InitECandidate.Solver.Wave8Stage.ConcreteInitHeap

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteStackLayout
open Classical InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.FastEnv InitECandidate.Solver.SelfContainedPipelineBridge
open ConcreteInitHeap

noncomputable abbrev stack (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (p : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config) :=
  pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
    (sourceFfi input) t m bitmapsDm sdm baselineInstalledState InitECandidate.nativeCode
    3788 ltconf InitECandidate.bitmaps p 0

/-- Exact concrete heap fields from the original machine installation premise.
No frontend state relation or heap-field equality is assumed. -/
theorem layout (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
    (p : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (ConcreteInitMemory.dataDomain oracles t bitmapsDm) sdm) :
    let s := stack oracles input t m bitmapsDm sdm p ltconf
    s.store.lookup .currHeap = some (.word (BitVec.ofNat 64 sourceBase)) ∧
    s.store.lookup .heapLength = some (.word (BitVec.ofNat 64 ((stackStart-sourceBase)/2))) ∧
    s.mdomain = (fun a => decide (addresses (BitVec.ofNat 64 sourceBase)
      ((stackStart-sourceBase)/8) a)) ∧
    s.ffi = sourceFfi input ∧ s.be = false ∧
    s.shMdomain = (fun a => sdm a && holByteAligned a) ∧
    (∀ a, addresses (BitVec.ofNat 64 sourceBase) ((stackStart-sourceBase)/8) a →
      s.memory a = m a) := by
  dsimp only
  obtain ⟨aux,success⟩ := ConcreteInitHeap.fullMakeInit_success oracles input t m
    bitmapsDm sdm p ltconf initialized
  obtain ⟨r2,r3,r4⟩ := ConcreteInitMemory.registers oracles t m bitmapsDm sdm initialized
  have cfg := oracleBackendConfigOk oracles
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bij,_⟩ := cfg
  have reg2 : (preState oracles input t m bitmapsDm sdm p ltconf).regs.lookup 2 =
      some (.word (BitVec.ofNat 64 sourceBase)) := by
    rw [s2_regs_lookup bij (.inl rfl)]
    exact congrArg (fun v => some (WordLocW.word v)) r2
  have reg3 : (preState oracles input t m bitmapsDm sdm p ltconf).regs.lookup 3 =
      some (.word (BitVec.ofNat 64 stackStart)) := by
    rw [s2_regs_lookup bij (.inr (.inl rfl))]
    exact congrArg (fun v => some (WordLocW.word v)) r3
  have reg4 : (preState oracles input t m bitmapsDm sdm p ltconf).regs.lookup 4 =
      some (.word (BitVec.ofNat 64 ramEnd)) := by
    rw [s2_regs_lookup bij (.inr (.inr rfl))]
    exact congrArg (fun v => some (WordLocW.word v)) r4
  obtain ⟨heapLength,stackLength,regEq,_,_,_,_,curr,len,domain,ffi,be,shared,mem⟩ :=
    PipelineInitLayout.initialized_layout (oracleCompilerConfig oracles).stackConf
      (oracleCompilerConfig oracles).dataConf (maximumHeap oracles) pointer
      baselineMachineConfig.target.config.addrOffset InitECandidate.bitmaps p
      (lab oracles input t m bitmapsDm sdm p ltconf)
      (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0
      (fun _ => (ltconf,[],[])) _ aux
      (BitVec.ofNat 64 sourceBase) (BitVec.ofNat 64 stackStart) (BitVec.ofNat 64 ramEnd)
      (BitVec.ofNat 64 (initDataRam+24)) (.inr rfl) (by decide)
      reg2 reg3 reg4
      (ConcreteInitMemory.headers oracles t m bitmapsDm sdm initialized ⟨0,by decide⟩)
      (by change maxStackAlloc ≤ 2 * DataToWord.maxHeapLimit 64
            RiscVConfig.pancakeRiscVBackendConfig.dataConf - 1; decide)
      (by decide) (by decide)
      ((InitCodeThm.byteAligned_iff (.inr rfl) _).2 (by decide))
      ((InitCodeThm.byteAligned_iff (.inr rfl) _).2 (by decide))
      (ConcreteInitHeap.heap_included oracles input t m bitmapsDm sdm p ltconf initialized)
      success
  rw [heap_boundary] at regEq
  have count : heapLength = (stackStart-sourceBase)/8 := by
    norm_num [sourceBase,stackStart,ramEnd,ramStart,ramSize,stackSize] at regEq ⊢
    omega
  subst heapLength
  refine ⟨curr,?_,domain,ffi,be,shared,mem⟩
  convert len using 2 <;> decide

#print axioms layout
end InitECandidate.Solver.Wave8Stage.ConcreteStackLayout
