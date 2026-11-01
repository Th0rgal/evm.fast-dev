import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
import InitECandidate.Solver.Wave8Stage.InitializedTransfer

/-! Light definition of the pipeline Lab initializer. Its body is identical to
SelfContainedPipelineBridge.pipelineLabInitState; a caller importing that
module can apply these theorems by definitional reduction, without making
this module depend on protected concrete-installation proofs. -/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.PipelineInitialization
open Classical Flapjack Compiler.Backend Compiler.Backend.LabToTarget
open Compiler.Backend.LabSem Compiler.Backend.StackLang Compiler.Encoders.Asm
noncomputable abbrev pipelineLabInitState {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (p : List (Nat × StackLang.HolProg width)) :
    Flapjack.Compiler.Backend.LabSem.State width LabToTarget.Config σ :=
  let regNames := c.stackConf.regNames
  let r1 := StackNames.findNameSpt regNames 2
  let r2 := StackNames.findNameSpt regNames 4
  let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
  let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
  let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
  LabToTarget.makeInit (C := LabToTarget.Config) mc ffi t m
    (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
    (fun a => sdm a && holByteAligned a) ms
    (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
    (LabToTarget.compile mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
    (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
      mc.target.config.addrOffset sp []))

/-- The Lab code used by fullMakeInit is exactly the code compiled by the
Lab-to-target pipeline, including all rawcall/alloc/remove/names passes. -/
theorem compile_eq_code2 {width : Nat} [NeZero width]
    (sc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (p : List (Nat × StackLang.HolProg width)) :
    StackToLab.compile sc dc maxHeap sp offset p =
      (StackNames.compileHOL sc.regNames
        (StackToLab.Proofs.FullMakeInitSemantics.code2 sc dc maxHeap sp offset p)).map
        StackToLab.progToSectionHOL := rfl

/-- Filtering the actual initializer retains its true code-buffer base and
uses compileLab only for the filtered state; the input uses ordinary compile. -/
theorem filtered_makeInit {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool) (ms : S)
    (code : LabProgHOL width) (bytes : List (BitVec 8)) (cbspace : Nat)
    (coracle : Nat → LabToTarget.Config × LabProgHOL width) :
    UnfilteredTransfer.filtered mc
      (makeInit mc ffi t m dm sdm ms code (compile mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle) =
      makeInit mc ffi t m dm sdm ms (LabFilter.filterSkip code) (compileLab mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
        (fun n => ((coracle n).1, LabFilter.filterSkip (coracle n).2)) := by
  have zero : LabFilter.Proofs.adjustPc 0 code = 0 := by
    rw [LabFilter.Proofs.adjustPc.eq_def]
    simp
  simp only [UnfilteredTransfer.filtered, makeInit, zero]

section Pipeline
variable {width : Nat} [NeZero width] {S Q F : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState F)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (p : List (Nat × StackLang.HolProg width))

/-- The explicit code2 view of Stage 4 is the very same unfiltered pipeline
state, including its compiler and all four target register oracles. -/
theorem code2_state_eq :
    { pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p with
      code := (StackNames.compileHOL c.stackConf.regNames
        (StackToLab.Proofs.FullMakeInitSemantics.code2 c.stackConf c.dataConf
          (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
          (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
          mc.target.config.addrOffset p)).map StackToLab.progToSectionHOL } =
    pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p := rfl

/-- Its makeInit form is the initialized-transfer interface verbatim. -/
theorem pipeline_eq_makeInit :
    let lab := pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p
    lab = makeInit mc ffi t m lab.memDomain lab.sharedMemDomain ms lab.code
      (compile mc.target.config) (mc.target.getPc ms + BitVec.ofNat width bytes.length)
      cbspace lab.compileOracle := rfl

/-- Completed Stage 4 observations survive skip filtering at the same clock.
This includes the exact FFI state, not only the non-timeout classification. -/
theorem filter_observation (k : Nat)
    (complete : (LabSem.evaluate
      {pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p with
        clock := k}).1 ≠ .timeOut) :
    let lab := pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p
    (LabSem.evaluate {UnfilteredTransfer.filtered mc lab with clock := k}).1 =
      (LabSem.evaluate {lab with clock := k}).1 ∧
    (LabSem.evaluate {UnfilteredTransfer.filtered mc lab with clock := k}).2.ffi =
      (LabSem.evaluate {lab with clock := k}).2.ffi :=
  UnfilteredTransfer.filter_observation mc _ rfl rfl k complete
end Pipeline

/-- Standard initialization guards derive the full true-base relation for the
exact pipeline state, with its heap/bitmap and aligned shared-memory domains. -/
theorem initialized_stateRel {F : Type}
    (c : Backend.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state Compiler.Encoders.RiscV.Target.RiscVProjection)
    (ffi : HolFfiState F) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool) (ms : RiscV.L3.riscv_state)
    (code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (ltconf : LabToTarget.Config) (p : List (Nat × StackLang.HolProg 64))
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : let lab := (pipelineLabInitState c mc ffi t m bitmapsDm sdm ms
        (progToBytes code2) cbspace ltconf p);
      InitializedTransfer.Initialization mc ms lab.code code2 labs clock i cbspace
        t m lab.memDomain lab.sharedMemDomain lab.compileOracle names info shiftedInfo) :
    LabToTarget.stateRel (mc, code2, labs, mc.target.getPc ms)
      (UnfilteredTransfer.filtered mc
        (pipelineLabInitState c mc ffi t m bitmapsDm sdm ms
          (progToBytes code2) cbspace ltconf p)) t ms := by
  let lab := pipelineLabInitState c mc ffi t m bitmapsDm sdm ms
    (progToBytes code2) cbspace ltconf p
  exact InitializedTransfer.initialized_stateRel mc ms ffi lab.code code2 labs clock i cbspace
    t m lab.memDomain lab.sharedMemDomain lab.compileOracle names info shiftedInfo init

#print axioms compile_eq_code2
#print axioms filtered_makeInit
#print axioms code2_state_eq
#print axioms pipeline_eq_makeInit
#print axioms filter_observation
#print axioms initialized_stateRel
end InitECandidate.Solver.Wave8Stage.PipelineInitialization
