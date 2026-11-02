import InitECandidate.Solver.SelfContainedStageBounds

set_option autoImplicit false

namespace InitECandidate.Solver.SelfContainedPipelineBridge
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.PanLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-! ## 2. Pipeline Stage Initial States (`PanToWord`, `WordToWord`, `WordToStack`, `StackToLab`) -/

/-- Stage 4 (`LabSem`) initial state constructed by `LabToTarget.makeInit` in `PanToTarget`. -/
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

/-- Stage 3 (`StackSem`) initial state constructed by `FullMakeInit.fullMakeInit` in `PanToTarget`. -/
noncomputable abbrev pipelineStackInitState {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (bitmaps : List (BitVec width)) (p : List (Nat × StackLang.HolProg width)) (dataSp : Nat) :
    StackSemStateFiniteExact width LabToTarget.Config σ :=
  let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
  let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
  let labst := pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p
  (FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
    mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
    dataSp (fun _ => (ltconf, [], []))).1

/-- Stage 2b (`WordSem` post-`WordToWord`) initial state constructed by `WordToStack.Native.Initialization.makeInit`. -/
noncomputable abbrev pipelineWordInitState {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (p : List (Nat × StackLang.HolProg width)) (dataSp : Nat) :
    WordSemStateFiniteExact width (Nat × LabToTarget.Config) σ :=
  let sst := pipelineStackInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf bitmaps p dataSp
  let k_reg := mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)
  let worac : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
    fun _ => ((bitmaps.length, ltconf), [])
  WordToStack.Native.Initialization.makeInit mc.target.config k_reg sst (sptFromAList wprog) worac

/-- Stage 2a (`WordSem` pre-`WordToWord`, output of `PanToWord`) initial state (`wst0`). -/
noncomputable abbrev pipelinePanToWordInitState {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (panCode : List (Pancake.PanLang.DeclHOL width))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (p : List (Nat × StackLang.HolProg width)) (dataSp : Nat) :
    WordSemStateFiniteExact width (Nat × LabToTarget.Config) σ :=
  { pipelineWordInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf wprog bitmaps p dataSp with
    code := sptFromAList (panToWordCompileProgHOL mc.target.config.isa panCode) }


end InitECandidate.Solver.SelfContainedPipelineBridge
