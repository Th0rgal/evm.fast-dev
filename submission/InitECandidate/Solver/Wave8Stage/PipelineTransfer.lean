import InitECandidate.Solver.Wave8Stage.CompileTransfer
import InitECandidate.Solver.Wave8Stage.PipelineInitialization

/-! Parameterized pipeline Stage 5 interface. Baseline machine/state constants,
sourceFfi input and bootstrapSteps are ordinary arguments; this file does not
import protected installation proofs or the heavy concrete pipeline module. -/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.PipelineTransfer
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target RiscV.L3
open PipelineInitialization

/-- Full pipeline Lab-to-target transfer from a successful ordinary compile.
Use baselineMachineConfig, baselineInitialState input, baselineInstalledState,
sourceFfi input and bootstrapSteps as arguments in the concrete application.
The relation base is exactly mc.target.getPc installed. -/
theorem stage5_lab_to_target_affine_not_timeOut {F : Type}
    (c : Backend.Config)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (initial installed : riscv_state) (ffi : HolFfiState F)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf output : LabToTarget.Config)
    (p : List (Nat × StackLang.HolProg 64))
    (compiled : LabToTarget.compile riscvConfig ltconf
      (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p).code =
        some (bytes, output))
    (position : ltconf.pos = 0)
    (safe : LabProps.noInstall
      (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p).code)
    (related : LabToTarget.stateRel
      (mc, CompileTransfer.compiledCode riscvConfig ltconf output
        (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p).code
        bytes compiled, output.labels, mc.target.getPc installed)
      (UnfilteredTransfer.filtered mc
        (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p))
      t installed)
    (tied : oracleTie mc installed
      (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p))
    (bootstrap k_lab : Nat)
    (bootstrapRun : ∀ fuel, evaluateTargetHOL mc ffi (bootstrap + fuel) initial =
      evaluateTargetHOL mc ffi fuel installed)
    (notError : (LabSem.evaluate
      {pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p with
        clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate
      {pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p with
        clock := k_lab}).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi (bootstrap + 9 * (k_lab + 1)) initial).1 ≠ .timeOut :=
  CompileTransfer.stage5_lab_to_target_affine_not_timeOut mc target initial installed
    (pipelineLabInitState c mc ffi t m bitmapsDm sdm installed bytes cbspace ltconf p) t
    ltconf output bytes compiled position safe rfl rfl related tied bootstrap k_lab
    bootstrapRun notError notTimeout

end InitECandidate.Solver.Wave8Stage.PipelineTransfer
