import InitECandidate.Solver.Wave8Stage.ConcreteBaseline.ExactBootstrap
import InitECandidate.Solver.Wave8Stage.ConcreteBaseline.EndpointTransport

/-! Concrete slope-nine transfer through the real 23077-step startup.
The Lab oracle is tied to the initial machine run, and is transported to
startup's actual endpoint by the checked interference-search identity. -/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteBaseline
open InitE InitECandidate.Proofs
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target RiscV.L3
open InitECandidate.Proofs.BootstrapAsmComposition
open Compiler.Backend.Semantics.TargetProps

/-- This concrete entry point assumes the full true-base relation at the
canonical installation, and the oracle tie to the actual initial machine.
It assumes neither a bootstrap run nor equality of startup's machine endpoint
to baselineInstalledState. -/
theorem stage5_lab_to_target_affine_not_timeOut {F : Type}
    (input : Guest.InputBlob) (lab : LabSem.State 64 Config F) (t : AsmState 64)
    (code2 : LabProgHOL 64) (labs acc : Spt (Spt Nat))
    (ffis : List HolFfiName) (clock : Nat)
    (compiled : removeLabels clock riscvConfig 0 acc ffis (LabFilter.filterSkip lab.code) =
      some (code2, labs))
    (safe : LabProps.noInstall lab.code)
    (compiler : lab.compile = compile baselineMachineConfig.target.config)
    (failed : lab.failed = false)
    (related : LabToTarget.stateRel
      (baselineMachineConfig, code2, labs,
        baselineMachineConfig.target.getPc baselineInstalledState)
      (UnfilteredTransfer.filtered baselineMachineConfig lab) t baselineInstalledState)
    (tied : oracleTie baselineMachineConfig (baselineInitialState input) lab)
    (k_lab : Nat)
    (notError : (LabSem.evaluate {lab with clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate {lab with clock := k_lab}).1 ≠ .timeOut) :
    (evaluateTargetHOL baselineMachineConfig lab.ffi
      (bootstrapSteps + 9 * (k_lab + 1)) (baselineInitialState input)).1 ≠ .timeOut := by
  obtain ⟨post, run, search, endpoint⟩ := ExactBootstrap.full_evaluator_exact lab.ffi
    (baselineInitialState input) (baselineInitialState_related input)
  have agreement := baseline_endpoint_agreement post endpoint
  have relation := stateRel_transport agreement code2 labs
    (baselineMachineConfig.target.getPc baselineInstalledState)
    (UnfilteredTransfer.filtered baselineMachineConfig lab) t related
  rw [← agreement.pc] at relation
  have postTie := oracleTie_shiftInterfer baselineMachineConfig (baselineInitialState input)
    post lab bootstrapSteps ⟨tied, fun k => by
      rw [Nat.add_comm k bootstrapSteps]
      exact search k⟩
  have identity := shiftInterfer_identity baselineMachineConfig rfl bootstrapSteps
  rw [identity] at postTie
  rw [run]
  exact UnfilteredTransfer.stage5_lab_to_target_affine_not_timeOut baselineMachineConfig rfl
    lab t post code2 labs acc ffis clock compiled safe compiler failed relation postTie
    k_lab notError notTimeout

/-- Halting specialization of the concrete transfer. -/
theorem stage5_lab_halt_to_target {F : Type}
    (input : Guest.InputBlob) (lab : LabSem.State 64 Config F) (t : AsmState 64)
    (code2 : LabProgHOL 64) (labs acc : Spt (Spt Nat))
    (ffis : List HolFfiName) (clock : Nat)
    (compiled : removeLabels clock riscvConfig 0 acc ffis (LabFilter.filterSkip lab.code) =
      some (code2, labs))
    (safe : LabProps.noInstall lab.code)
    (compiler : lab.compile = compile baselineMachineConfig.target.config)
    (failed : lab.failed = false)
    (related : LabToTarget.stateRel
      (baselineMachineConfig, code2, labs,
        baselineMachineConfig.target.getPc baselineInstalledState)
      (UnfilteredTransfer.filtered baselineMachineConfig lab) t baselineInstalledState)
    (tied : oracleTie baselineMachineConfig (baselineInitialState input) lab)
    (k_lab : Nat) (outcome : HolOutcome)
    (halt : (LabSem.evaluate {lab with clock := k_lab}).1 = .halt outcome) :
    (evaluateTargetHOL baselineMachineConfig lab.ffi
      (bootstrapSteps + 9 * (k_lab + 1)) (baselineInitialState input)).1 ≠ .timeOut := by
  apply stage5_lab_to_target_affine_not_timeOut input lab t code2 labs acc ffis clock
    compiled safe compiler failed related tied k_lab
  · rw [halt]; intro impossible; cases impossible
  · rw [halt]; intro impossible; cases impossible

#print axioms stage5_lab_to_target_affine_not_timeOut
#print axioms stage5_lab_halt_to_target
end InitECandidate.Solver.Wave8Stage.ConcreteBaseline
