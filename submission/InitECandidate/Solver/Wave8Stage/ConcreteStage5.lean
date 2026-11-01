import InitECandidate.Solver.Wave8Stage.ConcreteBaseline.InitializedTransfer

/-! Corrected concrete Stage 5 halt-transfer interface. The initialized Lab
state uses oracles from the actual initial target run, the relation uses the
true native entry 0x80001070, and startup is proved with its exact cost. -/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteStage5
open InitE InitECandidate.Proofs
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target RiscV.L3
open ConcreteBaseline

/-- A completed initialized Lab run transfers through the real submitted
bootstrap with slope nine. The fourteen standard installation guards are
explicit; no bootstrap run, oracle tie, or state relation is assumed. -/
theorem stage5_lab_to_target_affine_not_timeOut {F : Type}
    (input : Guest.InputBlob) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : InitializedTransfer.Initialization baselineMachineConfig baselineInstalledState
      code code2 labs clock i cbspace t m dm sdm coracle names info shiftedInfo)
    (safe : LabProps.noInstall code) (k_lab : Nat) (outcome : HolOutcome)
    (halt : (LabSem.evaluate
      {Initialized.initialLab input ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 = .halt outcome) :
    (evaluateTargetHOL baselineMachineConfig ffi
      (23077 + 9 * (k_lab + 1)) (baselineInitialState input)).1 ≠ .timeOut := by
  rw [← bootstrapSteps_eq]
  apply Initialized.stage5_lab_to_target_affine_not_timeOut input ffi code code2 labs
    clock i cbspace t m dm sdm coracle names info shiftedInfo init safe k_lab
  · rw [halt]; intro impossible; cases impossible
  · rw [halt]; intro impossible; cases impossible

#print axioms stage5_lab_to_target_affine_not_timeOut
end InitECandidate.Solver.Wave8Stage.ConcreteStage5
