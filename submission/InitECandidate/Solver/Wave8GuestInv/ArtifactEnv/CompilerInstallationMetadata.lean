import InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.BaselineSubmission

open scoped InitECandidate.Proofs.CompilerComputation
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation

/-! ## Section CompilerInstallationMetadata -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitECandidate.Solver.Wave8GuestInv.ArtifactEnv
open InitE InitECandidate.Proofs
open InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend.LabToTarget

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem baseline_installation_metadata :
    baselineLabConfig.ffiNames = some baselineNames ∧
    baselineMmio.map (fun rec => nativePc+rec.entryPc) =
      (baselineEntryPcs.map BitVec.toNat).drop 2 ∧
    3788+InitECandidate.nativeCode.length+ffiOffset*(2+3) < 2^64 := by
  rw [LiteralFacts.nativeCode_length]
  decide_cbv

end InitECandidate.Solver.Wave8GuestInv.ArtifactEnv


#print axioms InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baseline_installation_metadata
