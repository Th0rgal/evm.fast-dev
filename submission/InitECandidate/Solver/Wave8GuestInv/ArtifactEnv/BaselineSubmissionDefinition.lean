import InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.StartupEnvironment

open scoped InitECandidate.Proofs.CompilerComputation
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation

/-! ## Section BaselineSubmissionDefinition -/

namespace InitECandidate.Solver.Wave8GuestInv.ArtifactEnv
open InitE InitECandidate.Proofs
open Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend.LabToTarget

def baselineSubmission : Submission :=
  { code := InitECandidate.code, K := .infinity
    anchorPc := nativePc, names := baselineNames, first := 2, extra := baselineMmio }

theorem baselineSubmission_machineConfig : baselineSubmission.machineConfig = baselineMachineConfig := rfl

theorem baseline_pureMemory : romMemory InitECandidate.code = initialMemory := rfl

theorem baselineSubmission_memory (input : Guest.InputBlob) :
    baselineSubmission.initialMemory input = (fun a =>
      if machineSharedDomain a then byteToBits ((Guest.guestHostMemory input a).getD 0)
      else initialMemory a) := by
  have h := submission_record_memory InitECandidate.code .infinity nativePc baselineNames 2 baselineMmio input
  rw [baseline_pureMemory] at h
  have hd : submissionSharedDomain = machineSharedDomain := rfl
  unfold hostOverlay at h
  rw [hd] at h
  exact h

theorem baselineSubmission_initialState (input : Guest.InputBlob) :
    baselineSubmission.initialState input = baselineInitialState input := by
  unfold Submission.initialState
  rw [baselineSubmission_memory]
  rfl



end InitECandidate.Solver.Wave8GuestInv.ArtifactEnv


