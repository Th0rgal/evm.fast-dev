import InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.PanInstallationCore

open scoped InitECandidate.Proofs.CompilerComputation
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation

/-! ## Section PanInstallation -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitECandidate.Solver.Wave8GuestInv.ArtifactEnv
open InitE InitECandidate.Proofs
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Pancake.Proofs.PanToTarget
set_option maxRecDepth 10000 in
theorem baseline_mmio_projection : baselineLabConfig.shmemExtra = baselineMmio := by decide_cbv

set_option maxRecDepth 10000 in
theorem baseline_pan_installed_metadata :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      baselineLabConfig.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineLabConfig.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ sourceMemory) ordinaryDomain sharedDomain := by
  have hregs : heapRegs pancakeRiscVBackendConfig.stackConf.regNames = (11,13) := by
    unfold pancakeRiscVBackendConfig
    rw [riscvBackendConfig_eq_executable]
    decide_cbv
  exact panInstalled_metadata_congr _ _ _ _ _ (some baselineNames) _ (11,13)
    _ _ baselineMmio _ _ (wlabWlocExact ∘ sourceMemory) _ ordinaryDomain _ sharedDomain
    baseline_installation_metadata.1 hregs baseline_mmio_projection rfl rfl rfl baseline_pan_installed_core

/-- Every compiler installation premise is certified after the bootstrap. -/
theorem baseline_pan_installed (input : Guest.InputBlob) :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      baselineLabConfig.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineLabConfig.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
  exact panInstalled_metadata_congr _ _ _ _ _ baselineLabConfig.ffiNames
    _ (heapRegs pancakeRiscVBackendConfig.stackConf.regNames) _ _ baselineLabConfig.shmemExtra
    _ _ (wlabWlocExact ∘ sourceMemory) _ ordinaryDomain _ sharedDomain
    rfl rfl rfl rfl (source_memory_domain input) rfl baseline_pan_installed_metadata

end InitECandidate.Solver.Wave8GuestInv.ArtifactEnv


#print axioms InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baseline_mmio_projection
#print axioms InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baseline_pan_installed_metadata
#print axioms InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baseline_pan_installed
