import InitECandidate.Proofs.CompilerComputation
import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CompilerConfigLiteral
import InitECandidate.Proofs.BootstrapMemory
import InitECandidate.Proofs.LiteralFacts
import InitECandidate.Proofs.MachineWordMemory
import InitECandidate.Proofs.BitmapImageFacts
import InitECandidate.Proofs.MachineConfigurationFields
import InitECandidate.Proofs.PanInstallationConstructor
import InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation.Separation
import InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation.Ordinary
import InitE.SubmissionInitialization
import InitE.SubmissionAdmission
import Flapjack.Compiler.Backend.Semantics.TargetSem.InitializationContracts
import Flapjack.Pancake.Proofs.PanToTarget.PanInstalled

open scoped InitECandidate.Proofs.CompilerComputation
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation

/-! ## Section BaselineMetadata -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitECandidate.Solver.Wave8GuestInv.ArtifactEnv
open InitE InitECandidate.Proofs
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Misc

@[irreducible] def baselineNames : List HolFfiName := baselineLabConfig.ffiNames.getD []
@[irreducible] def baselineMmio : List ShmemInfoNum := baselineLabConfig.shmemExtra

def dispatchAddress (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((1+i)*ffiOffset)

def baselineEntryPcs : List (BitVec 64) :=
  ((List.range 2).map fun i => BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((3+i)*ffiOffset)) ++
    (baselineMmio.map fun rec => BitVec.ofNat 64 nativePc + BitVec.ofNat 64 rec.entryPc)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem baseline_finite_facts :
    ffiNameBoundaryValid baselineNames 2 ∧
    (∀ i : Fin baselineNames.length, 2 ≤ i.val →
      mmioRecordValid (BitVec.ofNat 64 nativePc) 2 baselineMmio i.val = true) ∧
    (∀ i : Fin 2, findIndex
      (BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((3+i.val)*ffiOffset))
      baselineEntryPcs 0 = some i.val) ∧
    (∀ i : Fin baselineEntryPcs.length, 2 ≤ i.val →
      dispatchAddress 0 ≠ baselineEntryPcs[i] ∧ dispatchAddress 1 ≠ baselineEntryPcs[i]) ∧
    baselineNames.length = baselineEntryPcs.length := by
  unfold ffiNameBoundaryValid baselineEntryPcs baselineNames baselineMmio baselineLabConfig
  exact of_decide_eq_true (by kernel_rfl)

end InitECandidate.Solver.Wave8GuestInv.ArtifactEnv


