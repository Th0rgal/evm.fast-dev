import InitECandidate.Solver.Wave8Stage.ConcreteBaseline.Transfer

/-! Concrete initialization uses register oracles of the actual submitted
machine run. The code-buffer PC remains the native entry plus emitted bytes. -/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteBaseline.Initialized
open InitE InitECandidate.Proofs
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target RiscV.L3

/-- Standard unfiltered Lab initializer, with oracles for the actual submitted
machine and code buffer based at the actual native entry. -/
noncomputable def initialLab {F : Type}
    (input : Guest.InputBlob) (ffi : HolFfiState F)
    (code : LabProgHOL 64) (bytes : List (BitVec 8)) (cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64) : LabSem.State 64 Config F :=
  makeInit baselineMachineConfig ffi t m dm sdm (baselineInitialState input) code
    (compile baselineMachineConfig.target.config)
    (baselineMachineConfig.target.getPc baselineInstalledState + BitVec.ofNat 64 bytes.length)
    cbspace coracle

/-- The full relation ignores the four register oracle fields; their separate
tie is to the actual initial run and is transported through startup. -/
theorem initialized_stateRel {F : Type}
    (input : Guest.InputBlob) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : InitializedTransfer.Initialization baselineMachineConfig baselineInstalledState
      code code2 labs clock i cbspace t m dm sdm coracle names info shiftedInfo) :
    LabToTarget.stateRel
      (baselineMachineConfig, code2, labs,
        baselineMachineConfig.target.getPc baselineInstalledState)
      (UnfilteredTransfer.filtered baselineMachineConfig
        (initialLab input ffi code (progToBytes code2) cbspace t m dm sdm coracle))
      t baselineInstalledState := by
  exact InitializedTransfer.initialized_stateRel baselineMachineConfig baselineInstalledState ffi
    code code2 labs clock i cbspace t m dm sdm coracle names info shiftedInfo init

/-- Concrete startup plus the initialized Lab transfer, with no assumed
state relation, oracle tie, target prefix or canonical endpoint equality. -/
theorem stage5_lab_to_target_affine_not_timeOut {F : Type}
    (input : Guest.InputBlob) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : InitializedTransfer.Initialization baselineMachineConfig baselineInstalledState
      code code2 labs clock i cbspace t m dm sdm coracle names info shiftedInfo)
    (safe : LabProps.noInstall code) (k_lab : Nat)
    (notError : (LabSem.evaluate
      {initialLab input ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate
      {initialLab input ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 ≠ .timeOut) :
    (evaluateTargetHOL baselineMachineConfig ffi
      (bootstrapSteps + 9 * (k_lab + 1)) (baselineInitialState input)).1 ≠ .timeOut := by
  exact ConcreteBaseline.stage5_lab_to_target_affine_not_timeOut input
    (initialLab input ffi code (progToBytes code2) cbspace t m dm sdm coracle) t code2 labs .ln
    (baselineMachineConfig.ffiNames.take i) clock init.2.2.2.2.1 safe rfl rfl
    (initialized_stateRel input ffi code code2 labs clock i cbspace t m dm sdm coracle
      names info shiftedInfo init) ⟨rfl,rfl,rfl,rfl⟩ k_lab notError notTimeout

#print axioms initialized_stateRel
#print axioms stage5_lab_to_target_affine_not_timeOut
end InitECandidate.Solver.Wave8Stage.ConcreteBaseline.Initialized
