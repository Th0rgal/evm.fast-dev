import InitECandidate.Solver.Wave8Stage.UnfilteredTransfer
import Flapjack.Compiler.Backend.LabToTarget.Initialization.InitialStateContracts

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.InitializedTransfer
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Backend.LabProps Compiler.Encoders.Asm Compiler.Encoders.AsmProps
  Compiler.Encoders.RiscV.Target RiscV.L3

/-- The unfiltered initializer used by the frontend/Stack pipeline. -/
noncomputable abbrev initialLab {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ms : riscv_state)
    (ffi : HolFfiState F) (code : LabProgHOL 64) (bytes : List (BitVec 8)) (cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64) : LabSem.State 64 Config F :=
  makeInit mc ffi t m dm sdm ms code (compile mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace coracle

/-- Exactly the fourteen guards of upstream `makeInit_stateRel`, for the
filtered compiler input and filtered oracle. There is no evaluator premise,
state-relation premise, target-fuel premise or numerical instruction bound. -/
def Initialization
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ms : riscv_state)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (newFfiNames : List HolFfiName) (info shiftedInfo : List ShmemInfoNum) : Prop :=
  let source := LabFilter.filterSkip code
  let oracle := fun n => ((coracle n).1, LabFilter.filterSkip (coracle n).2)
  goodCode mc.target.config (.ln : Spt (Spt Nat)) source ∧ mcConfOk mc ∧
  (noShareMemInst source → compilerOracleOk oracle labs (progToBytes code2).length
    mc.target.config mc.ffiNames) ∧
  Misc.listSubset ((findFfiNames source).filter (fun x => match x with
    | .extCall _ => true | _ => false)) (mc.ffiNames.take i) = true ∧
  removeLabels clock mc.target.config 0 .ln (mc.ffiNames.take i) source = some (code2,labs) ∧
  goodInitState mc ms (progToBytes code2) cbspace t m dm sdm ∧
  getShmemInfo code2 0 [] [] = (newFfiNames,info) ∧
  shiftedInfo = info.map (fun rec => { rec with
    entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
    exitPc := (mc.target.getPc ms).toNat + rec.exitPc }) ∧
  mc.ffiNames.drop i = newFfiNames ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
  shiftedInfo.map ShmemInfoNum.entryPc = (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
  mc.mmioInfo = List.zip ((List.range shiftedInfo.length).map (fun index => index+i))
    (shiftedInfo.map (fun rec => (rec.nbytes,
      HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff), rec.reg,
      BitVec.ofNat 64 rec.exitPc))) ∧
  noInstallOrNoShareMem source mc.ffiNames ∧
  (∀ bn, bn < cbspace → BitVec.ofNat 64 bn + BitVec.ofNat 64 (progToBytes code2).length +
    mc.target.getPc ms ∉ mc.ffiEntryPcs.take i)

/-- Derive the genuine full relation at the true code base from initialization.
The code-buffer position alone includes the byte-image shift. -/
theorem initialized_stateRel {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ms : riscv_state) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : Initialization mc ms code code2 labs clock i cbspace t m dm sdm coracle
      names info shiftedInfo) :
    LabToTarget.stateRel (mc, code2, labs, mc.target.getPc ms)
      (UnfilteredTransfer.filtered mc
        (initialLab mc ms ffi code (progToBytes code2) cbspace t m dm sdm coracle)) t ms := by
  have rel := makeInit_stateRel (G := Nat) mc ms ffi (LabFilter.filterSkip code) code2 labs
    clock i cbspace t m dm sdm
    (fun n => ((coracle n).1, LabFilter.filterSkip (coracle n).2)) names info shiftedInfo init
  have zero : LabFilter.Proofs.adjustPc 0 code = 0 := by
    rw [LabFilter.Proofs.adjustPc.eq_def]
    simp
  simpa only [UnfilteredTransfer.filtered, initialLab, makeInit, zero] using rel

/-- Quantitative transfer from the actual unfiltered initializer, deriving the
full true-base state relation internally from the standard installation guards. -/
theorem initialized_not_timeOut {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (ms : riscv_state) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : Initialization mc ms code code2 labs clock i cbspace t m dm sdm coracle
      names info shiftedInfo)
    (safe : LabProps.noInstall code) (k_lab : Nat)
    (notError : (LabSem.evaluate
      {initialLab mc ms ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate
      {initialLab mc ms ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi (9 * (k_lab + 1)) ms).1 ≠ .timeOut := by
  have related := initialized_stateRel mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle names info shiftedInfo init
  have compiled := init.2.2.2.2.1
  rw [target] at compiled
  exact UnfilteredTransfer.stage5_lab_to_target_affine_not_timeOut mc target
    (initialLab mc ms ffi code (progToBytes code2) cbspace t m dm sdm coracle) t ms code2 labs .ln
    (mc.ffiNames.take i) clock compiled safe rfl rfl related
    (oracleTie_makeInit mc ffi t m dm sdm ms code (compile mc.target.config) _ cbspace coracle)
    k_lab notError notTimeout

/-- Main initialized Stage 5 halt-to-target transfer. Every relation premise is
proved by the initializer; the source clock is consumed with slope nine. -/
theorem stage5_lab_to_target_affine_not_timeOut {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (ms : riscv_state) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : Initialization mc ms code code2 labs clock i cbspace t m dm sdm coracle
      names info shiftedInfo)
    (safe : LabProps.noInstall code) (k_lab : Nat) (outcome : HolOutcome)
    (halt : (LabSem.evaluate
      {initialLab mc ms ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 = .halt outcome) :
    (evaluateTargetHOL mc ffi (9 * (k_lab + 1)) ms).1 ≠ .timeOut := by
  apply initialized_not_timeOut mc target ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle names info shiftedInfo init safe k_lab
  · rw [halt]; intro impossible; cases impossible
  · rw [halt]; intro impossible; cases impossible

#print axioms initialized_stateRel
#print axioms initialized_not_timeOut
#print axioms stage5_lab_to_target_affine_not_timeOut
end InitECandidate.Solver.Wave8Stage.InitializedTransfer
