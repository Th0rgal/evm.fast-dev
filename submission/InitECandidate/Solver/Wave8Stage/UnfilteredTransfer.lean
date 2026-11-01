import InitECandidate.Solver.Wave8Stage.AffineTransfer
import Flapjack.Compiler.Backend.LabFilter.Proofs.Semantics
import Flapjack.Compiler.Backend.LabToTarget.FilterSkipSafety

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.UnfilteredTransfer
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Backend.LabProps Compiler.Encoders.Asm Compiler.Encoders.AsmProps
  Compiler.Encoders.RiscV.Target RiscV.L3

/-- The actual skip-filter state transformation. Its compiler is `compileLab`;
the unfiltered state retains the ordinary `compile` function. -/
noncomputable def filtered {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (lab : LabSem.State width Config F) :
    LabSem.State width Config F :=
  { lab with
    code := LabFilter.filterSkip lab.code
    pc := LabFilter.Proofs.adjustPc lab.pc lab.code
    compile := compileLab mc.target.config
    compileOracle := fun n => ((lab.compileOracle n).1,
      LabFilter.filterSkip (lab.compileOracle n).2) }

/-- Forward skip-filter transport at the same clock, derived from the full
reverse simulation and stability of an already completed unfiltered run. -/
theorem filter_observation {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (lab : LabSem.State width Config F)
    (compiler : lab.compile = compile mc.target.config) (failed : lab.failed = false)
    (k : Nat) (completed : (LabSem.evaluate {lab with clock := k}).1 ≠ .timeOut) :
    (LabSem.evaluate {filtered mc lab with clock := k}).1 =
      (LabSem.evaluate {lab with clock := k}).1 ∧
    (LabSem.evaluate {filtered mc lab with clock := k}).2.ffi =
      (LabSem.evaluate {lab with clock := k}).2.ffi := by
  have rel : LabFilter.Proofs.stateRel {filtered mc lab with clock := k} {lab with clock := k} :=
    ⟨⟨compileLab mc.target.config, rfl, compiler⟩, failed⟩
  obtain ⟨extra, post, run, ffi⟩ := LabFilter.Proofs.filterCorrect
    {filtered mc lab with clock := k} {lab with clock := k} _ _ ⟨rfl, rel, failed⟩
  have extended := evaluateAddClock {lab with clock := k} _ _ extra ⟨rfl, completed⟩
  rw [extended] at run
  have results := congrArg Prod.fst run
  have states := congrArg Prod.snd run
  exact ⟨results.symm, ffi.trans (congrArg LabSem.State.ffi states).symm⟩

theorem noInstall_filterSkip {width : Nat} [NeZero width] (code : LabProgHOL width)
    (safe : LabProps.noInstall code) : LabProps.noInstall (LabFilter.filterSkip code) := by
  intro pc w bytes n fetch
  obtain ⟨pc', original⟩ := LabToTarget.FilterSkip.asmFetchAuxFilterSkip code pc
    (.labAsm .install w bytes n) ⟨fetch, rfl⟩
  exact safe pc' w bytes n original

/-- Stage 5 consumes the unfiltered Lab run produced by Stage 4. The relation
is to the genuine filtered initialization at the true installed PC. -/
theorem stage5_lab_to_target_affine_not_timeOut {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (lab : LabSem.State 64 Config F) (t : AsmState 64) (ms : riscv_state)
    (code2 : LabProgHOL 64) (labs acc : Spt (Spt Nat)) (ffis : List HolFfiName) (clock : Nat)
    (compiled : removeLabels clock riscvConfig 0 acc ffis (LabFilter.filterSkip lab.code) =
      some (code2, labs))
    (safe : LabProps.noInstall lab.code)
    (compiler : lab.compile = compile mc.target.config) (failed : lab.failed = false)
    (related : LabToTarget.stateRel (mc, code2, labs, mc.target.getPc ms) (filtered mc lab) t ms)
    (tied : oracleTie mc ms lab) (k_lab : Nat)
    (notError : (LabSem.evaluate {lab with clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate {lab with clock := k_lab}).1 ≠ .timeOut) :
    (evaluateTargetHOL mc lab.ffi (9 * (k_lab + 1)) ms).1 ≠ .timeOut := by
  have observation := filter_observation mc lab compiler failed k_lab notTimeout
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, similar, _⟩ := id related
  have targetSafe : LabProps.noInstall code2 :=
    CanonicalRuntime.noInstall_similar code2 _ (codeSimilar_sym _ _ similar)
      (noInstall_filterSkip lab.code safe)
  exact AffineTransfer.stage5_lab_to_target_affine_not_timeOut mc target (filtered mc lab) t ms
    (LabFilter.filterSkip lab.code) code2 labs acc ffis clock compiled targetSafe related tied
    k_lab (observation.1 ▸ notError) (observation.1 ▸ notTimeout)

/-- The bootstrap prefix adds its exact cost to the Stage 5 affine bound. -/
theorem stage5_after_bootstrap_not_timeOut {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState F)
    (initial installed : riscv_state) (bootstrap k_lab : Nat)
    (bootstrapRun : ∀ fuel, evaluateTargetHOL mc ffi (bootstrap + fuel) initial =
      evaluateTargetHOL mc ffi fuel installed)
    (post : (evaluateTargetHOL mc ffi (9 * (k_lab + 1)) installed).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi (bootstrap + 9 * (k_lab + 1)) initial).1 ≠ .timeOut := by
  rw [bootstrapRun]
  exact post

#print axioms filter_observation
#print axioms stage5_lab_to_target_affine_not_timeOut
#print axioms stage5_after_bootstrap_not_timeOut
end InitECandidate.Solver.Wave8Stage.UnfilteredTransfer
