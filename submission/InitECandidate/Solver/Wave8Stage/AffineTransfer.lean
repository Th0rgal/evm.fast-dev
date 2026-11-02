import InitECandidate.Solver.Wave8Stage.QuantitativeAssembly
import InitECandidate.Solver.Wave8Stage.CanonicalRuntime
import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClock

/-! Quantitative transfer for the full Lab and RISC-V semantics. The code base
is the actual installed PC. Canonical compilation supplies the padding bound;
no numerical simulation premise is supplied by the caller. -/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.AffineTransfer
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Backend.LabProps Compiler.Encoders.Asm Compiler.Encoders.AsmProps
  Compiler.Encoders.RiscV.Target
  RiscV.L3

/-- A checked non-error/non-timeout Lab run transfers at slope nine, retaining
its exact result and FFI. The base is `mc.target.getPc ms`, with no image shift. -/
theorem lab_to_target_affine_run {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (lab : LabSem.State 64 Config F) (t : AsmState 64) (ms : riscv_state)
    (source code2 : LabProgHOL 64) (labs acc : Spt (Spt Nat))
    (ffis : List HolFfiName) (clock : Nat)
    (compiled : removeLabels clock riscvConfig 0 acc ffis source = some (code2, labs))
    (safe : LabProps.noInstall code2)
    (related : LabToTarget.stateRel (mc, code2, labs, mc.target.getPc ms) lab t ms)
    (tied : oracleTie mc ms lab)
    (k_lab : Nat) (result : MachineResult) (post : LabSem.State 64 Config F)
    (run : LabSem.evaluate {lab with clock := k_lab} = (result, post))
    (notError : result ≠ .error) (notTimeout : result ≠ .timeOut) :
    ∃ ms2, evaluateTargetHOL mc lab.ffi (9 * (k_lab + 1)) ms = (result, ms2, post.ffi) := by
  have bounded : Quantitative.CodeBound mc.target code2 := by
    rw [target]
    exact CanonicalRuntime.codeBound code2
      (CanonicalLineBounds.removeLabels_bound clock 0 acc ffis source code2 labs (by decide) compiled)
      safe
  have enc : encoderCorrect mc.target := by
    rw [target]
    exact Flapjack.RiscV.TargetProof.riscv_encoder_correct
  have tiedClock : oracleTie mc ms {lab with clock := k_lab} := tied
  have relClock := (stateRel_clock (mc, code2, labs, mc.target.getPc ms) lab t ms k_lab).mpr related
  obtain ⟨extra, bound, ms2, simulation⟩ :=
    Quantitative.compileCorrectFor_all {lab with clock := k_lab} result mc post code2 labs t ms
      (mc.target.getPc ms) ⟨tiedClock, run, notError, enc, relClock, bounded⟩
  have fuel : k_lab + extra ≤ 9 * (k_lab + 1) := by simp only at bound; omega
  have extended := evaluateTargetAddClock mc lab.ffi (k_lab + extra) ms
    (9 * (k_lab + 1) - (k_lab + extra)) result ms2 post.ffi simulation notTimeout
  rw [Nat.add_sub_of_le fuel] at extended
  exact ⟨ms2, extended⟩

/-- Stage 5 at the true installed code base. No contradictory shifted-base
relation and no existential target-clock premise is used. -/
theorem stage5_lab_to_target_affine_not_timeOut {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (lab : LabSem.State 64 Config F) (t : AsmState 64) (ms : riscv_state)
    (source code2 : LabProgHOL 64) (labs acc : Spt (Spt Nat))
    (ffis : List HolFfiName) (clock : Nat)
    (compiled : removeLabels clock riscvConfig 0 acc ffis source = some (code2, labs))
    (safe : LabProps.noInstall code2)
    (related : LabToTarget.stateRel (mc, code2, labs, mc.target.getPc ms) lab t ms)
    (tied : oracleTie mc ms lab)
    (k_lab : Nat)
    (notError : (LabSem.evaluate {lab with clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate {lab with clock := k_lab}).1 ≠ .timeOut) :
    (evaluateTargetHOL mc lab.ffi (9 * (k_lab + 1)) ms).1 ≠ .timeOut := by
  obtain ⟨ms2, simulation⟩ := lab_to_target_affine_run mc target lab t ms source code2 labs acc
    ffis clock compiled safe related tied k_lab _ _ rfl notError notTimeout
  simpa only [simulation] using notTimeout

end InitECandidate.Solver.Wave8Stage.AffineTransfer
