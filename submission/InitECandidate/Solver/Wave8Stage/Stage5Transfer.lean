import InitECandidate.Solver.Wave8Stage.InitializedTransfer
import Flapjack.Compiler.Backend.LabSem.Semantics

/-! Stage 5 entry point for the unfiltered initialized Lab state. The target
clock includes the exact bootstrap prefix and nine instructions per Lab tick.
The full target relation is derived at the installed PC by `InitializedTransfer`.
-/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target RiscV.L3
open InitializedTransfer

/-- Semantic nonfailure excludes error at every finite Lab clock. This is
separate from the non-timeout conclusion supplied by Stages 1–4. -/
theorem lab_run_not_error_of_nonfail {width : Nat} [NeZero width] {C F : Type}
    (lab : LabSem.State width C F) (nonfail : LabSem.semantics lab ≠ .fail) (k : Nat) :
    (LabSem.evaluate {lab with clock := k}).1 ≠ .error := by
  intro error
  apply nonfail
  unfold LabSem.semantics
  rw [if_pos ⟨k, error⟩]

/-- Full initialized Stage 5 transfer including the bootstrap prefix. `init`
is the standard upstream installation contract, with no state-relation,
numerical instruction-bound or target-suffix-run premise. The relation proved by
the initializer uses `mc.target.getPc installed`, never the code-buffer end.
-/
theorem stage5_lab_to_target_affine_not_timeOut {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (initial installed : riscv_state) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : Initialization mc installed code code2 labs clock i cbspace t m dm sdm coracle
      names info shiftedInfo)
    (safe : LabProps.noInstall code) (k_lab : Nat)
    (notError : (LabSem.evaluate
      {initialLab mc installed ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate
      {initialLab mc installed ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 ≠ .timeOut)
    (bootstrap : Nat)
    (bootstrapRun : ∀ fuel, evaluateTargetHOL mc ffi (bootstrap + fuel) initial =
      evaluateTargetHOL mc ffi fuel installed) :
    (evaluateTargetHOL mc ffi (bootstrap + 9 * (k_lab + 1)) initial).1 ≠ .timeOut := by
  rw [bootstrapRun]
  exact initialized_not_timeOut mc target installed ffi code code2 labs clock i cbspace t m dm sdm
    coracle names info shiftedInfo init safe k_lab notError notTimeout

end InitECandidate.Solver.Wave8Stage
